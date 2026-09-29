-- Prove2me | solution 1 for Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/908703dd-cf06-5add-9daa-91558b895c64

import Definitions.Def_IharaIota
import Definitions.Def_Gamma0Away
import Definitions.Def_Gamma0AwayUnitsChar
import Definitions.Def_IharaAmalgam
import Definitions.Def_IharaAmalgamMap
import Definitions.Def_IharaMennickeCarrier
import Theorems.Thm_Ihara_amalgamToGamma0Away_injective
import Theorems.Thm_Ihara_amalgamToGamma0Away_surjective
import Theorems.Thm_Ihara_finite_abelianization_gamma0Away
import Theorems.Thm_Ihara_exists_principalCongruenceAway_le_of_finiteIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_exists_coprime_forall_mem_Gamma_apply_eq_zero
p2m_attr_erase "simp" "Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply"

open scoped MatrixGroups

set_option autoImplicit false

namespace IharaCoefficients

open Ihara CongruenceSubgroup

private def toMul {Γ : Type*} [Group Γ] {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) :
    Γ →* Multiplicative A where
  toFun g := Multiplicative.ofAdd (φ (Additive.ofMul g))
  map_one' := by simp
  map_mul' a b := by simp [ofMul_mul, map_add, ofAdd_add]

private theorem toMul_apply {Γ : Type*} [Group Γ] {A : Type*} [AddCommGroup A]
    (φ : Additive Γ →+ A) (g : Γ) :
    toMul φ g = Multiplicative.ofAdd (φ (Additive.ofMul g)) := rfl

private theorem vertexZero_eq (N q : ℕ) (g : Gamma0 N) :
    (⟨vertexZero N q g, vertexZero_mem N q g⟩ : ↥(Gamma0Away N q)) =
      amalgamToGamma0Away N q (iharaVertex N q 0 g) :=
  Subtype.ext (by rw [coe_amalgamToGamma0Away, amalgamToAway_vertex_zero])

private theorem vertexOne_eq (N q : ℕ) (g : Gamma0 N) :
    (⟨vertexOne N q g, vertexOne_mem N q g⟩ : ↥(Gamma0Away N q)) =
      amalgamToGamma0Away N q (iharaVertex N q 1 g) :=
  Subtype.ext (by rw [coe_amalgamToGamma0Away, amalgamToAway_vertex_one])

private theorem step1_lift (N q : ℕ) (A : Type*) [AddCommGroup A]
    (φ ψ : Additive (Gamma0 N) →+ A)
    (hker : ∀ γ : Gamma0 (N * q),
      φ (Additive.ofMul (ι₀ N q γ)) + ψ (Additive.ofMul (ι₁ N q γ)) = 0)
    (hinj : Function.Injective (amalgamToGamma0Away N q))
    (hsurj : Function.Surjective (amalgamToGamma0Away N q)) :
    ∃ Φ : ↥(Gamma0Away N q) →* Multiplicative A,
      (∀ g : Gamma0 N, Φ ⟨vertexZero N q g, vertexZero_mem N q g⟩ =
          Multiplicative.ofAdd (φ (Additive.ofMul g))) ∧
      (∀ g : Gamma0 N, Φ ⟨vertexOne N q g, vertexOne_mem N q g⟩ =
          Multiplicative.ofAdd (-ψ (Additive.ofMul g))) := by
  have hcompat : (toMul φ).comp (ι₀ N q) = (toMul (-ψ)).comp (ι₁ N q) := by
    ext γ
    simp only [MonoidHom.comp_apply, toMul_apply, AddMonoidHom.neg_apply]
    congr 1
    exact eq_neg_of_add_eq_zero_left (hker γ)
  let e : iharaAmalgam N q ≃* ↥(Gamma0Away N q) :=
    MulEquiv.ofBijective (amalgamToGamma0Away N q) ⟨hinj, hsurj⟩
  have he : ∀ x : iharaAmalgam N q, e.symm (amalgamToGamma0Away N q x) = x := fun x =>
    e.symm_apply_apply x
  refine ⟨(iharaLift (toMul φ) (toMul (-ψ)) hcompat).comp e.symm.toMonoidHom, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, vertexZero_eq, he, iharaLift_vertex_zero,
      toMul_apply]
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, vertexOne_eq, he, iharaLift_vertex_one,
      toMul_apply, AddMonoidHom.neg_apply]

private theorem step2_index_ker_ne_zero (G : Type*) [Group G] (A : Type*) [AddCommGroup A]
    (hfin : Finite (Abelianization G)) (Φ : G →* Multiplicative A) : Φ.ker.index ≠ 0 := by
  have hcomm : (commutator G).index ≠ 0 := by
    haveI : Finite (G ⧸ commutator G) := hfin
    show Nat.card (G ⧸ commutator G) ≠ 0
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hcomm (Subgroup.index_dvd_of_le (Abelianization.commutator_subset_ker Φ))

private theorem natCast_dvd_of_zAwayToZMod_eq_zero (N q : ℕ) (hNq : Nat.Coprime N q) {z : ZAway q}
    (hz : zAwayToZMod N q hNq z = 0) : (N : ZAway q) ∣ z := by
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (q : ℤ)) z
  simp only at h
  have ha : ((a : ℤ) : ZMod N) = 0 := by
    have h' := congrArg (zAwayToZMod N q hNq) h
    rw [map_mul, hz, zero_mul, zAwayToZMod_algebraMap] at h'
    exact h'.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a N).mp ha
  have hs : IsUnit (algebraMap ℤ (ZAway q) s) := IsLocalization.map_units (ZAway q) s
  refine ⟨algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹, ?_⟩
  have hN : (N : ZAway q) = algebraMap ℤ (ZAway q) (N : ℤ) := by simp
  calc z = z * algebraMap ℤ (ZAway q) s * ↑hs.unit⁻¹ := by
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
    _ = algebraMap ℤ (ZAway q) a * ↑hs.unit⁻¹ := by rw [h]
    _ = (N : ZAway q) * (algebraMap ℤ (ZAway q) b * ↑hs.unit⁻¹) := by
        rw [hb, map_mul, hN, mul_assoc]

private theorem principalCongruenceAway_le_gamma0Away (N q : ℕ) (hNq : Nat.Coprime N q) :
    principalCongruenceAway N q hNq ≤ Gamma0Away N q := by
  intro g hg
  rw [mem_principalCongruenceAway_iff] at hg
  rw [mem_Gamma0Away]
  refine natCast_dvd_of_zAwayToZMod_eq_zero N q hNq ?_
  have h := congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 0) hg
  simp only [slAwayReduction_coe, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h
  exact h

private theorem step3_finiteIndex_map (N q : ℕ) (hq : q.Prime) (hNq : N.Coprime q)
    (K : Subgroup ↥(Gamma0Away N q)) (hK : K.index ≠ 0) :
    (K.map (Gamma0Away N q).subtype).FiniteIndex := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hq.one_lt.ne' (Nat.coprime_zero_left q |>.mp hNq)
  haveI : NeZero N := ⟨hN0⟩
  have hΓ : (Gamma0Away N q).index ≠ 0 := by
    have hdvd := Subgroup.index_dvd_of_le (principalCongruenceAway_le_gamma0Away N q hNq)
    have hP : (principalCongruenceAway N q hNq).index ≠ 0 := by
      show (slAwayReduction N q hNq).ker.index ≠ 0
      rw [Subgroup.index_ker]
      exact Nat.card_pos.ne'
    exact ne_zero_of_dvd_ne_zero hP hdvd
  exact ⟨by rw [Subgroup.index_map_subtype]; exact Nat.mul_ne_zero hK hΓ⟩

private theorem map_map_eq_one (q M : ℕ) (hMq : Nat.Coprime M q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma M) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ (ZAway q))).map (zAwayToZMod M q hMq) = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.mp hγ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, h00, h01, h10, h11]

private theorem step5_mem_principal (N q M : ℕ) (hMq : Nat.Coprime M q) (g : Gamma0 N)
    (hg : (g : SL(2, ℤ)) ∈ Gamma M) :
    vertexZero N q g ∈ principalCongruenceAway M q hMq ∧
      vertexOne N q g ∈ principalCongruenceAway M q hMq := by
  have h1 := map_map_eq_one q M hMq (g : SL(2, ℤ)) hg
  constructor
  · rw [mem_principalCongruenceAway_iff]
    apply Subtype.ext
    rw [slAwayReduction_coe, coe_vertexZero, Matrix.SpecialLinearGroup.coe_one]
    exact h1
  · rw [mem_principalCongruenceAway_iff]
    apply Subtype.ext
    rw [slAwayReduction_coe, coe_vertexOne, Matrix.SpecialLinearGroup.coe_one, Matrix.map_mul,
      Matrix.map_mul, h1, mul_one, ← Matrix.map_mul, wMat_mul_wMatInv]
    exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem mem_of_coe_mem_map_subtype {q : ℕ} {Γ : Subgroup SL(2, ZAway q)} {K : Subgroup Γ}
    {g : Γ} (h : (g : SL(2, ZAway q)) ∈ K.map Γ.subtype) : g ∈ K := by
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp h
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

private theorem step6_vanish (N q : ℕ) (A : Type*) [AddCommGroup A]
    (φ ψ : Additive (Gamma0 N) →+ A) (Φ : ↥(Gamma0Away N q) →* Multiplicative A)
    (h₀ : ∀ g : Gamma0 N, Φ ⟨vertexZero N q g, vertexZero_mem N q g⟩ =
        Multiplicative.ofAdd (φ (Additive.ofMul g)))
    (h₁ : ∀ g : Gamma0 N, Φ ⟨vertexOne N q g, vertexOne_mem N q g⟩ =
        Multiplicative.ofAdd (-ψ (Additive.ofMul g)))
    (L : Subgroup (SL(2, ZAway q))) (hL : L ≤ Φ.ker.map (Gamma0Away N q).subtype)
    (g : Gamma0 N) (hg₀ : vertexZero N q g ∈ L) (hg₁ : vertexOne N q g ∈ L) :
    φ (Additive.ofMul g) = 0 ∧ ψ (Additive.ofMul g) = 0 := by
  have k₀ : (⟨vertexZero N q g, vertexZero_mem N q g⟩ : ↥(Gamma0Away N q)) ∈ Φ.ker :=
    mem_of_coe_mem_map_subtype (hL hg₀)
  have k₁ : (⟨vertexOne N q g, vertexOne_mem N q g⟩ : ↥(Gamma0Away N q)) ∈ Φ.ker :=
    mem_of_coe_mem_map_subtype (hL hg₁)
  rw [MonoidHom.mem_ker, h₀, ofAdd_eq_one] at k₀
  rw [MonoidHom.mem_ker, h₁, ofAdd_eq_one, neg_eq_zero] at k₁
  exact ⟨k₀, k₁⟩

end IharaCoefficients

open Ihara IharaCoefficients in
theorem solution (N q : ℕ) (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : Type*) [AddCommGroup A]
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      φ (Additive.ofMul (ι₀ N q γ)) + ψ (Additive.ofMul (ι₁ N q γ)) = 0) :
    ∃ M : ℕ, 0 < M ∧ Nat.Coprime M q ∧
      ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
        φ (Additive.ofMul γ) = 0 ∧ ψ (Additive.ofMul γ) = 0 := by
  have hNq : N.Coprime q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm
  obtain ⟨Φ, h₀, h₁⟩ := step1_lift N q A φ ψ hker
    (Ihara.amalgamToGamma0Away_injective hq hNq) (Ihara.amalgamToGamma0Away_surjective N q hNq hq)
  have hK : Φ.ker.index ≠ 0 :=
    step2_index_ker_ne_zero _ A (Ihara.finite_abelianization_gamma0Away hq hNq) Φ
  haveI : (Φ.ker.map (Ihara.Gamma0Away N q).subtype).FiniteIndex :=
    step3_finiteIndex_map N q hq hNq Φ.ker hK
  obtain ⟨M, hMq, hM0, hle⟩ :=
    Ihara.exists_principalCongruenceAway_le_of_finiteIndex hq (Φ.ker.map (Ihara.Gamma0Away N q).subtype)
  refine ⟨M, Nat.pos_of_ne_zero hM0, hMq, fun γ hγ => ?_⟩
  obtain ⟨hγ₀, hγ₁⟩ := step5_mem_principal N q M hMq γ hγ
  exact step6_vanish N q A φ ψ Φ h₀ h₁ (Ihara.principalCongruenceAway M q hMq) hle γ hγ₀ hγ₁

end S_Ihara_exists_coprime_forall_mem_Gamma_apply_eq_zero
end P2MW
export P2MW.S_Ihara_exists_coprime_forall_mem_Gamma_apply_eq_zero (solution)
