-- Prove2me | solution 1 for IntermediateField.inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/88d12821-50c5-5206-bf5f-f074d09d65ef

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr

set_option autoImplicit false

open scoped Pointwise
open NumberField

namespace S15
namespace Bridge

namespace MuInert

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma mem_inertiaSubgroupIn_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K,
        (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

theorem apply_mem_iff {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) (x : L) : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A :=
    MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem apply_sub_self_mem_nonunits {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) {x : L} (hx : x ∈ A) :
    σ x - x ∈ A.nonunits := by
  obtain ⟨hd, hI⟩ := mem_inertiaSubgroupIn_iff.mp hσ
  set a : A := ⟨x, hx⟩
  set g : A.decompositionSubgroup K := ⟨σ, hd⟩
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g = 1 := MonoidHom.mem_ker.mp hI
  have happ : (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A) g) (IsLocalRing.residue A a)
      = g • (IsLocalRing.residue A a) := rfl
  have hres : IsLocalRing.residue A (g • a) = IsLocalRing.residue A a := by
    rw [IsLocalRing.ResidueField.residue_smul, ← happ, hker]
    rfl
  have hmem : g • a - a ∈ IsLocalRing.maximalIdeal A := by
    have h0 : IsLocalRing.residue A (g • a - a) = 0 := by
      rw [map_sub, hres, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hcoe : ((g • a - a : A) : L) = σ x - x := rfl
  have := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hmem
  rwa [hcoe] at this

theorem mul_mem_nonunits {A : ValuationSubring L} {a b : L} (ha : a ∈ A.nonunits) (hb : b ∈ A) :
    a * b ∈ A.nonunits := by
  have ha' : a ∈ A := A.nonunits_subset ha
  have h1 : (⟨a, ha'⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp ha
  have h2 : (⟨a, ha'⟩ * ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.mul_mem_right _ _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

end MuInert

theorem mem_of_isIntegral (P : ValuationSubring (AlgebraicClosure ℚ)) {x : AlgebraicClosure ℚ}
    (hx : IsIntegral ℤ x) : x ∈ P := by

  obtain ⟨f, hf, hfx⟩ := hx
  have hx' : IsIntegral P x := by
    refine ⟨f.map (Int.castRingHom P), hf.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap P (AlgebraicClosure ℚ)).comp (Int.castRingHom P))
        (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hfx
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := P) (K := AlgebraicClosure ℚ)).mp hx'
  rw [← hy]
  exact y.2

open MuInert in
theorem inertia_le_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hFd : FiniteDimensional ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hdisc : haveI : NumberField F := @NumberField.mk _ _ inferInstance hFd;
             ¬ (q : ℤ) ∣ NumberField.discr F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup := by
  classical
  haveI : NumberField F := @NumberField.mk _ _ inferInstance hFd
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  by_contra hne

  set τ₀ : F →ₐ[ℚ] AlgebraicClosure ℚ := F.val with hτ₀
  set τ₁ : F →ₐ[ℚ] AlgebraicClosure ℚ :=
    (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp F.val with hτ₁
  have hτ : τ₁ ≠ τ₀ := by
    intro h
    apply hne
    intro x hx
    have := DFunLike.congr_fun h ⟨x, hx⟩
    simp [hτ₀, hτ₁] at this
    exact this

  set b := integralBasis F with hb
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
      = Fintype.card (F →ₐ[ℚ] AlgebraicClosure ℚ) := by
    rw [AlgHom.card ℚ F (AlgebraicClosure ℚ), Module.finrank_eq_card_basis b]
  set e : Module.Free.ChooseBasisIndex ℤ (𝓞 F) ≃ (F →ₐ[ℚ] AlgebraicClosure ℚ) :=
    Fintype.equivOfCardEq hcard with he
  set M := Algebra.embeddingsMatrixReindex ℚ (AlgebraicClosure ℚ) (⇑b) e with hM
  have hdisc_eq : algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.discr ℚ b) = M.det ^ 2 :=
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ (AlgebraicClosure ℚ) b e
  have hMij : ∀ i j, M i j = (e j) (b i) := by
    intro i j
    simp [hM, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply]

  have hint : ∀ i j, M i j ∈ P := by
    intro i j
    rw [hMij, hb, integralBasis_apply]
    exact mem_of_isIntegral P
      (map_isIntegral_int (e j : F →+* AlgebraicClosure ℚ)
        (RingOfIntegers.isIntegral_coe ((RingOfIntegers.basis F) i)))

  set MP : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) P :=
    fun i j => ⟨M i j, hint i j⟩ with hMP_def
  have hMP : (P.subtype).mapMatrix MP = M := by
    ext i j; rfl
  have hdetP : ((MP.det : P) : AlgebraicClosure ℚ) = M.det := by
    change P.subtype MP.det = M.det
    rw [RingHom.map_det, hMP]

  set j₀ := e.symm τ₀ with hj₀
  set j₁ := e.symm τ₁ with hj₁
  have hj : j₀ ≠ j₁ := fun h => hτ (e.symm.injective h).symm
  have hbP : ∀ i, ((b i : F) : AlgebraicClosure ℚ) ∈ P := by
    intro i
    have := hint i j₀
    rwa [hMij, hj₀, Equiv.apply_symm_apply] at this
  have hcong : ∀ i, IsLocalRing.residue P (MP i j₁) = IsLocalRing.residue P (MP i j₀) := by
    intro i
    apply Ideal.Quotient.eq.mpr
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    have h1 : (((MP i j₁ - MP i j₀ : P)) : AlgebraicClosure ℚ)
        = σ ((b i : F) : AlgebraicClosure ℚ) - ((b i : F) : AlgebraicClosure ℚ) := by
      change M i j₁ - M i j₀ = _
      rw [hMij, hMij, hj₀, hj₁, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
    rw [h1]
    exact apply_sub_self_mem_nonunits hσ (hbP i)

  have hres : IsLocalRing.residue P MP.det = 0 := by
    rw [RingHom.map_det]
    refine Matrix.det_zero_of_column_eq hj (fun k => ?_)
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
    exact (hcong k).symm
  have hdet : M.det ∈ P.nonunits := by
    rw [← hdetP]
    exact ValuationSubring.coe_mem_nonunits_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hres)
  have hdet2 : M.det ^ 2 ∈ P.nonunits := by
    rw [pow_two]
    exact mul_mem_nonunits hdet (P.nonunits_subset hdet)

  have hd : ((NumberField.discr F : ℤ) : AlgebraicClosure ℚ) ∈ P.nonunits := by
    have h1 : ((NumberField.discr F : ℤ) : AlgebraicClosure ℚ)
        = algebraMap ℚ (AlgebraicClosure ℚ) (Algebra.discr ℚ b) := by
      rw [hb, ← coe_discr, map_intCast]
    rw [h1, hdisc_eq]
    exact hdet2

  have hcop : IsCoprime (q : ℤ) (NumberField.discr F) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq).irreducible).mpr hdisc
  obtain ⟨u, w, huw⟩ := hcop
  have hone : (1 : AlgebraicClosure ℚ) ∈ P.nonunits := by
    have e1 : (1 : AlgebraicClosure ℚ)
        = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)
          + ((NumberField.discr F : ℤ) : AlgebraicClosure ℚ) * (w : AlgebraicClosure ℚ) := by
      have := congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) huw
      push_cast at this
      linear_combination -this
    rw [e1]
    exact add_mem (mul_mem_nonunits hP (intCast_mem P.toSubring _))
      (mul_mem_nonunits hd (intCast_mem P.toSubring _))
  rw [ValuationSubring.mem_nonunits_iff, map_one] at hone
  exact lt_irrefl 1 hone

end S15.Bridge

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hdisc : haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›;
             ¬ (q : ℤ) ∣ NumberField.discr F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup :=
  S15.Bridge.inertia_le_fixingSubgroup F q hq hdisc P hP

end S_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
end P2MW
export P2MW.S_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr (solution)
