-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_discRiders_of_affineChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/45e83ede-947b-573e-bf38-d11bb83482e1

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_exists_finite_subgroup_forall_levelAutBar_mem
import Theorems.Thm_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_discRiders_of_affineChart

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace DiscRidersReduce

open Polynomial

theorem mem_iff_mem_range_of_fibre
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφu : φ.FormallyUnramified) (hφf : φ.EssFiniteType)
    (ht : φ X ∈ maximalIdeal S)
    {E : Type} [Field E] (ρ : S →+* E)
    (hker : ∀ f : S, ρ f = 0 ↔ φ (C ϖ) ∣ f)
    (ht0 : ρ (φ X) ≠ 0)
    (V : ValuationSubring E) (hV : ∀ f : S, ρ f ∈ V)
    (hcen : ∀ f : S, f ∈ maximalIdeal S → IsLocalRing.residue ↥V ⟨ρ f, hV f⟩ = 0)
    (hfrac : ∀ x : E, ∃ a b : S, ρ b ≠ 0 ∧ x * ρ b = ρ a) :
    ∀ x : E, x ∈ V ↔ x ∈ Set.range ρ := by
  classical
  let T : Subring E := ρ.range
  let π : S →+* ↥T := ρ.rangeRestrict
  have hπ : Function.Surjective π := ρ.rangeRestrict_surjective
  have hcoe : ∀ f : S, ((π f : ↥T) : E) = ρ f := fun f => rfl
  have hTV : ∀ y : ↥T, (y : E) ∈ V := by
    intro y
    obtain ⟨f, hf⟩ := RingHom.mem_range.mp y.2
    rw [← hf]
    exact hV f
  have hkerπ : RingHom.ker π = Ideal.span {φ (C ϖ)} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, ← hker f, Subtype.ext_iff, hcoe]
    rfl
  have hT0 : π (φ X) ≠ 0 := by
    intro h
    apply ht0
    rw [← hcoe, h]
    rfl
  obtain ⟨hdvr, -⟩ :=
    IsLocalRing.isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial
      ϖ hϖ φ hφu hφf ht π hπ hkerπ hT0

  have hnonunit : ∀ y : ↥T, ¬ IsUnit y → (⟨(y : E), hTV y⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro y hy
    obtain ⟨f, rfl⟩ := hπ y
    have hf : f ∈ maximalIdeal S := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hy (hu.map π)
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact hcen f hf
  intro x
  constructor
  · intro hx
    by_contra hxT
    obtain ⟨a, b, hb0, hab⟩ := hfrac x
    have ha0 : ρ a ≠ 0 := by
      intro ha
      apply hxT
      have hx0 : x = 0 := (mul_eq_zero.mp (hab.trans ha)).resolve_right hb0
      exact ⟨0, by rw [hx0, map_zero]⟩
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible ↥T
    have hπa : π a ≠ 0 := fun h => ha0 (by rw [← hcoe, h]; rfl)
    have hπb : π b ≠ 0 := fun h => hb0 (by rw [← hcoe, h]; rfl)
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπa hp
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπb hp
    have hp0 : (p : E) ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
    have hua : ρ a = ((u : ↥T) : E) * (p : E) ^ m := by
      rw [← hcoe a, hu]; push_cast; ring
    have hvb : ρ b = ((v : ↥T) : E) * (p : E) ^ n := by
      rw [← hcoe b, hv]; push_cast; ring
    rcases Nat.lt_or_ge m n with hmn | hnm
    swap
    ·
      apply hxT
      let w : ↥T := (u : ↥T) * ↑(v⁻¹) * p ^ (m - n)
      have hvinv : (((↑(v⁻¹) : ↥T)) : E) * ((v : ↥T) : E) = 1 := by
        have h := congrArg (fun z : ↥T => (z : E)) v.inv_mul
        push_cast at h
        exact h
      have key : (w : E) * ρ b = ρ a := by
        rw [hua, hvb]
        simp only [w]
        push_cast
        calc ((u : ↥T) : E) * ((↑(v⁻¹) : ↥T) : E) * (p : E) ^ (m - n) * (((v : ↥T) : E) * (p : E) ^ n)
            = ((u : ↥T) : E) * ((((↑(v⁻¹) : ↥T)) : E) * ((v : ↥T) : E)) * ((p : E) ^ (m - n) * (p : E) ^ n) := by ring
          _ = ((u : ↥T) : E) * (p : E) ^ m := by rw [hvinv, mul_one, ← pow_add, Nat.sub_add_cancel hnm]
      have hxw : x = (w : E) := mul_right_cancel₀ hb0 (hab.trans key.symm)
      obtain ⟨s, hs⟩ := hπ w
      exact ⟨s, by rw [← hcoe, hs, hxw]⟩
    ·
      let w : ↥T := (v : ↥T) * ↑(u⁻¹) * p ^ (n - m)
      have huinv : ((u : ↥T) : E) * (((↑(u⁻¹) : ↥T)) : E) = 1 := by
        have h := congrArg (fun z : ↥T => (z : E)) u.mul_inv
        push_cast at h
        exact h
      have h1 : x * (((v : ↥T) : E) * (p : E) ^ (n - m)) * (p : E) ^ m = ((u : ↥T) : E) * (p : E) ^ m := by
        calc x * (((v : ↥T) : E) * (p : E) ^ (n - m)) * (p : E) ^ m
            = x * (((v : ↥T) : E) * ((p : E) ^ (n - m) * (p : E) ^ m)) := by ring
          _ = x * (((v : ↥T) : E) * (p : E) ^ n) := by rw [← pow_add, Nat.sub_add_cancel hmn.le]
          _ = ρ a := by rw [← hvb]; exact hab
          _ = _ := hua
      have h2 : x * (((v : ↥T) : E) * (p : E) ^ (n - m)) = ((u : ↥T) : E) :=
        mul_right_cancel₀ (pow_ne_zero m hp0) h1
      have hxw : x * (w : E) = 1 := by
        calc x * (w : E) = x * (((v : ↥T) : E) * (p : E) ^ (n - m)) * (((↑(u⁻¹) : ↥T)) : E) := by
              simp only [w]; push_cast; ring
          _ = 1 := by rw [h2, huinv]
      have hwmax : (⟨(w : E), hTV w⟩ : ↥V) ∈ maximalIdeal ↥V := by
        have hpmax := hnonunit p hp.not_isUnit
        obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
        have hsplit : (⟨(w : E), hTV w⟩ : ↥V) =
            ⟨((((v : ↥T) * ↑(u⁻¹) * p ^ k : ↥T)) : E), hTV _⟩ * ⟨(p : E), hTV p⟩ := by
          apply Subtype.ext
          show (w : E) = ((((v : ↥T) * ↑(u⁻¹) * p ^ k : ↥T)) : E) * (p : E)
          simp only [w]
          push_cast
          rw [hk, pow_succ]
          ring
        rw [hsplit]
        exact Ideal.mul_mem_left _ _ hpmax
      have hunit : IsUnit (⟨(w : E), hTV w⟩ : ↥V) :=
        isUnit_iff_exists_inv.mpr ⟨⟨x, hx⟩, Subtype.ext (by show (w : E) * x = 1; rw [mul_comm]; exact hxw)⟩
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hwmax)) hunit
  · rintro ⟨f, rfl⟩
    exact hV f

section Transport
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

def ZR (Q : Place K E) (x : E) : Prop :=
  ∃ hm : x ∈ Q.toValuationSubring, IsLocalRing.residue ↥Q.toValuationSubring ⟨x, hm⟩ = 0

def NV (Q : Place K E) (x : E) : Prop :=
  ∃ hm : x ∈ Q.toValuationSubring, IsLocalRing.residue ↥Q.toValuationSubring ⟨x, hm⟩ ≠ 0

theorem nv_iff_not_zr (Q : Place K E) (x : E) (hm : x ∈ Q.toValuationSubring) : NV Q x ↔ ¬ ZR Q x :=
  ⟨fun ⟨_, h⟩ ⟨_, h'⟩ => h h', fun h => ⟨hm, fun h' => h ⟨hm, h'⟩⟩⟩

theorem zr_smul_iff (σ : E ≃ₐ[K] E) (Q : Place K E) (x : E) : ZR (σ • Q) (σ x) ↔ ZR Q x := by
  constructor
  · rintro ⟨hm, h0⟩
    have hm' : x ∈ Q.toValuationSubring := (Place.Transport.mem_smul_iff' σ Q x).mp hm
    refine ⟨hm', ?_⟩
    rw [Place.Transport.residue_smul σ Q hm' hm] at h0
    exact (map_eq_zero_iff _ (Place.smulResidueAlgEquiv σ Q).injective).mp h0
  · rintro ⟨hm, h0⟩
    have hm' : σ x ∈ (σ • Q).toValuationSubring := (Place.Transport.mem_smul_iff' σ Q x).mpr hm
    refine ⟨hm', ?_⟩
    rw [Place.Transport.residue_smul σ Q hm hm', h0, map_zero]

theorem nv_smul_iff (σ : E ≃ₐ[K] E) (Q : Place K E) (x : E) : NV (σ • Q) (σ x) ↔ NV Q x := by
  constructor
  · rintro ⟨hm, h0⟩
    have hm' : x ∈ Q.toValuationSubring := (Place.Transport.mem_smul_iff' σ Q x).mp hm
    exact (nv_iff_not_zr Q x hm').mpr (fun h => (nv_iff_not_zr _ _ hm).mp ⟨hm, h0⟩ ((zr_smul_iff σ Q x).mpr h))
  · rintro ⟨hm, h0⟩
    have hm' : σ x ∈ (σ • Q).toValuationSubring := (Place.Transport.mem_smul_iff' σ Q x).mpr hm
    exact (nv_iff_not_zr _ _ hm').mpr (fun h => (nv_iff_not_zr Q x hm).mp ⟨hm, h0⟩ ((zr_smul_iff σ Q x).mp h))

theorem ord_nonneg_of_mem (v : Place K E) {f : E} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem evalAt_inv_smul (τ : E ≃ₐ[K] E) (P : Place K E) (hP : P.IsRational) (f : E) :
    (τ⁻¹ • P).evalAt f = P.evalAt (τ f) := by
  have hr : (τ⁻¹ • P).IsRational := (Place.Transport.isRational_smul_iff τ⁻¹ P).mpr hP
  have h := Place.Transport.evalAt_smul τ (τ⁻¹ • P) hr f
  rw [smul_inv_smul] at h
  exact h.symm

end Transport

section Stab
variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem stab_closure (B : Subring F) (Sgen : Set (F ≃ₐ[L] F))
    (hfwd : ∀ s ∈ Sgen, ∀ f ∈ B, s f ∈ B) (hbwd : ∀ s ∈ Sgen, ∀ f ∈ B, s.symm f ∈ B) :
    ∀ τ ∈ Subgroup.closure Sgen, ∀ f, f ∈ B ↔ τ f ∈ B := by
  intro τ hτ
  induction hτ using Subgroup.closure_induction with
  | mem s hs =>
    intro f
    refine ⟨hfwd s hs f, fun h => ?_⟩
    have := hbwd s hs (s f) h
    rwa [AlgEquiv.symm_apply_apply] at this
  | one => intro f; simp
  | mul a b _ _ iha ihb =>
    intro f
    rw [AlgEquiv.mul_apply]
    exact (ihb f).trans (iha (b f))
  | inv a _ iha =>
    intro f
    have h := iha (a.symm f)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [AlgEquiv.aut_inv]
    exact h.symm

theorem symm_mem_of_finite (B : Subring F) (G : Subgroup (F ≃ₐ[L] F)) (hG : Finite ↥G)
    (s : F ≃ₐ[L] F) (hs : s ∈ G) (h : ∀ f ∈ B, s f ∈ B) : ∀ f ∈ B, s.symm f ∈ B := by
  haveI := hG
  have hfin : IsOfFinOrder (⟨s, hs⟩ : ↥G) := isOfFinOrder_of_finite _
  obtain ⟨n, hn, hsn⟩ := hfin.exists_pow_eq_one
  have hsn' : s ^ n = 1 := by
    have := congrArg Subtype.val hsn
    simpa using this
  have hpow : ∀ k : ℕ, ∀ f, f ∈ B → (s ^ k) f ∈ B := by
    intro k
    induction k with
    | zero => intro f hf; simpa using hf
    | succ k ih => intro f hf; rw [pow_succ, AlgEquiv.mul_apply]; exact ih _ (h f hf)
  have hsymm : s.symm = s ^ (n - 1) := by
    have hmul : s * s ^ (n - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hsn'
    rw [← AlgEquiv.aut_inv]
    exact inv_eq_of_mul_eq_one_right hmul
  intro f hf
  rw [hsymm]
  exact hpow _ f hf

end Stab

section UnitLemma
variable {F : Type*} [Field F]

theorem mk_mem_maximalIdeal_iff (S : Subring F) [IsLocalRing ↥S] (f : F) (hf : f ∈ S) :
    (⟨f, hf⟩ : ↥S) ∈ maximalIdeal ↥S ↔ (f = 0 ∨ f⁻¹ ∉ S) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    by_contra h
    push Not at h
    obtain ⟨hf0, hinv⟩ := h
    exact hu (isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩)
  · rintro h ⟨u, hu⟩
    have h1 : f * ((↑(u⁻¹) : ↥S) : F) = 1 := by
      have h2 := congrArg (fun z : ↥S => (z : F)) u.mul_inv
      simp only [hu] at h2
      push_cast at h2
      exact h2
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1
      exact zero_ne_one h1
    rcases h with h | h
    · exact hf0 h
    · apply h
      rw [← (eq_inv_of_mul_eq_one_right h1)]
      exact (↑(u⁻¹) : ↥S).2

end UnitLemma
end DiscRidersReduce

open DiscRidersReduce in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))
      (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) →
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS)
        (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)

        (hfracB : ∀ x : FSS, ∃ g h : ↥B, R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ≠ 0 ∧ x * R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ = R.residue ⟨((g : ↥B) : ↥(fieldBar q M')), hBR _ (g).2⟩)
        (N : Finset (Place (ResidueField ↥A) FSS))
    (hNiff : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔ ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring)
    (hNeqv : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
          (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N))
        (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
        (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
        (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* (ResidueField ↥A)))
        (hS : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

        (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ (Sb Q)) ∧
        (∀ a : ↥Ab, (((φb Q) (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
        (∀ a : ↥Ab, (χb Q) ((φb Q) (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
        (χb Q) ((φb Q) Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ (Sb Q) → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        ((φb Q)).FormallySmooth ∧ ((φb Q)).FormallyUnramified ∧ ((φb Q)).EssFiniteType ∧

        (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ (φb Q) (Polynomial.C ϖb) ∣ f) ∧

        (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField ((χb Q) f)) ∧
        (∃ hR : (((φb Q) Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨(((φb Q) Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ (Sb Q)) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ (Sb Q) ↔ ∃ g h : ↥B, (∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩, hm⟩ ≠ 0) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))))
        (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
        (hDb : ∀ (Q : Place (ResidueField ↥A) FSS) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q ↔ (P.IsRational ∧
        (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
        (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))),
      (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧
      (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧
      (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q))) := by
  intro F₀ B alg hjB hBst FSS _ _ R hBR hfracB N hNiff hNeqv Sb φb χb hS Db hDb

  have stab : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}, ∀ f, f ∈ B ↔ τ f ∈ B := by
    apply stab_closure
    · rintro s ⟨ζ, γ, hγ, rfl⟩ f hf
      exact hBst ζ γ hγ f hf
    · rintro s ⟨ζ, γ, hγ, rfl⟩
      obtain ⟨G, hGfin, hGmem, -⟩ :=
        ModularCurve.FullLevel.exists_finite_subgroup_forall_levelAutBar_mem q M' hqM' ζ
      exact symm_mem_of_finite B G hGfin _ (hGmem γ hγ) (hBst ζ γ hγ)

  have hDb' : ∀ (Q₁ : Place (ResidueField ↥A) FSS) (_ : IsLocalRing ↥(Sb Q₁))
      (_ : RingHom.ker (χb Q₁) = maximalIdeal ↥(Sb Q₁)) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')),
      P ∈ Db Q₁ ↔ (P.IsRational ∧
        (∀ f : ↥(fieldBar q M'), f ∈ Sb Q₁ → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ Sb Q₁ → (A.valuation (P.evalAt f) < 1 ↔ (f = 0 ∨ f⁻¹ ∉ Sb Q₁)))) := by
    intro Q₁ instQ₁ hker₁ P
    rw [hDb Q₁ P]
    have hχ : ∀ f : ↥(Sb Q₁), χb Q₁ f = 0 ↔ ((f : ↥(fieldBar q M')) = 0 ∨ (f : ↥(fieldBar q M'))⁻¹ ∉ Sb Q₁) := by
      intro f
      rw [← RingHom.mem_ker, hker₁]
      exact mk_mem_maximalIdeal_iff (Sb Q₁) f f.2
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun f hf => h2 ⟨f, hf⟩, fun f hf => (h3 ⟨f, hf⟩).trans (hχ ⟨f, hf⟩)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, fun f => h2 f f.2, fun f => (h3 f f.2).trans (hχ f).symm⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro Q Q' hQ hQ' P hP hP'
    haveI : IsDiscreteValuationRing ↥Ab := hdvrb
    obtain ⟨-, -, -, hχtQ, ⟨instQ, hkerQ⟩, -, -, -, hφuQ, hφfQ, ⟨hSRQ, hcenQ⟩, hresQ, ⟨hXRQ, hordQ⟩, hBSQ, hpinQ⟩ := hS Q hQ
    obtain ⟨-, -, -, hχtQ', ⟨instQ', hkerQ'⟩, -, -, -, hφuQ', hφfQ', ⟨hSRQ', hcenQ'⟩, hresQ', ⟨hXRQ', hordQ'⟩, hBSQ', hpinQ'⟩ :=
      hS Q' hQ'
    obtain ⟨-, -, hPcen⟩ := (hDb' Q instQ hkerQ P).mp hP
    obtain ⟨-, -, hPcen'⟩ := (hDb' Q' instQ' hkerQ' P).mp hP'

    have hinvB : ∀ b : ↥(fieldBar q M'), b ∈ B → ((b = 0 ∨ b⁻¹ ∉ Sb Q) ↔ (b = 0 ∨ b⁻¹ ∉ Sb Q')) :=
      fun b hb => (hPcen b (hBSQ b hb)).symm.trans (hPcen' b (hBSQ' b hb))

    have hNV : ∀ (Q₁ : Place (ResidueField ↥A) FSS) (_ : IsLocalRing ↥(Sb Q₁))
        (_ : RingHom.ker (χb Q₁) = maximalIdeal ↥(Sb Q₁))
        (_ : ∀ f : ↥(Sb Q₁), ∃ (hR : (f : ↥(fieldBar q M')) ∈ R.integers)
            (hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q₁.toValuationSubring),
            IsLocalRing.residue ↥Q₁.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q₁.ResidueField ((χb Q₁) f))
        (hBS₁ : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q₁) (h : ↥B),
        NV Q₁ (R.residue ⟨(h : ↥(fieldBar q M')), hBR _ h.2⟩) ↔
          ¬ ((h : ↥(fieldBar q M')) = 0 ∨ (h : ↥(fieldBar q M'))⁻¹ ∉ Sb Q₁) := by
      intro Q₁ inst₁ hker₁ hres₁ hBS₁ h
      obtain ⟨hR, hm, e⟩ := hres₁ ⟨h, hBS₁ _ h.2⟩
      have key : ZR Q₁ (R.residue ⟨(h : ↥(fieldBar q M')), hBR _ h.2⟩) ↔ χb Q₁ ⟨h, hBS₁ _ h.2⟩ = 0 := by
        constructor
        · rintro ⟨hm', h0⟩
          have e' : algebraMap (ResidueField ↥A) Q₁.ResidueField (χb Q₁ ⟨h, hBS₁ _ h.2⟩) = 0 := by
            rw [← e]; exact h0
          exact (map_eq_zero_iff _ (algebraMap (ResidueField ↥A) Q₁.ResidueField).injective).mp e'
        · intro h0
          exact ⟨hm, by rw [e, h0, map_zero]⟩
      rw [← mk_mem_maximalIdeal_iff (Sb Q₁) (h : ↥(fieldBar q M')) (hBS₁ _ h.2), ← hker₁, RingHom.mem_ker, ← key]
      exact nv_iff_not_zr Q₁ _ hm

    have hSS : ∀ f : ↥(fieldBar q M'), f ∈ Sb Q ↔ f ∈ Sb Q' := by
      intro f
      rw [hpinQ f, hpinQ' f]
      constructor
      · rintro ⟨g, h, hnv, hfh⟩
        exact ⟨g, h, (hNV Q' instQ' hkerQ' hresQ' hBSQ' h).mpr
          ((hinvB h h.2).not.mp ((hNV Q instQ hkerQ hresQ hBSQ h).mp hnv)), hfh⟩
      · rintro ⟨g, h, hnv, hfh⟩
        exact ⟨g, h, (hNV Q instQ hkerQ hresQ hBSQ h).mpr
          ((hinvB h h.2).not.mpr ((hNV Q' instQ' hkerQ' hresQ' hBSQ' h).mp hnv)), hfh⟩

    have hVal : ∀ (Q₁ : Place (ResidueField ↥A) FSS) (_ : IsLocalRing ↥(Sb Q₁))
        (_ : RingHom.ker (χb Q₁) = maximalIdeal ↥(Sb Q₁))
        (_ : (χb Q₁) ((φb Q₁) Polynomial.X) = 0)
        (_ : (φb Q₁).FormallyUnramified) (_ : (φb Q₁).EssFiniteType)
        (hSR₁ : ∀ f : ↥(Sb Q₁), (f : ↥(fieldBar q M')) ∈ R.integers)
        (_ : ∀ f : ↥(Sb Q₁), (⟨(f : ↥(fieldBar q M')), hSR₁ f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔
            (φb Q₁) (Polynomial.C ϖb) ∣ f)
        (_ : ∀ f : ↥(Sb Q₁), ∃ (hR : (f : ↥(fieldBar q M')) ∈ R.integers)
            (hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q₁.toValuationSubring),
            IsLocalRing.residue ↥Q₁.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q₁.ResidueField ((χb Q₁) f))
        (hXR₁ : (((φb Q₁) Polynomial.X : ↥(Sb Q₁)) : ↥(fieldBar q M')) ∈ R.integers)
        (_ : Q₁.ord (R.residue ⟨(((φb Q₁) Polynomial.X : ↥(Sb Q₁)) : ↥(fieldBar q M')), hXR₁⟩) = 1)
        (_ : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q₁),
        ∀ x : FSS, x ∈ Q₁.toValuationSubring ↔
          ∃ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), f ∈ Sb Q₁ ∧ R.residue ⟨f, hf⟩ = x := by
      intro Q₁ inst₁ hker₁ hχt₁ hφu₁ hφf₁ hSR₁ hcen₁ hres₁ hXR₁ hord₁ hBS₁
      let ρ : ↥(Sb Q₁) →+* FSS :=
        R.residue.comp
          { toFun := fun f => ⟨(f : ↥(fieldBar q M')), hSR₁ f⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      have hρ : ∀ f : ↥(Sb Q₁), ρ f = R.residue ⟨(f : ↥(fieldBar q M')), hSR₁ f⟩ := fun f => rfl
      have ht₁ : (φb Q₁) Polynomial.X ∈ maximalIdeal ↥(Sb Q₁) := by
        rw [← hker₁, RingHom.mem_ker]; exact hχt₁
      have hkerρ : ∀ f : ↥(Sb Q₁), ρ f = 0 ↔ (φb Q₁) (Polynomial.C ϖb) ∣ f := by
        intro f
        rw [← hcen₁ f, ← R.ker_residue, RingHom.mem_ker, hρ]
      have ht0₁ : ρ ((φb Q₁) Polynomial.X) ≠ 0 := by
        intro h0
        rw [hρ] at h0
        have := hord₁
        rw [h0, Place.ord_zero] at this
        exact zero_ne_one this
      have hV₁ : ∀ f : ↥(Sb Q₁), ρ f ∈ Q₁.toValuationSubring := by
        intro f
        obtain ⟨_, hm, _⟩ := hres₁ f
        rw [hρ]; exact hm
      have hcenV : ∀ f : ↥(Sb Q₁), f ∈ maximalIdeal ↥(Sb Q₁) →
          IsLocalRing.residue ↥Q₁.toValuationSubring ⟨ρ f, hV₁ f⟩ = 0 := by
        intro f hf
        obtain ⟨hR, hm, e⟩ := hres₁ f
        have h0 : χb Q₁ f = 0 := by rw [← RingHom.mem_ker, hker₁]; exact hf
        rw [h0, map_zero] at e
        exact e
      have hfrac₁ : ∀ x : FSS, ∃ a b : ↥(Sb Q₁), ρ b ≠ 0 ∧ x * ρ b = ρ a := by
        intro x
        obtain ⟨g, h, h0, e⟩ := hfracB x
        exact ⟨⟨g, hBS₁ _ g.2⟩, ⟨h, hBS₁ _ h.2⟩, h0, e⟩
      have key := mem_iff_mem_range_of_fibre ϖb hϖb (φb Q₁) hφu₁ hφf₁ ht₁ ρ hkerρ ht0₁
        Q₁.toValuationSubring hV₁ hcenV hfrac₁
      intro x
      rw [key x]
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨f, hSR₁ f, f.2, (hρ f).symm⟩
      · rintro ⟨f, hf, hfS, rfl⟩
        exact ⟨⟨f, hfS⟩, hρ _⟩
    have hVQ := hVal Q instQ hkerQ hχtQ hφuQ hφfQ hSRQ hcenQ hresQ hXRQ hordQ hBSQ
    have hVQ' := hVal Q' instQ' hkerQ' hχtQ' hφuQ' hφfQ' hSRQ' hcenQ' hresQ' hXRQ' hordQ' hBSQ'
    apply Place.ext
    ext x
    rw [hVQ x, hVQ' x]
    constructor
    · rintro ⟨f, hf, hfS, e⟩; exact ⟨f, hf, (hSS f).mp hfS, e⟩
    · rintro ⟨f, hf, hfS, e⟩; exact ⟨f, hf, (hSS f).mpr hfS, e⟩
  ·
    intro Q hQ P hP
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hBS, -⟩ := hS Q hQ
    obtain ⟨-, hreg, -⟩ := (hDb Q P).mp hP
    exact ord_nonneg_of_mem P (hreg ⟨_, hBS _ hjB⟩).1
  ·
    intro τ hτmem hτ Q
    refine ⟨hNeqv τ hτmem hτ Q, fun hQ => ?_⟩
    set σ := R.resAut τ hτ with hσ
    have hσQ : σ • Q ∉ N := fun h => hQ ((hNeqv τ hτmem hτ Q).mp h)
    have stabτ := stab τ hτmem
    obtain ⟨-, -, -, -, ⟨instQ, hkerQ⟩, -, -, -, -, -, -, hresQ, -, hBSQ, hpinQ⟩ := hS Q hQ
    obtain ⟨-, -, -, -, ⟨instσ, hkerσ⟩, -, -, -, -, -, -, hresσ, -, hBSσ, hpinσ⟩ := hS (σ • Q) hσQ

    have memS : ∀ f : ↥(fieldBar q M'), f ∈ Sb Q ↔ τ f ∈ Sb (σ • Q) := by
      intro f
      rw [hpinQ f, hpinσ (τ f)]
      constructor
      · rintro ⟨g, h, hNV, hfh⟩
        refine ⟨⟨τ g, (stabτ g).mp g.2⟩, ⟨τ h, (stabτ h).mp h.2⟩, ?_, ?_⟩
        · have e : R.residue ⟨((⟨τ h, (stabτ h).mp h.2⟩ : ↥B) : ↥(fieldBar q M')), hBR _ ((stabτ h).mp h.2)⟩
              = σ (R.residue ⟨(h : ↥(fieldBar q M')), hBR _ h.2⟩) := by
            rw [hσ, RegularProlongation.resAut_residue]
          rw [e]
          exact (nv_smul_iff σ Q _).mpr hNV
        · show τ f * τ (h : ↥(fieldBar q M')) = τ (g : ↥(fieldBar q M'))
          rw [← map_mul, hfh]
      · rintro ⟨g, h, hNV, hfh⟩
        have hg' : τ.symm (g : ↥(fieldBar q M')) ∈ B := (stabτ _).mpr (by rw [τ.apply_symm_apply]; exact g.2)
        have hh' : τ.symm (h : ↥(fieldBar q M')) ∈ B := (stabτ _).mpr (by rw [τ.apply_symm_apply]; exact h.2)
        refine ⟨⟨_, hg'⟩, ⟨_, hh'⟩, ?_, ?_⟩
        · have e : σ (R.residue ⟨((⟨τ.symm (h : ↥(fieldBar q M')), hh'⟩ : ↥B) : ↥(fieldBar q M')), hBR _ hh'⟩)
              = R.residue ⟨(h : ↥(fieldBar q M')), hBR _ h.2⟩ := by
            rw [hσ]
            exact R.residue_symm_eq τ hτ ⟨(h : ↥(fieldBar q M')), hBR _ h.2⟩
          rw [← e] at hNV
          exact (nv_smul_iff σ Q _).mp hNV
        · apply τ.injective
          show τ (f * τ.symm (h : ↥(fieldBar q M'))) = τ (τ.symm (g : ↥(fieldBar q M')))
          rw [map_mul, τ.apply_symm_apply, τ.apply_symm_apply]
          exact hfh
    ext P
    rw [RegularProlongation.mem_smulDisc_iff, hDb' Q instQ hkerQ (τ⁻¹ • P), hDb' (σ • Q) instσ hkerσ P]
    constructor
    · rintro ⟨hrat, hreg, hcen⟩
      have hratP : P.IsRational := (Place.Transport.isRational_smul_iff τ⁻¹ P).mp hrat
      refine ⟨hratP, fun f' hf' => ?_, fun f' hf' => ?_⟩
      · have hf : τ.symm f' ∈ Sb Q := (memS _).mpr (by rw [τ.apply_symm_apply]; exact hf')
        obtain ⟨h1, h2⟩ := hreg _ hf
        rw [Place.Transport.mem_inv_smul_iff, τ.apply_symm_apply] at h1
        rw [evalAt_inv_smul τ P hratP, τ.apply_symm_apply] at h2
        exact ⟨h1, h2⟩
      · have hf : τ.symm f' ∈ Sb Q := (memS _).mpr (by rw [τ.apply_symm_apply]; exact hf')
        have h3 := hcen _ hf
        rw [evalAt_inv_smul τ P hratP, τ.apply_symm_apply] at h3
        rw [h3, map_eq_zero_iff _ τ.symm.injective, ← map_inv₀, memS, τ.apply_symm_apply]
    · rintro ⟨hratP, hreg, hcen⟩
      have hrat : (τ⁻¹ • P).IsRational := (Place.Transport.isRational_smul_iff τ⁻¹ P).mpr hratP
      refine ⟨hrat, fun f hf => ?_, fun f hf => ?_⟩
      · have hf' : τ f ∈ Sb (σ • Q) := (memS f).mp hf
        obtain ⟨h1, h2⟩ := hreg _ hf'
        rw [Place.Transport.mem_inv_smul_iff, evalAt_inv_smul τ P hratP]
        exact ⟨h1, h2⟩
      · have hf' : τ f ∈ Sb (σ • Q) := (memS f).mp hf
        have h3 := hcen _ hf'
        rw [evalAt_inv_smul τ P hratP, h3, map_eq_zero_iff _ τ.injective, ← map_inv₀, ← memS]

end S_ModularCurve_FullLevel_supersingularProlongation_discRiders_of_affineChart
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_discRiders_of_affineChart (solution)
