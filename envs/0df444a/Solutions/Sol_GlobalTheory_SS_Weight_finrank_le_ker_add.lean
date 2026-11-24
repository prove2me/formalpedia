-- Prove2me | solution 1 for GlobalTheory.SS.Weight.finrank_le_ker_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:45:01.416799+00:00
-- url     : https://prove2.me/submissions/428d05d5-0ab5-4966-818d-b2a95871a81e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing
import Theorems.Thm_GlobalTheory_T_finrank_le_of_weights_unipotent_symplectic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors
namespace GlobalTheory.SS.Weight
theorem _root_.solution (l : ℕ) [Fact l.Prime] {T : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (B : LinearMap.BilinForm ℤ_[l] T) (hB : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hsk : ∀ x y, B y x = - B x y) (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ) (hq : 2 ≤ q)
    (hN : IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1)) (hS : ∀ x y, B (S x) (S y) = B x y)
    (hΦ : ∀ x y, B (Φ x) (Φ y) = q * B x y) (hc : Φ * S = S ^ q * Φ)
    (W : Submodule ℤ_[l] T) (P : Polynomial ℤ)
    (hP : ∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < q) (hW : ∀ x ∈ W, Φ x = q • x)
    (c : ℕ) (hc0 : c ≠ 0)
    (hPW : ∀ x, S x = x →
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j • (Φ^[j] (c • x)) ∈ W) :
    finrank ℤ_[l] T ≤ finrank ℤ_[l] (LinearMap.ker ((S : T →ₗ[ℤ_[l]] T) - 1)) +
      finrank ℤ_[l] W := by
  let V := ℚ_[l] ⊗[ℤ_[l]] T
  let ι : T →ₗ[ℤ_[l]] V := TensorProduct.mk ℤ_[l] ℚ_[l] T 1
  haveI hloc : IsLocalizedModule (ℤ_[l])⁰ ι := inferInstanceAs
    (IsLocalizedModule (ℤ_[l])⁰ (TensorProduct.mk ℤ_[l] ℚ_[l] T 1))
  have hinj : Function.Injective ι :=
    (IsLocalizedModule.injective_iff_isRegular (ℤ_[l])⁰ ι).2 fun s =>
      IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)
  have hsurj : ∀ v : V, ∃ (s : ℚ_[l]) (t : T), v = s • ι t := by
    intro v
    obtain ⟨⟨t, s⟩, h⟩ := IsLocalizedModule.surj (ℤ_[l])⁰ ι v
    have hs : (algebraMap ℤ_[l] ℚ_[l] s) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).2 (nonZeroDivisors.ne_zero s.2)
    refine ⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, t, ?_⟩
    rw [eq_inv_smul_iff₀ hs, algebraMap_smul]
    exact h
  let S' : V ≃ₗ[ℚ_[l]] V := LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T S
  let Φ' : V ≃ₗ[ℚ_[l]] V := LinearEquiv.baseChange ℤ_[l] ℚ_[l] T T Φ
  have hS' : ∀ t, S' (ι t) = ι (S t) := fun t => LinearEquiv.baseChange_tmul ..
  have hΦ' : ∀ t, Φ' (ι t) = ι (Φ t) := fun t => LinearEquiv.baseChange_tmul ..
  let B' : LinearMap.BilinForm ℚ_[l] V := B.baseChange ℚ_[l]
  have hB' : ∀ x y, B' (ι x) (ι y) = algebraMap ℤ_[l] ℚ_[l] (B x y) := fun x y => by
    have := LinearMap.BilinForm.baseChange_tmul (A := ℚ_[l]) B 1 x 1 y
    rw [mul_one, ← Algebra.algebraMap_eq_smul_one] at this
    exact this
  have hsk' : ∀ x y, B' y x = - B' x y := by
    intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hB', hsk x y, map_neg, smul_eq_mul]
    ring
  have hleft : ∀ x, (∀ y, B' x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨s, x, rfl⟩ := hsurj x
    by_cases hs : s = 0
    · simp [hs]
    have : x = 0 := hB x fun y => by
      have := hx (ι y)
      simp only [map_smul, LinearMap.smul_apply, hB', smul_eq_mul, mul_eq_zero, hs,
        false_or] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 this
    simp [this]
  have hfix : ∀ v, S' v = v → ∃ (s : ℚ_[l]) (t : T), S t = t ∧ v = s • ι t := by
    intro v hv
    obtain ⟨s, t, rfl⟩ := hsurj v
    by_cases hs : s = 0
    · exact ⟨0, 0, by simp, by simp [hs]⟩
    refine ⟨s, t, hinj ?_, rfl⟩
    rw [map_smul, hS'] at hv
    exact smul_right_injective V hs hv
  have hmem : ∀ (U : Submodule ℤ_[l] T) (s : ℚ_[l]) (t : T), t ∈ U →
      s • ι t ∈ U.localized' ℚ_[l] (ℤ_[l])⁰ ι := fun U s t ht =>
    Submodule.smul_mem _ _ ⟨t, ht, 1, IsLocalizedModule.mk'_one _ _ _⟩
  have hrk : ∀ (U : Submodule ℤ_[l] T),
      finrank ℚ_[l] (U.localized' ℚ_[l] (ℤ_[l])⁰ ι) = finrank ℤ_[l] U := fun U => by
    rw [IsLocalization.finrank_eq ℚ_[l] (ℤ_[l])⁰ le_rfl,
      IsLocalizedModule.finrank_eq (ℤ_[l])⁰ (U.toLocalized' ℚ_[l] (ℤ_[l])⁰ ι) le_rfl]
  have hit : ∀ (E : T ≃ₗ[ℤ_[l]] T) (E' : V ≃ₗ[ℚ_[l]] V), (∀ t, E' (ι t) = ι (E t)) →
      ∀ (j : ℕ) t, E'^[j] (ι t) = ι (E^[j] t) := by
    intro E E' h j
    induction j with
    | zero => intro t; rfl
    | succ j ih => intro t; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h, ih]
  have main := GlobalTheory.T.finrank_le_of_weights_unipotent_symplectic ℚ_[l] V B' ⟨hleft, fun y hy => hleft y fun x => by
      rw [hsk' x y, hy x, neg_zero]⟩ hsk' S' Φ' q hq ?_ ?_ ?_ ?_
    (W.localized' ℚ_[l] (ℤ_[l])⁰ ι) P hP ?_ ?_
  · have h1 : finrank ℚ_[l] V = finrank ℤ_[l] T := Module.finrank_baseChange
    rw [h1, hrk] at main
    refine main.trans (Nat.add_le_add_right ?_ _)
    rw [← hrk]
    refine Submodule.finrank_mono fun v hv => ?_
    obtain ⟨s, t, ht, rfl⟩ := hfix v (by simpa [sub_eq_zero] using hv)
    exact hmem _ s t (by simpa [sub_eq_zero] using ht)
  · have := hN.map (Module.End.baseChangeHom ℤ_[l] ℚ_[l] T)
    rw [map_sub, map_one] at this
    exact this
  · intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hS', hB', hS]
  · intro x y
    obtain ⟨s, x, rfl⟩ := hsurj x
    obtain ⟨s', y, rfl⟩ := hsurj y
    simp only [map_smul, LinearMap.smul_apply, hΦ', hB', hΦ, map_mul, map_natCast, smul_eq_mul]
    ring
  · ext v
    obtain ⟨s, t, rfl⟩ := hsurj v
    have h1 : Φ (S t) = S^[q] (Φ t) := by
      have := LinearEquiv.congr_fun hc t
      rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply] at this
    rw [map_smul, map_smul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.pow_apply,
      hS', hΦ', hΦ', hit S S' hS', h1]
  · intro v hv
    rw [Submodule.localized'_eq_span] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨t, ht, rfl⟩ := hv
      rw [hΦ', hW t ht, map_nsmul, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul a x _ hx => rw [map_smul, hx, smul_comm]
  · intro v hv
    obtain ⟨s, t, ht, rfl⟩ := hfix v hv
    have hc1 : (c : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc0
    have h1 : s • ι t = (s * (c : ℚ_[l])⁻¹) • ι (c • t) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_assoc, inv_mul_cancel₀ hc1,
        mul_one]
    have h2 := hmem W (s * (c : ℚ_[l])⁻¹) _ (hPW t ht)
    rw [h1, map_smul, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
    convert h2 using 2
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ← hit Φ Φ' hΦ', LinearMap.smul_apply, Module.End.pow_apply]
    rfl
end GlobalTheory.SS.Weight
