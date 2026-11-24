-- Prove2me | solution 1 for GlobalTheory.CMCurves.latticeJ_eq_of_class_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:32.776854+00:00
-- url     : https://prove2.me/submissions/88d7babd-32b6-449f-948c-a0001bf51d99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsFieldCmCurvesUnitDiscriminant
import Theorems.Thm_GlobalTheory_CMCurves_latticeJ_eq_of_isHomothetic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors UpperHalfPlane
noncomputable section
open GlobalTheory
open GlobalTheory.CMCurves
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.CMCurves
theorem _root_.solution (σ : K →+* ℂ) {L L' : PeriodPair} {𝔞 𝔞' : (Ideal (𝓞 K))⁰}
    {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (h' : ∀ z, z ∈ L'.lattice ↔ ∃ a ∈ (𝔞' : Ideal (𝓞 K)), z = c' * σ (a : K))
    (e : ClassGroup.mk0 𝔞 = ClassGroup.mk0 𝔞') : latticeJ L' = latticeJ L := by
  obtain ⟨x, y, hx, hy, he⟩ := ClassGroup.mk0_eq_mk0_iff.1 e
  have hxK : σ (x : K) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast hx)
  have hyK : σ (y : K) ≠ 0 := (map_ne_zero σ).2 (by exact_mod_cast hy)
  have hk : IsHomothetic (c' * σ (x : K) / (c * σ (y : K))) L L' := by
    intro w
    rw [h', h]
    constructor
    · rintro ⟨a', ha', hw⟩
      have hm : y * a' ∈ Ideal.span {x} * (𝔞 : Ideal (𝓞 K)) := by
        rw [he]; exact Ideal.mem_span_singleton_mul.2 ⟨a', ha', rfl⟩
      obtain ⟨a, ha, hxa⟩ := Ideal.mem_span_singleton_mul.1 hm
      refine ⟨a, ha, ?_⟩
      have hs : σ (x : K) * σ (a : K) = σ (y : K) * σ (a' : K) := by
        simpa using congrArg (fun t : 𝓞 K => σ (t : K)) hxa
      apply mul_left_cancel₀ (mul_ne_zero hc' hxK)
      have hw' : c' * σ (x : K) * w = c * σ (y : K) * (c' * σ (a' : K)) := by
        rw [← hw]; field_simp
      linear_combination hw' - c * c' * hs
    · rintro ⟨a, ha, rfl⟩
      have hm : x * a ∈ Ideal.span {y} * (𝔞' : Ideal (𝓞 K)) := by
        rw [← he]; exact Ideal.mem_span_singleton_mul.2 ⟨a, ha, rfl⟩
      obtain ⟨a', ha', hxa⟩ := Ideal.mem_span_singleton_mul.1 hm
      refine ⟨a', ha', ?_⟩
      have hs : σ (y : K) * σ (a' : K) = σ (x : K) * σ (a : K) := by
        simpa using congrArg (fun t : 𝓞 K => σ (t : K)) hxa
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hc hyK)]
      linear_combination (-(c * c')) * hs
  exact latticeJ_eq_of_isHomothetic hk
end GlobalTheory.CMCurves
