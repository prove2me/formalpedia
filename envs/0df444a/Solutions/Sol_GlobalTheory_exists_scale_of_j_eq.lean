-- Prove2me | solution 1 for GlobalTheory.exists_scale_of_j_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:02.790531+00:00
-- url     : https://prove2.me/submissions/07981f88-6419-467f-9222-c41d18554c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {a b a' b' : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0)
    (h' : a' ^ 3 - 27 * b' ^ 2 ≠ 0)
    (e : a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = a' ^ 3 * (a ^ 3 - 27 * b ^ 2)) :
    ∃ u : ℂ, u ≠ 0 ∧ a' = u ^ 2 * a ∧ b' = u ^ 3 * b := by
  have e' : a ^ 3 * b' ^ 2 = a' ^ 3 * b ^ 2 := by linear_combination -e / 27
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by rintro rfl; simp at h
    have ha' : a' = 0 := by simpa [hb] using e'
    subst ha'
    have hb' : b' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b' / b) (n := 3) (by norm_num)
    refine ⟨u, ?_, by simp, by rw [hu]; field_simp⟩
    rintro rfl
    exact div_ne_zero hb' hb (by simpa using hu.symm)
  by_cases hb : b = 0
  · subst hb
    have hb' : b' = 0 := by simpa [ha] using e'
    subst hb'
    have ha' : a' ≠ 0 := by rintro rfl; simp at h'
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a' / a) (n := 2) (by norm_num)
    refine ⟨u, ?_, by rw [hu]; field_simp, by simp⟩
    rintro rfl
    exact div_ne_zero ha' ha (by simpa using hu.symm)
  have ha' : a' ≠ 0 := by
    rintro rfl
    have : b' = 0 := by simpa [ha] using e'
    simp [this] at h'
  have hb' : b' ≠ 0 := by
    rintro rfl
    simp [ha', hb] at e'
  refine ⟨b' * a / (b * a'), by simp [*], ?_, ?_⟩
  · field_simp
    linear_combination -e'
  · field_simp
    linear_combination -e'
end GlobalTheory
