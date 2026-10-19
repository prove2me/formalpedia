-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant.gtStabilizerArrowheadNode_injective_of_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/b2561522-e4bc-4c90-8b7c-d1d7a2ac1861

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCharacteristicDeterminant_gtStabilizerArrowheadNode_injective_of_gap

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
theorem _root_.solution
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (h : FiniteInterlacing (n + 1) lam mu) :
    Function.Injective
      (gtStabilizerArrowheadNode
        (wallShift (n + 1) (r + 1))
        (stabilizerShift (n + 1) mu)) := by
  apply gtStabilizerArrowheadNode_injective_of_gap
    (wallShift (n + 1) (r + 1))
    (stabilizerShift (n + 1) mu) h.wallShift_pos
  · intro i
    unfold stabilizerShift wallShift
    have hi : i.val ≤ r := by have := i.isLt; omega
    have hireal : (i.val : ℝ) ≤ r := by exact_mod_cast hi
    have hmu : (0 : ℝ) ≤ mu i := Nat.cast_nonneg _
    push_cast
    linarith
  · have hanti : Antitone mu := by
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      exact (h.2 i.succ).1.trans (by
        simpa using (h.2 i.castSucc).2)
    have hstrict : StrictAnti (stabilizerShift (n + 1) mu) := by
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have hm := hanti (Fin.castSucc_le_succ i)
      unfold stabilizerShift
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hmreal : (mu i.succ : ℝ) ≤ (mu i.castSucc : ℝ) := by
        exact_mod_cast hm
      push_cast
      linarith
    exact hstrict.injective
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCharacteristicDeterminant
