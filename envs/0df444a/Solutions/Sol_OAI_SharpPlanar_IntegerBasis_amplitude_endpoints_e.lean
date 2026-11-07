-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T00:41:18.11314+00:00
-- url     : https://prove2.me/submissions/84863d87-0508-4e11-809c-dea5cf292521

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_aTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerAlpha_bTable_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_density_check_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_phase12_periodic_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_uAmplitudeBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_vAmplitudeBox_contains_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_norm_le_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic_e).map_mod_nat n

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains_e ⟨n%12,by omega⟩ j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains_e ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar.IntegerBasis
open IntegerIntervals IntegerAlpha

lemma amplitude_endpoints_e_oai (n : ℕ) (hn : n%12 ∈ residues) (j : Fin 6) :
    ‖uAmplitude n j.val ((j.val:ℝ)/6)‖ ≤ densityCap j ∧
    ‖uAmplitude n j.val (((j.val:ℝ)+1)/6)‖ ≤ densityCap j ∧
    ‖vAmplitude n j.val‖ ≤ densityCap j := by
  obtain ⟨hc0,hc1,hcv⟩ := density_check_e n hn j
  have ha := aLookup_contains n j
  have hb := bLookup_contains n j
  refine ⟨?_,?_,CBox.norm_le_rat_e (vAmplitudeBox_contains_e ha) hcv⟩
  · exact CBox.norm_le_rat_e
      (uAmplitudeBox_contains_e (by simpa using RBox.contains_rat_e j.val 6 (by norm_num)) ha hb) hc0
  · exact CBox.norm_le_rat_e
      (uAmplitudeBox_contains_e (by simpa using RBox.contains_rat_e (j.val+1) 6 (by norm_num)) ha hb) hc1

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e_oai := @OAI.SharpPlanar.IntegerBasis.amplitude_endpoints_e_oai
