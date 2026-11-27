-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.haarGL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:34.464918+00:00
-- url     : https://prove2.me/submissions/d8c360c7-6b7b-43a9-87e7-bf28bde4c602

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable (μ₀ : Measure (Fin n × Fin n → F)) [μ₀.IsAddHaarMeasure]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution :
    haarGL F n μ₀ = (μ₀.comap fun (g : GL (Fin n) F) (ij : Fin n × Fin n) =>
      (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2).withDensity
        fun g => (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [haarGL, LinearChart.haar]
  congr 1
  funext g
  rw [glChart_leftModulus]
end GroundTheory.Automorphic.Measures
