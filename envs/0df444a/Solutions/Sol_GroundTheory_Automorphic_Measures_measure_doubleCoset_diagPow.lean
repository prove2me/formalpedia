-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.measure_doubleCoset_diagPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:43:46.063618+00:00
-- url     : https://prove2.me/submissions/61349f51-6080-4bab-add1-95f9451f2705

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Measures_measure_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


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
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsMulLeftInvariant] (a : Fin n → ℤ) :
    μ (doubleCoset (Cartan.diagPow F n a) (GLnLocal.integralGL F n : Set (GL (Fin n) F))
        (GLnLocal.integralGL F n)) =
      (((GLnLocal.integralGL F n).map (MulAut.conj (Cartan.diagPow F n a)).toMonoidHom).relIndex
        (GLnLocal.integralGL F n) : ℝ≥0∞) * μ (GLnLocal.integralGL F n) :=
  measure_doubleCoset μ (GLnLocal.isOpen_integralGL F n) (GLnLocal.isCompact_integralGL F n) _
end GroundTheory.Automorphic.Measures
