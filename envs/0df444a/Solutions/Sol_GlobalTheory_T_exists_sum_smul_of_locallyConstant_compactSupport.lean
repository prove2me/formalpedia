-- Prove2me | solution 1 for GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:48.504323+00:00
-- url     : https://prove2.me/submissions/9f90b648-f4a4-4a27-bb61-a6fb3ca71bd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupport
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupportStatement
import Theorems.Thm_GlobalTheory_LocConstTensor_exists_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V] [Module ℂ V] (T : Z → V) (_ : IsLocallyConstant T) (K : Set Z) (_ : IsCompact K) (_ : ∀ y, y ∉ K → T y = 0), ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  first | exact @GlobalTheory.LocConstTensor.exists_sum | exact GlobalTheory.LocConstTensor.exists_sum | (intros; apply GlobalTheory.LocConstTensor.exists_sum <;> assumption)
end _root_.GlobalTheory.T
