-- Prove2me | solution 1 for GlobalTheory.powerSeries_extend_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:46.626818+00:00
-- url     : https://prove2.me/submissions/d40ec21c-2b8f-4cd4-8cfc-338aa2b260ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompCMulMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowerSeriesRingHomExtendingFiniteFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K]
    [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K)
    (io : O₁ →+* K) (h : ∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧
      Φ PowerSeries.X = i PowerSeries.X ∧
      ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first
  | exact @_root_.GlobalTheory.PowerSeriesCompositionMap.main
  | exact _root_.GlobalTheory.PowerSeriesCompositionMap.main
  | (apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerSeriesCompositionMap.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerSeriesCompositionMap.main ..)
end GlobalTheory
