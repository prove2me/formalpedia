-- Prove2me | solution 1 for GlobalTheory.RestrMeas.cyl_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.705539+00:00
-- url     : https://prove2.me/submissions/50041903-e18e-437f-a4ae-c4d947e2695f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}
variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}
namespace GlobalTheory.RestrMeas
theorem _root_.solution (S : Finset V) (A : ∀ w, Set (Ya w)) :
    cyl pa pf K S A K = {x | (∀ w, pa w x ∈ A w) ∧ ∀ v, pf v x ∈ K v} :=
  Set.ext fun _ => and_congr_right fun _ =>
    ⟨fun h v => (Classical.em (v ∈ S)).elim (h.1 v) (h.2 v), fun h => ⟨fun v _ => h v, fun v _ => h v⟩⟩
end GlobalTheory.RestrMeas
