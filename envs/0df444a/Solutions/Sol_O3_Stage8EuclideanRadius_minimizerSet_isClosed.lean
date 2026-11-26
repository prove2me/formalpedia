-- Prove2me | solution 1 for O3.Stage8EuclideanRadius.minimizerSet_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:45.73386+00:00
-- url     : https://prove2.me/submissions/2158c42c-2ef5-49f6-a87f-cb9d33ff3f40

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_O3_Stage8EuclideanRadius
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3 O3.Stage8EuclideanRadius
open O3
namespace O3.Stage8EuclideanRadius
theorem _root_.solution {d : ℕ} (P : AdmissibleInstance d 2) :
    IsClosed (MinimizerSet P.f) := by
  have hf : Continuous P.f := continuous_iff_continuousAt.mpr fun x ↦
    (P.gradient_spec x).1.continuousAt
  change IsClosed {x | ∀ y, P.f x ≤ P.f y}
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun y ↦
      isClosed_le hf (continuous_const : Continuous (fun _ : Vec d ↦ P.f y)))
end O3.Stage8EuclideanRadius
