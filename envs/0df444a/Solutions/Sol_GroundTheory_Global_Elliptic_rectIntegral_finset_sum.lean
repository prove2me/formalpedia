-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:44.182572+00:00
-- url     : https://prove2.me/submissions/7319d785-1f30-44a4-ad66-7ffb19688108

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_add
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ} {f g : ℂ → E}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBoundary z w)) :
    rectIntegral (fun u ↦ ∑ i ∈ s, f i u) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rectIntegral_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [rectIntegral_add (hf a (Finset.mem_insert_self a s))
      (continuousOn_finsetSum _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]
end GroundTheory.Global.Elliptic
