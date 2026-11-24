-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:35.362805+00:00
-- url     : https://prove2.me/submissions/b3d9e0dd-00b6-4c99-a7f3-94e189d4fd48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_bdInt_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {a b c d : ℝ} {B : Set ℂ} (h : SidesIn a b c d B) {ι : Type*} (S : Finset ι)
    {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, ContinuousOn (f i) B) :
    bdInt a b c d (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, bdInt a b c d (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [bdInt]
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [bdInt_add h (hf i (Finset.mem_insert_self _ _))
      (continuousOn_finset_sum _ fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]
end GlobalTheory.ResRect
