-- Prove2me | solution 1 for GlobalTheory.TensHead.piOp_tprod_update
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.183305+00:00
-- url     : https://prove2.me/submissions/2ff2f094-2b87-425e-881b-2f01eff42088

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory.TensHead
open scoped TensorProduct in
private lemma piOp_tprod {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ y) =
      PiTensorProduct.tprod ℂ (Function.update y i (g (y i))) := by
  unfold _root_.GlobalTheory.TensHead.piOp
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]
end GlobalTheory.TensHead
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
open scoped TensorProduct
namespace GlobalTheory.TensHead
namespace _root_.GlobalTheory.TensHead
theorem _root_.solution {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by
  rw [piOp_tprod]
  simp
end _root_.GlobalTheory.TensHead
end GlobalTheory.TensHead
