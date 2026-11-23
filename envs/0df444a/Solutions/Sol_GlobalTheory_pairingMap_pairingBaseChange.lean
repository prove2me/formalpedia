-- Prove2me | solution 1 for GlobalTheory.pairingMap_pairingBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:25.5708+00:00
-- url     : https://prove2.me/submissions/d9519573-3ec0-40bb-9860-366fe2dae59d

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open CartierDual
variable {R : Type*} [CommSemiring R]
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]
namespace GlobalTheory
theorem _root_.solution (u : H ⊗[R] K) (x : A ⊗[R] CartierDual R H) :
    pairingMap A (pairingBaseChange A u) (baseChangeLinear R A H x) =
      (pairingMap R u).baseChange A x := by
  induction x with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a φ =>
    induction u with
    | zero => simp [pairingMap, pairingBaseChange]
    | add s t hs ht =>
      simp only [pairingMap, pairingBaseChange, tmul_add, map_add, LinearMap.add_apply,
        LinearMap.baseChange_tmul] at hs ht ⊢
      rw [hs, ht]
    | tmul h k => simp [pairingBaseChange, smul_tmul', ← smul_tmul]
end GlobalTheory
