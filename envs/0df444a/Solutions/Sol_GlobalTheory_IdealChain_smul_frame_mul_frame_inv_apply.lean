-- Prove2me | solution 1 for GlobalTheory.IdealChain.smul_frame_mul_frame_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:45.605956+00:00
-- url     : https://prove2.me/submissions/1082dce5-e5e6-49e9-8f7b-665c823c2a92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain
namespace GlobalTheory.IdealChain
theorem _root_.solution {k : Type} [Field k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (a : k) (b b' : ℕ → kˣ)
    (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r : n ⊕ Fin c) (s : n' ⊕ Fin c') :
    (a • ((frame n c b).val * y * ((frame n' c' b')⁻¹).val)) r s =
      a * Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹) s * y r s := by
  have h1 : (frame n c b).val =
      Matrix.diagonal (Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k))) := by
    rw [← Matrix.fromBlocks_diagonal]; rfl
  have h2 : ((frame n' c' b')⁻¹).val =
      Matrix.diagonal (Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹)) := by
    rw [← Matrix.fromBlocks_diagonal]
    simp only [← Units.val_inv_eq_inv_val]
    rfl
  rw [h1, h2, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  ring
end GlobalTheory.IdealChain
