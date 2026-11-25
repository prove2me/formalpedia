-- Prove2me | solution 1 for GlobalTheory.LocFlat.PureColPf.coords_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:43.920798+00:00
-- url     : https://prove2.me/submissions/d8147c48-d5a2-4f18-97d1-e37f3464b6fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition
import Theorems.Thm_P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_val__94b5cad94009
import Theorems.Thm_P2M_GlobalTheory_LocFlat_PureColPf_typeFrame_inv_val__6c94e0f85deb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] {n n' ι ι' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
namespace GlobalTheory.LocFlat.PureColPf
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (u : n ⊕ Fin c) (v : n' ⊕ Fin c') :
    (((typeFrame ϖ o).bas⁻¹).val * x * (typeFrame ϖ o').bas.val) u v =
      Sum.elim (fun _ => 1) (fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) u * x u v *
        Sum.elim (fun _ => 1) (fun i : Fin c' => (ϖ : k) ^ (i.val + 1)) v := by
  rw [typeFrame_inv_val', typeFrame_val', mul_diagonal, diagonal_mul]
end GlobalTheory.LocFlat.PureColPf
