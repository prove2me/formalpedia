-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_tmPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:53:28.920224+00:00
-- url     : https://prove2.me/submissions/1c2a00ab-f8fa-4ab2-a757-d8ac8741510c

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial Formalism.REAL
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  unfold tmPoly
  split_ifs with h
  · refine (natDegree_add_le _ _).trans ?_
    refine max_le ((natDegree_sub_le _ _).trans (max_le natDegree_X_le ?_)) ?_ <;> simp
  · simp
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
