-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_tmPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:39.162918+00:00
-- url     : https://prove2.me/submissions/567b0df9-b70c-4d18-8ed1-9d611d09fcc2

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_evU_apply

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  unfold tmPoly Tm
  split_ifs <;> simp [evU_apply, map_sub]
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
