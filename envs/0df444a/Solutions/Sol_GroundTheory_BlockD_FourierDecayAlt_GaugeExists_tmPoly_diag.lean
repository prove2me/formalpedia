-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.tmPoly_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:06.580934+00:00
-- url     : https://prove2.me/submissions/d1f7b3f0-0d4f-43ac-b07d-b8597d091c6c

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub

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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  unfold tmPoly
  simp only [if_true, map_sub]
  abel
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
