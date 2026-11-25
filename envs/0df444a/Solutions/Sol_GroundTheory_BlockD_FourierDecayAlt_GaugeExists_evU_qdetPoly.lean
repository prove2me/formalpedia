-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:47.73808+00:00
-- url     : https://prove2.me/submissions/e9af1ec8-95a3-4851-854a-b3bc561afde9

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_GaugeExists_evU_tmPoly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  unfold qdetPoly qdet qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 1
    congr 1
    funext k
    simp [Function.comp, evU_tmPoly]
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
