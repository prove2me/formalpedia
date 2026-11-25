-- Prove2me | solution 1 for GlobalTheory.HTLat.fg_grLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:45.256258+00:00
-- url     : https://prove2.me/submissions/8513cc1f-6c9e-4657-84f2-d14e37423768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_fg_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]
variable (v : Valuation C ℝ≥0)
variable {v}
namespace GlobalTheory.HTLat
theorem _root_.solution (hv : v.Integers O) {La : Submodule O U} (hfg : La.FG) (F' F : Submodule C U) :
    (grLat La F' F).FG := (fg_inf hv hfg F).map _
end GlobalTheory.HTLat
