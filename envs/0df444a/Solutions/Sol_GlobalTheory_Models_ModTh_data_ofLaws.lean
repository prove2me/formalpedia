-- Prove2me | solution 1 for GlobalTheory.Models.ModTh.data_ofLaws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:01.030116+00:00
-- url     : https://prove2.me/submissions/241a8400-0987-4d8e-953e-85dabd41e7e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.Models
namespace ModTh
theorem _root_.solution {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (Y : ModData k G n) (h : Law.All F Dt Y) :
    (ModTh.ofLaws Y h).data = Y := rfl
end ModTh
end GlobalTheory.Models
