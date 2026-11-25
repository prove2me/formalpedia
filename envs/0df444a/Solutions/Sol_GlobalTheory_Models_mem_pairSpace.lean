-- Prove2me | solution 1 for GlobalTheory.Models.mem_pairSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:23.076493+00:00
-- url     : https://prove2.me/submissions/1a20e0d1-f58a-4390-a5a4-f97073771a07

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
theorem _root_.solution {m r : ℕ} {D : ModPG R n (Vc k m)} {Dt : TopData n r} {N : Lats k n m}
    {b g : ZMod n → Vc k m} : (b, g) ∈ pairSpace D Dt N ↔ InZZ D Dt N b g := Iff.rfl
end GlobalTheory.Models
