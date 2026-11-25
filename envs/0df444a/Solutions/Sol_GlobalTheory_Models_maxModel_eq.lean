-- Prove2me | solution 1 for GlobalTheory.Models.maxModel_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:18.92516+00:00
-- url     : https://prove2.me/submissions/b1dd23c5-3ff6-4fc4-aa98-2f0f8e57b2b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
import Theorems.Thm_GlobalTheory_Models_IsModel_le_maxModel

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
theorem _root_.solution {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A : Ob k G}
    {N : Lats k n A.m} (h : IsModel F Base A N) (hmax : ∀ N', IsModel F Base A N' → ∀ i, N' i ≤ N i) :
    maxModel F Base A = N :=
  funext fun i => le_antisymm (iSup_le fun N' => hmax N'.1 N'.2 i) (h.le_maxModel i)
end GlobalTheory.Models
