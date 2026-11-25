-- Prove2me | solution 1 for GlobalTheory.Models.IsModel.of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:25.596561+00:00
-- url     : https://prove2.me/submissions/d6688beb-8d62-47ee-a039-01859e9a4c40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.Models
namespace IsModel
theorem _root_.solution {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A : Ob k G}
    {N : Lats k n A.m} (hA : F.Obj A) (h : Base A N) : IsModel F Base A N := by
  refine ⟨A, N, A, LinearMap.id, LinearMap.id, h, fun _ _ => rfl, Function.injective_id, fun _ _ => rfl,
    Function.surjective_id, funext fun i => ?_⟩
  ext x
  simp [DFun.push, DFun.pre, F.map_id A hA i]
end IsModel
end GlobalTheory.Models
