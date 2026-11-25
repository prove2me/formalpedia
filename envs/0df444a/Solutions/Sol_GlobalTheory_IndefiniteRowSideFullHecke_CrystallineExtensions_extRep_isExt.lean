-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:30.831415+00:00
-- url     : https://prove2.me/submissions/7b410a95-e4e9-4c53-bfc4-9ec673a3400a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineExtensions
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
variable {G : Type} [Group G] {LL : Type} [Field LL] {V W : Type} [AddCommGroup V] [Module LL V]
  [AddCommGroup W] [Module LL W]
variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
theorem _root_.solution (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ)) :
    IsExt ρ (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) ∧
      IsCocycleOf (extRep ρ c) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL) (c : G → V) := by
  refine ⟨⟨LinearMap.inl_injective, Function.Exact.inl_snd, LinearMap.snd_surjective, fun g x => ?_,
    fun _ _ => rfl⟩, (0, 1), rfl, fun g => ?_⟩
  · simp [extRep]
  · simp [extRep]
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions
