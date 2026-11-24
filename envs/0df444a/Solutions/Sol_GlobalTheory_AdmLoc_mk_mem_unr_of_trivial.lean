-- Prove2me | solution 1 for GlobalTheory.AdmLoc.mk_mem_unr_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:13:26.035831+00:00
-- url     : https://prove2.me/submissions/77def874-94e1-40ee-854b-e7d8796b8bb3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
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
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {O G : Type} [CommRing O] [Group G]
variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
variable [TopologicalSpace G]
namespace GlobalTheory.AdmLoc
theorem _root_.solution {π : Representation O G M} (hπ : ∀ g m, π g m = m) (I : Subgroup G)
    (z : ↥(Z1 π ⊤)) : (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∀ g ∈ I, (z : G → M) g = 0 := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩ g hg
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg, hπ, hπ] at h1
    simpa using h1
  · intro h
    exact ⟨z, ⟨0, fun g hg => by simp [h g hg]⟩, rfl⟩
end GlobalTheory.AdmLoc
