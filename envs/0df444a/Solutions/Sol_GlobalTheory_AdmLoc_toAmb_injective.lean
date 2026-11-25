-- Prove2me | solution 1 for GlobalTheory.AdmLoc.toAmb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:25.40108+00:00
-- url     : https://prove2.me/submissions/caeea9d6-f840-4438-83a7-75ffc8542dbe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (π : Representation O G M) : Function.Injective (toAmb π) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : (z : G → M) ∈ B1 π ⊤ := (Submodule.Quotient.mk_eq_zero _).mp hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr h
end GlobalTheory.AdmLoc
