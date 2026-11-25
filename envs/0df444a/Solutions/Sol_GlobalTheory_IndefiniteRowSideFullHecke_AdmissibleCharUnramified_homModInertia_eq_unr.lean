-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:09.647801+00:00
-- url     : https://prove2.me/submissions/95c06e0e-d96d-4615-a84b-6082be17bd32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_AdmissibleCharUnramified
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdmissibleCharUnramified_twCoef_chi_one
import Theorems.Thm_GlobalTheory_AdmLoc_mk_mem_unr_of_trivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
theorem _root_.solution (I : Subgroup G) :
    homModInertia Γ X I = (unr (twCoef (Γ.Wchi 1) Γ.χ₁ X) I : Set _) := by
  ext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  constructor
  · rintro ⟨z', hz, h⟩
    rw [← hz]
    exact (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z').mpr h
  · intro h
    exact ⟨z, rfl, (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z).mp h⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
