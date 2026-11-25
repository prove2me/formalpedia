-- Prove2me | solution 1 for GlobalTheory.AdmLoc.Ea_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:44:30.600555+00:00
-- url     : https://prove2.me/submissions/7a2301bb-75c7-446f-a192-645ef680104f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_twistRep_apply
import Theorems.Thm_GlobalTheory_AdmLoc_twist_twCoef
import Theorems.Thm_GlobalTheory_AdmLoc_extRep_apply

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
variable (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0)
namespace GlobalTheory.AdmLoc
theorem _root_.solution (z : ↥(Z1 (twCoef W χ X) ⊤)) (g : G) (m : M ⊗[O] X) (y : O) :
    Ea W χ hc z g (m, Ideal.Quotient.mk _ y) =
      (coefRep W X g m + ((χ g : O) * y) • (z : G → M ⊗[O] X) g, Ideal.Quotient.mk _ ((χ g : O) * y)) := by
  rw [Ea, twistRep_apply, extRep_apply, ← twist_twCoef W χ X, twistRep_apply, Prod.smul_mk, smul_add, smul_smul]
  rfl
end GlobalTheory.AdmLoc
