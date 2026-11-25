-- Prove2me | solution 1 for GlobalTheory.AdmLoc.Ea_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:40:15.410159+00:00
-- url     : https://prove2.me/submissions/d223e0ed-4814-472b-b617-d0034ef81039

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
variable (W : Representation O G M) (χ : G →* Oˣ) {X : Type} [AddCommGroup X] [Module O X] {c : O}
    (hc : ∀ x : X, c • x = 0)
namespace GlobalTheory.AdmLoc
theorem _root_.solution (z : ↥(Z1 (twCoef W χ X) ⊤)) (g : G) (x : (M ⊗[O] X) × (O ⧸ Ideal.span {c})) :
    (Ea W χ hc z g x).2 = (χ g : O) • x.2 := rfl
end GlobalTheory.AdmLoc
