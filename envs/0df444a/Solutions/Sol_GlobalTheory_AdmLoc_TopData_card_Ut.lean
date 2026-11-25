-- Prove2me | solution 1 for GlobalTheory.AdmLoc.TopData.card_Ut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:29:37.26032+00:00
-- url     : https://prove2.me/submissions/100f4377-a877-4fca-93e4-87be6d1f4d8c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_card_block
import Theorems.Thm_GlobalTheory_AdmLoc_TopData_card_U

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
open GlobalTheory.AdmLoc.TopData
variable {n r : ℕ} (D : TopData n r)
namespace GlobalTheory.AdmLoc.TopData
theorem _root_.solution (i : ZMod n) : Multiset.card (D.Ut i) = r + D.t := by
  rw [Ut, Multiset.card_add, card_U, B, card_block]
end GlobalTheory.AdmLoc.TopData
