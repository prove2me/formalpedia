-- Prove2me | solution 1 for GlobalTheory.AdmLoc.TopData.mem_Ut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:44.696613+00:00
-- url     : https://prove2.me/submissions/3f15fac7-3e41-42ec-9c6b-b44967a8efdd

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
open GlobalTheory.AdmLoc.TopData
variable {n r : ℕ} (D : TopData n r)
namespace GlobalTheory.AdmLoc.TopData
theorem _root_.solution (i : ZMod n) {u : ℤ} (hu : u ∈ D.Ut i) : 1 ≤ u ∧ u ≤ (D.h i : ℤ) - 1 := D.range i u hu
end GlobalTheory.AdmLoc.TopData
