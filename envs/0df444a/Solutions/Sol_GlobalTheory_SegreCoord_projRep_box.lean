-- Prove2me | solution 1 for GlobalTheory.SegreCoord.projRep_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:06:22.190529+00:00
-- url     : https://prove2.me/submissions/b1cb9f44-0866-418e-826e-2c72c34beea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_loc_of_secCoord
import Theorems.Thm_GlobalTheory_SegreCoord_secCoord_of_loc
import Theorems.Thm_GlobalTheory_SegreCoord_killed_iff
import Theorems.Thm_GlobalTheory_SegreCoord_box_killed
import Theorems.Thm_GlobalTheory_SegreCoord_box_unique
import Theorems.Thm_GlobalTheory_SegreCoord_box_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP
namespace GlobalTheory.SegreCoord
theorem _root_.solution : ProjRep (segreIdeal I) (p ≫ s) (boxLB M p q) (boxTh th p q) := by
  refine ⟨DVR.linComb_isLB _ H.1 _ _, fun T _ β x w hx hw => ?_, fun T _ β w hs hw => ?_⟩
  · obtain ⟨h₁, h₂⟩ := box_killed H hP hx (loc_of_secCoord hw)
    exact ⟨h₁, (killed_iff I β w).2 h₂⟩
  · obtain ⟨x, hx, hl⟩ := box_exists H hP hs ((killed_iff I β w).1 hw)
    exact ⟨x, ⟨hx, secCoord_of_loc hs hl⟩, fun x' h' => box_unique H hP h'.1 hx (loc_of_secCoord h'.2) hl⟩
end GlobalTheory.SegreCoord
