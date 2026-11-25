-- Prove2me | solution 1 for GlobalTheory.PrimSec.mem_basicOpen_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:51.11433+00:00
-- url     : https://prove2.me/submissions/fa3a858b-29e7-4008-a343-b3ae2d69e1ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
import Theorems.Thm_GlobalTheory_PrimSec_mem_basicOpen_rs
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.PrimSec
theorem _root_.solution (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (AbLaw.cst f W r) ↔ r ∉ (f x).asIdeal := by
  refine (mem_basicOpen_rs le_top _ hx).trans ?_
  have e₁ := f.preimage_basicOpen_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₂ := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  refine (congrArg (x ∈ ·) e₁).to_iff.symm.trans ?_
  exact (congrArg (f x ∈ ·) e₂).to_iff
end GlobalTheory.PrimSec
