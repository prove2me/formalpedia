-- Prove2me | solution 1 for GlobalTheory.ZM.RepMap.coord_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:03.993971+00:00
-- url     : https://prove2.me/submissions/610e0be6-7ebf-4fb7-9612-bb3c5503759f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepMap_gs_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}
namespace GlobalTheory.ZM.RepMap
theorem _root_.solution {M : LB X} {th : σ → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : σ → R}
    (h : SecCoord M th x v) (p : Sp R) (k : M.ι) (hk : x p ∈ M.U k) :
    ∃ t : ((Sp R).presheaf.stalk p)ˣ, ∀ i, gs x p (M.U k) ((th i).f k) =
      ((Sp R).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * t := by
  obtain ⟨τ, -, h⟩ := h
  have hp : p ∈ (M.pull x).U (fun _ => k) := mem_pull.2 hk
  refine ⟨gm (𝟙 _) p _ (τ.s fun _ => k), fun i => ?_⟩
  have e := congrArg (gs (𝟙 _) p _) (h i (fun _ => k) (RepBC.pull_le M x _))
  rw [gs_appLE x _ _ _ (𝟙 _) p hp, gs_mul _ p _ hp, gs_res _ p _ hp, gs_one p ⊤ trivial, Category.id_comp] at e
  rw [← gs_unit _ p _ hp]
  exact e
end GlobalTheory.ZM.RepMap
