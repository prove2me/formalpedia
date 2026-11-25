-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.locTriv_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:28.070963+00:00
-- url     : https://prove2.me/submissions/efcfaf80-a1fa-4eb0-b8ff-08c0712bc986

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_GlobalTheory_AbLaw_CubeGen_TrivAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution (p : Y ⟶ T) : locTriv L φ ε p ⊆ fibTriv L φ ε p := by
  rintro t ⟨U, hU, h⟩
  have hr : Set.range (T.fromSpecResidueField t) = {t} := Scheme.range_fromSpecResidueField t
  refine ⟨T.residueField t, inferInstance, T.fromSpecResidueField t, _, _, _, hr.ge rfl,
    IsPullback.of_hasPullback p (T.fromSpecResidueField t), ?_⟩
  have := h.comp (IsOpenImmersion.lift (p ⁻¹ᵁ U).ι (pullback.fst p (T.fromSpecResidueField t)) (by
    rw [Scheme.Pullback.range_fst, hr, Scheme.Opens.range_ι]
    intro y hy
    exact (congrArg (· ∈ U) hy).mpr hU))
  rwa [IsOpenImmersion.lift_fac] at this
end GlobalTheory.AbLaw.CubeGen
