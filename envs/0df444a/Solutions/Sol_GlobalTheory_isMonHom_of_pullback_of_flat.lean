-- Prove2me | solution 1 for GlobalTheory.isMonHom_of_pullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:50.415352+00:00
-- url     : https://prove2.me/submissions/24f257fe-014e-4811-ac4c-c4a1eb6f91db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Theorems.Thm_GlobalTheory_pullback_map_injective_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {S S' : Scheme.{0}} (f : S' ⟶ S) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
namespace GlobalTheory
theorem _root_.solution {G G' : Over S} [MonObj G] [MonObj G'] (F : G ⟶ G')
    [Flat G.hom] [IsSeparated G'.hom] [h : IsMonHom ((Over.pullback f).map F)] : IsMonHom F := by
  have h1 : Flat (𝟙_ (Over S)).hom := by
    change Flat (𝟙 S)
    infer_instance
  have h2 : Flat (G ⊗ G).hom := by
    change Flat (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  constructor
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.one_hom ((Over.pullback f).map F)
    simp only [Functor.obj.η_def, Category.assoc] at this
    rw [Functor.map_comp]
    exact (cancel_epi _).1 this
  · apply pullback_map_injective_of_flat f
    have := IsMonHom.mul_hom ((Over.pullback f).map F)
    simp only [Functor.obj.μ_def, Category.assoc] at this
    rw [Functor.LaxMonoidal.μ_natural_assoc] at this
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi _).1 this
end GlobalTheory
