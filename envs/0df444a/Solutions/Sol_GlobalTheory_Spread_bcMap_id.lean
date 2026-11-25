-- Prove2me | solution 1 for GlobalTheory.Spread.bcMap_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:59.308543+00:00
-- url     : https://prove2.me/submissions/4eb0bcbc-e233-4b4d-bf96-92f198df4f8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable {R R' A : Type} [CommRing R] [CommRing R'] [CommRing A] [Algebra k R] [Algebra k R']
  [Algebra k A]
namespace GlobalTheory.Spread
theorem _root_.solution : bcMap pB (AlgHom.id k R) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.id_comp]
  · rw [bcMap_snd, Category.id_comp]
    exact (congrArg _ (Spec.map_id _)).trans (Category.comp_id _)
end GlobalTheory.Spread
