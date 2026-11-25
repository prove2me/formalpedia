-- Prove2me | solution 1 for GlobalTheory.Spread.eq_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:29:23.495277+00:00
-- url     : https://prove2.me/submissions/25e3f05b-fe79-475c-ae08-0ea9aebfabf9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra

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
theorem _root_.solution (f : R →ₐ[k] A)
    {j : pullback pB (spMap (algebraMap k A)) ⟶ pullback pB (spMap (algebraMap k R))}
    (h₁ : j ≫ pullback.fst _ _ = pullback.fst _ _)
    (h₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f.toRingHom) : j = bcMap pB f := by
  apply pullback.hom_ext
  · rw [h₁, bcMap_fst]
  · rw [h₂, bcMap_snd]
end GlobalTheory.Spread
