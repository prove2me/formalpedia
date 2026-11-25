-- Prove2me | solution 1 for GlobalTheory.T.exterior_square_vector_bundle_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:43.730974+00:00
-- url     : https://prove2.me/submissions/f60c8415-9527-4061-b71e-3beb2174d9f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRankStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_vb_exteriorPower_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (g : ℕ), VB R V g → VB R (⋀[R]^2 V) (g.choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | exact GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.vb_exteriorPower_two <;> assumption)
end _root_.GlobalTheory.T
