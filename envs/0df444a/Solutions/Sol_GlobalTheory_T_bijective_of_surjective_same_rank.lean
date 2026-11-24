-- Prove2me | solution 1 for GlobalTheory.T.bijective_of_surjective_same_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:52.187808+00:00
-- url     : https://prove2.me/submissions/8e30e248-6fa6-414e-aa0b-f510a4fc044e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BijectiveOfSurjectiveSameRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BijectiveOfSurjectiveSameRankStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_bijective_of_surjective_of_VB


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
theorem _root_.solution : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B, Function.Surjective f → Function.Bijective f := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | exact GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB <;> assumption)
end _root_.GlobalTheory.T
