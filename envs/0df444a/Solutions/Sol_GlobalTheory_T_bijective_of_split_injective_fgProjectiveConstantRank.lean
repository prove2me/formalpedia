-- Prove2me | solution 1 for GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:22:25.893154+00:00
-- url     : https://prove2.me/submissions/2bf64596-711c-440b-9642-4edbf99f6c7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfSplitInjectiveFgProjectiveConstantRan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfSplitInjectiveFgProjectiveConstantRanStatement
import Theorems.Thm_GlobalTheory_AbCoh_bijective_of_split_of_FP


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  first | exact @GlobalTheory.AbCoh.bijective_of_split_of_FP | exact GlobalTheory.AbCoh.bijective_of_split_of_FP | (intros; apply GlobalTheory.AbCoh.bijective_of_split_of_FP <;> assumption)
end _root_.GlobalTheory.T
