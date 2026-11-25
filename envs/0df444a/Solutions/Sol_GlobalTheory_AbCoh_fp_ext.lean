-- Prove2me | solution 1 for GlobalTheory.AbCoh.fp_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:02.910815+00:00
-- url     : https://prove2.me/submissions/654006ba-5c13-453b-9425-95cf54978e86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgProjectiveConstantRankExtensionAndProd
import Theorems.Thm_GlobalTheory_AbCoh_fp_prod

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
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ)
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hW : FP R W a) (hH : FP R H b) : FP R M (a + b) := by
  have hWH := fp_prod R W H a b hW hH
  obtain ⟨-, hHp, -⟩ := hH
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : H →ₗ[R] H) hp
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  obtain ⟨hf, hpr, hr⟩ := hWH
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun q => ?_⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) q, hr q]
end GlobalTheory.AbCoh
