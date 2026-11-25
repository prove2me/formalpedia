-- Prove2me | solution 1 for GlobalTheory.AbCoh.fp_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:42.947943+00:00
-- url     : https://prove2.me/submissions/165cacad-8c9d-43ee-a162-11c0b1e4f668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgProjectiveConstantRankExtensionAndProd

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
theorem _root_.solution (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup H] [Module R H] (a b : ℕ) (hW : FP R W a) (hH : FP R H b) :
    FP R (W × H) (a + b) := by
  obtain ⟨hWf, hWp, hWr⟩ := hW
  obtain ⟨hHf, hHp, hHr⟩ := hH
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have := Module.rankAtStalk_prod (R := R) W H
  rw [congrFun this p, Pi.add_apply, hWr p, hHr p]
end GlobalTheory.AbCoh
