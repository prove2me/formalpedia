-- Prove2me | solution 1 for GlobalTheory.SympBasis.rel_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:00:06.110014+00:00
-- url     : https://prove2.me/submissions/d75d44e4-24f6-4dea-ab6c-7ea2e22ce6e7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis

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
open GlobalTheory GlobalTheory.SympBasis
namespace GlobalTheory.SympBasis
theorem _root_.solution {M U : Type} [CommMonoid M] [CommGroup U] (W : M → U → Prop) (h1 : W 1 1)
    (hm : ∀ x x' c c', W x c → W x' c' → W (x * x') (c * c')) {J : Type} (s : Finset J) (p : J → M) (u : J → U)
    (a : J → ℕ) (hp : ∀ i, W (p i) (u i)) : W (∏ i ∈ s, p i ^ a i) (∏ i ∈ s, u i ^ a i) := by
  classical
  have hpow : ∀ i (n : ℕ), W (p i ^ n) (u i ^ n) := by
    intro i n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact hm _ _ _ _ ih (hp i)
  refine Finset.induction_on s (by simpa using h1) ?_
  intro j t hj ih
  rw [Finset.prod_insert hj, Finset.prod_insert hj]
  exact hm _ _ _ _ (hpow j (a j)) ih
end GlobalTheory.SympBasis
