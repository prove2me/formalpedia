-- Prove2me | solution 1 for GlobalTheory.CoordChart.clear_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:30.419582+00:00
-- url     : https://prove2.me/submissions/073b047d-5c38-4f51-83bb-9f365a03fb08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoordChart
namespace GlobalTheory.CoordChart
theorem _root_.solution {o σ R L : Type} [CommRing o] [CommRing R] [CommRing L] (β : o →+* R) (φ : R →+* L)
    (v : σ → R) (w : σ → L) (t : R) (h : ∀ a, w a * φ t = φ (v a)) (F : MvPolynomial σ o) :
    ∃ (r : R) (m : ℕ), MvPolynomial.eval₂ (φ.comp β) w F * φ t ^ m = φ r := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨β c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r, m, h1⟩ := hp
    obtain ⟨r', m', h2⟩ := hq
    refine ⟨r * t ^ m' + r' * t ^ m, m + m', ?_⟩
    rw [MvPolynomial.eval₂_add, map_add, map_mul, map_mul, ← h1, ← h2, map_pow, map_pow]
    ring
  | mul_X p a hp =>
    obtain ⟨r, m, h1⟩ := hp
    refine ⟨r * v a, m + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, ← h1, ← h a]
    ring
end GlobalTheory.CoordChart
