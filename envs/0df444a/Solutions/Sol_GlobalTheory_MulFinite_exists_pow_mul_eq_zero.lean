-- Prove2me | solution 1 for GlobalTheory.MulFinite.exists_pow_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:16.081295+00:00
-- url     : https://prove2.me/submissions/e0f8e072-f882-4814-8bb4-c8905fce2385

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {k R : Type} [CommRing k] [CommRing R] (hk : IsField k) (φ : k →+* R)
    (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hk.toField
  obtain ⟨p, hp, h0⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h0
  rw [add_comm]
  exact h0
end GlobalTheory.MulFinite
