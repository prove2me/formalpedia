-- Prove2me | solution 1 for GlobalTheory.SS.PowCmp.le_of_zpow_mul_unit_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:41:08.384801+00:00
-- url     : https://prove2.me/submissions/ad24bb04-60ab-4b91-88a6-4ede97777727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Theorems.Thm_GlobalTheory_SS_PowCmp_j_cstR
import Theorems.Thm_GlobalTheory_SS_PowCmp_not_isUnit_cstR
import Theorems.Thm_GlobalTheory_SS_PowCmp_j_app_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PowCmp
namespace GlobalTheory.SS.PowCmp
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (M : Model R A) (W : M.Y.left.Opens), ((W : Set M.Y.left) ∩ M.sp).Nonempty → ∀ (σ s : Γ(M.Y.left, W)) (a b : ℤ), IsUnit σ → cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ a) * (M.j.app W).hom σ = cstK A (M.j ⁻¹ᵁ W) (algebraMap R K π ^ b) * (M.j.app W).hom s → b ≤ a := by
  intro R K _ _ _ _ _ _ π hirr A M U hU σ s a b hs e'
  by_contra hlt
  have hπ : π ∈ IsLocalRing.maximalIdeal R := hirr.not_isUnit
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by omega⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hirr.ne_zero
  have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ a)) := (IsUnit.mk0 _ (zpow_ne_zero a hp)).map _
  rw [hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cstR, ← map_mul] at e'
  have := j_app_injective M U (hu.mul_left_cancel e')
  rw [this, pow_succ, map_mul] at hs
  exact not_isUnit_cstR M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))
end GlobalTheory.SS.PowCmp
