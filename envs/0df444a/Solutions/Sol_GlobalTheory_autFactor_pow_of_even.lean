-- Prove2me | solution 1 for GlobalTheory.autFactor_pow_of_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:47.441939+00:00
-- url     : https://prove2.me/submissions/5e4a266c-5f03-4326-8a40-e6d638cf4237

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMemThetaLevelCharApplyNeZero
import Theorems.Thm_GlobalTheory_eC_nat_mul
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
private lemma eC_even_mul_half_char_eq_one {g : ℕ} {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {N : ℕ} (hN : Even N) (n n' : Fin g → ℤ) :
    eC ((N : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)) = 1 := by
  have half : ∀ c : Fin g → ℝ, (∀ i, c i = 0 ∨ c i = 1 / 2) → ∃ p : Fin g → ℤ, ∀ i, (c i : ℂ) = (p i : ℂ) / 2 := by
    intro c hc
    refine ⟨fun i => if c i = 0 then 0 else 1, fun i => ?_⟩
    rcases hc i with h | h
    · simp [h]
    · have : c i ≠ 0 := by rw [h]; norm_num
      simp only [h]
      norm_num
  obtain ⟨p, hp⟩ := half a ha
  obtain ⟨q, hq⟩ := half b hb
  obtain ⟨m, rfl⟩ := hN
  have key : ((m + m : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) =
      ((∑ i, (m : ℤ) * p i * n' i - ∑ i, (m : ℤ) * q i * n i : ℤ) : ℂ) := by
    simp only [dotProduct, ofRealVec, ofIntVec, hp, hq]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, eC_int]
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}
namespace GlobalTheory
theorem _root_.solution (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {N : ℕ} (hN : Even N) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    autFactor a b τ n n' z ^ N =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
  rw [autFactor, mul_pow, ← eC_nat_mul, ← eC_nat_mul, eC_even_mul_half_char_eq_one ha hb hN n n', _root_.one_mul]
  congr 1
  ring
end GlobalTheory
