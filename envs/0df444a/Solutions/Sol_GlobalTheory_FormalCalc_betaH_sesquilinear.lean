-- Prove2me | solution 1 for GlobalTheory.FormalCalc.betaH_sesquilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:24.464983+00:00
-- url     : https://prove2.me/submissions/fecfaaee-e6a7-4755-936e-66b03733b6c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_BetaHSumSmulRight
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_OactH
import Theorems.Thm_GlobalTheory_FormalCalc_OactH_mul
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_smul_left
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_smul_right
import Theorems.Thm_GlobalTheory_FormalCalc_betaH_sum_right
import Theorems.Thm_GlobalTheory_FormalCalc_OactH_sum_smul
import Theorems.Thm_GlobalTheory_FormalCalc_dAct_add_and_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
namespace GlobalTheory.FormalCalc
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O),
    (∀ (a : O) ξ η, betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)) ∧
    (∀ (a b : O) ξ, OactH k B (a * b) ξ = OactH k B a (OactH k B b ξ)) ∧
    (∀ (a b : O) ξ, OactH k B (a + b) ξ = OactH k B a ξ + OactH k B b ξ) ∧
    (∀ ξ, OactH k B 1 ξ = ξ) ∧
    ∀ (n n' : ℕ) (c : Fin n → k) (a : Fin n → O) (c' : Fin n' → k) (a' : Fin n' → O) ξ η,
      (∑ i, c i • OactH k B (a i) ξ = ξ) → (∑ i, c' i • OactH k B (a' i) η = η) →
      (∀ ζ, ∑ i, ∑ i', (c i * c' i') • OactH k B (star (a i) * a' i') ζ = 0) →
      betaH k ξ η = 0 := by
  intro R _ d O _ _ k _ _ _ B
  obtain ⟨hadd, hone⟩ := dAct_add_and_one R d O k B
  refine ⟨betaH_OactH k B, OactH_mul k B, fun a b ξ => ?_, fun ξ => ?_, ?_⟩
  · simp only [OactH, star_add, hadd, Matrix.transpose_add, Matrix.add_mulVec, Prod.mk_add_mk]
  · simp [OactH, hone]
  · intro n n' c a c' a' ξ η hξ hη h0
    have h1 : betaH k ξ η = ∑ i, c i * betaH k ξ (OactH k B (star (a i)) η) := by
      conv_lhs => rw [← hξ]
      rw [betaH_sum_smul_left]
      simp only [betaH_OactH]
    have h2 : ∀ i, OactH k B (star (a i)) η =
        ∑ i', c' i' • OactH k B (star (a i) * a' i') η := fun i => by
      conv_lhs => rw [← hη]
      rw [OactH_sum_smul]
      simp only [OactH_mul]
    have h3 : betaH k ξ (∑ i, ∑ i', (c i * c' i') • OactH k B (star (a i) * a' i') η) = 0 := by
      rw [h0]; simp [betaH]
    rw [h1, ← h3, betaH_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2, betaH_sum_smul_right, betaH_sum_smul_right, Finset.mul_sum]
    simp only [mul_assoc]
end GlobalTheory.FormalCalc
