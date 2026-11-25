-- Prove2me | solution 1 for GlobalTheory.ThetaAddition.addition_level_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:57:20.696709+00:00
-- url     : https://prove2.me/submissions/572dc77b-4680-4441-8749-9a11602d9e7f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
import Theorems.Thm_GlobalTheory_ThetaAddition_exists_sum_mul
import Theorems.Thm_GlobalTheory_ThetaAddition_left_mem
import Theorems.Thm_GlobalTheory_ThetaAddition_right_mem
import Theorems.Thm_GlobalTheory_EvaluationSpanTopToricGeometry_exists_sum_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAddition
namespace GlobalTheory.ThetaAddition
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f f' : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → (Differentiable ℂ f' ∧ ∀ (n n' : Fin g → ℤ) z, f' (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f' z) → ∃ (n : ℕ) (h k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, (Differentiable ℂ (h i) ∧ ∀ (n n' : Fin g → ℤ) z, (h i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (h i) z) ∧ (Differentiable ℂ (k i) ∧ ∀ (n n' : Fin g → ℤ) z, (k i) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((2 * N : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (k i) z)) ∧ ∀ z w, f (z + w) * f' (z - w) = ∑ i, h i z * k i w) := by
  intro H1 H2 g τ hτ N hN f f' hf hf'
  have hN2 : 1 ≤ 2 * N := by omega
  have hle : thetaLevel (2 * N) τ ≤ _ := fun φ hφ => H2 g τ hτ (2 * N) hN2 φ hφ
  haveI : FiniteDimensional ℂ (thetaLevel (2 * N) τ) := by
    haveI := FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun (c : Fin g → Fin (2 * N)) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / (2 * N : ℕ)) 0 (((2 * N : ℕ) : ℂ) • z) (((2 * N : ℕ) : ℂ) • τ)))
    exact Submodule.finiteDimensional_of_le hle
  exact exists_sum_mul (thetaLevel (2 * N) τ) (thetaLevel (2 * N) τ)
    (fun z w => f (z + w) * f' (z - w)) (left_mem τ N hf hf') (right_mem τ N hf hf')
end GlobalTheory.ThetaAddition
