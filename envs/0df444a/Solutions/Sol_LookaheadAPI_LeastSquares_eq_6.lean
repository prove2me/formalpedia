-- Prove2me | solution 1 for LookaheadAPI.LeastSquares.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:33:21.306498+00:00
-- url     : https://prove2.me/submissions/39c0acfe-fdff-4e10-a9e1-8063e7b40ee9

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_BellmanOperator
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

open Matrix

namespace Aux_LALSeq6
open LookaheadAPI.LeastSquares

lemma ls_unique {S : Type*} [Fintype S] [DecidableEq S] {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : Finset S) (y : S → ℝ) (hdet : (gram Φ D).det ≠ 0) (θ : Fin d → ℝ)
    (hmin : ∀ θ' : Fin d → ℝ, ∑ i ∈ D, ((Φ *ᵥ θ) i - y i) ^ 2 ≤ ∑ i ∈ D, ((Φ *ᵥ θ') i - y i) ^ 2) :
    Φ *ᵥ θ = lsOp Φ D *ᵥ y := by
  set F := featuresOn Φ D with hF
  set G := gram Φ D with hG
  set yD : D → ℝ := restrictTo D *ᵥ y with hyD
  have hyDi : ∀ i : D, yD i = y i := by
    intro i
    simp [hyD, restrictTo, mulVec, dotProduct]
  have hobj : ∀ θ' : Fin d → ℝ, ∑ i ∈ D, ((Φ *ᵥ θ') i - y i) ^ 2 =
      (F *ᵥ θ' - yD) ⬝ᵥ (F *ᵥ θ' - yD) := by
    intro θ'
    rw [← Finset.sum_coe_sort D]
    simp only [dotProduct, Pi.sub_apply, hyDi, sq]
    rfl
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set θs : Fin d → ℝ := G⁻¹ *ᵥ (Fᵀ *ᵥ yD) with hθs
  set r : D → ℝ := F *ᵥ θs - yD with hr
  have hnormal : Fᵀ *ᵥ r = 0 := by
    rw [hr, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hθs, Matrix.mulVec_mulVec]
    have : Fᵀ * F = G := rfl
    rw [this, Matrix.mul_nonsing_inv G hGu, Matrix.one_mulVec, sub_self]
  have hpyth : ∀ θ' : Fin d → ℝ, (F *ᵥ θ' - yD) ⬝ᵥ (F *ᵥ θ' - yD) =
      (F *ᵥ (θ' - θs)) ⬝ᵥ (F *ᵥ (θ' - θs)) + r ⬝ᵥ r := by
    intro θ'
    have e1 : F *ᵥ θ' - yD = F *ᵥ (θ' - θs) + r := by
      rw [hr, Matrix.mulVec_sub]; abel
    have e2 : (F *ᵥ (θ' - θs)) ⬝ᵥ r = 0 := by
      rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, hnormal, dotProduct_zero]
    rw [e1, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm r (F *ᵥ (θ' - θs)), e2]
    ring
  have h1 := hmin θs
  rw [hobj, hobj, hpyth, hpyth, sub_self, Matrix.mulVec_zero, zero_dotProduct] at h1
  have hz : (F *ᵥ (θ - θs)) ⬝ᵥ (F *ᵥ (θ - θs)) = 0 := by
    have : 0 ≤ (F *ᵥ (θ - θs)) ⬝ᵥ (F *ᵥ (θ - θs)) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    linarith
  rw [dotProduct_self_eq_zero] at hz
  have hGz : G *ᵥ (θ - θs) = 0 := by
    have : G = Fᵀ * F := rfl
    rw [this, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have he : θ - θs = 0 := by
    have : θ - θs = G⁻¹ *ᵥ (G *ᵥ (θ - θs)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hGu, Matrix.one_mulVec]
    rw [this, hGz, Matrix.mulVec_zero]
  have hθ : θ = θs := sub_eq_zero.1 he
  rw [hθ, hθs, hyD]
  simp only [lsOp, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rfl

end Aux_LALSeq6

open LookaheadAPI.LeastSquares Aux_LALSeq6 in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (εLA : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hrank : ∀ k : ℕ, (gram Φ (D k)).det ≠ 0)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) (k : ℕ) :
    J (k + 1) = Φ *ᵥ θ (k + 1) ∧
    Φ *ᵥ θ (k + 1) = lsOp Φ (D k) *ᵥ noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) := by
  obtain ⟨_, hmin, hJ⟩ := hrun k
  exact ⟨hJ, ls_unique Φ (D k) _ (hrank k) (θ (k + 1)) hmin⟩
