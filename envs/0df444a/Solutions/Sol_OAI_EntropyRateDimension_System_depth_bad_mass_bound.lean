-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.depth_bad_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:08:57.630016+00:00
-- url     : https://prove2.me/submissions/445a59e5-6003-4035-8c65-be14740861b0

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uα
open scoped BigOperators
variable {α : Type uα} [Fintype α]
theorem h41n_sum_append {β : Type*} [Fintype β] {a b : ℕ} (g : (Fin (a+b) → β) → ℝ) :
    ∑ W, g W = ∑ x : Fin a → β, ∑ y : Fin b → β, g (Fin.append x y) := by
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  rfl

theorem h41n_wordWeight_append {ι : Type*} [Fintype ι] (S : System ι) {m n : ℕ}
    (v1 : Fin m → ι) (v2 : Fin n → ι) :
    S.wordWeight (Fin.append v1 v2) = S.wordWeight v1 * S.wordWeight v2 := by
  simp only [System.wordWeight]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem h41n_wordDepth_sum {ι : Type*} [Fintype ι] (S : System ι) {n : ℕ} (w : Fin n → ι) :
    S.wordDepth w = ∑ j, S.letterDepth (w j) := by
  unfold System.wordDepth System.letterDepth
  rw [System.completeMap_slope, Finset.abs_prod,
    Real.log_prod (fun j _ => (S.ratio_pos (w j)).ne'), ← Finset.sum_div, Finset.sum_neg_distrib]

theorem h41n_lyap {ι : Type*} [Fintype ι] (S : System ι) :
    S.lyapunov = ∑ a, S.weight a * S.letterDepth a := by
  unfold System.lyapunov System.letterDepth
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem h41n_var_sum {ι : Type*} [Fintype ι] (S : System ι) (X : ι → ℝ)
    (hX0 : ∑ a, S.weight a * X a = 0) (n : ℕ) :
    ∑ w : Fin n → ι, S.wordWeight w * (∑ j, X (w j))^2 = n * ∑ a, S.weight a * X a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h41n_sum_append (a := n) (b := 1)]
    have key : ∀ (w : Fin n → ι) (v : Fin 1 → ι),
        S.wordWeight (Fin.append w v) * (∑ j, X (Fin.append w v j))^2 =
        S.wordWeight w * (S.weight (v 0) *
          ((∑ j, X (w j))^2 + 2 * (∑ j, X (w j)) * X (v 0) + X (v 0)^2)) := by
      intro w v
      have hv : S.wordWeight v = S.weight (v 0) := by simp [System.wordWeight]
      rw [h41n_wordWeight_append, Fin.sum_univ_add, hv]
      simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_one]
      ring
    simp only [key]
    trans ∑ w : Fin n → ι, S.wordWeight w * ((∑ j, X (w j))^2 + ∑ a, S.weight a * X a^2)
    · apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.mul_sum]
      congr 1
      rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
        (fun v : Fin 1 → ι => S.weight (v 0) *
          ((∑ j, X (w j))^2 + 2 * (∑ j, X (w j)) * X (v 0) + X (v 0)^2))
        (fun a => S.weight a * ((∑ j, X (w j))^2 + 2 * (∑ j, X (w j)) * X a + X a^2))
        (fun v => rfl)]
      have e : ∀ a, S.weight a * ((∑ j, X (w j))^2 + 2 * (∑ j, X (w j)) * X a + X a^2) =
          (∑ j, X (w j))^2 * S.weight a + 2 * (∑ j, X (w j)) * (S.weight a * X a) +
            S.weight a * X a^2 := fun a => by ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, S.weight_sum, hX0]
      ring
    · rw [Finset.sum_congr rfl (fun w _ => mul_add _ _ _), Finset.sum_add_distrib, ih,
        ← Finset.sum_mul, S.wordWeight_sum]
      push_cast
      ring

theorem solution (S : System α) {A : ℝ} (hA : S.lyapunov < A)
    {n : ℕ} (hn : 0 < n) :
    (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0) ≤
      S.depthVariance/((n : ℝ)*(A-S.lyapunov)^2) := by
  let X : α → ℝ := fun a => S.letterDepth a - S.lyapunov
  have hX0 : ∑ a, S.weight a * X a = 0 := by
    simp only [X, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, S.weight_sum, one_mul]
    rw [← h41n_lyap]
    ring
  have hV : ∑ a, S.weight a * X a ^ 2 = S.depthVariance := rfl
  have hD : ∀ w : Fin n → α, S.wordDepth w - n * S.lyapunov = ∑ j, X (w j) := by
    intro w
    rw [h41n_wordDepth_sum]
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hAl : 0 < A - S.lyapunov := sub_pos.mpr hA
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hK : 0 < ((n:ℝ) * (A - S.lyapunov))^2 := by positivity
  calc (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)
      ≤ ∑ w : Fin n → α, S.wordWeight w * (∑ j, X (w j))^2 / ((n:ℝ) * (A - S.lyapunov))^2 := by
        apply Finset.sum_le_sum
        intro w _
        split_ifs with h
        · rw [le_div_iff₀ hK, ← hD]
          apply mul_le_mul_of_nonneg_left _ (S.wordWeight_pos w).le
          have h1 : (n:ℝ) * (A - S.lyapunov) ≤ S.wordDepth w - n * S.lyapunov := by nlinarith
          exact pow_le_pow_left₀ (by positivity) h1 2
        · exact div_nonneg (mul_nonneg (S.wordWeight_pos w).le (sq_nonneg _)) hK.le
    _ = (∑ w : Fin n → α, S.wordWeight w * (∑ j, X (w j))^2) / ((n:ℝ) * (A - S.lyapunov))^2 := by
        rw [Finset.sum_div]
    _ = S.depthVariance / ((n:ℝ) * (A - S.lyapunov)^2) := by
        rw [h41n_var_sum S X hX0 n, hV]
        have h1 : (n:ℝ) ≠ 0 := hnpos.ne'
        have h2 : A - S.lyapunov ≠ 0 := hAl.ne'
        field_simp

