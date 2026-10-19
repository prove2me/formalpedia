-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.expected_capacity_targets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:35:41.980657+00:00
-- url     : https://prove2.me/submissions/7189a8f4-039a-41f4-9f8a-db4a695dba57

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]
theorem h41n_sum_append {α : Type*} [Fintype α] {a b : ℕ} (g : (Fin (a+b) → α) → ℝ) :
    ∑ W, g W = ∑ x : Fin a → α, ∑ y : Fin b → α, g (Fin.append x y) := by
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  rfl

open OAI OAI.EntropyRateDimension in
theorem hn2_wordAverage_segment {α : Type*} [Fintype α] (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by
  obtain ⟨r, rfl⟩ : ∃ r, H = j + n + r := ⟨H - (j+n), by omega⟩
  have hww : ∀ {a b : ℕ} (x : Fin a → α) (y : Fin b → α),
      S.wordWeight (Fin.append x y) = S.wordWeight x * S.wordWeight y := by
    intro a b x y
    simp only [System.wordWeight]
    rw [Fin.prod_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hl : ∀ (a : Fin j → α) (b : Fin n → α) (c : Fin r → α),
      ((List.ofFn a ++ List.ofFn b ++ List.ofFn c).drop j).take n = List.ofFn b := by
    intro a b c
    rw [List.append_assoc, List.drop_left' (by simp), List.take_left' (by simp)]
  unfold System.wordAverage
  rw [h41n_sum_append]
  rw [h41n_sum_append]
  simp only [hww, List.ofFn_fin_append, hl]
  trans ∑ a : Fin j → α, ∑ b : Fin n → α, S.wordWeight a * (S.wordWeight b * f (List.ofFn b))
  · apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    rw [show S.wordWeight a * (S.wordWeight b * f (List.ofFn b)) = (∑ c : Fin r → α, S.wordWeight c) *
      (S.wordWeight a * (S.wordWeight b * f (List.ofFn b))) by rw [S.wordWeight_sum, one_mul],
      Finset.sum_mul]
    apply Finset.sum_congr rfl; intro c _; ring
  · simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, S.wordWeight_sum, one_mul]

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed in
theorem hn2_law_cast {α β : Type*} [Fintype α] [DecidableEq β] (S : System α) (tag : α → β)
    {m n : ℕ} (h : m = n) (w : Fin n → α) :
    law S tag (fun i : Fin m => w (Fin.cast h i)) = law S tag w := by
  subst h; rfl

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed in
theorem hn2_listLaw_ofFn {α β : Type*} [Fintype α] [DecidableEq β] (S : System α) (tag : α → β)
    {n : ℕ} (w : Fin n → α) : listLaw S tag (List.ofFn w) = law S tag w := by
  unfold listLaw
  have : (List.ofFn w).get = fun i => w (Fin.cast (List.length_ofFn) i) := by
    funext i; simp; rfl
  rw [this, hn2_law_cast]

open OAI OAI.EntropyRateDimension in
theorem hn2_listDepth_ofFn {α : Type*} [Fintype α] (S : System α) {n : ℕ} (w : Fin n → α) :
    S.listDepth (List.ofFn w) = S.wordDepth w := by
  unfold System.listDepth System.wordDepth
  rw [System.completeMap_slope, Finset.abs_prod, Real.log_prod (fun j _ => (S.ratio_pos (w j)).ne'),
    List.map_ofFn, List.sum_ofFn, ← Finset.sum_neg_distrib, Finset.sum_div]
  rfl

open OAI OAI.EntropyRateDimension in
theorem hn2_listDepth_append {α : Type*} [Fintype α] (S : System α) (U V : List α) :
    S.listDepth (U ++ V) = S.listDepth U + S.listDepth V := by
  unfold System.listDepth; simp

open OAI OAI.EntropyRateDimension in
theorem hn2_sum_target_shift (f : ℤ → ℝ) (a B c T : ℤ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hB : B+c ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, if a ≤ L-c ∧ L-c ≤ B then f (L-c) else 0)=
      ∑ ℓ ∈ Finset.Icc a B, f ℓ := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun L => L - c) (fun ℓ => ℓ + c)
  · intro L hL
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hL ⊢
    exact hL.2
  · intro ℓ hℓ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hℓ ⊢
    refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  · intro L _; simp
  · intro ℓ _; simp
  · intro L _; rfl

theorem solution (S : System α) (tag : α → β)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B T : ℤ)
    (ha : 1 ≤ a)
    (hcover : ∀ W : List α, 0 ≤ ⌈S.listDepth (W.take j)⌉ ∧ B+⌈S.listDepth (W.take j)⌉ ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j))=
      pairBudget S tag A' a B n := by
  classical
  set c : List α → ℤ := fun W => ⌈S.listDepth (W.take j)⌉ with hc
  let G : List α → ℝ := fun V => if S.listDepth V ≤ A'*n then
      ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag V) ℓ else 0
  have hW : ∀ W : List α, (∑ L ∈ Finset.Icc 1 T, retainedCapacity S tag A' n a B L W j) =
      G ((W.drop j).take n) := by
    intro W
    have hdep : S.listDepth (W.take (j+n)) - S.listDepth (W.take j) = S.listDepth ((W.drop j).take n) := by
      rw [List.take_add, hn2_listDepth_append]; ring
    unfold retainedCapacity Retained
    simp only [hdep]
    simp only [G]
    by_cases hd : S.listDepth ((W.drop j).take n) ≤ A'*n
    · rw [if_pos hd]
      simp only [hd, true_and]
      obtain ⟨h0, h1⟩ := hcover W
      have := hn2_sum_target_shift
        (fun ℓ => capacity (listLaw S tag ((W.drop j).take n)) ℓ) a B (c W) T ha h0 h1
      exact this
    · rw [if_neg hd]
      apply Finset.sum_eq_zero; intro L _
      rw [if_neg (fun h => hd h.1)]
  have hL : (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j)) =
      S.wordAverage H (fun W => G ((W.drop j).take n)) := by
    unfold System.wordAverage
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro W _
    rw [← Finset.mul_sum, hW]
  rw [hL, hn2_wordAverage_segment S hH G]
  unfold System.wordAverage pairBudget
  apply Finset.sum_congr rfl; intro w _
  simp only [G, hn2_listDepth_ofFn, hn2_listLaw_ofFn]
  split_ifs <;> simp

