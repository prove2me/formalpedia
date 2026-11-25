-- Prove2me | solution 1 for JEPAGeneralization.empirical_jepa_risk_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:47:23.744464+00:00
-- url     : https://prove2.me/submissions/05017fb9-d06c-4df4-8f9a-bba4fc0c1389

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic
set_option autoImplicit false
open Finset
namespace JEPAGeneralization

lemma Eprod {X : Type*} [Fintype X] (pX : X → ℝ) {n : ℕ} (h : Fin n → X → ℝ) :
    ∑ D : Fin n → X, datasetProb pX D * ∏ l, h l (D l) = ∏ l, ∑ y, pX y * h l y := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun D _ => ?_
  unfold datasetProb
  rw [← Finset.prod_mul_distrib]

lemma E1 {X : Type*} [Fintype X] (pX : X → ℝ) (hs : ∑ x, pX x = 1) {n : ℕ} (i : Fin n)
    (F : X → ℝ) : ∑ D : Fin n → X, datasetProb pX D * F (D i) = ∑ x, pX x * F x := by
  have h1 : ∀ D : Fin n → X, F (D i) = ∏ l, (if l = i then F (D l) else 1) := by
    intro D; simp
  simp only [h1]
  rw [Eprod pX (fun l y => if l = i then F y else 1)]
  have h2 : ∀ l, ∑ y, pX y * (if l = i then F y else 1) =
      if l = i then ∑ x, pX x * F x else 1 := by
    intro l; split_ifs <;> simp [hs]
  simp only [h2]
  simp

lemma E2 {X : Type*} [Fintype X] (pX : X → ℝ) (hs : ∑ x, pX x = 1) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (F : X → X → ℝ) :
    ∑ D : Fin n → X, datasetProb pX D * F (D i) (D j) =
      ∑ x, ∑ z, pX x * pX z * F x z := by
  classical
  have h1 : ∀ D : Fin n → X, F (D i) (D j) = ∑ x, ∑ z, F x z *
      ∏ l, ((if l = i then (if D l = x then (1:ℝ) else 0) else 1) *
        (if l = j then (if D l = z then (1:ℝ) else 0) else 1)) := by
    intro D
    simp only [Finset.prod_mul_distrib]
    simp
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h3 : ∀ D : Fin n → X, datasetProb pX D * (F x z * ∏ l, ((if l = i then
      (if D l = x then (1:ℝ) else 0) else 1) * (if l = j then (if D l = z then (1:ℝ) else 0) else 1)))
      = F x z * (datasetProb pX D * ∏ l, ((if l = i then
      (if D l = x then (1:ℝ) else 0) else 1) * (if l = j then (if D l = z then (1:ℝ) else 0) else 1))) := by
    intro D; ring
  simp only [h3]
  rw [← Finset.mul_sum, Eprod pX (fun l y => (if l = i then (if y = x then (1:ℝ) else 0) else 1) *
    (if l = j then (if y = z then (1:ℝ) else 0) else 1))]
  have h2 : ∀ l, ∑ y, pX y * ((if l = i then (if y = x then (1:ℝ) else 0) else 1) *
      (if l = j then (if y = z then (1:ℝ) else 0) else 1)) =
      (if l = i then pX x else 1) * (if l = j then pX z else 1) := by
    intro l
    by_cases hi : l = i
    · subst hi; simp [hij]
    · by_cases hj : l = j
      · subst hj; simp [hi]
      · simp [hi, hj, hs]
  simp only [h2]
  rw [Finset.prod_mul_distrib]
  simp
  ring

theorem empirical_jepa_risk_unbiased {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w)
    (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) (n : ℕ) (hn : 2 ≤ n) :
    ∑ D : Fin n → X, datasetProb pX D * empRiskN pX w f g a D = spectralLoss pX w f g a := by
  obtain ⟨_, hs, hpos, _, _⟩ := hw
  set φ : X → X → ℝ := fun x x' => dot (g (f x) a) (f x') with hφ
  set T : X → X → ℝ := fun x x' => transProb pX w a x x' with hT
  set F1 : X → ℝ := fun x => ∑ x', T x x' * φ x x' with hF1
  set F2 : X → X → ℝ := fun x z => ∑ x', T z x' * φ x x' ^ 2 with hF2
  have hR : ∀ D : Fin n → X, empRiskN pX w f g a D =
      -2 * ((1 / (n : ℝ)) * ∑ i, F1 (D i)) +
        (1 / ((n : ℝ) * ((n : ℝ) - 1))) * ∑ i, ∑ j, (if i = j then 0 else F2 (D i) (D j)) := by
    intro D; rfl
  simp only [hR, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hA : ∀ i : Fin n, ∑ D : Fin n → X, datasetProb pX D * (-2 * (1 / (n : ℝ) * F1 (D i))) =
      -2 * (1 / (n : ℝ)) * ∑ x, ∑ x', w x x' a * φ x x' := by
    intro i
    have := E1 pX hs i F1
    have e : ∀ D : Fin n → X, datasetProb pX D * (-2 * (1 / (n : ℝ) * F1 (D i))) =
        -2 * (1 / (n : ℝ)) * (datasetProb pX D * F1 (D i)) := fun D => by ring
    simp only [e, ← Finset.mul_sum, this]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hF1, hT, transProb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    have := (hpos x).ne'
    field_simp
  have hB : ∀ i j : Fin n, ∑ D : Fin n → X, datasetProb pX D *
      (1 / ((n : ℝ) * ((n : ℝ) - 1)) * (if i = j then 0 else F2 (D i) (D j))) =
      if i = j then 0 else (1 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ x, ∑ x', pX x * nextMarg w a x' * φ x x' ^ 2 := by
    intro i j
    split_ifs with hij
    · simp
    · have := E2 pX hs i j hij F2
      have e : ∀ D : Fin n → X, datasetProb pX D * (1 / ((n : ℝ) * ((n : ℝ) - 1)) *
          F2 (D i) (D j)) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) * (datasetProb pX D * F2 (D i) (D j)) :=
        fun D => by ring
      simp only [e, ← Finset.mul_sum, this]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hF2, hT, transProb, nextMarg, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      refine Finset.sum_congr rfl fun z _ => ?_
      have := (hpos z).ne'
      field_simp
  rw [Finset.sum_comm]
  simp only [hA]
  have hB' : ∀ i : Fin n, ∑ D : Fin n → X, ∑ j, datasetProb pX D *
      (1 / ((n : ℝ) * ((n : ℝ) - 1)) * (if i = j then 0 else F2 (D i) (D j))) =
      ∑ j, (if i = j then 0 else (1 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ x, ∑ x', pX x * nextMarg w a x' * φ x x' ^ 2) := by
    intro i; rw [Finset.sum_comm]; simp only [hB]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → X)))]
  simp only [hB']
  set C2 := ∑ x, ∑ x', pX x * nextMarg w a x' * φ x x' ^ 2
  set C1 := ∑ x, ∑ x', w x x' a * φ x x'
  have hite : ∀ i j : Fin n, (if i = j then (0:ℝ) else 1 / ((n : ℝ) * ((n : ℝ) - 1)) * C2) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) * C2 - if i = j then 1 / ((n : ℝ) * ((n : ℝ) - 1)) * C2 else 0 := by
    intro i j; split_ifs <;> simp
  simp only [hite, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold spectralLoss
  field_simp
  ring

end JEPAGeneralization
open JEPAGeneralization in
theorem solution {X A : Type*} [Fintype X] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w)
    (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (a : A) (n : ℕ) (hn : 2 ≤ n) :
    ∑ D : Fin n → X, datasetProb pX D * empRiskN pX w f g a D = spectralLoss pX w f g a :=
  empirical_jepa_risk_unbiased pX w hw f g a n hn
