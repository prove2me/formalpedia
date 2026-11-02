-- Prove2me | solution 1 for LatticeHamSim.CommLR.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:31:41.575514+00:00
-- url     : https://prove2.me/submissions/d7f381a0-c74f-4e8a-b18a-7d477166c352

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
import Theorems.Thm_LatticeHamSim_CommLR_proposition_13_a
import Theorems.Thm_LatticeHamSim_CommLR_proposition_13_b
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_Eq37

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

@[simp]
lemma consEquiv_pair {m : ℕ} (A : Finset Λ) (f : Fin m → Finset Λ) :
    (Fin.consEquiv (fun _ : Fin (m + 1) => Finset Λ)) (A, f) = Fin.cons A f := rfl

lemma linkedGet_zero {k : ℕ} (Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedGet (Fin.cons Q Z') 0 = Q := by
  unfold linkedGet
  rw [dif_pos (Nat.succ_pos k)]
  rfl

lemma linkedGet_succ {k : ℕ} (Q : Finset Λ) (Z' : Fin k → Finset Λ) (j : ℕ) :
    linkedGet (Fin.cons Q Z') (j + 1) = linkedGet Z' j := by
  unfold linkedGet
  by_cases hj : j < k
  · have hj1 : j + 1 < k + 1 := Nat.succ_lt_succ hj
    rw [dif_pos hj1, dif_pos hj]
    rfl
  · have hj1 : ¬ j + 1 < k + 1 := fun h => hj (Nat.lt_of_succ_lt_succ h)
    rw [dif_neg hj1, dif_neg hj]

lemma linkedCondition_zero {k : ℕ} (X Q : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedCondition X (Fin.cons Q Z') 0 ↔ meets X Q := by
  unfold linkedCondition
  rw [if_pos rfl, linkedGet_zero]

lemma linkedCondition_one {k : ℕ} (X Q R : Finset Λ) (Z' : Fin k → Finset Λ) :
    linkedCondition X (Fin.cons Q (Fin.cons R Z')) 1 ↔ meets Q R := by
  unfold linkedCondition
  rw [if_neg (by decide), if_neg (by decide)]
  change meets (linkedGet (Fin.cons Q (Fin.cons R Z')) 0)
    (linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1)) ↔ meets Q R
  rw [linkedGet_zero, linkedGet_succ, linkedGet_zero]

lemma linkedCondition_add_two {k : ℕ} (X Q R : Finset Λ) (Z' : Fin k → Finset Λ) (i : ℕ) :
    linkedCondition X (Fin.cons Q (Fin.cons R Z')) (i + 2) ↔ linkedCondition (Q ∪ R) Z' i := by
  by_cases hi0 : i = 0
  · subst hi0
    unfold linkedCondition
    rw [if_neg (by decide), if_pos (by decide), if_pos rfl]
    change meets (linkedGet (Fin.cons Q (Fin.cons R Z')) 0 ∪
        linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1))
        (linkedGet (Fin.cons Q (Fin.cons R Z')) (0 + 1 + 1)) ↔
      meets (Q ∪ R) (linkedGet Z' 0)
    rw [linkedGet_zero, linkedGet_succ, linkedGet_zero, linkedGet_succ, linkedGet_succ]
  · have hi2 : i + 2 ≠ 0 := by omega
    unfold linkedCondition
    rw [if_neg hi2, if_neg hi0]
    have hmod : (i + 2) % 2 = i % 2 := Nat.add_mod_right i 2
    rw [hmod]
    split_ifs with heven
    · have hi_ge2 : 2 ≤ i := by omega
      have h1 : i + 2 - 2 = (i - 2) + 1 + 1 := by omega
      have h2 : i + 2 - 1 = (i - 1) + 1 + 1 := by omega
      have h3 : i + 2 = i + 1 + 1 := by omega
      rw [h1, h2, h3, linkedGet_succ, linkedGet_succ, linkedGet_succ, linkedGet_succ,
        linkedGet_succ, linkedGet_succ]
    · have h2 : i + 2 - 1 = (i - 1) + 1 + 1 := by omega
      have h3 : i + 2 = i + 1 + 1 := by omega
      rw [h2, h3, linkedGet_succ, linkedGet_succ, linkedGet_succ, linkedGet_succ]

lemma indicator_iff {P Q : Prop} (h : P ↔ Q) : indicator P = indicator Q := by
  unfold indicator
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 (h.mp h1)
  · exfalso; exact h1 (h.mpr h2)
  · rfl

lemma linkedWeight_one (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) :
    linkedWeight h X Y 1 =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q ∧ meets Q Y), ‖h Q‖ := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 1 => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Finset.univ_unique, Finset.sum_singleton]
  rw [Fin.prod_univ_one]
  simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero, Nat.sub_self]
  rw [indicator_iff (linkedCondition_zero X Q _), linkedGet_zero]
  unfold indicator
  by_cases h1 : meets X Q <;> by_cases h2 : meets Q Y <;> simp [h1, h2]

lemma linkedWeight_two (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) :
    linkedWeight h X Y 2 =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R Y), ‖h Q‖ * ‖h R‖ := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 2 => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin 1 => Finset Λ)), Fintype.sum_prod_type]
  split_ifs with hXQ
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [Finset.univ_unique, Finset.sum_singleton]
    rw [Fin.prod_univ_two]
    simp only [consEquiv_pair, Fin.val_zero, Fin.val_one, Fin.cons_zero, Fin.cons_one]
    rw [indicator_iff (linkedCondition_zero X Q _),
        indicator_iff (linkedCondition_one X Q R _)]
    change (‖h Q‖ * indicator (meets X Q) * (‖h R‖ * indicator (meets Q R))) *
        indicator (meets (linkedGet (Fin.cons Q (Fin.cons R default)) (0 + 1)) Y) =
      if meets Q R ∧ meets R Y then ‖h Q‖ * ‖h R‖ else 0
    rw [linkedGet_succ, linkedGet_zero]
    unfold indicator
    by_cases h2 : meets Q R <;> by_cases h3 : meets R Y <;> simp [hXQ, h2, h3]
  · refine Finset.sum_eq_zero (fun R _ => ?_)
    rw [Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_two]
    simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero]
    rw [indicator_iff (linkedCondition_zero X Q _)]
    unfold indicator
    rw [if_neg hXQ]
    ring

lemma linkedWeight_add_two (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X Y : Finset Λ) (k : ℕ) (hk : 1 ≤ k) :
    linkedWeight h X Y (k + 2) =
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
          ‖h Q‖ * ‖h R‖ * linkedWeight h (Q ∪ R) Y k := by
  unfold linkedWeight
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 2) => Finset Λ)), Fintype.sum_prod_type]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => Finset Λ)), Fintype.sum_prod_type]
  split_ifs with hXQ
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    split_ifs with hQR
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Z' _ => ?_)
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [consEquiv_pair, Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_add]
      rw [indicator_iff (linkedCondition_zero X Q _),
          indicator_iff (linkedCondition_one X Q R Z')]
      have hprod : (∏ i : Fin k, ‖h (Z' i)‖ *
          indicator (linkedCondition X (Fin.cons Q (Fin.cons R Z')) (i.val + 1 + 1))) =
          ∏ i : Fin k, ‖h (Z' i)‖ * indicator (linkedCondition (Q ∪ R) Z' i.val) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [indicator_iff (linkedCondition_add_two X Q R Z' i.val)]
      have hlast : linkedGet (Fin.cons Q (Fin.cons R Z')) (k + 2 - 1) = linkedGet Z' (k - 1) := by
        have hksub : k + 2 - 1 = (k - 1) + 1 + 1 := by omega
        rw [hksub, linkedGet_succ, linkedGet_succ]
      rw [hprod, hlast]
      unfold indicator
      rw [if_pos hXQ, if_pos hQR]
      ring
    · refine Finset.sum_eq_zero (fun Z' _ => ?_)
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [consEquiv_pair, Fin.val_zero, Fin.val_succ, Fin.cons_zero, Fin.cons_succ, Nat.zero_add]
      rw [indicator_iff (linkedCondition_one X Q R Z')]
      unfold indicator
      rw [if_neg hQR]
      ring
  · refine Finset.sum_eq_zero (fun R _ => ?_)
    refine Finset.sum_eq_zero (fun Z' _ => ?_)
    rw [Fin.prod_univ_succ]
    simp only [consEquiv_pair, Fin.val_zero, Fin.cons_zero]
    rw [indicator_iff (linkedCondition_zero X Q _)]
    unfold indicator
    rw [if_neg hXQ]
    ring

lemma setDist_le_infDist (P Y : Finset Λ) (p : Λ) (hp : p ∈ P) :
    setDist P Y ≤ Metric.infDist p (Y : Set Λ) := by
  unfold setDist
  split_ifs with hne
  · have hYne : Y.Nonempty := hne.snd
    have hYu : (Y : Set Λ).Nonempty := Finset.coe_nonempty.mpr hYne
    rw [Metric.le_infDist hYu]
    intro y hy
    have hyY : y ∈ Y := Finset.mem_coe.mp hy
    have hmem : (p, y) ∈ P ×ˢ Y := Finset.mem_product.mpr ⟨hp, hyY⟩
    exact Finset.inf'_le (fun x : Λ × Λ => dist x.1 x.2) hmem
  · exact Metric.infDist_nonneg

lemma sum_exp_neg_infDist_le (P Y : Finset Λ) (μ : ℝ) (hμ : 0 < μ) :
    ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (Y : Set Λ))) ≤
      (P.card : ℝ) * Real.exp (-(μ * setDist P Y)) := by
  calc ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (Y : Set Λ)))
      ≤ ∑ p ∈ P, Real.exp (-(μ * setDist P Y)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        apply Real.exp_le_exp.mpr
        have h := setDist_le_infDist P Y p hp
        nlinarith
    _ = (P.card : ℝ) * Real.exp (-(μ * setDist P Y)) := by simp

lemma linkedWeight_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => x ∈ Z),
        ‖h Z‖ * (Z.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Z : Set Λ)) ≤ ζ)
    (Y : Finset Λ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (X : Finset Λ),
      linkedWeight h X Y k ≤
        2 ^ ((k - 1) / 2) * ζ ^ k *
          ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ)))
  | 0, hk, _ => by omega
  | 1, _, X => by
    rw [linkedWeight_one]
    simpa using (proposition_13_a h ζ μ hζ hμ h15 X Y).1
  | 2, _, X => by
    rw [linkedWeight_two]
    simpa using (proposition_13_b h ζ μ hζ hμ h15 X Y).1
  | k + 1 + 2, _, X => by
    rw [linkedWeight_add_two h X Y (k + 1) (Nat.le_add_left 1 k)]
    have hstep1 :
        ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
          ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
            ‖h Q‖ * ‖h R‖ * linkedWeight h (Q ∪ R) Y (k + 1) ≤
        (2 ^ (k / 2) * ζ ^ (k + 1)) *
        ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
          ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
            ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) Y)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun Q _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun R _ => ?_)
      have hih := linkedWeight_le h ζ μ hζ hμ h15 Y (k + 1) (Nat.le_add_left 1 k) (Q ∪ R)
      simp only [Nat.add_sub_cancel] at hih
      have hsum_le := sum_exp_neg_infDist_le (Q ∪ R) Y μ hμ
      have hih2 : linkedWeight h (Q ∪ R) Y (k + 1) ≤
          2 ^ (k / 2) * ζ ^ (k + 1) * (((Q ∪ R).card : ℝ) * Real.exp (-(μ * setDist (Q ∪ R) Y))) :=
        hih.trans (mul_le_mul_of_nonneg_left hsum_le (by positivity))
      calc ‖h Q‖ * ‖h R‖ * linkedWeight h (Q ∪ R) Y (k + 1)
          ≤ ‖h Q‖ * ‖h R‖ *
            (2 ^ (k / 2) * ζ ^ (k + 1) * (((Q ∪ R).card : ℝ) * Real.exp (-(μ * setDist (Q ∪ R) Y)))) :=
            mul_le_mul_of_nonneg_left hih2 (by positivity)
        _ = (2 ^ (k / 2) * ζ ^ (k + 1)) *
            (((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) Y))) := by ring
    have hstep2 := (proposition_13_b h ζ μ hζ hμ h15 X Y).2
    have hdiv : (k + 1 + 2 - 1) / 2 = k / 2 + 1 := by omega
    calc ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
          ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
            ‖h Q‖ * ‖h R‖ * linkedWeight h (Q ∪ R) Y (k + 1)
        ≤ (2 ^ (k / 2) * ζ ^ (k + 1)) *
          ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets X Q),
            ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
              ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) Y)) := hstep1
      _ ≤ (2 ^ (k / 2) * ζ ^ (k + 1)) *
          (2 * ζ ^ 2 * ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ)))) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = 2 ^ ((k + 1 + 2 - 1) / 2) * ζ ^ (k + 1 + 2) *
          ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by
          rw [hdiv, pow_succ, pow_add]
          ring

end Aux_LHS_Eq37

open LatticeHamSim.CommLR Aux_LHS_Eq37 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η ζ μ : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => x ∈ Z),
        ‖h Z‖ * (Z.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Z : Set Λ)) ≤ ζ)
    (X Y : Finset Λ) (t : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
      linkedWeight h X Y k ≤
      (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
      2 ^ ((k - 1) / 2) * ζ ^ k *
        ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by
  have hlw := linkedWeight_le h ζ μ hζ hμ h15 Y k hk X
  have hcoeff : 0 ≤ (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) := by positivity
  calc (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) * linkedWeight h X Y k
      ≤ (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
        (2 ^ ((k - 1) / 2) * ζ ^ k * ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ)))) :=
        mul_le_mul_of_nonneg_left hlw hcoeff
    _ = (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
        2 ^ ((k - 1) / 2) * ζ ^ k *
          ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by ring
