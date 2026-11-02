-- Prove2me | solution 1 for LatticeHamSim.CommLR.proposition_13_b
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:21:59.902328+00:00
-- url     : https://prove2.me/submissions/ac8a3e93-d41c-4487-9f68-d9fe4dac10e1

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_Prop13b

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma infDist_le_diam_add_diam_add_setDist (Q R S : Finset Λ)
    (p q₀ : Λ) (hp : p ∈ Q) (hqQ : q₀ ∈ Q) (hqR : q₀ ∈ R) :
    Metric.infDist p (S : Set Λ) ≤
      Metric.diam (Q : Set Λ) + Metric.diam (R : Set Λ) + setDist (Q ∪ R) S := by
  unfold setDist
  split_ifs with hne
  · obtain ⟨⟨x₀, s₀⟩, hmem, heq⟩ := Finset.exists_mem_eq_inf' hne (fun x => dist x.1 x.2)
    have hx₀ : x₀ ∈ Q ∪ R := (Finset.mem_product.mp hmem).1
    have hs₀ : s₀ ∈ S := (Finset.mem_product.mp hmem).2
    rw [heq]
    have h1 : Metric.infDist p (S : Set Λ) ≤ dist p s₀ :=
      Metric.infDist_le_dist_of_mem (Finset.mem_coe.mpr hs₀)
    have h2 : dist p s₀ ≤ dist p x₀ + dist x₀ s₀ := dist_triangle p x₀ s₀
    rcases Finset.mem_union.mp hx₀ with hxQ | hxR
    · have h3 : dist p x₀ ≤ Metric.diam (Q : Set Λ) :=
        Metric.dist_le_diam_of_mem Q.finite_toSet.isBounded hp hxQ
      have h4 : 0 ≤ Metric.diam (R : Set Λ) := Metric.diam_nonneg
      linarith
    · have h3 : dist p x₀ ≤ dist p q₀ + dist q₀ x₀ := dist_triangle p q₀ x₀
      have h4 : dist p q₀ ≤ Metric.diam (Q : Set Λ) :=
        Metric.dist_le_diam_of_mem Q.finite_toSet.isBounded hp hqQ
      have h5 : dist q₀ x₀ ≤ Metric.diam (R : Set Λ) :=
        Metric.dist_le_diam_of_mem R.finite_toSet.isBounded hqR hxR
      linarith
  · have hSe : S = ∅ := by
      by_contra hS
      have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      have hQRne : (Q ∪ R).Nonempty := ⟨p, Finset.mem_union_left R hp⟩
      exact hne (Finset.Nonempty.product hQRne hSne)
    subst hSe
    simp only [Finset.coe_empty, Metric.infDist_empty, add_zero]
    linarith [Metric.diam_nonneg (s := (Q : Set Λ)), Metric.diam_nonneg (s := (R : Set Λ))]

lemma exp_neg_setDist_union_le (Q R S : Finset Λ)
    (p q₀ : Λ) (hp : p ∈ Q) (hqQ : q₀ ∈ Q) (hqR : q₀ ∈ R) (μ : ℝ) (hμ : 0 < μ) :
    Real.exp (-(μ * setDist (Q ∪ R) S)) ≤
      Real.exp (μ * Metric.diam (Q : Set Λ)) *
      Real.exp (μ * Metric.diam (R : Set Λ)) *
      Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := infDist_le_diam_add_diam_add_setDist Q R S p q₀ hp hqQ hqR
  nlinarith

lemma sum_R_meets_Q_le (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (Q : Finset Λ) :
    ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
      ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) ≤
    (Q.card : ℝ) * ζ := by
  have hstep1 :
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) ≤
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        ∑ x ∈ Q, (if x ∈ R then ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) else 0) := by
    refine Finset.sum_le_sum (fun R hR => ?_)
    have hm : (Q ∩ R).Nonempty := (Finset.mem_filter.mp hR).2
    have hcard : (1 : ℝ) ≤ ((Q ∩ R).card : ℝ) := by exact_mod_cast hm.card_pos
    have hcard_eq : ((Q ∩ R).card : ℝ) = ∑ x ∈ Q, (if x ∈ R then (1 : ℝ) else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      simp
    calc ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))
        ≤ (‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))) * ((Q ∩ R).card : ℝ) :=
          le_mul_of_one_le_right (by positivity) hcard
      _ = ∑ x ∈ Q, (if x ∈ R then ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) else 0) := by
          rw [hcard_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          split_ifs <;> ring
  refine hstep1.trans ?_
  rw [Finset.sum_comm]
  calc ∑ x ∈ Q, ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        (if x ∈ R then ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) else 0)
      ≤ ∑ x ∈ Q, ζ := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [← Finset.sum_filter (p := fun R : Finset Λ => x ∈ R)]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun R _ _ => by positivity)) (h15 x)
        intro R hR
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
        exact hR.2
    _ = (Q.card : ℝ) * ζ := by simp

lemma part2 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ *
          Real.exp (-(μ * setDist (Q ∪ R) S))) ≤
      2 * ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  have hstep1 :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
          ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) S)) ≤
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ∑ p ∈ P, (if p ∈ Q then
          2 * ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
    refine Finset.sum_le_sum (fun Q hQ => ?_)
    have hmP : (P ∩ Q).Nonempty := (Finset.mem_filter.mp hQ).2
    have hcardP : (1 : ℝ) ≤ ((P ∩ Q).card : ℝ) := by exact_mod_cast hmP.card_pos
    have hcardP_eq : ((P ∩ Q).card : ℝ) = ∑ p ∈ P, (if p ∈ Q then (1 : ℝ) else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      simp
    set lhsQ : ℝ := ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
      ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) S))
    have hlhsQ_nn : 0 ≤ lhsQ := by
      unfold lhsQ
      exact Finset.sum_nonneg (fun R _ => by positivity)
    calc lhsQ
        ≤ lhsQ * ((P ∩ Q).card : ℝ) := by nlinarith
      _ = ∑ p ∈ P, (if p ∈ Q then lhsQ else 0) := by
          rw [hcardP_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          split_ifs <;> ring
      _ ≤ ∑ p ∈ P, (if p ∈ Q then
            2 * ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
            ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          split_ifs with hpQ
          · unfold lhsQ
            have hR_bound :
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
                  ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) S)) ≤
                (2 * ‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
                  ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_le_sum (fun R hR => ?_)
              obtain ⟨q₀, hq₀⟩ := (Finset.mem_filter.mp hR).2
              have hqQ : q₀ ∈ Q := (Finset.mem_inter.mp hq₀).1
              have hqR : q₀ ∈ R := (Finset.mem_inter.mp hq₀).2
              have hQ1 : (1 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p, hpQ⟩
              have hR1 : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨q₀, hqR⟩
              have hcard_un : ((Q ∪ R).card : ℝ) ≤ (Q.card : ℝ) + (R.card : ℝ) := by
                exact_mod_cast Finset.card_union_le Q R
              have hcard_prod : ((Q ∪ R).card : ℝ) ≤ 2 * (Q.card : ℝ) * (R.card : ℝ) ^ 2 := by
                have h1 : (Q.card : ℝ) + (R.card : ℝ) ≤ 2 * (Q.card : ℝ) * (R.card : ℝ) := by nlinarith
                have hR2 : (R.card : ℝ) ≤ (R.card : ℝ) ^ 2 := by nlinarith
                have h2 : 2 * (Q.card : ℝ) * (R.card : ℝ) ≤ 2 * (Q.card : ℝ) * (R.card : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_left hR2 (by positivity)
                linarith
              have hexp := exp_neg_setDist_union_le Q R S p q₀ hpQ hqQ hqR μ hμ
              calc ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ * Real.exp (-(μ * setDist (Q ∪ R) S))
                  = (((Q ∪ R).card : ℝ) * Real.exp (-(μ * setDist (Q ∪ R) S))) * (‖h Q‖ * ‖h R‖) := by ring
                _ ≤ ((2 * (Q.card : ℝ) * (R.card : ℝ) ^ 2) *
                    (Real.exp (μ * Metric.diam (Q : Set Λ)) *
                      Real.exp (μ * Metric.diam (R : Set Λ)) *
                      Real.exp (-(μ * Metric.infDist p (S : Set Λ))))) * (‖h Q‖ * ‖h R‖) := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    exact mul_le_mul hcard_prod hexp (by positivity) (by positivity)
                _ = (2 * ‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                      Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                    (‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))) := by ring
            refine hR_bound.trans ?_
            have hsumR := sum_R_meets_Q_le h ζ μ hζ h15 Q
            calc (2 * ‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
                  ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))
                ≤ (2 * ‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) * ((Q.card : ℝ) * ζ) :=
                  mul_le_mul_of_nonneg_left hsumR (by positivity)
              _ = 2 * ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by ring
          · exact le_rfl
  refine hstep1.trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hsub :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then
          2 * ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) ≤
      (2 * ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
        ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) := by
    rw [Finset.mul_sum, ← Finset.sum_filter (p := fun Q : Finset Λ => p ∈ Q)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (t := Finset.univ.filter (fun Q : Finset Λ => p ∈ Q)) ?_ (fun Q _ _ => by positivity)) ?_
    · intro Q hQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ ⊢
      exact hQ.2
    · refine le_of_eq (Finset.sum_congr rfl (fun Q _ => ?_))
      ring
  calc ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then
          2 * ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0)
      ≤ (2 * ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
        ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) := hsub
    _ ≤ (2 * ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) * ζ :=
        mul_le_mul_of_nonneg_left (h15 p) (by positivity)
    _ = 2 * ζ ^ 2 * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by ring

lemma part1 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
        ‖h Q‖ * ‖h R‖) ≤
      ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  have hstep1 :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
          ‖h Q‖ * ‖h R‖ ≤
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ∑ p ∈ P, (if p ∈ Q then
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
    refine Finset.sum_le_sum (fun Q hQ => ?_)
    have hmP : (P ∩ Q).Nonempty := (Finset.mem_filter.mp hQ).2
    have hcardP : (1 : ℝ) ≤ ((P ∩ Q).card : ℝ) := by exact_mod_cast hmP.card_pos
    have hcardP_eq : ((P ∩ Q).card : ℝ) = ∑ p ∈ P, (if p ∈ Q then (1 : ℝ) else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      simp
    set lhsQ : ℝ := ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
      ‖h Q‖ * ‖h R‖
    have hlhsQ_nn : 0 ≤ lhsQ := by
      unfold lhsQ
      exact Finset.sum_nonneg (fun R _ => by positivity)
    calc lhsQ
        ≤ lhsQ * ((P ∩ Q).card : ℝ) := by nlinarith
      _ = ∑ p ∈ P, (if p ∈ Q then lhsQ else 0) := by
          rw [hcardP_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          split_ifs <;> ring
      _ ≤ ∑ p ∈ P, (if p ∈ Q then
            ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
            ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          split_ifs with hpQ
          · unfold lhsQ
            have hR_bound :
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
                  ‖h Q‖ * ‖h R‖ ≤
                (‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
                  ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ)) := by
              have hsubR : Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S) ⊆
                  Finset.univ.filter (fun R : Finset Λ => meets Q R) := by
                intro R hR
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
                exact hR.1
              rw [Finset.mul_sum]
              refine le_trans (Finset.sum_le_sum (fun R hR => ?_))
                (Finset.sum_le_sum_of_subset_of_nonneg hsubR (fun R _ _ => by positivity))
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR
              obtain ⟨⟨q₀, hq₀⟩, ⟨s₀, hs₀⟩⟩ := hR
              have hqQ : q₀ ∈ Q := (Finset.mem_inter.mp hq₀).1
              have hqR : q₀ ∈ R := (Finset.mem_inter.mp hq₀).2
              have hsR : s₀ ∈ R := (Finset.mem_inter.mp hs₀).1
              have hsS : s₀ ∈ S := (Finset.mem_inter.mp hs₀).2
              have hQ1 : (1 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨p, hpQ⟩
              have hR1 : (1 : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨q₀, hqR⟩
              have hR2 : (1 : ℝ) ≤ (R.card : ℝ) ^ 2 := by nlinarith
              have hcard_prod : (1 : ℝ) ≤ (Q.card : ℝ) * (R.card : ℝ) ^ 2 :=
                one_le_mul_of_one_le_of_one_le hQ1 hR2
              have hsd0 : setDist (Q ∪ R) S ≤ 0 := by
                unfold setDist
                have hmem : (s₀, s₀) ∈ (Q ∪ R) ×ˢ S :=
                  Finset.mem_product.mpr ⟨Finset.mem_union_right Q hsR, hsS⟩
                rw [dif_pos ⟨(s₀, s₀), hmem⟩]
                have hle := Finset.inf'_le (fun x : Λ × Λ => dist x.1 x.2) hmem
                simpa using hle
              have hexp1 : (1 : ℝ) ≤ Real.exp (-(μ * setDist (Q ∪ R) S)) := by
                rw [← Real.exp_zero]
                apply Real.exp_le_exp.mpr
                nlinarith
              have hexp2 := exp_neg_setDist_union_le Q R S p q₀ hpQ hqQ hqR μ hμ
              have hexp := hexp1.trans hexp2
              calc ‖h Q‖ * ‖h R‖ = (1 * 1) * (‖h Q‖ * ‖h R‖) := by ring
                _ ≤ (((Q.card : ℝ) * (R.card : ℝ) ^ 2) *
                    (Real.exp (μ * Metric.diam (Q : Set Λ)) *
                      Real.exp (μ * Metric.diam (R : Set Λ)) *
                      Real.exp (-(μ * Metric.infDist p (S : Set Λ))))) * (‖h Q‖ * ‖h R‖) := by
                    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                    exact mul_le_mul hcard_prod hexp zero_le_one (by positivity)
                _ = (‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                      Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                    (‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))) := by ring
            refine hR_bound.trans ?_
            have hsumR := sum_R_meets_Q_le h ζ μ hζ h15 Q
            calc (‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
                ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
                  ‖h R‖ * (R.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (R : Set Λ))
                ≤ (‖h Q‖ * (Q.card : ℝ) * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) * ((Q.card : ℝ) * ζ) :=
                  mul_le_mul_of_nonneg_left hsumR (by positivity)
              _ = ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
                  ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by ring
          · exact le_rfl
  refine hstep1.trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hsub :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) ≤
      (ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
        ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) := by
    rw [Finset.mul_sum, ← Finset.sum_filter (p := fun Q : Finset Λ => p ∈ Q)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (t := Finset.univ.filter (fun Q : Finset Λ => p ∈ Q)) ?_ (fun Q _ _ => by positivity)) ?_
    · intro Q hQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ ⊢
      exact hQ.2
    · refine le_of_eq (Finset.sum_congr rfl (fun Q _ => ?_))
      ring
  calc ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) *
          ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0)
      ≤ (ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) *
        ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ)) := hsub
    _ ≤ (ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) * ζ :=
        mul_le_mul_of_nonneg_left (h15 p) (by positivity)
    _ = ζ ^ 2 * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by ring

end Aux_LHS_Prop13b

attribute [local instance] Classical.propDecidable

open LatticeHamSim.CommLR Aux_LHS_Prop13b in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
        ‖h Q‖ * ‖h R‖) ≤
      ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) ∧
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ *
          Real.exp (-(μ * setDist (Q ∪ R) S))) ≤
      2 * ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) :=
  ⟨part1 h ζ μ hζ hμ h15 P S, part2 h ζ μ hζ hμ h15 P S⟩
