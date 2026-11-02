-- Prove2me | solution 1 for LatticeHamSim.CommLR.proposition_13_a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:18:53.19843+00:00
-- url     : https://prove2.me/submissions/e118a080-877e-4302-8aff-74562d277c5e

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_Prop13a

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma infDist_le_diam_add_setDist (Q S : Finset Λ) (p : Λ) (hp : p ∈ Q) :
    Metric.infDist p (S : Set Λ) ≤ Metric.diam (Q : Set Λ) + setDist Q S := by
  unfold setDist
  split_ifs with hne
  · obtain ⟨⟨q₀, s₀⟩, hmem, heq⟩ := Finset.exists_mem_eq_inf' hne (fun x => dist x.1 x.2)
    have hq₀ : q₀ ∈ Q := (Finset.mem_product.mp hmem).1
    have hs₀ : s₀ ∈ S := (Finset.mem_product.mp hmem).2
    rw [heq]
    have h1 : Metric.infDist p (S : Set Λ) ≤ dist p s₀ :=
      Metric.infDist_le_dist_of_mem (Finset.mem_coe.mpr hs₀)
    have h2 : dist p s₀ ≤ dist p q₀ + dist q₀ s₀ := dist_triangle p q₀ s₀
    have h3 : dist p q₀ ≤ Metric.diam (Q : Set Λ) :=
      Metric.dist_le_diam_of_mem Q.finite_toSet.isBounded hp hq₀
    linarith
  · have hSe : S = ∅ := by
      by_contra hS
      have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      exact hne ( Finset.Nonempty.product ⟨p, hp⟩ hSne )
    subst hSe
    simp only [Finset.coe_empty, Metric.infDist_empty, add_zero]
    exact Metric.diam_nonneg

lemma exp_neg_setDist_le (Q S : Finset Λ) (p : Λ) (hp : p ∈ Q) (μ : ℝ) (hμ : 0 < μ) :
    Real.exp (-(μ * setDist Q S)) ≤
      Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := infDist_le_diam_add_setDist Q S p hp
  nlinarith

lemma part2 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))) ≤
      ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  have hstep1 :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S)) ≤
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        ∑ p ∈ P, (if p ∈ Q then ‖h Q‖ * (Q.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
    refine Finset.sum_le_sum (fun Q hQ => ?_)
    have hm : (P ∩ Q).Nonempty := (Finset.mem_filter.mp hQ).2
    have hcard : (1 : ℝ) ≤ ((P ∩ Q).card : ℝ) := by exact_mod_cast hm.card_pos
    have hcard_eq : ((P ∩ Q).card : ℝ) = ∑ p ∈ P, (if p ∈ Q then (1 : ℝ) else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
      simp
    calc ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))
        ≤ (‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))) * ((P ∩ Q).card : ℝ) :=
          le_mul_of_one_le_right (by positivity) hcard
      _ = ∑ p ∈ P, (if p ∈ Q then ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S)) else 0) := by
          rw [hcard_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          split_ifs <;> ring
      _ ≤ ∑ p ∈ P, (if p ∈ Q then ‖h Q‖ * (Q.card : ℝ) ^ 2 *
            Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          split_ifs with hpQ
          · have hexp := exp_neg_setDist_le Q S p hpQ μ hμ
            have hnn : 0 ≤ ‖h Q‖ * (Q.card : ℝ) ^ 2 := by positivity
            calc ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))
                ≤ ‖h Q‖ * (Q.card : ℝ) ^ 2 *
                  (Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ)))) :=
                  mul_le_mul_of_nonneg_left hexp hnn
              _ = ‖h Q‖ * (Q.card : ℝ) ^ 2 *
                  Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by ring
          · exact le_rfl
  refine hstep1.trans ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hsub :
      ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then ‖h Q‖ * (Q.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0) ≤
      (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
        ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ))) *
        Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
    rw [Finset.sum_mul, ← Finset.sum_filter (p := fun Q : Finset Λ => p ∈ Q)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun Q _ _ => by positivity)
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ ⊢
    exact hQ.2
  calc ∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
        (if p ∈ Q then ‖h Q‖ * (Q.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Q : Set Λ)) * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) else 0)
      ≤ (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => p ∈ Q),
          ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (μ * Metric.diam (Q : Set Λ))) *
          Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := hsub
    _ ≤ ζ * Real.exp (-(μ * Metric.infDist p (S : Set Λ))) :=
        mul_le_mul_of_nonneg_right (h15 p) (le_of_lt (Real.exp_pos _))

lemma part1 (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q ∧ meets Q S),
      ‖h Q‖) ≤ ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by
  refine le_trans ?_ (part2 h ζ μ hζ hμ h15 P S)
  have hsub : Finset.univ.filter (fun Q : Finset Λ => meets P Q ∧ meets Q S) ⊆
      Finset.univ.filter (fun Q : Finset Λ => meets P Q) := by
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ ⊢
    exact hQ.1
  refine le_trans (Finset.sum_le_sum (fun Q hQ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Q _ _ => by positivity))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
  obtain ⟨⟨p, hp⟩, ⟨s, hs⟩⟩ := hQ
  have hpQ : p ∈ Q := (Finset.mem_inter.mp hp).2
  have hsQ : s ∈ Q := (Finset.mem_inter.mp hs).1
  have hsS : s ∈ S := (Finset.mem_inter.mp hs).2
  have hQne : Q.Nonempty := ⟨p, hpQ⟩
  have hcard1 : (1 : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hQne.card_pos
  have hsq1 : (1 : ℝ) ≤ (Q.card : ℝ) ^ 2 := by nlinarith
  have hsd0 : setDist Q S ≤ 0 := by
    unfold setDist
    have hmem : (s, s) ∈ Q ×ˢ S := Finset.mem_product.mpr ⟨hsQ, hsS⟩
    rw [dif_pos ⟨(s, s), hmem⟩]
    have hle := Finset.inf'_le (fun x : Λ × Λ => dist x.1 x.2) hmem
    simpa using hle
  have hexp1 : (1 : ℝ) ≤ Real.exp (-(μ * setDist Q S)) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc ‖h Q‖ = ‖h Q‖ * 1 * 1 := by ring
    _ ≤ ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hsq1 (norm_nonneg _)) hexp1 zero_le_one (by positivity)

end Aux_LHS_Prop13a

attribute [local instance] Classical.propDecidable

open LatticeHamSim.CommLR Aux_LHS_Prop13a in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q ∧ meets Q S),
      ‖h Q‖) ≤ ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) ∧
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))) ≤
      ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) :=
  ⟨part1 h ζ μ hζ hμ h15 P S, part2 h ζ μ hζ hμ h15 P S⟩
