-- Prove2me | solution 1 for InvShareComp.Exog.proposition_1a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:58:05.897736+00:00
-- url     : https://prove2.me/submissions/02ca85ab-ed9f-4296-9178-79f3c85a0d26

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

open MeasureTheory Classical

namespace InvShareAux
open MeasureTheory InvShareComp.Exog

theorem ae_supp {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) :
    ∀ᵐ ω ∂ν, ω ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 := by
  rw [ae_iff]; exact hν.support

theorem int_cont {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : Integrable f ν := by
  have := hν.prob
  have hrestr : ν.restrict (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_supp hν)
  rw [← hrestr]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem int_ite {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (p : ℝ × ℝ → Prop)
    [DecidablePred p] (hp : MeasurableSet {ω | p ω}) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : Integrable (fun ω => if p ω then f ω else 0) ν := by
  have h := (int_cont hν f hf).indicator hp
  have e : (fun ω => if p ω then f ω else 0) = {ω | p ω}.indicator f := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [e]; exact h

theorem swap_eq {ν : Measure (ℝ × ℝ)} (hν : IsDemandLaw ν) (g : ℝ × ℝ → ℝ) :
    ∫ ω, g (ω.2, ω.1) ∂ν = ∫ ω, g ω ∂ν := by
  have h := integral_map_equiv (μ := ν) (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) g
  have hm : Measure.map (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) ν = ν := hν.exch
  rw [hm] at h
  rw [h]; rfl

end InvShareAux

open InvShareComp.Exog InvShareAux in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ))
    (hν : IsDemandLaw ν) (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc 0 (P.cbar - P.δ)) :
    sHat P ν t I - sHatN P ν I = (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) ∧
    0 ≤ Wval ν I ∧
    (t < (P.cbar - P.δ) / 2 → sHatN P ν I ≤ sHat P ν t I) ∧
    ((P.cbar - P.δ) / 2 < t → sHat P ν t I ≤ sHatN P ν I) ∧
    (0 < P.β → 0 < Wval ν I →
      (t < (P.cbar - P.δ) / 2 → sHatN P ν I < sHat P ν t I) ∧
      ((P.cbar - P.δ) / 2 < t → sHat P ν t I < sHatN P ν I)) := by
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  -- measurability of the regions
  have m1 : MeasurableSet {ω : ℝ × ℝ | ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2} := by
    measurability
  have m2 : MeasurableSet {ω : ℝ × ℝ | ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1} := by measurability
  have m3 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2} := by measurability
  have m4 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I} := by
    measurability
  have m5 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1} := by measurability
  have m6 : MeasurableSet {ω : ℝ × ℝ | 2 * I ≤ ω.1} := by measurability
  have i1 := int_ite hν _ m1 (fun ω => (t + P.δ) * ω.1) (by fun_prop)
  have i2 := int_ite hν _ m2 (fun ω => P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2) (by fun_prop)
  have i3 := int_ite hν _ m3 (fun ω => t * ω.2) (by fun_prop)
  have i4 := int_ite hν _ m4 (fun ω => t * ω.1) (by fun_prop)
  have i5 := int_ite hν _ m5 (fun ω => P.cbar * ω.1) (by fun_prop)
  have iw1 := int_ite hν _ m1 (fun ω => ω.1) (by fun_prop)
  have iw2 := int_ite hν _ m2 (fun ω => ω.2) (by fun_prop)
  have iw3 := int_ite hν _ m3 (fun ω => ω.2) (by fun_prop)
  have iw4 := int_ite hν _ m4 (fun ω => ω.1) (by fun_prop)
  have ie := int_ite hν _ m6 (fun ω => ω.1) (by fun_prop)
  have hA : Aval P ν t I = (∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2
        then (t + P.δ) * ω.1 else 0) ∂ν)
      + ∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1
        then P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2 else 0) ∂ν := by
    unfold Aval; exact integral_add i1 i2
  have hB : Bval P ν t I = (∫ ω, (if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then t * ω.2 else 0) ∂ν)
      + (∫ ω, (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then t * ω.1 else 0) ∂ν)
      + ∫ ω, (if 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1 then P.cbar * ω.1 else 0) ∂ν := by
    unfold Bval
    have j1 := integral_add (i3.add i4) i5
    have j2 := integral_add i3 i4
    simp only [Pi.add_apply] at j1 j2
    rw [j1, j2]
  have hW : Wval ν I = (∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2
        then ω.1 else 0) ∂ν)
      + ∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then ω.2 else 0) ∂ν := by
    unfold Wval; exact integral_add iw1 iw2
  -- Lemma A.1 transfers
  have hA1a : (∫ ω, (if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then t * ω.2 else 0) ∂ν)
      = t * ∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then ω.1 else 0) ∂ν := by
    rw [← integral_const_mul, ← swap_eq hν]
    congr 1; funext ω
    simp only [mul_ite, mul_zero]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by linarith⟩
  have hA1b : (∫ ω, (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then t * ω.1 else 0) ∂ν)
      = t * ∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then ω.2 else 0) ∂ν := by
    rw [← integral_const_mul, ← swap_eq hν]
    congr 1; funext ω
    simp only [mul_ite, mul_zero]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, h1⟩
  -- pointwise identity
  have hpt : ∀ ω : ℝ × ℝ, P.cbar * (if 2 * I ≤ ω.1 then ω.1 else 0)
      = (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then (t + P.δ) * ω.1 else 0)
        + (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1
            then P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2 else 0)
        + (if 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1 then P.cbar * ω.1 else 0)
        + (P.cbar - t - P.δ) * ((if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2
            then ω.1 else 0) + (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then ω.2 else 0)) := by
    intro ω
    simp only [← not_lt]
    by_cases h1 : ω.2 < 2 * I <;> by_cases h2 : ω.1 < 2 * I <;>
      by_cases h3 : ω.1 < 4 * I - ω.2 <;>
      simp only [h1, h2, h3, not_true, not_false_eq_true, and_true, true_and, and_false,
        false_and, if_true, if_false] <;>
      first | ring1 | (exfalso; simp only [not_lt] at *; linarith)
  have hE : P.cbar * (∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν)
      = (∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2
        then (t + P.δ) * ω.1 else 0) ∂ν)
      + (∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1
        then P.cbar * ω.1 - P.cbar * ω.2 + (t + P.δ) * ω.2 else 0) ∂ν)
      + (∫ ω, (if 2 * I ≤ ω.2 ∧ 2 * I ≤ ω.1 then P.cbar * ω.1 else 0) ∂ν)
      + (P.cbar - t - P.δ) * Wval ν I := by
    rw [← integral_const_mul, integral_congr_ae (ae_of_all _ hpt)]
    have j1 := integral_add ((i1.add i2).add i5) ((iw1.add iw2).const_mul (P.cbar - t - P.δ))
    have j2 := integral_add (i1.add i2) i5
    have j3 := integral_add i1 i2
    have j4 := integral_add iw1 iw2
    simp only [Pi.add_apply] at j1 j2 j3 j4
    rw [j1, j2, j3, integral_const_mul, j4, hW]
  have hkey : SVal P ν t I - (P.p * mean ν - P.cbar * ∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν)
      = (P.cbar - 2 * t - P.δ) * Wval ν I := by
    unfold SVal
    rw [hA, hB, hA1a, hA1b]
    have := hE
    rw [hW] at this ⊢
    linarith
  have hid : sHat P ν t I - sHatN P ν I
      = (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) := by
    unfold sHat sHatN
    rw [show P.β * SVal P ν t I / (2 * P.k) - P.β * (P.p * mean ν - P.cbar *
        ∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν) / (2 * P.k)
        = P.β * (SVal P ν t I - (P.p * mean ν - P.cbar *
        ∫ ω, (if 2 * I ≤ ω.1 then ω.1 else 0) ∂ν)) / (2 * P.k) by ring, hkey]
    ring
  have hW0 : 0 ≤ Wval ν I := by
    unfold Wval
    apply integral_nonneg_of_ae
    filter_upwards [ae_supp hν] with ω hω
    obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hω
    simp only [Pi.zero_apply]
    apply add_nonneg <;> split_ifs <;> linarith
  have hk2 : 0 < 2 * P.k := by linarith
  refine ⟨hid, hW0, ?_, ?_, ?_⟩
  · intro h
    have : 0 ≤ (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) := by
      apply div_nonneg _ hk2.le
      apply mul_nonneg (mul_nonneg (by linarith) hβ) hW0
    linarith
  · intro h
    have : (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hk2.le
      apply mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hβ) hW0
    linarith
  · intro hb hw
    constructor
    · intro h
      have : 0 < (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) := by
        apply div_pos _ hk2
        apply mul_pos (mul_pos (by linarith) hb) hw
      linarith
    · intro h
      have : (P.cbar - 2 * t - P.δ) * P.β * Wval ν I / (2 * P.k) < 0 := by
        apply div_neg_of_neg_of_pos _ hk2
        apply mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hb) hw
      linarith
