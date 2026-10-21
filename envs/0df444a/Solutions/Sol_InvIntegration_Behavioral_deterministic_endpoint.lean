-- Prove2me | solution 1 for InvIntegration.Behavioral.deterministic_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:14:52.698567+00:00
-- url     : https://prove2.me/submissions/ce601d76-e538-4f61-9ad6-5bb0e40a9d85

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral
open MeasureTheory ProbabilityTheory

lemma iib_G_vh (P : Params) (hS : P.Standing) : G P P.vh = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, hsupp, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic P.vh) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  have h0 : ∫ t in Set.Ioi P.vh, P.g t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    apply hsupp
    intro hx'
    exact absurd hx'.2 (not_lt.mpr (le_of_lt hx))
  linarith

lemma iib_one_sub_G (P : Params) (hS : P.Standing) (x : ℝ) :
    1 - G P x = ∫ t in Set.Ioi x, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, h1, -⟩ := hS
  unfold G
  have h := integral_add_compl (s := Set.Iic x) measurableSet_Iic hint
  rw [Set.compl_Iic] at h
  linarith

lemma iib_G_sub (P : Params) (hS : P.Standing) (a b : ℝ) (hab : a ≤ b) :
    G P b - G P a = ∫ t in Set.Ioc a b, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, -, -, -, -, -⟩ := hS
  unfold G
  rw [← Set.Iic_union_Ioc_eq_Iic hab, setIntegral_union (Set.Iic_disjoint_Ioc le_rfl)
    measurableSet_Ioc hint.integrableOn hint.integrableOn]
  ring

lemma iib_pos_of_sub (P : Params) (hS : P.Standing) (s a : Set ℝ) (hsub : s ⊆ a)
    (hpos : 0 < ∫ t in s, P.g t) : 0 < ∫ t in a, P.g t := by
  obtain ⟨-, -, -, -, -, -, -, -, hint, hnn, -, -, -, -⟩ := hS
  refine lt_of_lt_of_le hpos ?_
  apply setIntegral_mono_set hint.integrableOn
  · exact Filter.Eventually.of_forall (fun x => hnn x)
  · exact Filter.Eventually.of_forall hsub

lemma iib_G_strict (P : Params) (hS : P.Standing) (a b : ℝ) (ha : P.vl < a) (hab : a < b)
    (hb : b ≤ P.vh) : G P a < G P b := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← sub_pos, iib_G_sub P hS a b hab.le]
  have hvh : a < P.vh := lt_of_lt_of_le hab hb
  set b' := min b ((a + P.vh) / 2)
  have h1 : a < b' := lt_min hab (by linarith)
  have h2 : b' < P.vh := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  apply iib_pos_of_sub P hS (Set.Ioo a b') _ _ (hsupp a b' ha h2 h1)
  intro x hx
  exact ⟨hx.1, le_trans hx.2.le (min_le_left _ _)⟩

lemma iib_Gbar_pos (P : Params) (hS : P.Standing) (v : ℝ) (hv : v < P.vh) (hvl : P.vl < v) :
    0 < Gbar P v := by
  have hsupp := hS.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Gbar
  rw [iib_one_sub_G P hS v]
  apply iib_pos_of_sub P hS (Set.Ioo v ((v + P.vh) / 2)) _ _
    (hsupp v ((v + P.vh) / 2) hvl (by linarith) (by linarith))
  intro x hx; exact hx.1

lemma iib_vstar_ge (P : Params) (hS : P.Standing) (ξ : ℝ) : P.p ≤ vstar P ξ := by
  have hpvh := hS.2.2.2.2.2.2.1
  unfold vstar
  split_ifs
  · exact hpvh.le
  · exact le_min hpvh.le (le_max_right _ _)

lemma iib_frac_le (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    (P.p - ξ * P.s) / (1 - ξ * P.δ) ≤ P.p := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by nlinarith
  rw [div_le_iff₀ h1]
  nlinarith

lemma iib_frac_ge (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : 0 ≤ ξ) (h : ξ * P.δ < 1) :
    P.p ≤ (P.p - ξ * P.s) / (1 - ξ * P.δ) := by
  obtain ⟨-, -, hδ, -, hsδ, -⟩ := hS
  have h1 : 0 < 1 - ξ * P.δ := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

lemma iib_vstar_nonpos (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ : ξ ≤ 0) :
    vstar P ξ = P.p := by
  have hpvh := hS.2.2.2.2.2.2.1
  have hδ := hS.2.2.1
  unfold vstar
  rw [if_neg (by nlinarith), max_eq_right (iib_frac_le P hS ξ hξ), min_eq_right hpvh.le]

/-- Any equilibrium has `v < vh`. -/
lemma iib_eq_lt_vh (P : Params) (hS : P.Standing) (m sd q v ξ : ℝ) (hm : 0 ≤ m)
    (hE : IsEquilibrium P m sd q v ξ) : v < P.vh := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hsc : P.s < P.c := hS.1
  have hcp : P.c < P.p := hS.2.1
  have hpvh := hS.2.2.2.2.2.2.1
  by_contra hcon
  have hvge : P.vh ≤ v := le_of_not_gt hcon
  have hvle : v ≤ P.vh := by
    rw [hv]; unfold vstar; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hveq : v = P.vh := le_antisymm hvle hvge
  have hGb : Gbar P v = 0 := by rw [hveq]; unfold Gbar; rw [iib_G_vh P hS]; ring
  -- profit is constant in x
  have hprof : ∀ q', profit P m sd v q' = (P.p - P.s) * min q' 0 - (P.c - P.s) * q' := by
    intro q'
    unfold profit demandLaw
    simp [hGb]
  have hq : q ≤ 0 := by
    have := hmax 0
    rw [hprof, hprof] at this
    by_contra hq; push Not at hq
    rw [min_eq_right hq.le] at this
    simp at this
    nlinarith
  have hξle : ξ ≤ 0 := by
    rw [hξ]; unfold fill2
    simp only []
    apply div_nonpos_of_nonpos_of_nonneg
    · apply integral_nonpos
      intro x
      simp only [hGb, zero_mul, sub_zero, max_eq_right hq]
      exact min_le_left _ _
    · exact mul_nonneg (le_max_right _ _) hm
  have := iib_vstar_nonpos P hS ξ hξle
  rw [← hv] at this
  linarith

end InvIntegration.Behavioral

open InvIntegration.Behavioral MeasureTheory ProbabilityTheory in
theorem solution (P : Params) (hS : P.Standing) (m : ℝ) (hm : 0 < m)
    (q v ξ : ℝ) (hE : IsEquilibrium P m 0 q v ξ) :
    ξ = 0 ∧ v = P.p := by
  obtain ⟨hmax, hv, hξ⟩ := hE
  have hsc : P.s < P.c := hS.1
  have hcp : P.c < P.p := hS.2.1
  have hlaw : demandLaw m 0 = Measure.dirac m := by
    unfold demandLaw; simp
  have hprof : ∀ q', profit P m 0 v q' =
      (P.p - P.s) * min q' (Gbar P v * m) - (P.c - P.s) * q' := by
    intro q'; unfold profit; rw [hlaw, integral_dirac]
  have hGb0 : 0 ≤ Gbar P v := by
    unfold Gbar; rw [iib_one_sub_G P hS v]
    exact setIntegral_nonneg measurableSet_Ioi (fun x _ => hS.2.2.2.2.2.2.2.2.2.1 x)
  set Q := Gbar P v * m with hQ
  have hQ0 : 0 ≤ Q := mul_nonneg hGb0 hm.le
  have hqQ : q = Q := by
    have h1 := hmax Q
    rw [hprof, hprof, min_self] at h1
    rcases lt_trichotomy q Q with h | h | h
    · rw [min_eq_left h.le] at h1; nlinarith
    · exact h
    · rw [min_eq_right h.le] at h1; nlinarith
  have hξ0 : ξ = 0 := by
    rw [hξ]; unfold fill2
    simp only []
    rw [hlaw, integral_dirac, ← hQ, hqQ, sub_self, max_self]
    have : min (0:ℝ) (max (G P v - G P (P.s / P.δ)) 0 * m) = 0 :=
      min_eq_left (mul_nonneg (le_max_right _ _) hm.le)
    rw [this, zero_div]
  refine ⟨hξ0, ?_⟩
  rw [hv, iib_vstar_nonpos P hS ξ hξ0.le]
