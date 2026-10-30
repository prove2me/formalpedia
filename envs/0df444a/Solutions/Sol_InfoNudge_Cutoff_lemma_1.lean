-- Prove2me | solution 1 for InfoNudge.Cutoff.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:59:22.630032+00:00
-- url     : https://prove2.me/submissions/59f2db69-ccf3-4ef0-8917-c8236388801f

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

open InfoNudge.Cutoff

namespace InfoNudgeSolL1

variable {M : Params}

lemma Kpos (hS : Standing M) : 0 < M.β * M.δ ^ 2 * M.C := by linarith [hS.2.2.2.2.1]

lemma lt_ta_iff (hS : Standing M) (θ : ℝ) : θ < ta M ↔ M.β * M.δ ^ 2 * θ * M.C < 1 := by
  have hK := Kpos hS
  unfold ta
  rw [lt_div_iff₀ hK]
  constructor <;> intro h <;> nlinarith

lemma gt_ta_iff (hS : Standing M) (θ : ℝ) : ta M < θ ↔ 1 < M.β * M.δ ^ 2 * θ * M.C := by
  have hK := Kpos hS
  unfold ta
  rw [div_lt_iff₀ hK]
  constructor <;> intro h <;> nlinarith

lemma spe_unique (hS : Standing M) (θh : ℝ) (hne : θh ≠ ta M) (a0 : Bool) (s1 : Bool → Bool)
    (h : IsSPE M θh a0 s1) : a0 = decide (θh < ta M) ∧ s1 = fun _ => decide (θh < ta M) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hK := (lt_ta_iff hS θh).mp hlt
    have hs : s1 = fun _ => true := by
      funext x0
      by_contra hc
      have hc' : s1 x0 = false := by simpa using hc
      have := h.1 x0 true
      rw [hc'] at this
      cases x0 <;> simp [U1, act] at this <;> linarith
    refine ⟨?_, by rw [hs]; simp [hlt]⟩
    have := h.2 true
    rw [hs] at this
    cases a0 <;> simp [U0, act, hlt] at this ⊢ <;> linarith
  · have hK := (gt_ta_iff hS θh).mp hgt
    have hn : ¬ θh < ta M := not_lt.mpr hgt.le
    have hs : s1 = fun _ => false := by
      funext x0
      by_contra hc
      have hc' : s1 x0 = true := by simpa using hc
      have := h.1 x0 false
      rw [hc'] at this
      cases x0 <;> simp [U1, act] at this <;> linarith
    refine ⟨?_, by rw [hs]; simp [hn]⟩
    have := h.2 false
    rw [hs] at this
    cases a0 <;> simp [U0, act, hn] at this ⊢ <;> linarith

lemma spe_const (hS : Standing M) (θh : ℝ) (hne : θh ≠ ta M) :
    IsSPE M θh (decide (θh < ta M)) (fun _ => decide (θh < ta M)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hK := (lt_ta_iff hS θh).mp hlt
    refine ⟨fun x0 x1 => ?_, fun x0 => ?_⟩
    · cases x0 <;> cases x1 <;> simp [U1, act, hlt] <;> linarith
    · cases x0 <;> simp [U0, act, hlt] <;> linarith
  · have hK := (gt_ta_iff hS θh).mp hgt
    have hn : ¬ θh < ta M := not_lt.mpr hgt.le
    refine ⟨fun x0 x1 => ?_, fun x0 => ?_⟩
    · cases x0 <;> cases x1 <;> simp [U1, act, hn] <;> linarith
    · cases x0 <;> simp [U0, act, hn] <;> linarith

/-- At `θh = ta` the utilities take a simple form. -/
lemma at_ta (hS : Standing M) :
    ∃ p q : ℝ, 0 < p ∧ q < 0 ∧ (∀ x0 x1, U0 M x0 x1 (ta M) = x1 * q) ∧
      (∀ x0 x1, U1 M x0 x1 (ta M) = -(x0 * p)) := by
  obtain ⟨hβ0, hβ1, hδ0, hδ1, hK, _, _⟩ := hS
  have hK0 : 0 < M.β * M.δ ^ 2 * M.C := by linarith
  have hC : 0 < M.C := by
    by_contra hc; push_neg at hc
    have : M.β * M.δ ^ 2 * M.C ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hA : M.β * M.δ ^ 2 * ta M * M.C = 1 := by
    unfold ta; field_simp
  have hta : 0 < ta M := by unfold ta; positivity
  refine ⟨M.β * M.δ * ta M * M.C, M.δ * (M.β - 1), by positivity,
    mul_neg_of_pos_of_neg hδ0 (by linarith), fun x0 x1 => ?_, fun x0 x1 => ?_⟩
  · unfold U0; linear_combination (-(x0) - x1 * M.δ) * hA
  · unfold U1; linear_combination (x1) * hA * (-1)

lemma lemma1 (hS : Standing M) (θh : ℝ) :
    (∃ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1) ∧
    (∀ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 a0 = decide (θh < ta M)) ∧
    (θh ≠ ta M → ∀ (a0 : Bool) (s1 : Bool → Bool), IsSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 = fun _ => decide (θh < ta M)) := by
  by_cases hne : θh ≠ ta M
  · refine ⟨⟨_, _, spe_const hS θh hne, ?_⟩, fun a0 s1 h => ?_, fun _ => spe_unique hS θh hne⟩
    · rintro ⟨b0, r1, hspe, h1, h2, h3⟩
      obtain ⟨rfl, rfl⟩ := spe_unique hS θh hne b0 r1 hspe
      rcases h3 with h3 | h3 <;> exact lt_irrefl _ h3
    · obtain ⟨rfl, rfl⟩ := spe_unique hS θh hne a0 s1 h.1
      exact ⟨rfl, rfl⟩
  · push_neg at hne
    subst hne
    obtain ⟨p, q, hp, hq, hU0, hU1⟩ := at_ta hS
    have hdec : decide (ta M < ta M) = false := by simp
    rw [hdec]
    have hspe0 : IsSPE M (ta M) false (fun _ => false) := by
      refine ⟨fun x0 x1 => ?_, fun x0 => ?_⟩
      · rw [hU1, hU1]
      · rw [hU0, hU0]
    have act_nn : ∀ b, 0 ≤ act b := fun b => by cases b <;> simp [act]
    have af : act false = 0 := by simp [act]
    have at' : act true = 1 := by simp [act]
    refine ⟨⟨false, fun _ => false, hspe0, ?_⟩, fun a0 s1 h => ?_, fun h => absurd rfl h⟩
    · rintro ⟨b0, r1, _, h1, h2, h3⟩
      simp only [hU0, hU1, af] at h1 h2 h3
      have e1 := mul_nonpos_of_nonneg_of_nonpos (act_nn (r1 b0)) hq.le
      have e2 := mul_nonneg (act_nn b0) hp.le
      rcases h3 with h3 | h3 <;> linarith
    · obtain ⟨_, hnd⟩ := h
      cases a0
      · refine ⟨rfl, ?_⟩
        cases hs : s1 false
        · rfl
        · exfalso; apply hnd
          refine ⟨false, fun _ => false, hspe0, ?_, ?_, Or.inl ?_⟩ <;>
            simp only [hU0, hU1, hs, af, at'] <;> linarith
      · exfalso; apply hnd
        have e1 := mul_nonpos_of_nonneg_of_nonpos (act_nn (s1 true)) hq.le
        refine ⟨false, fun _ => false, hspe0, ?_, ?_, Or.inr ?_⟩ <;>
          simp only [hU0, hU1, af, at'] <;> linarith

end InfoNudgeSolL1

open InfoNudgeSolL1 in
theorem solution (M : Params) (hS : Standing M) (θh : ℝ) :
    (∃ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1) ∧
    (∀ (a0 : Bool) (s1 : Bool → Bool), IsEfficientSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 a0 = decide (θh < ta M)) ∧
    (θh ≠ ta M → ∀ (a0 : Bool) (s1 : Bool → Bool), IsSPE M θh a0 s1 →
      a0 = decide (θh < ta M) ∧ s1 = fun _ => decide (θh < ta M)) :=
  lemma1 hS θh
