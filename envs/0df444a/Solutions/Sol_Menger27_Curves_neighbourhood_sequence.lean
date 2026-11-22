-- Prove2me | solution 1 for Menger27.Curves.neighbourhood_sequence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:56:15.425677+00:00
-- url     : https://prove2.me/submissions/e169caa8-8405-4b6b-ba0f-7660714c383a

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

set_option autoImplicit false

namespace Menger27.Curves.NbhdSeqProof

open Set Metric

variable {X : Type*} [MetricSpace X]

/-- Below some open neighbourhood `W₀` of a point of exact order `n`, every open neighbourhood
of the point has at least `n` boundary points. -/
theorem exists_floor (p : X) (n : ℕ) (horder : HasOrder p n) :
    ∃ W₀ : Set X, IsOpen W₀ ∧ p ∈ W₀ ∧
      ∀ V : Set X, IsOpen V → p ∈ V → V ⊆ W₀ → (n : ℕ∞) ≤ (frontier V).encard := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨univ, isOpen_univ, mem_univ p, fun V _ _ _ => by simp⟩
  · have h := horder.2 (n - 1) (by omega)
    unfold OrderAtMost at h
    push Not at h
    obtain ⟨W₀, hW₀o, hpW₀, hW₀⟩ := h
    refine ⟨W₀, hW₀o, hpW₀, fun V hVo hpV hVW => ?_⟩
    have h1 := (ENat.add_one_le_iff (ENat.natCast_ne_top (n - 1))).mpr (hW₀ V hVo hpV hVW)
    have h2 : ((n - 1 : ℕ) : ℕ∞) + 1 = (n : ℕ∞) := by norm_cast; omega
    rwa [h2] at h1

/-- One step of the construction: inside any open neighbourhood `U` of `p` there is an open
neighbourhood `V` of `p` with `closure V ⊆ U`, `V ⊆ W₀ ∩ ball p (1/(k+1))` and at most `n`
boundary points. -/
theorem step (p : X) (n : ℕ) (horder : HasOrder p n) (W₀ : Set X) (hW₀ : IsOpen W₀)
    (hpW : p ∈ W₀) (k : ℕ) (U : Set X) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ closure V ⊆ U ∧ V ⊆ W₀ ∧
      V ⊆ ball p (1 / ((k : ℝ) + 1)) ∧ (frontier V).encard ≤ n := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.inter hW₀) p ⟨hpU, hpW⟩
  have hr0 : 0 < min (ε / 2) (1 / ((k : ℝ) + 1)) := lt_min (by linarith) (by positivity)
  obtain ⟨V, hVo, hpV, hVr, hVn⟩ := horder.1 (ball p (min (ε / 2) (1 / ((k : ℝ) + 1))))
    isOpen_ball (mem_ball_self hr0)
  have hrε : min (ε / 2) (1 / ((k : ℝ) + 1)) < ε :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsub : ball p (min (ε / 2) (1 / ((k : ℝ) + 1))) ⊆ U ∩ W₀ :=
    (ball_subset_ball hrε.le).trans hball
  refine ⟨V, hVo, hpV, ?_, fun x hx => (hsub (hVr hx)).2,
    hVr.trans (ball_subset_ball (min_le_right _ _)), hVn⟩
  calc closure V ⊆ closure (ball p (min (ε / 2) (1 / ((k : ℝ) + 1)))) := closure_mono hVr
    _ ⊆ closedBall p (min (ε / 2) (1 / ((k : ℝ) + 1))) := closure_ball_subset_closedBall
    _ ⊆ ball p ε := closedBall_subset_ball hrε
    _ ⊆ U := fun x hx => (hball hx).1

end Menger27.Curves.NbhdSeqProof

open Set Metric Filter Topology Menger27.Curves Menger27.Curves.NbhdSeqProof

set_option linter.unusedVariables false in
theorem solution {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ) (horder : HasOrder p n) :
    ∃ U : ℕ → Set X,
      (∀ k, IsOpen (U k) ∧ p ∈ U k ∧ Bornology.IsBounded (U k) ∧
        (frontier (U k)).encard = n ∧
        (∀ V : Set X, IsOpen V → p ∈ V → V ⊆ U k →
          n ≤ (frontier V).encard) ∧
        closure (U (k + 1)) ⊆ U k) ∧
      Filter.Tendsto (fun k => Metric.diam (U k)) Filter.atTop (nhds 0) := by
  obtain ⟨W₀, hW₀o, hpW₀, hW₀⟩ := exists_floor p n horder
  choose f hfo hfp hfcl hfW hfball hfn using step p n horder W₀ hW₀o hpW₀
  let seq : ℕ → {U : Set X // IsOpen U ∧ p ∈ U} := fun k =>
    Nat.rec (motive := fun _ => {U : Set X // IsOpen U ∧ p ∈ U})
      ⟨f 0 univ isOpen_univ (mem_univ p), hfo _ _ _ _, hfp _ _ _ _⟩
      (fun k S => ⟨f (k + 1) S.1 S.2.1 S.2.2, hfo _ _ _ _, hfp _ _ _ _⟩) k
  have hrep : ∀ k, ∃ (U' : Set X) (hU' : IsOpen U') (hpU' : p ∈ U'),
      (seq k).1 = f k U' hU' hpU' := by
    intro k
    cases k with
    | zero => exact ⟨univ, isOpen_univ, mem_univ p, rfl⟩
    | succ k => exact ⟨(seq k).1, (seq k).2.1, (seq k).2.2, rfl⟩
  have hsubW : ∀ k, (seq k).1 ⊆ W₀ := by
    intro k
    obtain ⟨U', hU', hpU', hk⟩ := hrep k
    rw [hk]
    exact hfW k U' hU' hpU'
  have hsubB : ∀ k, (seq k).1 ⊆ ball p (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨U', hU', hpU', hk⟩ := hrep k
    rw [hk]
    exact hfball k U' hU' hpU'
  have hle : ∀ k, (frontier (seq k).1).encard ≤ n := by
    intro k
    obtain ⟨U', hU', hpU', hk⟩ := hrep k
    rw [hk]
    exact hfn k U' hU' hpU'
  refine ⟨fun k => (seq k).1, fun k => ⟨(seq k).2.1, (seq k).2.2, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isBounded_ball.subset (hsubB k)
  · exact le_antisymm (hle k) (hW₀ _ (seq k).2.1 (seq k).2.2 (hsubW k))
  · intro V hVo hpV hVU
    exact hW₀ V hVo hpV (hVU.trans (hsubW k))
  · exact hfcl (k + 1) (seq k).1 (seq k).2.1 (seq k).2.2
  · have hdiam : ∀ k : ℕ, diam (seq k).1 ≤ 2 * (1 / ((k : ℝ) + 1)) := fun k =>
      (diam_mono (hsubB k) isBounded_ball).trans (diam_ball (by positivity))
    have hlim : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun k => diam_nonneg) hdiam
