-- Prove2me | solution 1 for HighUncertHT.Game.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:55:30.045536+00:00
-- url     : https://prove2.me/submissions/cadab980-dd24-421a-8b9b-43fb18d749f7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_HJB
import Definitions.Def_HighUncertHT_Game_Priority
import Definitions.Def_HighUncertHT_Game_Lindley
import Theorems.Thm_HighUncertHT_Game_betaStar_admissible
import Theorems.Thm_HighUncertHT_Game_theorem_1
import Theorems.Thm_HighUncertHT_Game_eq_47
import Theorems.Thm_HighUncertHT_Game_eq_55
import Theorems.Thm_HighUncertHT_Game_theorem_2_2

open MeasureTheory Filter Topology
open scoped ENNReal
open HighUncertHT.Game

theorem solution {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u) :
    Tendsto (fun n => value S n) atTop (𝓝 (ENNReal.ofReal (u 0))) := by
  classical
  -- a default adversary control (constant distributions)
  have hne : ∀ n : ℕ, Nonempty (AdversaryControl S n) := by
    intro n
    let π0 : Fin L → ProbabilityMeasure ℝ := fun ℓ => (S.cls_nonempty n ℓ).some
    exact ⟨{ policy := fun _ _ ℓ => π0 ℓ
             policy_mem := fun _ _ ℓ => (S.cls_nonempty n ℓ).some_mem
             kernel := fun _ => ProbabilityTheory.Kernel.const _
               (Measure.pi (fun ℓ => (π0 ℓ : Measure ℝ)))
             kernel_eq := fun _ _ => by simp }⟩
  -- Upper bound: limsup Vⁿ ≤ u(0)
  have hup : limsup (fun n => value S n) atTop ≤ ENNReal.ofReal (u 0) := by
    set s : ℕ → ℝ≥0∞ := fun n => ⨆ f : AdversaryControl S n, cost S n (betaStar S n) f with hs
    have hVs : ∀ᶠ n in atTop, value S n ≤ s n := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact iInf₂_le (betaStar S n) (betaStar_admissible S n hn)
    have hs_le : limsup s atTop ≤ ENNReal.ofReal (u 0) := by
      by_contra hcon
      rw [not_le] at hcon
      obtain ⟨y, hy1, hy2⟩ := exists_between hcon
      have hfreq : ∃ᶠ n in atTop, y < s n := frequently_lt_of_lt_limsup (by isBoundedDefault) hy2
      have hch : ∀ n : ℕ, ∃ f : AdversaryControl S n, y < s n → y < cost S n (betaStar S n) f := by
        intro n
        by_cases h : y < s n
        · obtain ⟨f, hf⟩ := lt_iSup_iff.mp h
          exact ⟨f, fun _ => hf⟩
        · exact ⟨(hne n).some, fun h' => absurd h' h⟩
      choose f hf using hch
      have h47 := eq_47 S u hu f
      have : y ≤ limsup (fun n => cost S n (betaStar S n) (f n)) atTop :=
        le_limsup_of_frequently_le' (hfreq.mono fun n hn => (hf n hn).le)
      exact absurd (this.trans h47) (not_le.mpr hy1)
    exact (limsup_le_limsup hVs).trans hs_le
  -- Lower bound: u(0) ≤ liminf Vⁿ
  have hlow : ENNReal.ofReal (u 0) ≤ liminf (fun n => value S n) atTop := by
    have hψ0 : ∀ n : ℕ, ∀ ℓ : Fin L, ∃ ψ : ℝ → ProbabilityMeasure ℝ, 1 ≤ n →
        (Measurable ψ ∧ (∀ z : ℝ, 0 ≤ z → ψ z ∈ S.cls n ℓ) ∧
        ∀ z : ℝ, 0 ≤ z →
          Hbar (d1 u z) (d2 u z) (drift (ψ z) (S.μ ℓ) n) (halfVar (ψ z)) =
            Hpre S n ℓ (d1 u z) (d2 u z)) := by
      intro n ℓ
      by_cases hn : 1 ≤ n
      · obtain ⟨ψ, h⟩ := theorem_2_2 S u hu n hn ℓ
        exact ⟨ψ, fun _ => h⟩
      · exact ⟨fun _ => (S.cls_nonempty n ℓ).some, fun h => absurd h hn⟩
    choose ψ hψ using hψ0
    obtain ⟨⟨a, ha⟩, h55⟩ := eq_55 S u hu ψ (fun n hn ℓ => hψ n ℓ hn)
    have hy := h55 a ha
    obtain ⟨hfin, hlim⟩ := theorem_1 S a
    set x : ℕ → ℝ≥0∞ := fun n => ⨅ β ∈ admissibleStrategies S n, cost S n β (a n) with hxdef
    set y : ℕ → ℝ≥0∞ := fun n => cost S n (betaStar S n) (a n) with hydef
    have hVx : ∀ n, x n ≤ value S n := by
      intro n
      exact iInf₂_mono fun β _ => le_iSup (fun f => cost S n β f) (a n)
    have hxy : ∀ n, 1 ≤ n → x n ≤ y n := fun n hn =>
      iInf₂_le (betaStar S n) (betaStar_admissible S n hn)
    have hx : ENNReal.ofReal (u 0) ≤ liminf x atTop := by
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      have hev : ∀ᶠ n in atTop, y n ≤ x n + (ε : ℝ≥0∞) := by
        have hlt : ∀ᶠ n in atTop, -(ε : ℝ) < (x n).toReal - (y n).toReal :=
          hlim.eventually (lt_mem_nhds (by simpa using hε))
        filter_upwards [hlt, eventually_ge_atTop 1] with n hn h1
        have hyt : y n ≠ ⊤ := hfin n h1
        have hxt : x n ≠ ⊤ := ne_top_of_le_ne_top hyt (hxy n h1)
        rw [← ENNReal.ofReal_toReal hyt, ← ENNReal.ofReal_toReal hxt, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      calc ENNReal.ofReal (u 0) ≤ liminf y atTop := hy
        _ ≤ liminf (fun n => x n + (ε : ℝ≥0∞)) atTop := liminf_le_liminf hev
        _ = liminf x atTop + ε := liminf_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
    exact hx.trans (liminf_le_liminf (Eventually.of_forall hVx))
  exact tendsto_of_le_liminf_of_limsup_le hlow hup
