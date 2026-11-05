-- Prove2me | solution 1 for NondomArb.Superhedge.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:36:17.377427+00:00
-- url     : https://prove2.me/submissions/bb62c48f-6ab9-4cac-9921-80c582c519f0

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
import Theorems.Thm_NondomArb_Superhedge_theorem_2_2
open MeasureTheory Filter Topology NondomArb.Superhedge.General
open NondomArb.Superhedge

namespace Thm23Aux

variable {Ω : Type*} [MeasurableSpace Ω] {Pset : Set (Measure Ω)}

lemma qs_mono {p q : Ω → Prop} (hp : QS Pset p) (h : ∀ ω, p ω → q ω) : QS Pset q := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  exact ⟨A, hA, fun ω hω => hsub (fun hp => hω (h ω hp)), h0⟩

lemma qs_and {p q : Ω → Prop} (hp : QS Pset p) (hq : QS Pset q) :
    QS Pset (fun ω => p ω ∧ q ω) := by
  obtain ⟨A, hA, hsub, h0⟩ := hp
  obtain ⟨B, hB, hsubB, h0B⟩ := hq
  refine ⟨A ∪ B, hA.union hB, fun ω hω => ?_,
    fun P hP => measure_union_null (h0 P hP) (h0B P hP)⟩
  by_cases h1 : p ω
  · exact Or.inr (hsubB fun h2 => hω ⟨h1, h2⟩)
  · exact Or.inl (hsub h1)

lemma qs_always (p : Ω → Prop) (h : ∀ ω, p ω) : QS Pset p :=
  ⟨∅, MeasurableSet.empty, fun ω hω => (hω (h ω)).elim, fun _ _ => measure_empty⟩

lemma qs_exists (hPne : Pset.Nonempty) (hPprob : ∀ P ∈ Pset, IsProbabilityMeasure P)
    {p : Ω → Prop} (hp : QS Pset p) : ∃ ω, p ω := by
  obtain ⟨A, _, hsub, h0⟩ := hp
  obtain ⟨P, hP⟩ := hPne
  haveI := hPprob P hP
  by_contra hcon
  have hU : (Set.univ : Set Ω) ⊆ A := fun ω _ => hsub (not_exists.mp hcon ω)
  have h1 := measure_mono (μ := P) hU
  rw [measure_univ, h0 P hP] at h1
  exact absurd h1 (by norm_num)

end Thm23Aux

namespace Thm23Aux

lemma wealth_meas {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m) {T d : ℕ}
    (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (H : ℕ → Ω → (Fin d → ℝ)) (hH : IsPredictable ℱ T H) : Measurable (wealth T S H) := by
  unfold wealth
  refine Finset.measurable_sum _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  have hHm : Measurable (H u) := (hH u hu').mono (ℱ.le u) le_rfl
  have hY : Measurable fun ω => S (u+1) ω - S u ω := (hS (u+1) hu').sub (hS u hu'.le)
  show Measurable fun ω => ∑ i, H u ω i * (S (u+1) ω - S u ω) i
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hHm).mul ((measurable_pi_apply i).comp hY)

lemma inCone_of_le {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Pset : Set (Measure Ω)) {T d : ℕ}
    (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (H : ℕ → Ω → (Fin d → ℝ)) (hH : IsPredictable ℱ T H) (W : Ω → ℝ) (hW : Measurable W)
    (hle : QS Pset (fun ω => W ω ≤ wealth T S H ω)) : InCone Pset ℱ T S W := by
  refine ⟨H, hH, fun ω => max (wealth T S H ω - W ω) 0,
    ((wealth_meas ℱ S hS H hH).sub hW).max measurable_const, fun ω => le_max_right _ _, ?_⟩
  refine qs_mono hle fun ω h => ?_
  show W ω = wealth T S H ω - max (wealth T S H ω - W ω) 0
  rw [max_eq_left (by linarith)]; ring

end Thm23Aux

open Thm23Aux in
theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Pset : Set (Measure Ω)) (hPne : Pset.Nonempty) (hPprob : ∀ P ∈ Pset, IsProbabilityMeasure P)
    {T d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S) (f : Ω → ℝ) (hf : Measurable f) :
    ⊥ < price Pset ℱ T S f ∧
      ∃ H : ℕ → Ω → (Fin d → ℝ), IsPredictable ℱ T H ∧
        QS Pset (fun ω => (f ω : EReal) ≤ price Pset ℱ T S f + ((wealth T S H ω : ℝ) : EReal)) := by
  classical
  set p := price Pset ℱ T S f with hp
  have hH0 : IsPredictable ℱ T (fun _ _ => (0 : Fin d → ℝ)) := fun u _ => measurable_const
  have hmem : ∀ y : ℝ, p < (y : EReal) → ∃ x' : ℝ, x' < y ∧ ∃ H, IsPredictable ℱ T H ∧
      QS Pset (fun ω => f ω ≤ x' + wealth T S H ω) := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := sInf_lt_iff.mp hy
    obtain ⟨x', rfl, H, hH, hq⟩ := hz
    exact ⟨x', by exact_mod_cast hzy, H, hH, hq⟩
  have hbot : ⊥ < p := by
    by_contra hcon
    have hp_bot : p = ⊥ := le_bot_iff.mp (not_lt.mp hcon)
    have hWm : ∀ n : ℕ, Measurable (fun ω => min (f ω + n) 1) :=
      fun n => (hf.add_const _).min measurable_const
    have hWn : ∀ n : ℕ, InCone Pset ℱ T S (fun ω => min (f ω + n) 1) := by
      intro n
      obtain ⟨x', hx', H, hH, hq⟩ := hmem (-(n:ℝ)) (by rw [hp_bot]; exact EReal.bot_lt_coe _)
      refine inCone_of_le ℱ Pset S hS H hH _ (hWm n) (qs_mono hq fun ω h => ?_)
      have := min_le_left (f ω + n) 1
      linarith
    have hconv : QS Pset (fun ω => Tendsto (fun n : ℕ => min (f ω + n) 1) atTop (𝓝 1)) := by
      refine qs_always _ fun ω => ?_
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (1 - f ω)
      filter_upwards [eventually_ge_atTop N] with n hn
      have : (N:ℝ) ≤ n := by exact_mod_cast hn
      exact (min_eq_right (by linarith)).symm
    obtain ⟨H, hH, K, _, hK0, hq⟩ := theorem_2_2 ℱ Pset hPne hPprob S hS hNA
      (fun n ω => min (f ω + n) 1) hWm hWn (fun _ => 1) measurable_const hconv
    have hge : QS Pset (fun ω => 0 ≤ wealth T S H ω) :=
      qs_mono hq fun ω h => by linarith [hK0 ω]
    have hzero := hNA H hH hge
    obtain ⟨ω, h1, h2⟩ := qs_exists hPne hPprob (qs_and hq hzero)
    have h1' : (1:ℝ) = wealth T S H ω - K ω := h1
    linarith [hK0 ω]
  refine ⟨hbot, ?_⟩
  by_cases htop : p = ⊤
  · refine ⟨_, hH0, qs_always _ fun ω => ?_⟩
    rw [htop, EReal.top_add_coe]; exact le_top
  set r := p.toReal with hr
  have hpr : p = (r : EReal) := (EReal.coe_toReal htop hbot.ne').symm
  have hWm : ∀ n : ℕ, Measurable (fun ω => f ω - r - 1 / ((n:ℝ) + 1)) :=
    fun n => (hf.sub_const _).sub_const _
  have hWn : ∀ n : ℕ, InCone Pset ℱ T S (fun ω => f ω - r - 1 / ((n:ℝ) + 1)) := by
    intro n
    obtain ⟨x', hx', H, hH, hq⟩ := hmem (r + 1 / ((n:ℝ) + 1)) (by
      rw [hpr]; exact_mod_cast (lt_add_of_pos_right r (by positivity)))
    refine inCone_of_le ℱ Pset S hS H hH _ (hWm n) (qs_mono hq fun ω h => ?_)
    linarith
  have hconv : QS Pset (fun ω => Tendsto (fun n : ℕ => f ω - r - 1 / ((n:ℝ) + 1)) atTop
      (𝓝 (f ω - r))) := by
    refine qs_always _ fun ω => ?_
    simpa using (tendsto_const_nhds (x := f ω - r)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨H, hH, K, _, hK0, hq⟩ := theorem_2_2 ℱ Pset hPne hPprob S hS hNA
    (fun n ω => f ω - r - 1 / ((n:ℝ) + 1)) hWm hWn (fun ω => f ω - r)
    (hf.sub_const _) hconv
  refine ⟨H, hH, qs_mono hq fun ω h => ?_⟩
  have h' : f ω - r = wealth T S H ω - K ω := h
  rw [hpr, ← EReal.coe_add]
  exact_mod_cast (by linarith [hK0 ω] : f ω ≤ r + wealth T S H ω)
