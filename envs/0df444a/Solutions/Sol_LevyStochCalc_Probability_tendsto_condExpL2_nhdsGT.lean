-- Prove2me | solution 1 for LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:06:32.628594+00:00
-- url     : https://prove2.me/submissions/a9406e46-9ec4-45b4-8d83-e3e0274a464f

import Definitions.Def_LevyStochCalc_Probability_CondExpRightContinuous_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right continuity in `L²` of the conditional expectation along a right-continuous filtration

For a filtration `ℱ` indexed by `ℝ` the σ-algebras `ℱ (t + 1/(n+1))` form an antitone sequence
whose infimum is `⨅ r > t, ℱ r`, which is `ℱ t` when `ℱ` is right-continuous. The `L²`
conditional expectations therefore converge to `𝔼[f | ℱ t]` along that sequence
(`LevyStochCalc.Probability.CondExpInf`), and `r ↦ ‖𝔼[f | ℱ r] − 𝔼[f | ℱ t]‖` is monotone on
`[t, ∞)` because the subspaces `lpMeas (ℱ r)` grow, so the convergence upgrades from the sequence
to the filter `𝓝[>] t`.

## Main statements

* `iInf_filtration_add_one_div` — `⨅ n, ℱ (t + 1/(n+1)) = ⨅ r > t, ℱ r`.
* `tendsto_condExpL2_nhdsGT` — `𝔼[f | ℱ r] → 𝔼[f | ℱ t]` in `L²` as `r ↓ t`.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}

section Sequence

variable (ℱ : Filtration ℝ m₀) (t : ℝ)

end Sequence



theorem _root_.proj_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection] (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by
  set p : ℕ → E := fun n => (V n).starProjection x with hp
  set a : ℕ → ℝ := fun n => ‖p n‖ ^ 2 with ha
  have hanti : Antitone a := LevyStochCalc.Probability.antitone_norm_sq_starProjection hV x
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  set L := ⨅ n, a n
  have hL : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciInf hanti hbdd
  have hLle : ∀ n, L ≤ a n := fun n => ciInf_le hbdd n
  have hpy : ∀ n m, n ≤ m → ‖p n - p m‖ ^ 2 = a n - a m := by
    intro n m hnm
    have := LevyStochCalc.Probability.norm_sq_starProjection_of_le (hV hnm) x
    simp only [ha, hp] at this ⊢
    linarith
  have hd : ∀ n N, N ≤ n → dist (p n) (p N) ≤ Real.sqrt (a N - L) := by
    intro n N hNn
    rw [dist_comm, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hpy N n hNn]
    exact Real.sqrt_le_sqrt (by linarith [hLle n])
  have hcau : CauchySeq p := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * Real.sqrt (a N - L)) (fun n m N hn hm => ?_) ?_
    · calc dist (p n) (p m) ≤ dist (p n) (p N) + dist (p N) (p m) := dist_triangle _ _ _
        _ ≤ Real.sqrt (a N - L) + Real.sqrt (a N - L) := by
          gcongr
          · exact hd n N hn
          · rw [dist_comm]; exact hd m N hm
        _ = 2 * Real.sqrt (a N - L) := by ring
    · have : Tendsto (fun N => a N - L) atTop (𝓝 0) := by
        simpa using hL.sub_const L
      simpa using (this.sqrt).const_mul 2
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  set W := ⨅ n, V n
  have hyW : y ∈ W := by
    rw [Submodule.mem_iInf]
    intro k
    refine (hclosed k).mem_of_tendsto hy ?_
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    exact hV hm ((V m).starProjection_apply_mem x)
  have horth : ∀ w ∈ W, inner ℝ (x - y) w = 0 := by
    intro w hw
    have hlim : Tendsto (fun n => inner ℝ (x - p n) w) atTop (𝓝 (inner ℝ (x - y) w)) :=
      ((tendsto_const_nhds.sub hy).inner tendsto_const_nhds)
    have hz : ∀ n, inner ℝ (x - p n) w = 0 := by
      intro n
      have hwn : w ∈ V n := (Submodule.mem_iInf _).1 hw n
      exact (V n).sub_starProjection_mem_orthogonal x w hwn |> fun h => by
        rw [real_inner_comm]; exact h
    simp only [hz] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have heq : W.starProjection x = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hyW horth
  rw [heq]
  exact hy

theorem _root_.cel_aux {m : ℕ → MeasurableSpace Ω} (hanti : Antitone m) (hle : ∀ n, m n ≤ m₀)
    (hle_inf : (⨅ n, m n) ≤ m₀) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ((condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ))) atTop
      (𝓝 ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))) := by
  have : ∀ n, Fact (m n ≤ m₀) := fun n => ⟨hle n⟩
  have : Fact ((⨅ n, m n) ≤ m₀) := ⟨hle_inf⟩
  set V : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => lpMeas ℝ ℝ (m n) 2 μ
  have hV : Antitone V := LevyStochCalc.Probability.antitone_lpMeas (m₀ := m₀) hanti
  have heq : (⨅ n, V n) = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := LevyStochCalc.Probability.lpMeas_iInf_of_antitone (m₀ := m₀) hanti
  have : (⨅ n, V n).HasOrthogonalProjection := by rw [heq]; infer_instance
  have hclosed : ∀ n, IsClosed ((V n : Set (Lp ℝ 2 μ))) := fun n => by
    rw [← Submodule.orthogonal_orthogonal (V n)]; exact Submodule.isClosed_orthogonal _
  have key := proj_aux hV hclosed f
  rw [LevyStochCalc.Probability.starProjection_congr heq f] at key
  exact key

theorem _root_.condExpL2_congr_sigma {m1 m2 : MeasurableSpace Ω} (h : m1 = m2) (h1 : m1 ≤ m₀)
    (h2 : m2 ≤ m₀) (f : Lp ℝ 2 μ) :
    (condExpL2 ℝ ℝ h1 f : Lp ℝ 2 μ) = condExpL2 ℝ ℝ h2 f := by
  subst h; rfl

theorem _root_.solution (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous] (t : ℝ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun r => ((condExpL2 ℝ ℝ (ℱ.le r) f : Lp ℝ 2 μ))) (𝓝[>] t)
      (𝓝 ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ))) := by
  have hI := LevyStochCalc.Probability.iInf_filtration_add_one_div_of_isRightContinuous ℱ t
  have hseq : Tendsto (fun n : ℕ => (condExpL2 ℝ ℝ (ℱ.le (t + 1 / (n + 1 : ℝ))) f : Lp ℝ 2 μ))
      atTop (𝓝 (condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ)) := by
    have h1 := cel_aux (m := fun n : ℕ => ℱ (t + 1 / (n + 1 : ℝ)))
      (LevyStochCalc.Probability.antitone_filtration_add_one_div ℱ t)
      (fun n => ℱ.le (t + 1 / (n + 1 : ℝ))) (by rw [hI]; exact ℱ.le t) f
    rwa [condExpL2_congr_sigma hI _ (ℱ.le t)] at h1
  have hmono : ∀ r (n : ℕ), t < r → r ≤ t + 1 / (n + 1 : ℝ) →
      dist (condExpL2 ℝ ℝ (ℱ.le r) f : Lp ℝ 2 μ) (condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ) ≤
      dist (condExpL2 ℝ ℝ (ℱ.le (t + 1 / (n + 1 : ℝ))) f : Lp ℝ 2 μ)
        (condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ) := by
    intro r n htr hrs
    have : Fact (ℱ t ≤ m₀) := ⟨ℱ.le t⟩
    have : Fact (ℱ r ≤ m₀) := ⟨ℱ.le r⟩
    have : Fact (ℱ (t + 1 / (n + 1 : ℝ)) ≤ m₀) := ⟨ℱ.le _⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact LevyStochCalc.Probability.norm_starProjection_sub_le_of_le
      (LevyStochCalc.Probability.lpMeas_mono (m₀ := m₀) (ℱ.mono htr.le))
      (LevyStochCalc.Probability.lpMeas_mono (m₀ := m₀) (ℱ.mono hrs)) f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hseq) ε hε
  have hsN : t < t + 1 / (N + 1 : ℝ) := LevyStochCalc.Probability.lt_add_one_div t N
  filter_upwards [Ioo_mem_nhdsGT hsN] with r hr
  exact lt_of_le_of_lt (hmono r N hr.1 hr.2.le) (hN N le_rfl)
