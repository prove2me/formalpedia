-- Prove2me | solution 1 for MaintPOMDP.Frontier.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:08:20.758501+00:00
-- url     : https://prove2.me/submissions/8895c66b-2c77-4aca-8f48-6ad6127156d5

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier
namespace Params

/-- Bellman is a `β`-contraction in the weighted metric `|ΔW(π)| ≤ d (π₀+π₁)`, `|ΔwF| ≤ d`. -/
theorem bellman_contract (M : Params) (hM : M.Standing) (A : ActSet)
    (V V' : (Vec → ℝ) × ℝ) (d : ℝ)
    (hW : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → |V.1 π - V'.1 π| ≤ d * (π 0 + π 1))
    (hF : |V.2 - V'.2| ≤ d) :
    (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      |(M.bellman A V).1 π - (M.bellman A V').1 π| ≤ M.β * d * (π 0 + π 1)) ∧
    |(M.bellman A V).2 - (M.bellman A V').2| ≤ M.β * d := by
  obtain ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  have hd : 0 ≤ d := le_trans (abs_nonneg _) hF
  have hp0 : |V.1 M.p0 - V'.1 M.p0| ≤ d := by
    have := hW M.p0 (by simp [p0, γ0bar]; linarith) (by simp [p0]; linarith)
    simpa [p0, γ0bar] using this
  have hp1 : |V.1 M.p1 - V'.1 M.p1| ≤ d * (1 - M.γ1) := by
    have := hW M.p1 (by simp [p1]) (by simp [p1, γ1bar]; linarith)
    simpa [p1, γ1bar] using this
  refine ⟨?_, ?_⟩
  · intro π h0 h1
    have hPP := hW (M.PPt π) (by simp [PPt, γ0bar]; nlinarith)
      (by simp [PPt, γ1bar]; nlinarith)
    simp only [PPt, γ0bar, γ1bar, Matrix.cons_val_zero, Matrix.cons_val_one] at hPP
    -- the three terms
    have eP : |(dot π (M.gP V.2) + M.β * V.1 (M.PPt π)) -
        (dot π (M.gP V'.2) + M.β * V'.1 (M.PPt π))| ≤ M.β * d * (π 0 + π 1) := by
      have e1 : (dot π (M.gP V.2) + M.β * V.1 (M.PPt π)) -
          (dot π (M.gP V'.2) + M.β * V'.1 (M.PPt π)) =
          π 1 * M.β * M.γ1 * (V.2 - V'.2) + M.β * (V.1 (M.PPt π) - V'.1 (M.PPt π)) := by
        simp only [dot, gP, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      rw [e1]
      have hPP' : |V.1 (M.PPt π) - V'.1 (M.PPt π)| ≤ d * (π 0 + (1 - M.γ1) * π 1) := by
        have : (1 - M.γ0) * π 0 + (M.γ0 * π 0 + (1 - M.γ1) * π 1) =
            π 0 + (1 - M.γ1) * π 1 := by ring
        simp only [PPt, γ0bar, γ1bar]
        rw [← this]; exact hPP
      calc |π 1 * M.β * M.γ1 * (V.2 - V'.2) + M.β * (V.1 (M.PPt π) - V'.1 (M.PPt π))|
          ≤ |π 1 * M.β * M.γ1 * (V.2 - V'.2)| + |M.β * (V.1 (M.PPt π) - V'.1 (M.PPt π))| :=
            abs_add_le _ _
        _ = π 1 * M.β * M.γ1 * |V.2 - V'.2| + M.β * |V.1 (M.PPt π) - V'.1 (M.PPt π)| := by
            rw [abs_mul (π 1 * M.β * M.γ1), abs_mul M.β,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ π 1 * M.β * M.γ1), abs_of_pos hb0]
        _ ≤ π 1 * M.β * M.γ1 * d + M.β * (d * (π 0 + (1 - M.γ1) * π 1)) := by
            gcongr
        _ = M.β * d * (π 0 + π 1) := by ring
    have eR : |(π 0 + π 1) * (M.cR + M.β * V.1 M.p0) - (π 0 + π 1) * (M.cR + M.β * V'.1 M.p0)|
        ≤ M.β * d * (π 0 + π 1) := by
      have : (π 0 + π 1) * (M.cR + M.β * V.1 M.p0) - (π 0 + π 1) * (M.cR + M.β * V'.1 M.p0)
          = ((π 0 + π 1) * M.β) * (V.1 M.p0 - V'.1 M.p0) := by ring
      rw [this, abs_mul, abs_of_nonneg (by positivity)]
      calc (π 0 + π 1) * M.β * |V.1 M.p0 - V'.1 M.p0| ≤ (π 0 + π 1) * M.β * d := by gcongr
        _ = _ := by ring
    have eI : |(dot π (M.gI V.2) + M.β * (π 0 * V.1 M.p0 + π 1 * V.1 M.p1)) -
        (dot π (M.gI V'.2) + M.β * (π 0 * V'.1 M.p0 + π 1 * V'.1 M.p1))|
        ≤ M.β * d * (π 0 + π 1) := by
      have e1 : (dot π (M.gI V.2) + M.β * (π 0 * V.1 M.p0 + π 1 * V.1 M.p1)) -
          (dot π (M.gI V'.2) + M.β * (π 0 * V'.1 M.p0 + π 1 * V'.1 M.p1)) =
          π 1 * M.β * M.γ1 * (V.2 - V'.2) + (π 0 * M.β) * (V.1 M.p0 - V'.1 M.p0)
            + (π 1 * M.β) * (V.1 M.p1 - V'.1 M.p1) := by
        simp only [dot, gI, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
      rw [e1]
      calc _ ≤ |π 1 * M.β * M.γ1 * (V.2 - V'.2) + (π 0 * M.β) * (V.1 M.p0 - V'.1 M.p0)|
              + |(π 1 * M.β) * (V.1 M.p1 - V'.1 M.p1)| := abs_add_le _ _
        _ ≤ |π 1 * M.β * M.γ1 * (V.2 - V'.2)| + |(π 0 * M.β) * (V.1 M.p0 - V'.1 M.p0)|
              + |(π 1 * M.β) * (V.1 M.p1 - V'.1 M.p1)| := by gcongr; exact abs_add_le _ _
        _ = π 1 * M.β * M.γ1 * |V.2 - V'.2| + (π 0 * M.β) * |V.1 M.p0 - V'.1 M.p0|
              + (π 1 * M.β) * |V.1 M.p1 - V'.1 M.p1| := by
            rw [abs_mul (π 1 * M.β * M.γ1), abs_mul (π 0 * M.β), abs_mul (π 1 * M.β) (V.1 M.p1 - V'.1 M.p1),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ π 1 * M.β * M.γ1),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ π 0 * M.β),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ π 1 * M.β)]
        _ ≤ π 1 * M.β * M.γ1 * d + (π 0 * M.β) * d + (π 1 * M.β) * (d * (1 - M.γ1)) := by
            gcongr
        _ = M.β * d * (π 0 + π 1) := by ring
    have hmin : ∀ a b a' b' : ℝ, |a - a'| ≤ M.β * d * (π 0 + π 1) →
        |b - b'| ≤ M.β * d * (π 0 + π 1) →
        |min a b - min a' b'| ≤ M.β * d * (π 0 + π 1) := by
      intro a b a' b' ha hb
      exact le_trans (abs_min_sub_min_le_max a b a' b') (max_le ha hb)
    cases A with
    | P => exact eP
    | PR => exact hmin _ _ _ _ eP eR
    | PIR => exact hmin _ _ _ _ (hmin _ _ _ _ eP eR) eI
  · show |(M.cF + M.β * V.1 M.p0) - (M.cF + M.β * V'.1 M.p0)| ≤ M.β * d
    have : (M.cF + M.β * V.1 M.p0) - (M.cF + M.β * V'.1 M.p0) = M.β * (V.1 M.p0 - V'.1 M.p0) := by
      ring
    rw [this, abs_mul, abs_of_pos hb0]
    gcongr

/-- Verification theorem: a fixed point of the Bellman operator (on beliefs `π ≥ 0`) of the
form `(minDot U, uF)` is the value-iteration limit. -/
theorem solves_of_fixed (M : Params) (hM : M.Standing) (A : ActSet) (U : Finset Vec)
    (hU : U.Nonempty) (uF : ℝ)
    (hfix : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → (M.bellman A (minDot U, uF)).1 π = minDot U π)
    (hF : M.cF + M.β * minDot U M.p0 = uF) : M.Solves A U uF := by
  have hb0 : 0 < M.β := hM.1
  have hb1 : M.β < 1 := hM.2.1
  set C : ℝ := |uF| + ∑ u ∈ U, (|u 0| + |u 1|) with hC
  have hsumnn : 0 ≤ ∑ u ∈ U, (|u 0| + |u 1|) :=
    Finset.sum_nonneg (fun u _ => by positivity)
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → |minDot U π| ≤ C * (π 0 + π 1) := by
    intro π h0 h1
    obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_inf' hU (dot π)
    have hmd : minDot U π = dot π u := by simp [minDot, hU, heq]
    rw [hmd]
    have hle : |u 0| + |u 1| ≤ ∑ u ∈ U, (|u 0| + |u 1|) :=
      Finset.single_le_sum (f := fun u : Vec => |u 0| + |u 1|) (fun u _ => by positivity) hu
    have hC' : |u 0| + |u 1| ≤ C := by rw [hC]; linarith [abs_nonneg uF]
    calc |dot π u| = |π 0 * u 0 + π 1 * u 1| := rfl
      _ ≤ |π 0 * u 0| + |π 1 * u 1| := abs_add_le _ _
      _ = π 0 * |u 0| + π 1 * |u 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
      _ ≤ π 0 * C + π 1 * C := by
          gcongr
          · linarith [abs_nonneg (u 1)]
          · linarith [abs_nonneg (u 0)]
      _ = C * (π 0 + π 1) := by ring
  -- the key estimate
  have key : ∀ n : ℕ, (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      |(M.VI A n).1 π - minDot U π| ≤ C * M.β ^ n * (π 0 + π 1)) ∧
      |(M.VI A n).2 - uF| ≤ C * M.β ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun π h0 h1 => ?_, ?_⟩
      · simp only [VI, Function.iterate_zero, id, pow_zero, mul_one, zero_sub, abs_neg]
        exact hbound π h0 h1
      · simp only [VI, Function.iterate_zero, id, pow_zero, mul_one, zero_sub, abs_neg]
        rw [hC]; linarith [hsumnn]
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hstep := M.bellman_contract hM A (M.VI A n) (minDot U, uF) (C * M.β ^ n) ih1 ih2
      have hVI : M.VI A (n + 1) = M.bellman A (M.VI A n) := by
        simp only [VI]; rw [Function.iterate_succ_apply']
      refine ⟨fun π h0 h1 => ?_, ?_⟩
      · rw [hVI, ← hfix π h0 h1]
        have := hstep.1 π h0 h1
        calc _ ≤ M.β * (C * M.β ^ n) * (π 0 + π 1) := this
          _ = C * M.β ^ (n + 1) * (π 0 + π 1) := by ring
      · rw [hVI]
        have h2 := hstep.2
        have : (M.bellman A (minDot U, uF)).2 = uF := by
          show M.cF + M.β * minDot U M.p0 = uF; exact hF
        rw [this] at h2
        calc _ ≤ M.β * (C * M.β ^ n) := h2
          _ = C * M.β ^ (n + 1) := by ring
  have hpow : Tendsto (fun n : ℕ => M.β ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1
  refine ⟨hU, fun π h0 h1 => ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => C * M.β ^ n * (π 0 + π 1)) atTop (𝓝 0) := by
      have := (hpow.const_mul C).mul_const (π 0 + π 1)
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (key n).1 π h0 h1) hlim
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => C * M.β ^ n) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (key n).2) hlim

theorem VI_succ (M : Params) (A : ActSet) (n : ℕ) : M.VI A (n + 1) = M.bellman A (M.VI A n) := by
  simp only [VI]; rw [Function.iterate_succ_apply']

theorem VI_one_bound (M : Params) (hM : M.Standing) (A : ActSet) :
    (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → |(M.VI A 1).1 π - (M.VI A 0).1 π| ≤ M.cF * (π 0 + π 1)) ∧
    |(M.VI A 1).2 - (M.VI A 0).2| ≤ M.cF := by
  obtain ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  rw [VI_succ]
  simp only [VI, Function.iterate_zero, id, bellman]
  refine ⟨fun π h0 h1 => ?_, ?_⟩
  · have tP : 0 ≤ dot π (M.gP 0) + M.β * 0 ∧ dot π (M.gP 0) + M.β * 0 ≤ M.cF * (π 0 + π 1) := by
      simp only [dot, gP, Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> nlinarith
    have tR : 0 ≤ (π 0 + π 1) * (M.cR + M.β * 0) ∧
        (π 0 + π 1) * (M.cR + M.β * 0) ≤ M.cF * (π 0 + π 1) := by
      constructor <;> nlinarith
    have tI : 0 ≤ dot π (M.gI 0) + M.β * (π 0 * 0 + π 1 * 0) ∧
        dot π (M.gI 0) + M.β * (π 0 * 0 + π 1 * 0) ≤ M.cF * (π 0 + π 1) := by
      simp only [dot, gI, Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> nlinarith
    rw [sub_zero, abs_le]
    cases A with
    | P => constructor <;> linarith [tP.1, tP.2, mul_nonneg (by linarith : (0:ℝ) ≤ M.cF) (add_nonneg h0 h1)]
    | PR =>
      constructor
      · have := le_min tP.1 tR.1
        linarith [mul_nonneg (by linarith : (0:ℝ) ≤ M.cF) (add_nonneg h0 h1)]
      · exact le_trans (min_le_left _ _) tP.2
    | PIR =>
      constructor
      · have := le_min (le_min tP.1 tR.1) tI.1
        linarith [mul_nonneg (by linarith : (0:ℝ) ≤ M.cF) (add_nonneg h0 h1)]
      · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) tP.2)
  · rw [abs_le]; constructor <;> nlinarith

theorem VI_consec (M : Params) (hM : M.Standing) (A : ActSet) (n : ℕ) :
    (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      |(M.VI A (n + 1)).1 π - (M.VI A n).1 π| ≤ M.cF * M.β ^ n * (π 0 + π 1)) ∧
    |(M.VI A (n + 1)).2 - (M.VI A n).2| ≤ M.cF * M.β ^ n := by
  induction n with
  | zero => simpa using M.VI_one_bound hM A
  | succ n ih =>
    have h := M.bellman_contract hM A (M.VI A (n + 1)) (M.VI A n) (M.cF * M.β ^ n) ih.1 ih.2
    rw [← VI_succ, ← VI_succ] at h
    refine ⟨fun π h0 h1 => ?_, ?_⟩
    · calc _ ≤ M.β * (M.cF * M.β ^ n) * (π 0 + π 1) := h.1 π h0 h1
        _ = _ := by ring
    · calc _ ≤ M.β * (M.cF * M.β ^ n) := h.2
        _ = _ := by ring

theorem prop2 (M : Params) (hM : M.Standing) (A : ActSet) :
    ∃ W : Vec → ℝ, ∃ wF : ℝ,
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → Tendsto (fun n => (M.VI A n).1 π) atTop (𝓝 (W π))) ∧
      Tendsto (fun n => (M.VI A n).2) atTop (𝓝 wF) ∧
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → W π = (M.bellman A (W, wF)).1 π) ∧
      wF = (M.cR + M.β * W M.p0) + M.cF - M.cR := by
  have hb0 : 0 < M.β := hM.1
  have hb1 : M.β < 1 := hM.2.1
  set W : Vec → ℝ := fun π => limUnder atTop (fun n => (M.VI A n).1 π) with hWdef
  set wF : ℝ := limUnder atTop (fun n => (M.VI A n).2) with hwFdef
  have hcauchy1 : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      ∀ n, dist ((M.VI A n).1 π) ((M.VI A (n + 1)).1 π) ≤ (M.cF * (π 0 + π 1)) * M.β ^ n := by
    intro π h0 h1 n
    rw [Real.dist_eq, abs_sub_comm]
    calc _ ≤ M.cF * M.β ^ n * (π 0 + π 1) := (M.VI_consec hM A n).1 π h0 h1
      _ = _ := by ring
  have hcauchy2 : ∀ n, dist ((M.VI A n).2) ((M.VI A (n + 1)).2) ≤ M.cF * M.β ^ n := by
    intro n; rw [Real.dist_eq, abs_sub_comm]; exact (M.VI_consec hM A n).2
  have hT1 : ∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      Tendsto (fun n => (M.VI A n).1 π) atTop (𝓝 (W π)) := by
    intro π h0 h1
    have hc := cauchySeq_of_le_geometric M.β _ hb1 (hcauchy1 π h0 h1)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨a, ha⟩
  have hT2 : Tendsto (fun n => (M.VI A n).2) atTop (𝓝 wF) := by
    have hc := cauchySeq_of_le_geometric M.β _ hb1 hcauchy2
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨a, ha⟩
  -- distance bounds to the limit
  have hd : ∀ n, (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      |(M.VI A n).1 π - W π| ≤ (M.cF * M.β ^ n / (1 - M.β)) * (π 0 + π 1)) ∧
      |(M.VI A n).2 - wF| ≤ M.cF * M.β ^ n / (1 - M.β) := by
    intro n
    refine ⟨fun π h0 h1 => ?_, ?_⟩
    · have := dist_le_of_le_geometric_of_tendsto M.β _ hb1 (hcauchy1 π h0 h1) (hT1 π h0 h1) n
      rw [Real.dist_eq] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    · have := dist_le_of_le_geometric_of_tendsto M.β _ hb1 hcauchy2 hT2 n
      rwa [Real.dist_eq] at this
  have hgeo : Tendsto (fun n : ℕ => M.cF * M.β ^ n / (1 - M.β)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb1).const_mul M.cF).div_const
      (1 - M.β)
    simpa using this
  have hstep : ∀ n, (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 →
      |(M.VI A (n + 1)).1 π - (M.bellman A (W, wF)).1 π| ≤
        M.β * (M.cF * M.β ^ n / (1 - M.β)) * (π 0 + π 1)) ∧
      |(M.VI A (n + 1)).2 - (M.bellman A (W, wF)).2| ≤ M.β * (M.cF * M.β ^ n / (1 - M.β)) := by
    intro n
    rw [VI_succ]
    exact M.bellman_contract hM A (M.VI A n) (W, wF) _ (hd n).1 (hd n).2
  refine ⟨W, wF, hT1, hT2, fun π h0 h1 => ?_, ?_⟩
  · have hA : Tendsto (fun n => (M.VI A (n + 1)).1 π) atTop (𝓝 (W π)) :=
      (hT1 π h0 h1).comp (tendsto_add_atTop_nat 1)
    have hB : Tendsto (fun n => (M.VI A (n + 1)).1 π) atTop (𝓝 ((M.bellman A (W, wF)).1 π)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n : ℕ => M.β * (M.cF * M.β ^ n / (1 - M.β)) * (π 0 + π 1))
          atTop (𝓝 0) := by
        simpa using (hgeo.const_mul M.β).mul_const (π 0 + π 1)
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hstep n).1 π h0 h1) hlim
    exact tendsto_nhds_unique hA hB
  · have hA : Tendsto (fun n => (M.VI A (n + 1)).2) atTop (𝓝 wF) :=
      hT2.comp (tendsto_add_atTop_nat 1)
    have hB : Tendsto (fun n => (M.VI A (n + 1)).2) atTop (𝓝 ((M.bellman A (W, wF)).2)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n : ℕ => M.β * (M.cF * M.β ^ n / (1 - M.β))) atTop (𝓝 0) := by
        simpa using hgeo.const_mul M.β
      exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hstep n).2) hlim
    have := tendsto_nhds_unique hA hB
    rw [this]
    show M.cF + M.β * W M.p0 = M.cR + M.β * W M.p0 + M.cF - M.cR
    ring

end Params
end MaintPOMDP.Frontier

open MaintPOMDP.Frontier

theorem solution (M : Params) (hM : M.Standing) (A : ActSet)
    (hA : A = ActSet.PR ∨ A = ActSet.PIR) :
    ∃ W : Vec → ℝ, ∃ wF : ℝ,
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → Tendsto (fun n => (M.VI A n).1 π) atTop (𝓝 (W π))) ∧
      Tendsto (fun n => (M.VI A n).2) atTop (𝓝 wF) ∧
      (∀ π : Vec, 0 ≤ π 0 → 0 ≤ π 1 → W π = (M.bellman A (W, wF)).1 π) ∧
      wF = (M.cR + M.β * W M.p0) + M.cF - M.cR :=
  Params.prop2 M hM A
