-- Prove2me | solution 1 for MaintPOMDP.Frontier.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:06:48.716346+00:00
-- url     : https://prove2.me/submissions/580262d7-ae93-4d01-8256-f47ccb6deccc

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
theorem minDot_singleton (u π : Vec) : minDot {u} π = dot π u := by
  simp [minDot]

theorem part1 (M : Params) (hM : M.Standing) (h : M.thrP ≤ M.cR) :
    M.Solves ActSet.PIR {M.uPdot} M.uFPdot := by
  obtain ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  have hM' : M.Standing := ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩
  have hD : 0 < M.D := by unfold D; nlinarith
  set K := (M.cP + M.β * M.γ1 * M.cF) / ((1 - M.β) * M.D) with hKdef
  have hK : K * ((1 - M.β) * M.D) = M.cP + M.β * M.γ1 * M.cF := by
    rw [hKdef]; field_simp [ne_of_gt (mul_pos (sub_pos.2 hb1) hD)]
    rw [mul_div_assoc, div_self (ne_of_gt (sub_pos.2 hb1)), mul_one]
  have hthr : M.thrP * M.D = M.cP + M.β * M.γ1 * M.cF := by
    unfold thrP; field_simp
  have hKthr : K * (1 - M.β) = M.thrP := by
    have : (K * (1 - M.β) - M.thrP) * M.D = 0 := by linear_combination hK - hthr
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hu0 : M.uPdot 0 = K * (M.β * M.γ0) := by simp [uPdot, hKdef]
  have hu1 : M.uPdot 1 = K * (1 - M.β + M.β * M.γ0) := by simp [uPdot, hKdef]
  have hDdef : M.D = 1 - M.β + M.β * (M.γ0 + M.γ1) := rfl
  apply solves_of_fixed M hM' ActSet.PIR {M.uPdot} (by simp) M.uFPdot
  · intro π h0 h1
    simp only [bellman, minDot_singleton]
    have eP : dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uPdot = dot π M.uPdot := by
      simp only [dot, gP, PPt, uFPdot, γ0bar, γ1bar, Matrix.cons_val_zero, Matrix.cons_val_one,
        hu0, hu1]
      rw [hDdef] at hK
      linear_combination (-(π 1)) * hK
    have hp0 : M.β * dot M.p0 M.uPdot = M.uPdot 0 := by
      simp only [dot, p0, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]; ring
    have eR : dot π M.uPdot ≤ (π 0 + π 1) * (M.cR + M.β * dot M.p0 M.uPdot) := by
      rw [hp0]
      simp only [dot, hu0, hu1]
      nlinarith [mul_nonneg h1 (sub_nonneg.2 h), mul_nonneg h0 (le_of_lt (by linarith : (0:ℝ) < M.cR))]
    have eI : dot π M.uPdot ≤ dot π (M.gI M.uFPdot) +
        M.β * (π 0 * dot M.p0 M.uPdot + π 1 * dot M.p1 M.uPdot) := by
      have : dot π (M.gI M.uFPdot) + M.β * (π 0 * dot M.p0 M.uPdot + π 1 * dot M.p1 M.uPdot)
          = (dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uPdot) + π 0 * M.cI
            + π 1 * (M.cI - M.cP) := by
        simp only [dot, gP, gI, PPt, p0, p1, γ0bar, γ1bar, Matrix.cons_val_zero,
          Matrix.cons_val_one]; ring
      rw [this, eP]
      nlinarith [mul_nonneg h0 (le_of_lt (by linarith : (0:ℝ) < M.cI)),
        mul_nonneg h1 (le_of_lt (sub_pos.2 hPI))]
    rw [eP, min_eq_left eR, min_eq_left eI]
  · simp only [minDot_singleton, uFPdot]
    have hp0 : M.β * dot M.p0 M.uPdot = M.uPdot 0 := by
      simp only [dot, p0, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]; ring
    linarith

theorem prop3 (M : Params) (hM : M.Standing) :
    M.Solves ActSet.P {M.uPdot} M.uFPdot := by
  obtain ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  have hM' : M.Standing := ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩
  have hD : 0 < M.D := by unfold D; nlinarith
  set K := (M.cP + M.β * M.γ1 * M.cF) / ((1 - M.β) * M.D) with hKdef
  have hK : K * ((1 - M.β) * M.D) = M.cP + M.β * M.γ1 * M.cF := by
    rw [hKdef]; field_simp [ne_of_gt (mul_pos (sub_pos.2 hb1) hD)]
    rw [mul_div_assoc, div_self (ne_of_gt (sub_pos.2 hb1)), mul_one]
  have hu0 : M.uPdot 0 = K * (M.β * M.γ0) := by simp [uPdot, hKdef]
  have hu1 : M.uPdot 1 = K * (1 - M.β + M.β * M.γ0) := by simp [uPdot, hKdef]
  have hDdef : M.D = 1 - M.β + M.β * (M.γ0 + M.γ1) := rfl
  apply solves_of_fixed M hM' ActSet.P {M.uPdot} (by simp) M.uFPdot
  · intro π h0 h1
    simp only [bellman, minDot_singleton]
    simp only [dot, gP, PPt, uFPdot, γ0bar, γ1bar, Matrix.cons_val_zero, Matrix.cons_val_one,
      hu0, hu1]
    rw [hDdef] at hK
    linear_combination (-(π 1)) * hK
  · simp only [minDot_singleton, uFPdot]
    have hp0 : M.β * dot M.p0 M.uPdot = M.uPdot 0 := by
      simp only [dot, p0, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]; ring
    linarith

end Params
end MaintPOMDP.Frontier

open MaintPOMDP.Frontier

theorem solution (M : Params) (hM : M.Standing) :
    M.Solves ActSet.P {M.uPdot} M.uFPdot :=
  Params.prop3 M hM
