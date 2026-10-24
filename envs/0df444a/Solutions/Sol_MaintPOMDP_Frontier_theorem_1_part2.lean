-- Prove2me | solution 1 for MaintPOMDP.Frontier.theorem_1_part2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T02:15:05.737634+00:00
-- url     : https://prove2.me/submissions/f1ced804-0823-4f78-8b15-5201908fbbb2

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

theorem minDot_pair' (x y π : Vec) : minDot {x, y} π = min (dot π x) (dot π y) := by
  simp [minDot]

/-- Scaled convex-combination domination. -/
theorem comb_le' (π0 π1 x0 x1 y0 y1 z0 z1 p q r : ℝ) (h0 : 0 ≤ π0) (h1 : 0 ≤ π1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 < r) (hpqr : p + q = r)
    (hz0 : p * x0 + q * y0 ≤ r * z0) (hz1 : p * x1 + q * y1 ≤ r * z1) :
    min (π0 * x0 + π1 * x1) (π0 * y0 + π1 * y1) ≤ π0 * z0 + π1 * z1 := by
  have hm1 := min_le_left (π0 * x0 + π1 * x1) (π0 * y0 + π1 * y1)
  have hm2 := min_le_right (π0 * x0 + π1 * x1) (π0 * y0 + π1 * y1)
  set m := min (π0 * x0 + π1 * x1) (π0 * y0 + π1 * y1)
  have : r * m ≤ r * (π0 * z0 + π1 * z1) := by
    calc r * m = p * m + q * m := by rw [← hpqr]; ring
      _ ≤ p * (π0 * x0 + π1 * x1) + q * (π0 * y0 + π1 * y1) := by gcongr
      _ = π0 * (p * x0 + q * y0) + π1 * (p * x1 + q * y1) := by ring
      _ ≤ π0 * (r * z0) + π1 * (r * z1) := by gcongr
      _ = r * (π0 * z0 + π1 * z1) := by ring
  exact le_of_mul_le_mul_left this hr

theorem assemble' (X Z P I : ℝ) (hP1 : P ≤ X) (hP2 : min X Z ≤ P) (hI : min X Z ≤ I) :
    min (min P Z) I = min X Z := by
  simp only [min_def] at *
  split_ifs at * <;> linarith

theorem t1part2 (M : Params) (hM : M.Standing) (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR)
    (hhi : M.cR < M.thrP)
 :
    M.Solves ActSet.PR {M.uPdot, M.uRPdot} M.uFPdot := by
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
  have hcR0 : 0 < M.cR := by linarith
  have hs : 0 < M.cP + M.β * M.γ1 * M.cF := by
    have := mul_pos (mul_pos hb0 hg10) (by linarith : (0:ℝ) < M.cF); linarith
  have hK0 : 0 < K := by rw [hKdef]; exact div_pos hs (mul_pos (sub_pos.2 hb1) hD)
  -- hypotheses in polynomial form
  set θ := M.thrP with hθ
  have hlo' : M.γ0 * θ ≤ M.γ1 * M.cR := by
    have := mul_le_mul_of_nonneg_left hlo hg10.le
    rw [show M.γ1 * (M.γ0 / M.γ1 * θ) = M.γ0 * θ by field_simp] at this
    exact this
  set Y := M.chat / M.D with hY
  have hchat : M.chat = M.D * Y := by rw [hY]; field_simp
  have hYdef : M.D * Y = M.D * (-(K * M.β ^ 2 * M.γ0 - K * M.β * M.γ0 + K * M.β - K
      + M.β * M.cF * M.γ1 - M.β * M.cR * M.γ1 + M.β * M.cR)) := by
    rw [← hchat]; unfold chat γ1bar; rw [hDdef] at hK ⊢
    linear_combination (-M.β * M.γ0 - 1) * hK
  have hYeq : Y = -(K * M.β ^ 2 * M.γ0 - K * M.β * M.γ0 + K * M.β - K
      + M.β * M.cF * M.γ1 - M.β * M.cR * M.γ1 + M.β * M.cR) :=
    mul_left_cancel₀ (ne_of_gt hD) hYdef
  have hθK : θ = K * (1 - M.β) := hKthr.symm
  clear_value K θ Y
  have hγθ : 0 ≤ M.cR - M.γ0 * θ := by
    have := mul_le_mul_of_nonneg_left hg11.le hcR0.le
    linarith only [this, hlo']
  have e1 : dot M.p0 M.uPdot ≤ dot M.p0 M.uRPdot := by
    simp only [dot, p0, uRPdot, diag, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]
    have : M.γ0 * θ = M.γ0 * K * (1 - M.β) := by rw [hθK]; ring
    linarith only [this, hγθ]
  apply solves_of_fixed M hM' ActSet.PR {M.uPdot, M.uRPdot} (by simp) M.uFPdot
  · intro π h0 h1
    simp only [bellman, minDot_pair']
    have e2 : dot M.p1 M.uRPdot ≤ dot M.p1 M.uPdot := by
      simp only [dot, p1, uRPdot, diag, γ1bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]
      have := mul_le_mul_of_nonneg_left hhi.le (sub_pos.2 hg11).le
      have h2 : (1 - M.γ1) * θ = (1 - M.γ1) * K * (1 - M.β) := by rw [hθK]; ring
      linarith only [this, h2]
    rw [min_eq_left e1]
    have tPu : dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uPdot = dot π M.uPdot := by
      simp only [dot, gP, PPt, uFPdot, γ0bar, γ1bar, Matrix.cons_val_zero, Matrix.cons_val_one,
        hu0, hu1]
      rw [hDdef] at hK
      linear_combination (-(π 1)) * hK
    have hdu : dot π M.uPdot = π 0 * (K * (M.β * M.γ0)) + π 1 * (K * (1 - M.β + M.β * M.γ0)) := by
      simp only [dot, hu0, hu1]
    have hdA : dot π M.uRPdot = π 0 * (M.cR + K * (M.β * M.γ0)) + π 1 * (M.cR + K * (M.β * M.γ0)) := by
      simp only [dot, uRPdot, diag, Matrix.cons_val_zero, Matrix.cons_val_one, hu0]
    have hq0 : M.β * (M.cR + K * (M.β * M.γ0)) - K * (M.β * M.γ0) = M.β * (M.cR - M.γ0 * θ) := by
      rw [hθK]; ring
    have ha0 : 0 < M.cR + K * (M.β * M.γ0) := add_pos hcR0 (mul_pos hK0 (mul_pos hb0 hg00))
    have hpA : 0 ≤ (1 - M.β) * (M.cR + K * (M.β * M.γ0)) :=
      mul_nonneg (sub_pos.2 hb1).le ha0.le
    have tPA : min (dot π M.uPdot) (dot π M.uRPdot) ≤
        dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uRPdot := by
      have Rr : dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uRPdot =
          π 0 * (M.β * (M.cR + K * (M.β * M.γ0))) + π 1 * (M.cP + M.β * M.γ1 * (K * (M.β * M.γ0) + M.cF)
          + M.β * (1 - M.γ1) * (M.cR + K * (M.β * M.γ0))) := by
        simp only [dot, gP, PPt, uFPdot, uRPdot, diag, γ0bar, γ1bar, Matrix.cons_val_zero,
          Matrix.cons_val_one, hu0]; ring
      rw [hdu, hdA, Rr]
      refine comb_le' (π 0) (π 1) _ _ _ _ _ _
        ((1 - M.β) * (M.cR + K * (M.β * M.γ0)))
        (M.β * (M.cR + K * (M.β * M.γ0)) - K * (M.β * M.γ0)) M.cR h0 h1 hpA
        (by rw [hq0]; exact mul_nonneg hb0.le hγθ) hcR0 (by ring) (le_of_eq (by ring)) ?_
      rw [hDdef] at hK
      have key : (1 - M.β) * (M.cR + K * (M.β * M.γ0)) * (K * (1 - M.β + M.β * M.γ0)) +
          (M.β * (M.cR + K * (M.β * M.γ0)) - K * (M.β * M.γ0)) * (M.cR + K * (M.β * M.γ0))
          + M.β * (θ - M.cR) * (M.γ1 * M.cR - M.γ0 * θ) =
          M.cR * (M.cP + M.β * M.γ1 * (K * (M.β * M.γ0) + M.cF)
            + M.β * (1 - M.γ1) * (M.cR + K * (M.β * M.γ0))) := by
        rw [hθK]; linear_combination M.cR * hK
      have := mul_nonneg (mul_nonneg hb0.le (sub_nonneg.2 hhi.le)) (sub_nonneg.2 hlo')
      linarith
    have tR : (π 0 + π 1) * (M.cR + M.β * dot M.p0 M.uPdot) = dot π M.uRPdot := by
      simp only [dot, p0, uRPdot, diag, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one,
        hu0, hu1]; ring
    -- assemble
    rw [tR]
    rcases min_choice (dot (M.PPt π) M.uPdot) (dot (M.PPt π) M.uRPdot) with hm | hm
    · rw [hm, tPu]
    · rw [hm]
      have hle : dot (M.PPt π) M.uRPdot ≤ dot (M.PPt π) M.uPdot := by
        rw [← hm]; exact min_le_left _ _
      have hPA : dot π (M.gP M.uFPdot) + M.β * dot (M.PPt π) M.uRPdot ≤ dot π M.uPdot := by
        have := mul_le_mul_of_nonneg_left hle hb0.le
        linarith only [this, tPu]
      apply le_antisymm
      · exact le_min (le_trans (min_le_left _ _) hPA) (min_le_right _ _)
      · exact le_min tPA (min_le_right _ _)
  · simp only [minDot_pair', uFPdot]
    rw [min_eq_left e1]
    have hp0 : M.β * dot M.p0 M.uPdot = M.uPdot 0 := by
      simp only [dot, p0, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]; ring
    linarith

theorem minDot_singleton' (u π : Vec) : minDot {u} π = dot π u := by
  simp [minDot]

theorem t1part1 (M : Params) (hM : M.Standing) (h : M.thrP ≤ M.cR) :
    M.Solves ActSet.PR {M.uPdot} M.uFPdot := by
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
  apply solves_of_fixed M hM' ActSet.PR {M.uPdot} (by simp) M.uFPdot
  · intro π h0 h1
    simp only [bellman, minDot_singleton']
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
    rw [eP, min_eq_left eR]
  · simp only [minDot_singleton', uFPdot]
    have hp0 : M.β * dot M.p0 M.uPdot = M.uPdot 0 := by
      simp only [dot, p0, γ0bar, Matrix.cons_val_zero, Matrix.cons_val_one, hu0, hu1]; ring
    linarith

theorem t1extreme (M : Params) (hM : M.Standing) (hhi : M.cR < M.thrP) :
    IsExtremeSet {M.uPdot, M.uRPdot} := by
  obtain ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  have hD : 0 < M.D := by unfold D; nlinarith
  have hdiff : M.uPdot 1 - M.uPdot 0 = M.thrP := by
    have h1b : (1 - M.β) ≠ 0 := ne_of_gt (sub_pos.2 hb1)
    have hDn : M.D ≠ 0 := ne_of_gt hD
    simp only [uPdot, thrP, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e : ∀ K : ℝ, K * (1 - M.β + M.β * M.γ0) - K * (M.β * M.γ0) = K * (1 - M.β) :=
      fun K => by ring
    rw [e]; field_simp
  have hlt0 : M.uPdot 0 < M.uRPdot 0 := by
    simp only [uRPdot, diag, Matrix.cons_val_zero]; linarith
  have hlt1 : M.uRPdot 1 < M.uPdot 1 := by
    simp only [uRPdot, diag, Matrix.cons_val_zero, Matrix.cons_val_one]; linarith
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · refine ⟨![1, 0], by simp [InSimplex], fun z hz hne => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact absurd rfl hne
    · simp [dot]; linarith
  · refine ⟨![0, 1], by simp [InSimplex], fun z hz hne => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [dot]; linarith
    · exact absurd rfl hne


end Params
end MaintPOMDP.Frontier

open MaintPOMDP.Frontier

theorem solution (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP) :
    M.Solves ActSet.PR {M.uPdot, M.uRPdot} M.uFPdot ∧ IsExtremeSet {M.uPdot, M.uRPdot} :=
  ⟨Params.t1part2 M hM hlo hhi, Params.t1extreme M hM hhi⟩
