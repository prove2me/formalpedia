-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_state_moment_from_forcing
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:33:23.35268+00:00
-- url     : https://prove2.me/submissions/00066b0b-083a-4c1c-b46a-9a300bb97b5d

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_work_conserving_pathwise_growth

open MeasureTheory Set
open scoped ENNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem abs_sum_nonneg {k : ℕ} (x : Fin k → ℝ) : 0 ≤ l1norm x :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (x i))

private theorem state_le_sup_forcing {k : ℕ} [NeZero k] (μ θ : Fin k → ℝ) (a : ℝ) (ha : 0 < a)
    (hμ : ∀ i, 0 < μ i) (hμa : ∀ i, μ i ≤ a) (hθ : ∀ i, 0 ≤ θ i) (hθa : ∀ i, θ i ≤ a)
    (x w q : ℝ → Fin k → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hint : ∀ t ∈ Icc 0 T, ∀ i,
      IntervalIntegrable (fun s => x s i) volume 0 t ∧
      IntervalIntegrable (fun s => w s i) volume 0 t ∧
      IntervalIntegrable (fun s => q s i) volume 0 t)
    (hqn : ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ q t i)
    (hq : ∀ t ∈ Icc 0 T, (∑ i, q t i) = max (∑ i, x t i) 0)
    (hEq : ∀ t ∈ Icc 0 T, ∀ i, x t i = w t i +
      ∫ s in (0 : ℝ)..t, ((μ i - θ i) * q s i - μ i * x s i)) :
    ENNReal.ofReal (l1norm (x T)) ≤
      ENNReal.ofReal ((k : ℝ) * (1 + a * T) ^ 2) * supDist w (fun _ => 0) T := by
  let C := (k : ℝ) * (1 + a * T) ^ 2
  let W := supDist w (fun _ => 0) T
  have hC : 0 < C := by
    have hk : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
    dsimp [C]
    positivity
  change ENNReal.ofReal (l1norm (x T)) ≤ ENNReal.ofReal C * W
  by_cases hW : W = ⊤
  · rw [hW, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hC)]
    exact le_top
  have hwb (t : ℝ) (ht : t ∈ Icc 0 T) : l1norm (w t) ≤ W.toReal := by
    have h : ENNReal.ofReal (l1norm (w t)) ≤ W :=
      le_iSup_of_le t (le_iSup_of_le ht (by simp [l1norm]))
    exact (ENNReal.ofReal_le_iff_le_toReal hW).1 h
  have hb := work_conserving_pathwise_growth μ θ a ha hμ hμa hθ hθa x w q T W.toReal hT
    ENNReal.toReal_nonneg hint hqn hq hwb hEq T ⟨hT, le_rfl⟩
  change l1norm (x T) ≤ C * W.toReal at hb
  refine (ENNReal.ofReal_le_ofReal hb).trans_eq ?_
  rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hW]

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (n : ℕ) (hn : 0 < n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsControlled n X0 X Ψ)
    (hWork : IsWorkConserving n X Ψ)
    (a : ℝ) (ha : 0 < a) (hμa : ∀ i, M.muN n i ≤ a) (hθa : ∀ i, M.thetaN n i ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (p : ℝ) (hp : 0 ≤ p) :
    let W (ω : Ω) (t : ℝ) (i : Fin k) :=
      M.Xhat0 n X0 i + M.Ahat n ω t i -
      M.Rhat n ω (queueTime X Ψ ω i t / n) i -
      M.Shat n ω (busyTime Ψ ω i t / n) i +
      ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * t
    (∫⁻ ω, ENNReal.ofReal (l1norm (M.Xhat n X ω T)) ^ p ∂M.P) ≤
      ENNReal.ofReal ((k : ℝ) * (1 + a * T) ^ 2) ^ p *
        ∫⁻ ω, (supDist (W ω) (fun _ => 0) T) ^ p ∂M.P := by
  let W (ω : Ω) (t : ℝ) (i : Fin k) :=
    M.Xhat0 n X0 i + M.Ahat n ω t i -
    M.Rhat n ω (queueTime X Ψ ω i t / n) i -
    M.Shat n ω (busyTime Ψ ω i t / n) i +
    ((M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n) * t
  let c : ℝ≥0∞ := ENNReal.ofReal ((k : ℝ) * (1 + a * T) ^ 2)
  have hfin : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  change (∫⁻ ω, ENNReal.ofReal (l1norm (M.Xhat n X ω T)) ^ p ∂M.P) ≤
    c ^ p * ∫⁻ ω, (supDist (W ω) (fun _ => 0) T) ^ p ∂M.P
  rw [← lintegral_const_mul' _ _ hfin]
  apply lintegral_mono
  intro ω
  let xx (s : ℝ) := M.Xhat n X ω s
  let pp (s : ℝ) := M.Psihat n Ψ ω s
  let qq (s : ℝ) := Phihat n X Ψ ω s
  let r : ℝ := Real.sqrt n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hn'
  have hpp (s : ℝ) (i : Fin k) : pp s i = xx s i - qq s i := by
    change (Ψ ω s i - M.rho i * n) / r = (X ω s i - M.rho i * n) / r - (X ω s i - Ψ ω s i) / r
    ring
  have hint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      IntervalIntegrable (fun s => xx s i) volume 0 t ∧
      IntervalIntegrable (fun s => pp s i) volume 0 t ∧
      IntervalIntegrable (fun s => qq s i) volume 0 t := by
    have h := hC.integrable ω i t ht
    have hp' : IntervalIntegrable (fun s => pp s i) volume 0 t :=
      (h.1.sub (intervalIntegrable_const (c := M.rho i * n))).div_const r
    have hq' : IntervalIntegrable (fun s => qq s i) volume 0 t := h.2.div_const r
    refine ⟨?_, hp', hq'⟩
    have he : (fun s => xx s i) = (fun s => pp s i + qq s i) := by
      funext s
      rw [hpp, sub_add_cancel]
    rw [he]
    exact hp'.add hq'
  have hqn (s : ℝ) (hs : 0 ≤ s) (i : Fin k) : 0 ≤ qq s i :=
    div_nonneg (hC.phi_nonneg ω s i hs) hr.le
  have hq (t : ℝ) (ht : 0 ≤ t) : (∑ i, qq t i) = max (∑ i, xx t i) 0 := by
    have hs : (∑ i, xx t i) = ((∑ i, X ω t i) - n) / r := by
      simp only [xx, SystemSequence.Xhat, ← Finset.sum_div, Finset.sum_sub_distrib,
        ← Finset.sum_mul, show (∑ i, M.rho i) = 1 from M.sum_rho, one_mul, r]
    simp only [qq, Phihat, ← Finset.sum_div, ← hWork ω t ht]
    rw [← max_div_div_right (show 0 ≤ Real.sqrt (n : ℝ) from hr.le), zero_div, hs]
  have hbalance (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      xx t i = W ω t i -
        M.muN n i * (∫ s in (0 : ℝ)..t, pp s i) -
        M.thetaN n i * (∫ s in (0 : ℝ)..t, qq s i) := by
    have hIntP : (∫ s in (0 : ℝ)..t, pp s i) = (busyTime Ψ ω i t - t * (M.rho i * n)) / r := by
      change (∫ s in (0 : ℝ)..t, (Ψ ω s i - M.rho i * n) / r) = _
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hC.integrable ω i t ht).1 intervalIntegrable_const]
      simp only [busyTime, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hIntQ : (∫ s in (0 : ℝ)..t, qq s i) = queueTime X Ψ ω i t / r :=
      intervalIntegral.integral_div _ _
    rw [hIntP, hIntQ]
    simp only [xx, W, SystemSequence.Xhat, SystemSequence.Xhat0, SystemSequence.Ahat,
      SystemSequence.Rhat, SystemSequence.Shat]
    rw [hC.eq7 ω t i ht]
    dsimp [r]
    have div_scale (s : ℝ) : (n : ℝ) * (s / n) = s := mul_div_cancel₀ _ hn'.ne'
    have rate_scale (b s : ℝ) : (n : ℝ) * b * (s / n) = b * s := by
      rw [mul_comm (n : ℝ) b, mul_assoc, div_scale]
    rw [div_scale, div_scale, rate_scale, rate_scale]
    ring
  let d (s : ℝ) (i : Fin k) := (M.muN n i - M.thetaN n i) * qq s i - M.muN n i * xx s i
  have hdint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) : IntervalIntegrable (fun s => d s i) volume 0 t :=
    ((hint t ht i).2.2.const_mul _).sub ((hint t ht i).1.const_mul _)
  have hE (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      xx t i = W ω t i + ∫ s in (0 : ℝ)..t, d s i := by
    rw [hbalance t ht i]
    dsimp only [d]
    rw [intervalIntegral.integral_sub ((hint t ht i).2.2.const_mul _) ((hint t ht i).1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have he : (∫ s in (0 : ℝ)..t, pp s i) =
        (∫ s in (0 : ℝ)..t, xx s i) - ∫ s in (0 : ℝ)..t, qq s i := by
      simp_rw [hpp]
      exact intervalIntegral.integral_sub (hint t ht i).1 (hint t ht i).2.2
    rw [he]
    ring
  have hWint (t : ℝ) (ht : 0 ≤ t) (i : Fin k) :
      IntervalIntegrable (fun s => W ω s i) volume 0 t := by
    have hcont : ContinuousOn (fun s => ∫ u in (0 : ℝ)..s, d u i) (Icc 0 t) := by
      simpa only [uIcc_of_le ht] using intervalIntegral.continuousOn_primitive_interval'
        (hdint t ht i) (left_mem_uIcc (a := (0 : ℝ)) (b := t))
    refine (intervalIntegrable_congr ?_).1 ((hint t ht i).1.sub (hcont.intervalIntegrable_of_Icc ht))
    intro s hs
    have hs0 : 0 ≤ s := (uIoc_of_le ht ▸ hs).1.le
    dsimp only
    rw [hE s hs0 i, add_sub_cancel_right]
  change ENNReal.ofReal (l1norm (xx T)) ^ p ≤ c ^ p * (supDist (W ω) (fun _ => 0) T) ^ p
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hp]
  apply ENNReal.rpow_le_rpow _ hp
  exact state_le_sup_forcing (M.muN n) (M.thetaN n) a ha (M.muN_pos n) hμa (M.thetaN_nonneg n)
    hθa xx (W ω) qq T hT (fun t ht i => ⟨(hint t ht.1 i).1, hWint t ht.1 i, (hint t ht.1 i).2.2⟩)
    (fun t ht => hqn t ht.1) (fun t ht => hq t ht.1) (fun t ht => hE t ht.1)
