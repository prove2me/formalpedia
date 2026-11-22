-- Prove2me | solution 1 for MasulloRH.localized_edge_pole_autocorrelation_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T20:05:45.516647+00:00
-- url     : https://prove2.me/submissions/ec886520-b819-4780-b2ae-5c83ac973da2

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped Topology

theorem solution
    (L α : ℝ) (hL : 0 < L) (hα : 0 < α) :
    let θ := fun x : ℝ => x - L * (⌊x / L⌋ : ℝ)
    let g := fun x : ℝ => if 0 ≤ x then
      Real.sqrt (2 * α) * Real.exp (-α * x + α * (2 * θ x - L)) else 0
    let K := fun R s : ℝ => ∫ t in (0 : ℝ)..max (R - s) 0, g t * g (t + s)
    let B := fun R s : ℝ => Real.exp (-α * s) *
      (1 - Real.exp (-2 * α * max (R - s) 0))
    Function.support g = Ici 0 ∧
    (∀ n : ℕ, (∫ t in (0 : ℝ)..(n : ℝ)*L, (g t)^2) =
      1 - Real.exp ((-2 * α) * ((n : ℝ) * L))) ∧
    (∫ t in Ioi (0 : ℝ), (g t)^2) = 1 ∧ ∀ R s : ℝ, 0 ≤ s →
      (K R s = 0 ↔ R ≤ s) ∧
      Real.exp (-2 * α * L) * B R s ≤ K R s ∧
      K R s ≤ Real.exp (2 * α * L) * B R s := by
  dsimp only
  let θ := fun x : ℝ => x - L * (⌊x / L⌋ : ℝ)
  let v := fun x : ℝ => Real.sqrt (2 * α) * Real.exp (-α * x + α * (2 * θ x - L))
  let g := fun x : ℝ => if 0 ≤ x then v x else 0
  have hvpos (x : ℝ) : 0 < v x := by dsimp [v]; positivity
  have hθ (x : ℝ) : 0 ≤ θ x ∧ θ x ≤ L := by
    have h₁ := (le_div_iff₀ hL).mp (Int.floor_le (x / L))
    have h₂ := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (x / L))
    dsimp [θ]
    constructor <;> linarith
  constructor
  · ext x
    change (g x ≠ 0) ↔ 0 ≤ x
    by_cases hx : 0 ≤ x <;> simp [g, hx, (hvpos x).ne']
  have hmeas : Measurable v := by
    dsimp [v, θ]; fun_prop
  have hgm : Measurable g := by
    exact Measurable.ite (p := fun t : ℝ => 0 ≤ t) measurableSet_Ici hmeas measurable_const
  let A := 2*α
  have hA : 0 < A := by dsimp [A]; positivity
  have sqv (x : ℝ) : (v x)^2 = A * Real.exp (A * (-x + (2 * θ x - L))) := by
    dsimp [v, A]
    rw [mul_pow, Real.sq_sqrt (by positivity), sq, ← Real.exp_add]
    congr 2
    ring
  have sqg (x : ℝ) : (g x)^2 ≤ (A * Real.exp (A*L)) * Real.exp ((-A)*x) := by
    by_cases hx : 0 ≤ x
    · simp only [g, if_pos hx, sqv]
      rw [mul_assoc A (Real.exp (A*L)), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (hθ x).2 hA.le
      linarith
    · simp only [g, if_neg hx, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have hgi : IntegrableOn (fun t => (g t)^2) (Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hA) 0).const_mul (A*Real.exp (A*L))).mono'
    · exact (hgm.pow_const 2).aestronglyMeasurable
    · apply Eventually.of_forall
      intro t
      change ‖(g t)^2‖ ≤ (A * Real.exp (A*L)) * Real.exp ((-A)*t)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g t))] using sqg t
  have hgi' (a b : ℝ) : IntervalIntegrable (fun t => (g t)^2) volume a b := by
    have hc : Continuous (fun t : ℝ => (A * Real.exp (A*L)) * Real.exp ((-A)*t)) := by fun_prop
    apply (hc.intervalIntegrable ..).mono_fun'
    · exact (hgm.pow_const 2).aestronglyMeasurable
    · apply Eventually.of_forall
      intro t
      change ‖(g t)^2‖ ≤ (A * Real.exp (A*L)) * Real.exp ((-A)*t)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (g t))] using sqg t
  let x := fun n : ℕ => (n : ℝ)*L
  have hx (n : ℕ) : x (n+1) = x n + L := by dsimp [x]; push_cast; ring
  have hcell (n : ℕ) : (∫ t in x n..x (n+1), (g t)^2) =
      Real.exp (-A * x n) - Real.exp (-A * x (n+1)) := by
    let C := -A * (2*x n+L)
    have hseg : (∫ t in x n..x (n+1), (g t)^2) =
        ∫ t in x n..x (n+1), Real.exp C * (A * Real.exp (A*t)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by rw [hx]; linarith)
      intro t ht
      have hxn : 0 ≤ x n := mul_nonneg (Nat.cast_nonneg _) hL.le
      have htpos : 0 ≤ t := hxn.trans ht.1.le
      have hfloor : ⌊t / L⌋ = (n : ℤ) := by
        apply Int.floor_eq_iff.mpr
        constructor
        · apply (le_div_iff₀ hL).mpr
          simpa [x] using ht.1.le
        · apply (div_lt_iff₀ hL).mpr
          simpa [x] using ht.2
      simp only [g, if_pos htpos, sqv, θ, hfloor, Int.cast_natCast]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      dsimp [C,x]
      ring
    rw [hseg, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.exp hA.ne', integral_exp, smul_eq_mul,
      mul_inv_cancel_left₀ hA.ne', mul_sub,
      ← Real.exp_add, ← Real.exp_add, hx]
    congr 2 <;> dsimp [C] <;> ring
  have hm (n : ℕ) : (∫ t in (0 : ℝ)..x n, (g t)^2) = 1 - Real.exp (-A*x n) := by
    induction n with
    | zero => simp [x]
    | succ n ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals (hgi' 0 (x n)) (hgi' (x n) (x (n+1))),
        ih, hcell]
      ring
  have hAeq : -A = -2 * α := by dsimp [A]; ring
  refine ⟨by simpa only [hAeq] using hm, ?_, ?_⟩
  · have hxtop : Tendsto x atTop atTop := tendsto_natCast_atTop_atTop.atTop_mul_const hL
    apply tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hgi hxtop)
    simp_rw [hm]
    have hxneg := hxtop.const_mul_atTop_of_neg (neg_lt_zero.mpr hA)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (Real.tendsto_exp_atBot.comp hxneg)
  intro R s hs
  let D := max (R - s) 0
  have hD : 0 ≤ D := le_max_right _ _
  let w := fun t : ℝ => 2 * α * Real.exp ((-2 * α) * t)
  let c := fun u : ℝ => Real.exp u * Real.exp (-α * s)
  have hw (u : ℝ) : Continuous (fun t => c u * w t) := by
    dsimp [w]; fun_prop
  have heq (t : ℝ) : v t * v (t + s) =
      (2 * α) * Real.exp ((-2 * α) * t + -α * s +
        α * (2 * θ t - L) + α * (2 * θ (t + s) - L)) := by
    dsimp [v]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (by positivity), ← Real.exp_add]
    congr 2
    ring
  have hbounds (t : ℝ) : c (-2 * α * L) * w t ≤ v t * v (t+s) ∧
      v t * v (t+s) ≤ c (2 * α * L) * w t := by
    have lower₁ := mul_nonneg hα.le (hθ t).1
    have lower₂ := mul_nonneg hα.le (hθ (t+s)).1
    have upper₁ := mul_le_mul_of_nonneg_left (hθ t).2 hα.le
    have upper₂ := mul_le_mul_of_nonneg_left (hθ (t+s)).2 hα.le
    have aux (u : ℝ) : c u * w t =
        (2 * α) * Real.exp ((-2 * α) * t + -α * s + u) := by
      dsimp [c, w]
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [heq, aux, aux]
    constructor <;> apply mul_le_mul_of_nonneg_left _ (by positivity) <;>
      apply Real.exp_le_exp.mpr <;> linarith
  have hvi : IntervalIntegrable (fun t => v t * v (t + s)) volume 0 D := by
    apply ((hw (2 * α * L)).intervalIntegrable ..).mono_fun'
    · exact (hmeas.mul (hmeas.comp (measurable_id.add_const s))).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro t
      change ‖v t * v (t+s)‖ ≤ c (2 * α * L) * w t
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hvpos _) (hvpos _))]
      exact (hbounds t).2
  have hInt (u : ℝ) : (∫ t in (0 : ℝ)..D, c u * w t) =
      Real.exp u * (Real.exp (-α * s) * (1 - Real.exp (-2 * α * D))) := by
    dsimp only [w, c]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left Real.exp (show -2 * α ≠ 0 by positivity),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
    ring
  have hagree : (∫ t in (0 : ℝ)..D, g t * g (t+s)) =
      ∫ t in (0 : ℝ)..D, v t * v (t+s) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hD] at ht
    simp [g, ht.1, add_nonneg ht.1 hs]
  let I := ∫ t in (0 : ℝ)..D, g t * g (t+s)
  let B := Real.exp (-α * s) * (1 - Real.exp (-2 * α * D))
  have hlow : Real.exp (-2 * α * L) * B ≤ I := by
    dsimp only [I, B]
    rw [hagree, ← hInt]
    exact intervalIntegral.integral_mono_on hD ((hw _).intervalIntegrable ..) hvi
      fun t _ => (hbounds t).1
  have hhigh : I ≤ Real.exp (2 * α * L) * B := by
    dsimp only [I, B]
    rw [hagree, ← hInt]
    exact intervalIntegral.integral_mono_on hD hvi ((hw _).intervalIntegrable ..)
      fun t _ => (hbounds t).2
  refine ⟨⟨?_, ?_⟩, hlow, hhigh⟩
  · change I = 0 → R ≤ s
    intro hi
    by_contra! h
    have hdpos : 0 < D := lt_of_lt_of_le (sub_pos.mpr h) (le_max_left _ _)
    have hexp : Real.exp (-2 * α * D) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      exact mul_neg_of_neg_of_pos (by linarith) hdpos
    have hbpos : 0 < B := mul_pos (Real.exp_pos _) (sub_pos.mpr hexp)
    exact (lt_of_lt_of_le (mul_pos (Real.exp_pos _) hbpos) hlow).ne' hi
  · intro h
    change I = 0
    simp [I, D, max_eq_right (sub_nonpos.mpr h)]
