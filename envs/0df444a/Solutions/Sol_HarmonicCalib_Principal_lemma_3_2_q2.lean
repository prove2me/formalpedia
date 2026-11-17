-- Prove2me | solution 1 for HarmonicCalib.Principal.lemma_3_2_q2
-- status  : ACCEPTED   (prove)
-- author  : @amenyxia
-- created : 2026-11-16T22:04:08.76668+00:00
-- url     : https://prove2.me/submissions/52671fbe-ca1d-44dc-be7d-f29181ffe1cd

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Hilbert
open HarmonicCalib.Principal

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal Matrix

noncomputable section


private lemma lq2_eq_norm (T : ℕ) (z : Fin T → ℝ) :
    lqNorm 2 z = ‖WithLp.toLp (2 : ℝ≥0∞) z‖ := by
  have hsum1 : ∑ t : Fin T, |z t| ^ (2 : ℝ) = ∑ t : Fin T, (z t) ^ (2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro t _
    calc
      |z t| ^ (2 : ℝ) = |z t| ^ (2 : ℕ) := Real.rpow_natCast _ 2
      _ = (z t) ^ (2 : ℕ) := sq_abs (z t)
      _ = (z t) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
  have hlhs : lqNorm 2 z = Real.sqrt (∑ t : Fin T, (z t) ^ (2 : ℝ)) := by
    dsimp only [lqNorm]
    rw [hsum1, (Real.sqrt_eq_rpow (∑ t : Fin T, (z t) ^ (2 : ℝ))).symm]
  have hsum2 : ∑ i : Fin T, ‖(WithLp.toLp (2 : ℝ≥0∞) z) i‖ ^ (2 : ℕ) =
      ∑ t : Fin T, ‖z t‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [PiLp.toLp_apply]
  have hsum3 : ∑ t : Fin T, ‖z t‖ ^ (2 : ℕ) = ∑ t : Fin T, (z t) ^ (2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro t _
    calc
      ‖z t‖ ^ (2 : ℕ) = |z t| ^ (2 : ℕ) := congrArg (· ^ (2 : ℕ)) (Real.norm_eq_abs (z t))
      _ = (z t) ^ (2 : ℕ) := sq_abs (z t)
      _ = (z t) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
  have hrhs : ‖WithLp.toLp (2 : ℝ≥0∞) z‖ = Real.sqrt (∑ t : Fin T, (z t) ^ (2 : ℝ)) := by
    rw [EuclideanSpace.norm_eq (WithLp.toLp (2 : ℝ≥0∞) z), hsum2, hsum3]
  rw [hlhs, hrhs]
private def Uy (T : ℕ) (y : Fin T → ℝ) (θ : ℝ) : ℂ :=
    ∑ t, (y t : ℂ) * Complex.exp (2 * (t : ℝ) * θ * Complex.I)

private def Vx (T : ℕ) (z : Fin T → ℝ) (θ : ℝ) : ℂ :=
    ∑ s, (z s : ℂ) * Complex.exp ((2 * (s : ℝ) + 1) * θ * Complex.I)

open Complex
open scoped ComplexConjugate

private lemma int_exp_even (n : ℤ) (hn : Even n) :
    ∫ x in (0)..(Real.pi), Complex.exp (↑n * x * Complex.I) =
      if n = 0 then (Real.pi : ℂ) else 0 := by
  split_ifs with hz
  · have hzero : ∀ x : ℝ, Complex.exp (↑n * x * Complex.I) = 1 := by
      intro x
      rw [hz]
      simp [Complex.exp_zero]
    simp only [hzero]
    rw [intervalIntegral.integral_const]
    simp [sub_zero]
  · have hne : (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hz) Complex.I_ne_zero
    have hred : ∀ x : ℝ, Complex.exp (↑n * x * Complex.I) =
        Complex.exp ((↑n : ℂ) * Complex.I * x) := by
      intro x
      ring
    simp only [hred]
    rw [integral_exp_mul_complex hne]
    have hpi : Complex.exp ((↑n : ℂ) * Complex.I * Real.pi) = 1 := by
      rcases hn with ⟨m, rfl⟩
      rw [show (↑(m + m : ℤ) : ℂ) * Complex.I * Real.pi = (m : ℤ) * (2 * Real.pi * Complex.I) by
        apply Complex.ext <;> (simp; try ring)]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have hzero : Complex.exp ((↑n : ℂ) * Complex.I * (0 : ℝ)) = 1 := by
      rw [show (↑n : ℂ) * Complex.I * (0 : ℝ) = (0 : ℂ) by simp]
      exact Complex.exp_zero
    rw [hpi, hzero]
    field_simp [hne]
    norm_num

private lemma int_sin_odd (k : ℤ) (hk : Odd k) :
    ∫ x in (0)..(Real.pi), Real.sin (↑k * x) = 2 / ↑k := by
  have hk0 : k ≠ 0 := by
    by_contra h
    rcases hk with ⟨m, rfl⟩
    omega
  have hk0r : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0
  have hA : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun x : ℝ => -Real.cos (k * x) / (k : ℝ)) (Real.sin (k * x)) x := by
    intro x hx
    have hlin := (hasDerivAt_id x).const_mul (k : ℝ)
    have hcos := (Real.hasDerivAt_cos ((k : ℝ) * x)).comp x hlin
    convert hcos.neg.div_const (k : ℝ) using 1
    all_goals try { exact AddCommGroup.ext_iff.mpr rfl }
    all_goals try { funext; rfl }
    all_goals field_simp [hk0r]
  have hI : IntervalIntegrable (fun x : ℝ => Real.sin (k * x))
      MeasureTheory.volume (0 : ℝ) Real.pi :=
    (Real.continuous_sin.comp
      ((continuous_const : Continuous fun _ : ℝ => (k : ℝ)).mul continuous_id)).intervalIntegrable (0 : ℝ) Real.pi
  have hFT : ∫ x in (0 : ℝ)..Real.pi, Real.sin (k * x) =
      -Real.cos (k * Real.pi) / (k : ℝ) - -Real.cos (k * 0) / (k : ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hA hI
  rw [hFT]
  have hcospi : Real.cos (k * Real.pi) = -1 := by
    rcases hk with ⟨m, rfl⟩
    rw [show ((2 * m + 1 : ℤ) : ℝ) * Real.pi = (m : ℤ) * (2 * Real.pi) + Real.pi by
      simp [Int.cast_add, Int.cast_mul]
      ring]
    exact Real.cos_int_mul_two_pi_add_pi m
  have hcos0 : Real.cos (k * 0) = 1 := by simp
  rw [hcospi, hcos0]
  field_simp [hk0r]
  ring

private lemma kernel_id (T : ℕ) (t s : Fin T) :
    (1 : ℝ) / (2 * (t : ℝ) - (s : ℝ) * 2 - 1) =
      (1 / 2) * ∫ x in (0)..(Real.pi), Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * x) := by
  have hkodd : Odd (2 * (t : ℤ) - 2 * (s : ℤ) - 1) := by
    rw [Int.odd_iff]
    omega
  let k : ℤ := 2 * (t : ℤ) - 2 * (s : ℤ) - 1
  have hkodd : Odd k := by
    dsimp only [k]
    rw [Int.odd_iff]
    omega
  have hd : (2 * (t : ℝ) - (s : ℝ) * 2 - 1 : ℝ) = (k : ℝ) := by
    dsimp only [k]
    norm_cast
    rw [show (s : ℕ) * 2 = 2 * (s : ℕ) by ring]
  have hI : (∫ x in (0)..(Real.pi), Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * x) : ℝ) =
      ∫ x in (0)..(Real.pi), Real.sin ((k : ℝ) * x) := by
    apply congrArg (fun f : ℝ → ℝ => ∫ x in (0)..(Real.pi), f x)
    funext x
    rw [show (2 * (t : ℝ) - 2 * (s : ℝ) - 1 : ℝ) = (k : ℝ) by
      dsimp only [k]
      norm_cast]
  rw [hI, int_sin_odd k hkodd]
  field_simp
  rw [show (2 * ((t : ℝ) - (s : ℝ)) - 1 : ℝ) = 2 * (t : ℝ) - (s : ℝ) * 2 - 1 by ring, hd]

private def W (T : ℕ) (c : Fin T → ℝ) (z : Fin T → ℝ) (θ : ℝ) : ℂ :=
  ∑ t, (z t : ℂ) * Complex.exp (c t * θ * Complex.I)

private lemma lq2sq (T : ℕ) (z : Fin T → ℝ) :
    ‖WithLp.toLp (2 : ℝ≥0∞) z‖ ^ 2 = ∑ t : Fin T, z t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq (WithLp.toLp (2 : ℝ≥0∞) z)]
  apply Finset.sum_congr rfl
  intro t _
  rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

-- Sup norm ≤ L² norm: for each coordinate |z t| ≤ √(∑ s z s²), and
-- ‖z‖ is the sup norm (pi_norm_le_iff_of_nonneg).
private lemma sup_le_l2 (T : ℕ) (z : Fin T → ℝ) :
    ‖z‖ ≤ ‖WithLp.toLp (2 : ℝ≥0∞) z‖ := by
  have hC : 0 ≤ ‖WithLp.toLp (2 : ℝ≥0∞) z‖ := norm_nonneg _
  rw [pi_norm_le_iff_of_nonneg hC]
  intro b
  calc
    ‖z b‖ = |z b| := Real.norm_eq_abs (z b)
    _ ≤ Real.sqrt (∑ s : Fin T, (z s) ^ 2) :=
      Real.abs_le_sqrt (Finset.single_le_sum (fun u _ => sq_nonneg (z u)) (Finset.mem_univ b))
    _ = Real.sqrt (‖WithLp.toLp (2 : ℝ≥0∞) z‖ ^ 2) := by rw [lq2sq T z]
    _ = ‖WithLp.toLp (2 : ℝ≥0∞) z‖ := Real.sqrt_sq hC

private lemma isometry_W (T : ℕ) (c : Fin T → ℝ) (z : Fin T → ℝ)
    (hc : ∀ t s : Fin T, c t - c s = (2 * ((t : ℤ) - (s : ℤ)) : ℝ)) :
    (∫ x in (0)..(Real.pi), (‖W T c z x‖ ^ 2 : ℝ)) =
      Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) z‖ ^ 2 := by
  have hpt : ∀ x : ℝ, Complex.ofReal (‖W T c z x‖ ^ 2) = (W T c z x) * conj (W T c z x) := by
    intro x
    rw [RCLike.mul_conj]
    norm_cast
  have hpt2 : ∀ x : ℝ, (W T c z x) * conj (W T c z x) =
      ∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) := by
    intro x
    have h1 : (W T c z x) * conj (W T c z x) =
        (∑ t : Fin T, (z t : ℂ) * Complex.exp (c t * x * Complex.I)) *
          conj (∑ t : Fin T, (z t : ℂ) * Complex.exp (c t * x * Complex.I)) := rfl
    rw [h1]
    have hconj : conj (∑ t : Fin T, (z t : ℂ) * Complex.exp (c t * x * Complex.I)) =
        ∑ t : Fin T, conj ((z t : ℂ) * Complex.exp (c t * x * Complex.I)) := by
      simp [star_sum]
    rw [hconj, Finset.sum_mul]
    rw [show (∑ t : Fin T, (z t : ℂ) * Complex.exp (c t * x * Complex.I) *
        (∑ s : Fin T, conj ((z s : ℂ) * Complex.exp (c s * x * Complex.I)))) =
        ∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * Complex.exp (c t * x * Complex.I) *
          conj ((z s : ℂ) * Complex.exp (c s * x * Complex.I)) by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
    ]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring_nf
    simp [star_mul, ← Complex.exp_conj]
    ring_nf
    calc
      _ = (z t : ℂ) * (z s : ℂ) * (Complex.exp (c t * x * Complex.I) *
          Complex.exp (-(x * Complex.I * c s))) := by ring
      _ = (z t : ℂ) * (z s : ℂ) * Complex.exp (c t * x * Complex.I + -(x * Complex.I * c s)) := by
        rw [← Complex.exp_add]
      _ = (z t : ℂ) * (z s : ℂ) * Complex.exp (c t * x * Complex.I - x * Complex.I * c s) := by rfl
  have hswap : (∫ x in (0)..(Real.pi), (∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I)) : ℂ) =
      ∑ t : Fin T, ∑ s : Fin T, ∫ x in (0)..(Real.pi), (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) := by
    have hcont : ∀ (t s : Fin T), Continuous fun x : ℝ => (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) := by
      intro t s
      continuity
    have hin : ∀ (t : Fin T),
        (∫ x in (0)..(Real.pi), (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I)) : ℂ) =
          ∑ s : Fin T, ∫ x in (0)..(Real.pi), (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) := by
      intro t
      have : ∀ (S : Finset (Fin T)),
          (∫ x in (0)..(Real.pi), (∑ u ∈ S, (z t : ℂ) * (z u : ℂ) * Complex.exp ((c t - c u) * x * Complex.I)) : ℂ) =
            ∑ u ∈ S, ∫ x in (0)..(Real.pi), (z t : ℂ) * (z u : ℂ) * Complex.exp ((c t - c u) * x * Complex.I) := by
        intro S
        induction S using Finset.induction with
        | empty => simp
        | insert u S hu IH =>
          have hc1 : Continuous fun x : ℝ => ∑ u ∈ S, (z t : ℂ) * (z u : ℂ) * Complex.exp ((c t - c u) * x * Complex.I) := by
            continuity
          rw [Finset.sum_insert hu]
          have hl : (∫ x in (0)..(Real.pi), (∑ u ∈ insert u S, (z t : ℂ) * (z u : ℂ) * Complex.exp ((c t - c u) * x * Complex.I)) : ℂ) =
              ∫ x in (0)..(Real.pi), ((z t : ℂ) * (z u : ℂ) * Complex.exp ((c t - c u) * x * Complex.I) +
                (∑ v ∈ S, (z t : ℂ) * (z v : ℂ) * Complex.exp ((c t - c v) * x * Complex.I))) := by
            apply congrArg (fun f : ℝ → ℂ => ∫ x in (0)..(Real.pi), f x)
            funext x
            rw [Finset.sum_insert hu]
          rw [hl]
          rw [intervalIntegral.integral_add
              (hcont t u |>.intervalIntegrable (0 : ℝ) Real.pi)
              (hc1.intervalIntegrable (0 : ℝ) Real.pi), IH]
      simpa using this Finset.univ
    have : ∀ (S : Finset (Fin T)),
        (∫ x in (0)..(Real.pi), (∑ t ∈ S, (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I))) : ℂ) =
          ∑ t ∈ S, ∫ x in (0)..(Real.pi), (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I)) := by
      intro S
      induction S using Finset.induction with
      | empty => simp
      | insert u S hu IH =>
        have hc1 : Continuous fun x : ℝ => ∑ t ∈ S, (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I)) := by
          continuity
        rw [Finset.sum_insert hu]
        have hl : (∫ x in (0)..(Real.pi), (∑ t ∈ insert u S, (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I))) : ℂ) =
            ∫ x in (0)..(Real.pi), ((∑ s : Fin T, (z u : ℂ) * (z s : ℂ) * Complex.exp ((c u - c s) * x * Complex.I)) +
              (∑ v ∈ S, (∑ s : Fin T, (z v : ℂ) * (z s : ℂ) * Complex.exp ((c v - c s) * x * Complex.I)))) := by
          apply congrArg (fun f : ℝ → ℂ => ∫ x in (0)..(Real.pi), f x)
          funext x
          rw [Finset.sum_insert hu]
        have hcu : Continuous fun x : ℝ => ∑ s : Fin T, (z u : ℂ) * (z s : ℂ) * Complex.exp ((c u - c s) * x * Complex.I) := by
          continuity
        rw [hl]
        rw [intervalIntegral.integral_add
            (hcu.intervalIntegrable (0 : ℝ) Real.pi)
            (hc1.intervalIntegrable (0 : ℝ) Real.pi), IH]
    have hout := this Finset.univ
    rw [hout]
    apply Finset.sum_congr rfl
    intro t _
    rw [hin t]
  have hterm : ∀ t s : Fin T,
      ∫ x in (0)..(Real.pi), (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) =
        (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0) := by
    intro t s
    rw [intervalIntegral.integral_const_mul]
    have hexp : (∫ x in (0)..(Real.pi), Complex.exp ((c t - c s) * x * Complex.I) : ℂ) =
        ∫ x in (0)..(Real.pi), Complex.exp (↑(2 * ((t : ℤ) - (s : ℤ))) * x * Complex.I) := by
      apply congrArg (fun f : ℝ → ℂ => ∫ x in (0)..(Real.pi), f x)
      funext x
      rw [show ((c t - c s) : ℂ) * x * Complex.I = (↑(2 * ((t : ℤ) - (s : ℤ))) : ℂ) * x * Complex.I by
        calc
          ((c t - c s) : ℂ) * x * Complex.I = ((c t - c s) : ℝ) * x * Complex.I := by norm_cast
          _ = ((2 * ((t : ℤ) - (s : ℤ)) : ℝ)) * x * Complex.I := by rw [hc t s]
          _ = (↑(2 * ((t : ℤ) - (s : ℤ))) : ℂ) * x * Complex.I := by norm_cast]
    rw [hexp]
    rw [int_exp_even (2 * ((t : ℤ) - (s : ℤ))) ⟨(t : ℤ) - (s : ℤ), by ring⟩]
    have hiff : (2 * ((t : ℤ) - (s : ℤ)) : ℤ) = 0 ↔ t = s := by
      constructor
      · intro h
        have h2 : (t : ℤ) - (s : ℤ) = 0 := by
          have : (2 : ℤ) = 0 ∨ (t : ℤ) - (s : ℤ) = 0 := Int.mul_eq_zero.mp h
          omega
        have h3 : (t : ℤ) = (s : ℤ) := Int.sub_eq_zero.mp h2
        exact Fin.ext_iff.mpr (by simpa using Int.cast_inj.mp h3)
      · intro h
        subst h
        norm_num
    simp only [hiff]
  have hdiag : (∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0)) =
      ∑ t : Fin T, (z t : ℂ) * (z t : ℂ) * (Real.pi : ℂ) := by
    apply Finset.sum_congr rfl
    intro t _
    have hd : (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0)) =
        (z t : ℂ) * (z t : ℂ) * (Real.pi : ℂ) := by
      rw [show (∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0)) =
          ∑ s : Fin T, (if t = s then (z t : ℂ) * (z s : ℂ) * (Real.pi : ℂ) else (z t : ℂ) * (z s : ℂ) * 0) by
        apply Finset.sum_congr rfl
        intro s _
        rw [mul_ite]
      , Finset.sum_ite]
      have h3 : (Finset.univ : Finset (Fin T)).filter (fun x : Fin T => t = x) = {t} := by
        ext x
        simp [eq_comm]
      rw [show ∑ x with t = x, (z t : ℂ) * (z x : ℂ) * (Real.pi : ℂ) =
          (∑ x ∈ Finset.univ.filter (fun x : Fin T => t = x), (z t : ℂ) * (z x : ℂ) * (Real.pi : ℂ)) from rfl,
        h3, Finset.sum_singleton]
      have hz2 : (∑ x with ¬t = x, (z t : ℂ) * (z x : ℂ) * 0 : ℂ) = 0 := by simp
      rw [hz2, add_zero]
    rw [hd]
  have hB : (∫ x in (0)..(Real.pi), Complex.ofReal (‖W T c z x‖ ^ 2)) =
      Complex.ofReal (Real.pi * ∑ t : Fin T, z t ^ 2) := by
    calc
      _ = ∫ x in (0)..(Real.pi), (W T c z x) * conj (W T c z x) := by
        congr
        funext x
        rw [hpt x]
      _ = ∫ x in (0)..(Real.pi), (∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I)) := by
        congr
        funext x
        rw [hpt2 x]
      _ = ∑ t : Fin T, ∑ s : Fin T, ∫ x in (0)..(Real.pi), (z t : ℂ) * (z s : ℂ) * Complex.exp ((c t - c s) * x * Complex.I) := by
        rw [hswap]
      _ = ∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        rw [hterm t s]
      _ = Complex.ofReal (Real.pi * ∑ t : Fin T, z t ^ 2) := by
        rw [show ∑ t : Fin T, ∑ s : Fin T, (z t : ℂ) * (z s : ℂ) * (if t = s then (Real.pi : ℂ) else 0) =
            ∑ t : Fin T, (z t : ℂ) * (z t : ℂ) * (Real.pi : ℂ) from hdiag]
        rw [← Finset.sum_mul]
        have : (∑ i : Fin T, (z i : ℂ) * (z i : ℂ)) = (∑ i : Fin T, (z i : ℝ) * (z i : ℝ)) := by
          norm_cast
        rw [this]
        rw [show (∑ i : Fin T, (z i : ℝ) * (z i : ℝ)) = (∑ i : Fin T, z i ^ 2) by
          apply Finset.sum_congr rfl
          intro i _
          ring]
        rw [mul_comm, Complex.ofReal_mul]
  have hreal2 : (∫ x in (0)..(Real.pi), ‖W T c z x‖ ^ 2) = Real.pi * ∑ t : Fin T, z t ^ 2 := by
    have hC2 : Complex.ofReal (∫ x in (0)..(Real.pi), ‖W T c z x‖ ^ 2) =
        Complex.ofReal (Real.pi * ∑ t : Fin T, z t ^ 2) := by
      rw [← intervalIntegral.integral_ofReal]
      exact hB
    exact (Complex.ofReal_inj.mp hC2)
  rw [hreal2, lq2sq]
private lemma isometry_U (T : ℕ) (y : Fin T → ℝ) :
    (∫ x in (0)..(Real.pi), ‖Uy T y x‖ ^ 2 : ℝ) =
      Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2 := by
  have hc : ∀ t s : Fin T, (fun t : Fin T => 2 * (t : ℝ)) t - (fun t : Fin T => 2 * (t : ℝ)) s =
      (2 * ((t : ℤ) - (s : ℤ)) : ℝ) := by
    intro t s
    simp
    ring
  have hw := isometry_W T (fun t : Fin T => 2 * (t : ℝ)) y hc
  have heq : ∀ x : ℝ, Uy T y x = W T (fun t : Fin T => 2 * (t : ℝ)) y x := by
    intro x
    rw [Uy, W]
    apply Finset.sum_congr rfl
    intro t _
    congr
    congr
    norm_cast
  have hW : (∫ x in (0)..(Real.pi), ‖Uy T y x‖ ^ 2) =
      (∫ x in (0)..(Real.pi), ‖W T (fun t : Fin T => 2 * (t : ℝ)) y x‖ ^ 2) := by
    congr
    funext x
    rw [heq x]
  rw [hW]
  exact hw

private lemma isometry_V (T : ℕ) (z : Fin T → ℝ) :
    (∫ x in (0)..(Real.pi), ‖Vx T z x‖ ^ 2 : ℝ) =
      Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) z‖ ^ 2 := by
  have hc : ∀ t s : Fin T, (fun t : Fin T => 2 * (t : ℝ) + 1) t -
      (fun t : Fin T => 2 * (t : ℝ) + 1) s = (2 * ((t : ℤ) - (s : ℤ)) : ℝ) := by
    intro t s
    simp
    ring
  have hw := isometry_W T (fun t : Fin T => 2 * (t : ℝ) + 1) z hc
  have heq : ∀ x : ℝ, Vx T z x = W T (fun t : Fin T => 2 * (t : ℝ) + 1) z x := by
    intro x
    rw [Vx, W]
    apply Finset.sum_congr rfl
    intro t _
    congr
    congr
    norm_cast
  have hW : (∫ x in (0)..(Real.pi), ‖Vx T z x‖ ^ 2) =
      (∫ x in (0)..(Real.pi), ‖W T (fun t : Fin T => 2 * (t : ℝ) + 1) z x‖ ^ 2) := by
    congr
    funext x
    rw [heq x]
  rw [hW]
  exact hw

private lemma hsin (θ : ℝ) : (exp (θ * I)).im = Real.sin θ := by
  rw [Complex.exp_im]
  simp [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_im, Complex.ofReal_re, Real.exp_zero]

private lemma hsinre (θ : ℝ) : (sin (θ : ℂ)).re = Real.sin θ := by
  rw [← Complex.ofReal_sin, Complex.ofReal_re]

private lemma hexpdiff (θ : ℝ) : exp (θ * I) - exp (-(θ * I)) = 2 * I * Real.sin θ := by
  apply Complex.ext
  <;> (simp [hsin, Complex.exp_re, Complex.exp_im, hsinre,
    Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_re, Complex.ofReal_im, Real.exp_zero]; try ring)

section im_identity_sec

variable (T : ℕ) (x y : Fin T → ℝ)

private def P (T : ℕ) (x y : Fin T → ℝ) (u : ℝ) : ℂ := Uy T y u * conj (Vx T x u)


private lemma hfactor (u : ℝ) :
    ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) = P T x y u := by
  have h1 : ∀ t s : Fin T, exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
      exp (2 * (t : ℝ) * u * I) * exp (-(2 * (s : ℝ) + 1) * u * I) := by
    intro t s
    rw [← Complex.exp_add]
    congr
    ring_nf
  have h2 : ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
      ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      (exp (2 * (t : ℝ) * u * I) * exp (-(2 * (s : ℝ) + 1) * u * I)) := by
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    rw [h1 t s]
  rw [h2]
  have h3 : ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      (exp (2 * (t : ℝ) * u * I) * exp (-(2 * (s : ℝ) + 1) * u * I)) =
      (∑ t : Fin T, (y t : ℂ) * exp (2 * (t : ℝ) * u * I)) *
      (∑ s : Fin T, (x s : ℂ) * exp (-(2 * (s : ℝ) + 1) * u * I)) := by
    rw [show (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
        (exp (2 * (t : ℝ) * u * I) * exp (-(2 * (s : ℝ) + 1) * u * I))) =
        ∑ t : Fin T, ∑ s : Fin T, ((y t : ℂ) * exp (2 * (t : ℝ) * u * I)) *
        ((x s : ℂ) * exp (-(2 * (s : ℝ) + 1) * u * I)) by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring]
    simp [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h3]
  have h4 : (∑ s : Fin T, (x s : ℂ) * exp (-(2 * (s : ℝ) + 1) * u * I)) =
      conj (Vx T x u) := by
    calc
      _ = conj (∑ s : Fin T, (x s : ℂ) * exp ((2 * (s : ℝ) + 1) * u * I)) := by
        have harg : ∀ s : Fin T, (-(2 * (s : ℝ) + 1) * u) * I =
            conj ((2 * (s : ℝ) + 1) * u * I) := by
          intro s
          apply Complex.ext
          <;> (simp; try ring)
        calc
          _ = ∑ s : Fin T, (x s : ℂ) * conj (exp ((2 * (s : ℝ) + 1) * u * I)) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [harg s, Complex.exp_conj]
          _ = conj (∑ s : Fin T, (x s : ℂ) * exp ((2 * (s : ℝ) + 1) * u * I)) := by
            simp [star_sum, star_mul]
      _ = conj (Vx T x u) := by rw [Vx]
  rw [h4]
  have h5 : (∑ t : Fin T, (y t : ℂ) * exp (2 * (t : ℝ) * u * I)) = Uy T y u := rfl
  rw [h5]
  rfl

private lemma hconjP (u : ℝ) :
    ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) = conj (P T x y u) := by
  have h : ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
      conj (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)) := by
    have hpt : ∀ (t s : Fin T), exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
        conj (exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)) := by
      intro t s
      have harg : (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) * I =
          conj ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) := by
        apply Complex.ext
        <;> (simp; try ring)
      rw [harg, Complex.exp_conj]
    calc
      _ = ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
          conj (exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)) := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        rw [hpt t s]
      _ = conj (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
          exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)) := by
        simp [star_sum, star_mul]
  rw [h, hfactor]

private lemma im_identity (u : ℝ) :
    ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
      Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) =
      (Uy T y u * conj (Vx T x u)).im := by
  let F (t s : Fin T) : ℂ :=
    ((y t) * (x s) : ℂ) * Complex.exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)
  let G (t s : Fin T) : ℂ :=
    ((y t) * (x s) : ℂ) * Complex.exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)
  have hP : P T x y u - conj (P T x y u) = ∑ t : Fin T, ∑ s : Fin T, (F t s - G t s) := by
    rw [← hconjP, ← hfactor]
    have h : ∀ (S : Finset (Fin T)),
        (∑ t ∈ S, ∑ s : Fin T, F t s) - (∑ t ∈ S, ∑ s : Fin T, G t s) =
          ∑ t ∈ S, ∑ s : Fin T, (F t s - G t s) := by
      intro S
      induction S using Finset.induction with
      | empty => simp
      | insert v S hv IH =>
        rw [Finset.sum_insert hv, Finset.sum_insert hv, Finset.sum_insert hv]
        have hsub : (∑ s : Fin T, F v s) - (∑ s : Fin T, G v s) =
            ∑ s : Fin T, (F v s - G v s) := by
          rw [Finset.sum_sub_distrib]
        calc
          _ = (∑ s : Fin T, F v s) - (∑ s : Fin T, G v s) +
              ((∑ t ∈ S, ∑ s : Fin T, F t s) - (∑ t ∈ S, ∑ s : Fin T, G t s)) := by ring
          _ = (∑ s : Fin T, (F v s - G v s)) +
              (∑ t ∈ S, ∑ s : Fin T, (F t s - G t s)) := by rw [hsub, IH]
    exact h Finset.univ
  have hQ : ∑ t : Fin T, ∑ s : Fin T, (F t s - G t s) =
      ∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
        (2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) := by
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [F, G]
    have hfac : ((y t) * (x s) : ℂ) *
        Complex.exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) -
        ((y t) * (x s) : ℂ) *
          Complex.exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
        ((y t) * (x s) : ℂ) * (Complex.exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) -
          Complex.exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I)) := by
      ring
    have hdiff : Complex.exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) -
        Complex.exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
        2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
      have he1 : Complex.exp ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
          Complex.exp (↑((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) * I) := by
        congr
        norm_cast
      have he2 : Complex.exp (-(2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u * I) =
          Complex.exp (-((↑((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) * I)) := by
        congr
        norm_cast
        simp
        ring
      rw [he1, he2]
      rw [hexpdiff ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)]
    rw [hfac, hdiff]
  have hS : (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
      (2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u))).im =
      ∑ t : Fin T, ∑ s : Fin T, 2 * (y t) * (x s) *
        Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
    have hpt : ∀ t s : Fin T, ((y t) * (x s) : ℂ) *
        (2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) =
        (↑(2 * (y t) * (x s) * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) : ℂ) * I := by
      intro t s
      apply Complex.ext
      <;> (simp; try ring)
    rw [show (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
        (2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u))) =
        ∑ t : Fin T, ∑ s : Fin T,
          (↑(2 * (y t) * (x s) * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) : ℂ) * I by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      exact hpt t s
    ]
    simp_rw [im_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re]
    ring
  have hL : (P T x y u - conj (P T x y u)).im = 2 * (P T x y u).im := by
    simp [Complex.conj_im]
    ring
  have H : (Uy T y u * conj (Vx T x u)).im =
      ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
        Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
    calc
      (Uy T y u * conj (Vx T x u)).im = ((P T x y u - conj (P T x y u)).im) / 2 := by
        rw [hL, show P T x y u = Uy T y u * conj (Vx T x u) from rfl]
        field_simp
      _ = (∑ t : Fin T, ∑ s : Fin T, (F t s - G t s)).im / 2 := by rw [hP]
      _ = (∑ t : Fin T, ∑ s : Fin T, ((y t) * (x s) : ℂ) *
          (2 * I * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u))).im / 2 := by
        rw [hQ]
      _ = (∑ t : Fin T, ∑ s : Fin T, 2 * (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) / 2 := by
        rw [hS]
      _ = ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
        have hdiv : (∑ t : Fin T, ∑ s : Fin T, 2 * (y t) * (x s) *
            Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) / 2 =
            ∑ t : Fin T, ∑ s : Fin T,
              2 * (y t) * (x s) * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) * (2 : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.sum_mul]
        rw [hdiv]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        ring
  exact H.symm

end im_identity_sec

private lemma two_var (T : ℕ) (x y : Fin T → ℝ) :
    |∑ t : Fin T, (y t) * ((hilbertK T).mulVec x) t| ≤
      Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ := by
  -- STEP 1: bilinear form as double sum over the kernel
  have h1 : ∑ t : Fin T, (y t) * ((hilbertK T).mulVec x) t =
      ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) := by
    simp only [Matrix.mulVec_apply_eq_sum, hilbertK, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro s _
    ring
  -- STEP 2: kernel_id per (t,s) + Fubini (integral_finsetSum) -> (1/2)·∫ sin-sum
  have h2 : (∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) : ℝ) =
      (1 / 2) * ∫ u in (0)..(Real.pi),
        ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
    have hkts : ∀ t s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) =
        ∫ u in (0)..(Real.pi), (1 / 2) * (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
      intro t s
      have hk := kernel_id T t s
      have hd : 2 * ((t : ℝ) - (s : ℝ)) - 1 = 2 * (t : ℝ) - (s : ℝ) * 2 - 1 := by ring
      have hk2 : (2 * (t : ℝ) - (s : ℝ) * 2 - 1)⁻¹ =
          (1 / 2) * ∫ u in (0)..(Real.pi), Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
        calc
          _ = (1 : ℝ) / (2 * (t : ℝ) - (s : ℝ) * 2 - 1) := by
            rw [div_eq_mul_inv]
            ring
          _ = (1 / 2) * ∫ u in (0)..(Real.pi), Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := hk
      rw [show (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) =
          (y t) * (x s) * (1 : ℝ) / (2 * (t : ℝ) - (s : ℝ) * 2 - 1) by
        rw [hd, div_eq_mul_inv, div_eq_mul_inv]
        ring]
      rw [div_eq_mul_inv, hk2]
      rw [mul_one, ← mul_assoc]
      rw [← intervalIntegral.integral_const_mul ((y t) * (x s) * (1 / 2))
        (fun u : ℝ => Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u))]
      congr
      funext u
      ring
    have hg : ∀ t s : Fin T,
        IntervalIntegrable (fun u : ℝ => (1 / 2) * (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) MeasureTheory.volume 0 Real.pi := by
      intro t s
      apply Continuous.intervalIntegrable
      continuity
    have hsum : ∀ t : Fin T,
        IntervalIntegrable (fun u : ℝ => ∑ s : Fin T, (1 / 2) * (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) MeasureTheory.volume 0 Real.pi := by
      intro t
      apply Continuous.intervalIntegrable
      continuity
    have hlhs : (∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) : ℝ) =
        ∫ u in (0)..(Real.pi), ∑ t : Fin T, ∑ s : Fin T,
          (1 / 2) * (y t) * (x s) * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) := by
      have hper : ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1) =
          ∑ t : Fin T, ∑ s : Fin T,
            (∫ u in (0)..(Real.pi), (1 / 2) * (y t) * (x s) *
              Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro s _
        exact hkts t s
      rw [hper]
      have h1 : ∑ t : Fin T, ∑ s : Fin T,
          (∫ u in (0)..(Real.pi), (1 / 2) * (y t) * (x s) *
            Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) =
          ∑ t : Fin T, (∫ u in (0)..(Real.pi), ∑ s : Fin T,
            (1 / 2) * (y t) * (x s) * Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← intervalIntegral.integral_finsetSum (fun s _ => hg t s)]
      rw [h1]
      rw [← intervalIntegral.integral_finsetSum (fun t _ => hsum t)]
    rw [hlhs]
    have hswap2 : ∫ u in (0)..(Real.pi), ∑ t : Fin T, ∑ s : Fin T, (1 / 2) * (y t) * (x s) *
        Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) =
        ∫ u in (0)..(Real.pi), (1 / 2) *
          (∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
            Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) := by
      congr
      funext u
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [show (1 / 2) * (∑ s : Fin T, (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) =
        (∑ s : Fin T, (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)) * (1 / 2) by ring]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hswap2]
    rw [intervalIntegral.integral_const_mul (1 / 2)
      (fun u : ℝ => ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
        Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u))]
  -- STEP 3: sin-sum = (Uy·conj Vx).im, pointwise in u (im_identity)
  have h3 : ∫ u in (0)..(Real.pi),
      ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
        Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u) =
      ∫ u in (0)..(Real.pi), (Uy T y u * conj (Vx T x u)).im := by
    congr
    funext u
    exact im_identity T x y u
  -- STEP 4: |(1/2)∫ Z.im| ≤ (1/2)∫ |Uy|·|Vx|
  have h4 : |(1 / 2 : ℝ) * ∫ u in (0)..(Real.pi), (Uy T y u * conj (Vx T x u)).im| ≤
      (1 / 2) * ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ := by
    rw [abs_mul, show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
    have hZabs : IntervalIntegrable (fun u : ℝ => |(Uy T y u * conj (Vx T x u)).im|)
        MeasureTheory.volume 0 Real.pi := by
      apply Continuous.intervalIntegrable
      dsimp only [Uy, Vx]
      continuity
    have hN : IntervalIntegrable (fun u : ℝ => ‖Uy T y u‖ * ‖Vx T x u‖)
        MeasureTheory.volume 0 Real.pi := by
      apply Continuous.intervalIntegrable
      dsimp only [Uy, Vx]
      continuity
    have hin : ∀ u ∈ Set.Icc (0 : ℝ) Real.pi,
        |(Uy T y u * conj (Vx T x u)).im| ≤ ‖Uy T y u‖ * ‖Vx T x u‖ := by
      intro u _
      calc
        |(Uy T y u * conj (Vx T x u)).im| ≤ ‖Uy T y u * conj (Vx T x u)‖ :=
          Complex.abs_im_le_norm (Uy T y u * conj (Vx T x u))
        _ = ‖Uy T y u‖ * ‖Vx T x u‖ := by
          rw [Complex.norm_mul, Complex.norm_conj]
    calc
      (1 / 2) * |∫ u in (0)..(Real.pi), (Uy T y u * conj (Vx T x u)).im| ≤
          (1 / 2) * ∫ u in (0)..(Real.pi), |(Uy T y u * conj (Vx T x u)).im| := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le)
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ ≤ (1 / 2) * ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_on Real.pi_pos.le hZabs hN hin)
          (by norm_num : 0 ≤ (1 / 2 : ℝ))
  -- STEP 5: L2 Cauchy-Schwarz: integral_mul_norm_le_Lp_mul_Lq with p = q = 2
  have h5 : ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ ≤
      (∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2) ^ (1 / (2 : ℝ)) *
        (∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2) ^ (1 / (2 : ℝ)) := by
    have hbUy : ∀ u : ℝ, ‖Uy T y u‖ ≤ ∑ t : Fin T, |y t| := by
      intro u
      calc
        ‖Uy T y u‖ ≤ ∑ t : Fin T, ‖(y t : ℂ) * Complex.exp (2 * (t : ℝ) * u * Complex.I)‖ :=
          norm_sum_le Finset.univ (fun t : Fin T => (y t : ℂ) * Complex.exp (2 * (t : ℝ) * u * Complex.I))
        _ = ∑ t : Fin T, |y t| := by
          apply Finset.sum_congr rfl
          intro t _
          have hw : (2 * (t : ℝ) * u * Complex.I).re = 0 := by
            simp
          calc
            ‖(y t : ℂ) * Complex.exp (2 * (t : ℝ) * u * Complex.I)‖ =
                ‖(y t : ℂ)‖ * ‖Complex.exp (2 * (t : ℝ) * u * Complex.I)‖ := Complex.norm_mul _ _
            _ = ‖(y t : ℂ)‖ * Real.exp ((2 * (t : ℝ) * u * Complex.I).re) := by
              rw [Complex.norm_exp]
            _ = ‖(y t : ℂ)‖ * Real.exp 0 := by rw [hw]
            _ = ‖(y t : ℂ)‖ := by norm_num
            _ = |y t| := by simp
    have hbVx : ∀ u : ℝ, ‖Vx T x u‖ ≤ ∑ s : Fin T, |x s| := by
      intro u
      calc
        ‖Vx T x u‖ ≤ ∑ s : Fin T, ‖(x s : ℂ) * Complex.exp ((2 * (s : ℝ) + 1) * u * Complex.I)‖ :=
          norm_sum_le Finset.univ (fun s : Fin T => (x s : ℂ) * Complex.exp ((2 * (s : ℝ) + 1) * u * Complex.I))
        _ = ∑ s : Fin T, |x s| := by
          apply Finset.sum_congr rfl
          intro s _
          have hw : (((2 * (s : ℝ) + 1) * u) * Complex.I).re = 0 := by
            simp
          calc
            ‖(x s : ℂ) * Complex.exp ((2 * (s : ℝ) + 1) * u * Complex.I)‖ =
                ‖(x s : ℂ)‖ * ‖Complex.exp ((2 * (s : ℝ) + 1) * u * Complex.I)‖ := Complex.norm_mul _ _
            _ = ‖(x s : ℂ)‖ * Real.exp ((((2 * (s : ℝ) + 1) * u) * Complex.I).re) := by
              rw [Complex.norm_exp]
            _ = ‖(x s : ℂ)‖ * Real.exp 0 := by rw [hw]
            _ = ‖(x s : ℂ)‖ := by norm_num
            _ = |x s| := by simp
    have hU : MeasureTheory.MemLp (fun u : ℝ => Uy T y u) (ENNReal.ofReal 2)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) := by
      apply MeasureTheory.MemLp.of_bound _ (∑ t : Fin T, |y t|) (Filter.Eventually.of_forall hbUy)
      apply Continuous.aestronglyMeasurable
      change Continuous (fun u : ℝ => Uy T y u)
      dsimp only [Uy]
      continuity
    have hV : MeasureTheory.MemLp (fun u : ℝ => Vx T x u) (ENNReal.ofReal 2)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) := by
      apply MeasureTheory.MemLp.of_bound _ (∑ s : Fin T, |x s|) (Filter.Eventually.of_forall hbVx)
      apply Continuous.aestronglyMeasurable
      change Continuous (fun u : ℝ => Vx T x u)
      dsimp only [Vx]
      continuity
    have H : (∫ u, ‖Uy T y u‖ * ‖Vx T x u‖ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) ≤
        (∫ u, ‖Uy T y u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) ^
          (1 / (2 : ℝ)) *
        (∫ u, ‖Vx T x u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) ^
          (1 / (2 : ℝ)) :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (f := fun u : ℝ => Uy T y u) (g := fun u : ℝ => Vx T x u)
        (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi))
        (p := 2) (q := 2) Real.HolderConjugate.two_two hU hV
    have hI1 : ∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ (2 : ℝ) =
        ∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro u _
      exact Real.rpow_natCast _ 2
    have hI2 : ∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ (2 : ℝ) =
        ∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro u _
      exact Real.rpow_natCast _ 2
    calc
      ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ =
          ∫ u, ‖Uy T y u‖ * ‖Vx T x u‖ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi) := by
        rw [intervalIntegral.integral_of_le Real.pi_pos.le]
      _ ≤
          (∫ u, ‖Uy T y u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) ^
            (1 / (2 : ℝ)) *
          (∫ u, ‖Vx T x u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi)) ^
            (1 / (2 : ℝ)) := H
      _ = (∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [← show ∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ (2 : ℝ) =
            ∫ u, ‖Uy T y u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi) by
          rw [intervalIntegral.integral_of_le Real.pi_pos.le],
          ← show ∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ (2 : ℝ) =
            ∫ u, ‖Vx T x u‖ ^ (2 : ℝ) ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Real.pi) by
          rw [intervalIntegral.integral_of_le Real.pi_pos.le]]
      _ = (∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2) ^ (1 / (2 : ℝ)) *
            (∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2) ^ (1 / (2 : ℝ)) := by
        rw [hI1, hI2]
  calc
    |∑ t : Fin T, (y t) * ((hilbertK T).mulVec x) t| =
      |∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) / (2 * ((t : ℝ) - (s : ℝ)) - 1)| := by rw [h1]
    _ = |(1 / 2) * ∫ u in (0)..(Real.pi),
        ∑ t : Fin T, ∑ s : Fin T, (y t) * (x s) *
          Real.sin ((2 * (t : ℝ) - 2 * (s : ℝ) - 1) * u)| := by rw [h2]
    _ = |(1 / 2) * ∫ u in (0)..(Real.pi), (Uy T y u * conj (Vx T x u)).im| := by rw [h3]
    _ ≤ (1 / 2) * ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ := h4
    _ ≤ (1 / 2) * ((∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2) ^ (1 / (2 : ℝ))) *
              ((∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2) ^ (1 / (2 : ℝ))) := by
      calc
        (1 / 2) * ∫ u in (0)..(Real.pi), ‖Uy T y u‖ * ‖Vx T x u‖ ≤
            (1 / 2) * ((∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2) ^ (1 / (2 : ℝ)) *
                (∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2) ^ (1 / (2 : ℝ))) := by
          nlinarith [h5]
        _ = (1 / 2) * ((∫ u in (0)..(Real.pi), ‖Uy T y u‖ ^ 2) ^ (1 / (2 : ℝ))) *
                ((∫ u in (0)..(Real.pi), ‖Vx T x u‖ ^ 2) ^ (1 / (2 : ℝ))) := by ring
    _ = (1 / 2) * ((Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2) ^ (1 / (2 : ℝ))) *
              ((Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ ^ 2) ^ (1 / (2 : ℝ))) := by
      rw [isometry_U, isometry_V]
    -- Final algebraic simplification: for A ≥ 0, (π · A²)^(1/2) = √π · A,
    -- so (1/2)·(π·‖y‖₂²)^(1/2)·(π·‖x‖₂²)^(1/2) = (π/2)·‖x‖₂·‖y‖₂.
    _ = Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ := by
      have hX : (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ ^ 2) ^ (1 / (2 : ℝ)) =
          Real.sqrt Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ := by
        have hnn : 0 ≤ ‖WithLp.toLp (2 : ℝ≥0∞) x‖ := norm_nonneg _
        rw [show (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ ^ 2) ^ (1 / (2 : ℝ)) =
                Real.sqrt (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ ^ 2) by
          rw [Real.sqrt_eq_rpow],
          Real.sqrt_mul (Real.pi_pos.le) _, Real.sqrt_sq hnn]
      have hY : (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2) ^ (1 / (2 : ℝ)) =
          Real.sqrt Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ := by
        have hnn : 0 ≤ ‖WithLp.toLp (2 : ℝ≥0∞) y‖ := norm_nonneg _
        rw [show (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2) ^ (1 / (2 : ℝ)) =
                Real.sqrt (Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2) by
          rw [Real.sqrt_eq_rpow],
          Real.sqrt_mul (Real.pi_pos.le) _, Real.sqrt_sq hnn]
      have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
        rw [← pow_two]
        exact Real.sq_sqrt (Real.pi_pos.le)
      calc
        (1 / 2) * ((Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ ^ 2) ^ (1 / (2 : ℝ))) *
            ((Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ ^ 2) ^ (1 / (2 : ℝ))) =
          (1 / 2) * (Real.sqrt Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) y‖) *
            (Real.sqrt Real.pi * ‖WithLp.toLp (2 : ℝ≥0∞) x‖) := by
          rw [hY, hX]
        _ = (1 / 2) * (Real.sqrt Real.pi * Real.sqrt Real.pi) *
            (‖WithLp.toLp (2 : ℝ≥0∞) y‖ * ‖WithLp.toLp (2 : ℝ≥0∞) x‖) := by ring
        _ = (1 / 2) * Real.pi *
            (‖WithLp.toLp (2 : ℝ≥0∞) y‖ * ‖WithLp.toLp (2 : ℝ≥0∞) x‖) := by
          rw [hpi]
        _ = Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) y‖ := by ring

theorem solution :
    ∀ (T : ℕ), 1 ≤ T → ∀ x : Fin T → ℝ,
      lqNorm 2 (Matrix.mulVec (hilbertK T) x) ≤ Real.pi / 2 * lqNorm 2 x ∧
      lqNorm 2 (Matrix.mulVec (hilbertK T).transpose x) ≤ Real.pi / 2 * lqNorm 2 x := by
  intro T hT x
  have h1 : ‖WithLp.toLp (2 : ℝ≥0∞) ((hilbertK T).mulVec x)‖ ≤
      Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ := by
    set Kx := (hilbertK T).mulVec x with hKx
    -- two_var with y := Kx (L² norms): |∑t (Kx t) * (K *ᵥ x) t| ≤ π/2 · ‖x‖₂ · ‖Kx‖₂
    have hb := two_var T x Kx
    rw [← hKx] at hb
    -- ∑t (Kx t) * (Kx t) = ‖Kx‖₂² (quadratic form via lq2sq)
    have heq : ∑ t : Fin T, (Kx t) * (Kx t) =
        ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ ^ 2 := by
      rw [show ∑ t : Fin T, (Kx t) * (Kx t) = ∑ t : Fin T, (Kx t) ^ 2 from by
        apply Finset.sum_congr rfl
        intro t _
        ring]
      exact (lq2sq T Kx).symm
    have hae : |∑ t : Fin T, (Kx t) * (Kx t)| = ∑ t : Fin T, (Kx t) * (Kx t) :=
      abs_of_nonneg (by rw [heq]; exact sq_nonneg _)
    have hbound : ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ ^ 2 ≤
        Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ := by
      calc
        ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ ^ 2 = ∑ t : Fin T, (Kx t) * (Kx t) := heq.symm
        _ = |∑ t : Fin T, (Kx t) * (Kx t)| := hae.symm
        _ ≤ Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ := hb
    by_cases hz : ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ = 0
    · rw [hz]
      exact mul_nonneg (by positivity) (norm_nonneg (WithLp.toLp (2 : ℝ≥0∞) x))
    · have hpos : 0 < ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ :=
        lt_of_le_of_ne (norm_nonneg (WithLp.toLp (2 : ℝ≥0∞) Kx)) (Ne.symm hz)
      have hmul : ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ * ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ ≤
          Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) Kx‖ := by
        rwa [pow_two] at hbound
      exact le_of_mul_le_mul_right hmul hpos
  have h2 : ‖WithLp.toLp (2 : ℝ≥0∞) ((hilbertK T).transpose.mulVec x)‖ ≤
      Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ := by
    set KTx := (hilbertK T).transpose.mulVec x with hKTx
    -- two_var with first arg KTx (L² norms): |∑t (x t) * (K *ᵥ KTx) t| ≤ π/2 · ‖KTx‖₂ · ‖x‖₂
    have hb := two_var T KTx x
    -- xᵀ K Kᵀ x = ‖Kᵀ x‖₂² via dotProduct_mulVec + mulVec_transpose
    have heq : ∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t =
        ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ ^ 2 := by
      calc
        ∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t =
            x ⬝ᵥ (hilbertK T) *ᵥ KTx := by rw [← dotProduct]
        _ = x ᵥ* hilbertK T ⬝ᵥ KTx := by rw [Matrix.dotProduct_mulVec]
        _ = (hilbertK T).transpose *ᵥ x ⬝ᵥ KTx := by rw [← Matrix.mulVec_transpose]
        _ = KTx ⬝ᵥ KTx := by rw [← hKTx]
        _ = ∑ s : Fin T, (KTx s) * (KTx s) := by rw [dotProduct]
        _ = ∑ s : Fin T, (KTx s) ^ 2 := by
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ ^ 2 := (lq2sq T KTx).symm
    have hae : |∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t| =
        ∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t :=
      abs_of_nonneg (by rw [heq]; exact sq_nonneg _)
    have hbound : ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ ^ 2 ≤
        Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ := by
      calc
        ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ ^ 2 =
            ∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t := heq.symm
        _ = |∑ t : Fin T, (x t) * ((hilbertK T).mulVec KTx) t| := hae.symm
        _ ≤ Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ := hb
        _ = Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ := by ring
    by_cases hz : ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ = 0
    · rw [hz]
      exact mul_nonneg (by positivity) (norm_nonneg (WithLp.toLp (2 : ℝ≥0∞) x))
    · have hpos : 0 < ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ :=
        lt_of_le_of_ne (norm_nonneg (WithLp.toLp (2 : ℝ≥0∞) KTx)) (Ne.symm hz)
      have hmul : ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ * ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ ≤
          Real.pi / 2 * ‖WithLp.toLp (2 : ℝ≥0∞) x‖ * ‖WithLp.toLp (2 : ℝ≥0∞) KTx‖ := by
        rwa [pow_two] at hbound
      exact le_of_mul_le_mul_right hmul hpos
  constructor
  · rw [lq2_eq_norm, lq2_eq_norm]
    exact h1
  · rw [lq2_eq_norm, lq2_eq_norm]
    exact h2

