-- Prove2me | solution 1 for LogSobolevMC.TwoPoint.eq_A_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:20:40.512539+00:00
-- url     : https://prove2.me/submissions/b5beec7e-da42-48ac-b3c4-9fa14fe6b85f

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting
open MarkovMixing LogSobolevMC.ChiSquare Filter Topology
open scoped BigOperators

private def q {V : Type*} [Fintype V] (π f : V → ℝ) : ℝ := ∑ y, (f y)^2 * π y

private lemma norm_sq {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) (hp : ∀ y, 0 ≤ π y) : (lpNorm π 2 f) ^ (2 : ℝ) = q π f := by
  have hq : 0 ≤ q π f := Finset.sum_nonneg (fun y _ => mul_nonneg (sq_nonneg _) (hp y))
  simp only [lpNorm, Real.rpow_two, sq_abs]
  change (q π f ^ (1 / (2 : ℝ))) ^ 2 = q π f
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num

private lemma ent_formula {V : Type*} [Fintype V] [DecidableEq V]
    (π f : V → ℝ) (hp : ∀ y, 0 ≤ π y) (hf : ∀ y, 0 < f y) (hq : 0 < q π f) :
    entL π f = (∑ y, (f y)^2 * Real.log ((f y)^2) * π y) - q π f * Real.log (q π f) := by
  unfold entL
  rw [norm_sq π f hp]
  simp only [Real.rpow_two, sq_abs]
  simp_rw [Real.log_div (pow_pos (hf _) 2).ne' hq.ne']
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [q, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  ring

private lemma dir_symm {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π f g : V → ℝ) (hr : DetailedBalance K π) :
    dirichlet K π f g = dirichlet K π g f := by
  simp only [dirichlet, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro y hy
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    have h := hr y z
    calc
      K z y * f y * g z * π z = (π z * K z y) * (f y * g z) := by ring
      _ = (π y * K y z) * (f y * g z) := by rw [h]
      _ = K y z * g z * f y * π y := by ring

private lemma dir_delta {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π u : V → ℝ) (x : V) :
    dirichlet K π u (fun y => if y = x then 1 else 0) =
      (u x - K.mulVec u x) * π x := by
  simp [dirichlet, mul_ite]

private lemma dir_deriv {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π u : V → ℝ) (x : V) (hr : DetailedBalance K π) :
    HasDerivAt (fun t : ℝ => dirichlet K π
      (fun y => u y + t * (if y = x then 1 else 0))
      (fun y => u y + t * (if y = x then 1 else 0)))
      (2 * (u x - K.mulVec u x) * π x) 0 := by
  let d : V → ℝ := fun y => if y = x then 1 else 0
  have hd : ∀ y, HasDerivAt (fun t : ℝ => u y + t * d y) (d y) 0 := by
    intro y
    simpa using ((hasDerivAt_id 0).mul_const (d y)).const_add (u y)
  have hm : ∀ y, HasDerivAt (fun t : ℝ => K.mulVec (fun z => u z + t*d z) y)
      (K.mulVec d y) 0 := by
    intro y
    simpa [Matrix.mulVec, dotProduct] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun z _ => (hd z).const_mul (K y z))
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ =>
    (((hd y).sub (hm y)).mul (hd y)).mul_const (π y))
  simp only [Pi.sub_apply, Pi.mul_apply, zero_mul, add_zero] at h
  have he : (∑ y, ((d y - K.mulVec d y) * u y + (u y - K.mulVec u y) * d y) * π y) =
      2 * (u x - K.mulVec u x) * π x := by
    rw [Finset.sum_congr rfl (fun y _ => add_mul _ _ _), Finset.sum_add_distrib]
    change dirichlet K π d u + dirichlet K π u d = _
    rw [dir_symm K π d u hr, dir_delta K π u x]
    ring
  rw [he] at h
  exact h

private lemma ent_deriv {V : Type*} [Fintype V] [DecidableEq V]
    (π u : V → ℝ) (x : V) (hp : ∀ y, 0 < π y) (hu : ∀ y, 0 < u y) :
    HasDerivAt (fun t : ℝ => entL π (fun y => u y + t * (if y = x then 1 else 0)))
      (2 * u x * π x * (Real.log ((u x)^2) - Real.log (q π u))) 0 := by
  let d : V → ℝ := fun y => if y = x then 1 else 0
  let f : ℝ → V → ℝ := fun t y => u y + t*d y
  have hd : ∀ y, HasDerivAt (fun t : ℝ => f t y) (d y) 0 := by
    intro y
    simpa [f] using ((hasDerivAt_id 0).mul_const (d y)).const_add (u y)
  have hq : 0 < q π u := by
    apply Finset.sum_pos' (fun y _ => mul_nonneg (sq_nonneg _) (hp y).le)
    exact ⟨x, Finset.mem_univ _, mul_pos (sq_pos_of_pos (hu x)) (hp x)⟩
  have hQ : HasDerivAt (fun t => q π (f t)) (2*u x*π x) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ => ((hd y).pow 2).mul_const (π y))
    simpa [f, d, q, mul_ite] using h
  have hS : HasDerivAt (fun t => ∑ y, (f t y)^2 * Real.log ((f t y)^2) * π y)
      (2*u x * (Real.log ((u x)^2)+1) * π x) 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun y _ =>
      (((hd y).pow 2).mul (((hd y).pow 2).log (by simpa [f] using (sq_pos_of_pos (hu y)).ne'))).mul_const (π y))
    simp only [Pi.mul_apply, Pi.pow_apply, f, zero_mul, add_zero, d,
      Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
    convert h using 1 <;> try rfl
    rw [Finset.sum_eq_single x]
    · simp only [if_true, mul_one]
      field_simp [(hu x).ne']
    · intro y hy hyx
      simp [hyx]
    · simp
  have H := hS.sub (hQ.mul (hQ.log (by simpa [f] using hq.ne')))
  have he : (fun t => entL π (f t)) =ᶠ[𝓝 0]
      (fun t => (∑ y, (f t y)^2 * Real.log ((f t y)^2) * π y) - q π (f t) * Real.log (q π (f t))) := by
    have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y, 0 < f t y := by
      rw [eventually_all]
      intro y
      exact (hd y).continuousAt.eventually_const_lt (by simpa [f] using hu y)
    have hQpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < q π (f t) :=
      hQ.continuousAt.eventually_const_lt (by simpa [f] using hq)
    filter_upwards [hpos,hQpos] with t ht hqt
    exact ent_formula π (f t) (fun y => (hp y).le) ht hqt
  have H' := H.congr_of_eventuallyEq he
  have hf0 : f 0 = u := by ext y; simp [f]
  rw [hf0] at H'
  convert H' using 1 <;> try rfl
  field_simp [hq.ne']
  ring

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hrev : DetailedBalance K π)
    (u : V → ℝ) (hu : ∀ x, 0 < u x) (hne : LogSobolevMC.ChiSquare.entL π u ≠ 0)
    (hmin : LogSobolevMC.ChiSquare.dirichlet K π u u = LogSobolevMC.ChiSquare.logSobolev K π * LogSobolevMC.ChiSquare.entL π u)
    (hα : 0 < LogSobolevMC.ChiSquare.logSobolev K π) :
    ∀ x, 2 * u x * Real.log (u x) - 2 * u x * Real.log (LogSobolevMC.ChiSquare.lpNorm π 2 u)
      - (1 / LogSobolevMC.ChiSquare.logSobolev K π) * (u x - K.mulVec u x) = 0 := by
  intro x
  let f : ℝ → V → ℝ := fun t y => u y + t * (if y = x then 1 else 0)
  have hf : f 0 = u := by ext y; simp [f]
  have hD := dir_deriv K π u x hrev
  have hE := ent_deriv π u x hπpos hu
  change HasDerivAt (fun t => dirichlet K π (f t) (f t)) _ 0 at hD
  change HasDerivAt (fun t => entL π (f t)) _ 0 at hE
  have hb : BddBelow {r : ℝ | ∃ g : V → ℝ, entL π g ≠ 0 ∧ r = dirichlet K π g g / entL π g} := by
    by_contra h
    have hz : logSobolev K π = 0 := by
      simpa [logSobolev, Real.sInf_empty] using csInf_of_not_bddBelow h
    linarith
  have hlocal : IsLocalMin (fun t => dirichlet K π (f t) (f t) / entL π (f t)) 0 := by
    have hn : ∀ᶠ t in 𝓝 (0 : ℝ), entL π (f t) ≠ 0 :=
      hE.continuousAt.eventually_ne (by simpa [hf] using hne)
    filter_upwards [hn] with t ht
    rw [hf, hmin, mul_div_cancel_right₀ _ hne]
    exact csInf_le hb ⟨f t, ht, rfl⟩
  have hR := hD.div hE (by simpa [hf] using hne)
  have hz := hlocal.hasDerivAt_eq_zero hR
  simp only [hf] at hz
  have hh := (div_eq_zero_iff).mp hz
  have hn : entL π u ^ 2 ≠ 0 := pow_ne_zero _ hne
  have hz' := hh.resolve_right hn
  rw [hmin] at hz'
  have hcancel : (u x - K.mulVec u x) = logSobolev K π * u x *
      (Real.log ((u x)^2) - Real.log (q π u)) := by
    have he : (2 * (u x - K.mulVec u x) * π x -
      logSobolev K π * (2 * u x * π x * (Real.log ((u x)^2) - Real.log (q π u)))) * entL π u = 0 := by
      nlinarith [hz']
    have he' := (mul_eq_zero.mp he).resolve_right hne
    have he'' : ((u x - K.mulVec u x) - logSobolev K π * u x *
        (Real.log ((u x)^2) - Real.log (q π u))) * (2*π x) = 0 := by nlinarith [he']
    have := (mul_eq_zero.mp he'').resolve_right (mul_ne_zero (by norm_num) (hπpos x).ne')
    linarith
  have hq : 0 < q π u := by
    apply Finset.sum_pos' (fun y _ => mul_nonneg (sq_nonneg _) (hπpos y).le)
    exact ⟨x, Finset.mem_univ _, mul_pos (sq_pos_of_pos (hu x)) (hπpos x)⟩
  have hnorm : 0 < lpNorm π 2 u := by
    simp only [lpNorm, Real.rpow_two, sq_abs]
    exact Real.rpow_pos_of_pos hq _
  have hlog : Real.log (q π u) = 2 * Real.log (lpNorm π 2 u) := by
    rw [← norm_sq π u (fun y => (hπpos y).le), Real.rpow_two, Real.log_pow]
    norm_num
  rw [Real.log_pow, hlog] at hcancel
  norm_num at hcancel
  rw [hcancel]
  field_simp [hα.ne']
  ring
#print axioms solution
