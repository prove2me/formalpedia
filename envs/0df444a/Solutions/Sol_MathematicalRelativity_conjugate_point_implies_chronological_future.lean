-- Prove2me | solution 1 for MathematicalRelativity.conjugate_point_implies_chronological_future
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:16:54.060011+00:00
-- url     : https://prove2.me/submissions/757dd57d-03ad-433e-a464-65f81329a631

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

/-! Disproof of c48bb4cb `MathematicalRelativity.conjugate_point_implies_chronological_future`.

`ConjugateToSurface` uses `deriv` (two-sided, `0` off differentiability) and imposes the Jacobi
equation and the initial condition at the closed endpoint `t = 0`, where the field is free for
`t < 0`. A field with a jump at `0` therefore meets the endpoint conditions vacuously, and the
remaining initial condition reduces to `∂_{Y₀} l⁺ = 0` (flat coordinates).

Counterexample: Minkowski space; the slice `x⁰ = 0` (a Cauchy surface: along any inextendible
causal curve `x⁰` is strictly increasing, and `x⁰ ± xᵃ` are monotone, so a bounded `x⁰` would
force a limit); the compact surface `x₁⁴ + x₂⁴ + x₃⁴ = 1` in it, whose unit normal
`n = (x₁³, x₂³, x₃³)/√(x₁⁶+x₂⁶+x₃⁶)` has `∂₁ n = 0` at `p = (0, 0, 0, 1)`; the outgoing null
geodesic `c t = (t, 0, 0, 1 + t)` on `[0, 2]` with `c' = l⁺ = ∂₀ + ∂₃`; and `t* = 1`.
The jump field `Y t = (t - 1) ∂₁` (`t ≥ 0`), `0` (`t < 0`) makes `c 1` formally conjugate.
But `c 2 = (2, 0, 0, 3)` is not in `I⁺(Σ)`: along a future timelike curve `x⁰ - x³` strictly
increases, which would force `x³ > 1` at the start, impossible on the surface. -/

set_option autoImplicit false

open scoped ContDiff
open Filter Topology

namespace MRDisC

open MathematicalRelativity

/-- Minkowski space in inertial coordinates. -/
def mink : Spacetime where
  g := fun _ i j => eta i j
  smooth := fun _ _ => contDiff_const
  symm := fun _ i j => by
    fin_cases i <;> fin_cases j <;> simp [eta]
  lorentz := fun _ => ⟨1, by simp, by simp; rfl⟩
  time_orient := fun _ => by simp [eta]

theorem mink_ip (x u v : Pt) :
    mink.ip x u v = -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 := by
  simp [Spacetime.ip, mink, eta, Fin.sum_univ_four, Matrix.diagonal_apply]

theorem mink_chr (a b c : Fin 4) : mink.christoffel a b c = fun _ => 0 := by
  funext x
  simp [Spacetime.christoffel, pd, mink]

theorem mink_riem (a b c d : Fin 4) (x : Pt) : mink.riemann a b c d x = 0 := by
  simp [Spacetime.riemann, mink_chr, pd]

/-- The time-zero unit vector. -/
def e0 : Pt := fun a => if a = 0 then 1 else 0

/-- The flat slice `x⁰ = 0` with normal `∂₀`. -/
noncomputable def flat : Slice mink where
  f := fun x => x 0
  f_smooth := contDiff_apply ℝ ℝ 0
  N := fun _ => e0
  N_smooth := fun _ => contDiff_const
  N_unit := fun x => by simp [mink_ip, e0]
  N_future := fun x => by simp [Spacetime.IsFuture, e0]
  N_normal := fun x => ⟨-1, by norm_num, fun a => by
    have h : fderiv ℝ (fun x : Pt => x 0) x = ContinuousLinearMap.proj 0 :=
      (hasFDerivAt_apply 0 x).fderiv
    simp only [pd, h]
    fin_cases a <;> simp [Spacetime.lower, mink, eta, e0, Matrix.diagonal_apply]⟩

theorem mink_covD (c Y : ℝ → Pt) (t : ℝ) (a : Fin 4) :
    mink.covDAlong c Y t a = deriv (fun s => Y s a) t := by
  simp [Spacetime.covDAlong, mink_chr]

theorem mink_lower (x v : Pt) (a : Fin 4) :
    mink.lower x v a = if a = 0 then -v 0 else v a := by
  fin_cases a <;> simp [Spacetime.lower, mink, eta, Fin.sum_univ_four, Matrix.diagonal_apply]

/-- A function with a jump along a filter converging to `x` has junk derivative `0` at `x`. -/
theorem deriv_jump {f : ℝ → ℝ} {x L : ℝ} {l : Filter ℝ} [l.NeBot] (hl : l ≤ 𝓝 x)
    (hne : L ≠ f x) (hev : ∀ᶠ y in l, f y = L) : deriv f x = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have h1 : Tendsto f l (𝓝 (f x)) := hd.continuousAt.tendsto.mono_left hl
  have h2 : Tendsto f l (𝓝 L) := tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm)
  exact hne (tendsto_nhds_unique h2 h1)

/-- `t - 1` on `[0, ∞)`, and `0` to the left of `0` (a jump at `0`). -/
noncomputable def yj (t : ℝ) : ℝ := if 0 ≤ t then t - 1 else 0

theorem deriv_yj (s : ℝ) : deriv yj s = if 0 < s then 1 else 0 := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have h : yj =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with u hu
      simp [yj, not_le.mpr (show u < 0 from hu)]
    rw [h.deriv_eq]; simp [not_lt.mpr hs.le]
  · rw [if_neg (lt_irrefl 0)]
    apply deriv_jump (l := 𝓝[<] 0) nhdsWithin_le_nhds (L := 0)
    · simp [yj]
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp [yj, not_le.mpr (show u < 0 from hu)]
  · have h : yj =ᶠ[𝓝 s] fun u => u - 1 := by
      filter_upwards [Ioi_mem_nhds hs] with u hu
      simp [yj, le_of_lt (show 0 < u from hu)]
    rw [h.deriv_eq]; simp [hs]

theorem deriv_yj_zero : deriv yj 0 = 0 := by simpa using deriv_yj 0

theorem deriv2_yj (t : ℝ) (ht : 0 ≤ t) : deriv (deriv yj) t = 0 := by
  have hfun : deriv yj = fun s => if 0 < s then (1:ℝ) else 0 := funext deriv_yj
  rw [hfun]
  rcases ht.eq_or_lt with rfl | ht
  · apply deriv_jump (l := 𝓝[>] 0) nhdsWithin_le_nhds (L := 1)
    · simp
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp [show (0:ℝ) < u from hu]
  · have h : (fun s : ℝ => if 0 < s then (1:ℝ) else 0) =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      simp [show (0:ℝ) < u from hu]
    rw [h.deriv_eq]; simp

/-- The junk Jacobi field: `(t - 1) ∂₁` on `[0, 1]`, jumping to `0` left of `0`. -/
noncomputable def Yj (t : ℝ) : Pt := fun a => if a = 1 then yj t else 0

theorem Yj_jacobi (c : ℝ → Pt) : mink.IsJacobiFieldOn c Yj (Set.Icc 0 1) := by
  refine ⟨fun a => ?_, fun t ht a => ?_⟩
  · by_cases ha : a = 1
    · subst ha
      simp only [Yj, if_true]
      exact (contDiff_id.sub (contDiff_const (c := (1:ℝ)))).contDiffOn.congr
        (fun t ht => by simp [yj, ht.1])
    · simp only [Yj, ha, if_false]
      exact contDiffOn_const
  · simp only [mink_covD, mink_riem, zero_mul, Finset.sum_const_zero]
    by_cases ha : a = 1
    · subst ha
      simpa [Yj] using deriv2_yj t ht.1
    · simp [Yj, ha]

/-! ### The flat slice is a Cauchy surface -/

theorem conv_top (x y : ℝ → ℝ) (hP : Monotone (fun t => x t + y t))
    (hM : Monotone (fun t => x t - y t)) (hneg : ∀ t, x t < 0) :
    ∃ L, Tendsto y atTop (𝓝 L) := by
  have hPb : BddAbove (Set.range (fun t => x t + y t)) := ⟨y 0 - x 0, by
    rintro _ ⟨t, rfl⟩
    rcases le_total t 0 with ht | ht
    · have h1 := hP ht; have h2 := hneg 0; simp only at h1 ⊢; linarith
    · have h1 := hM ht; have h2 := hneg t; have h3 := hneg 0; simp only at h1 ⊢; linarith⟩
  have hMb : BddAbove (Set.range (fun t => x t - y t)) := ⟨-y 0 - x 0, by
    rintro _ ⟨t, rfl⟩
    rcases le_total t 0 with ht | ht
    · have h1 := hM ht; have h2 := hneg 0; simp only at h1 ⊢; linarith
    · have h1 := hP ht; have h2 := hneg t; have h3 := hneg 0; simp only at h1 ⊢; linarith⟩
  have h1 := tendsto_atTop_ciSup hP hPb
  have h2 := tendsto_atTop_ciSup hM hMb
  refine ⟨((⨆ t, x t + y t) - (⨆ t, x t - y t)) / 2, ?_⟩
  refine ((h1.sub h2).div_const 2).congr (fun t => ?_)
  ring

theorem conv_bot (x y : ℝ → ℝ) (hP : Monotone (fun t => x t + y t))
    (hM : Monotone (fun t => x t - y t)) (hpos : ∀ t, 0 < x t) :
    ∃ L, Tendsto y atBot (𝓝 L) := by
  have hPb : BddBelow (Set.range (fun t => x t + y t)) := ⟨y 0 - x 0, by
    rintro _ ⟨t, rfl⟩
    rcases le_total t 0 with ht | ht
    · have h1 := hM ht; have h2 := hpos t; have h3 := hpos 0; simp only at h1 ⊢; linarith
    · have h1 := hP ht; have h2 := hpos 0; simp only at h1 ⊢; linarith⟩
  have hMb : BddBelow (Set.range (fun t => x t - y t)) := ⟨-y 0 - x 0, by
    rintro _ ⟨t, rfl⟩
    rcases le_total t 0 with ht | ht
    · have h1 := hP ht; have h2 := hpos t; have h3 := hpos 0; simp only at h1 ⊢; linarith
    · have h1 := hM ht; have h2 := hpos 0; simp only at h1 ⊢; linarith⟩
  have h1 := tendsto_atBot_ciInf hP hPb
  have h2 := tendsto_atBot_ciInf hM hMb
  refine ⟨((⨅ t, x t + y t) - (⨅ t, x t - y t)) / 2, ?_⟩
  refine ((h1.sub h2).div_const 2).congr (fun t => ?_)
  ring

theorem flat_cauchy : mink.IsCauchySurface flat.carrier := by
  intro c hc
  obtain ⟨⟨hcd, hcv⟩, hnt, hnb⟩ := hc
  have hdiff : ∀ a, Differentiable ℝ (fun s => c s a) := fun a =>
    (contDiffOn_univ.mp (hcd a)).differentiable (by norm_num)
  have hv : ∀ t, 0 < vel c t 0 ∧
      ∀ i : Fin 4, vel c t i ≤ vel c t 0 ∧ -vel c t i ≤ vel c t 0 := by
    intro t
    obtain ⟨⟨hcaus, _⟩, hfut⟩ := hcv t (Set.mem_univ t)
    rw [mink_ip] at hcaus
    rw [Spacetime.IsFuture] at hfut
    refine ⟨hfut, fun i => ?_⟩
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      constructor <;>
      nlinarith [mul_self_nonneg (vel c t 1), mul_self_nonneg (vel c t 2),
        mul_self_nonneg (vel c t 3), mul_self_nonneg (vel c t 0)]
  have hP : ∀ a, Monotone (fun t => c t 0 + c t a) := fun a =>
    monotone_of_deriv_nonneg ((hdiff 0).add (hdiff a)) (fun t => by
      rw [deriv_fun_add (hdiff 0 t) (hdiff a t)]
      have h := (hv t).2 a
      change 0 ≤ vel c t 0 + vel c t a
      linarith [h.2])
  have hM : ∀ a, Monotone (fun t => c t 0 - c t a) := fun a =>
    monotone_of_deriv_nonneg ((hdiff 0).sub (hdiff a)) (fun t => by
      rw [deriv_fun_sub (hdiff 0 t) (hdiff a t)]
      have h := (hv t).2 a
      change 0 ≤ vel c t 0 - vel c t a
      linarith [h.1])
  have hsm : StrictMono (fun t => c t 0) := strictMono_of_deriv_pos (fun t => (hv t).1)
  have hup : ∃ t, 0 ≤ c t 0 := by
    by_contra hcon
    push Not at hcon
    apply hnt
    choose L hL using fun a => conv_top (fun t => c t 0) (fun t => c t a) (hP a) (hM a) hcon
    exact ⟨L, tendsto_pi_nhds.mpr hL⟩
  have hdown : ∃ t, c t 0 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnb
    choose L hL using fun a => conv_bot (fun t => c t 0) (fun t => c t a) (hP a) (hM a) hcon
    exact ⟨L, tendsto_pi_nhds.mpr hL⟩
  obtain ⟨t1, ht1⟩ := hup
  obtain ⟨t2, ht2⟩ := hdown
  obtain ⟨t0, ht0⟩ : (0:ℝ) ∈ Set.range (fun t => c t 0) :=
    intermediate_value_univ t2 t1 (hdiff 0).continuous ⟨ht2, ht1⟩
  refine ⟨t0, ht0, fun t ht => hsm.injective ?_⟩
  exact (show c t 0 = 0 from ht).trans ht0.symm

/-! ### A compact surface with a flat direction: `x₁⁴ + x₂⁴ + x₃⁴ = 1` in `x⁰ = 0` -/

/-- Sum of sixth powers of the spatial coordinates. -/
def S6 (x : Pt) : ℝ := x 1 ^ 6 + x 2 ^ 6 + x 3 ^ 6

/-- Defining function of the superellipsoid. -/
def hq (x : Pt) : ℝ := x 1 ^ 4 + x 2 ^ 4 + x 3 ^ 4 - 1

/-- Unit normal of the level sets of `hq` inside the slice. -/
noncomputable def nq (x : Pt) : Pt :=
  fun a => if a = 0 then 0 else x a ^ 3 / Real.sqrt (S6 x)

/-- Where `∇hq ≠ 0`. -/
def Uq : Set Pt := {x | 0 < S6 x}

theorem contDiff_S6 : ContDiff ℝ ∞ S6 := by unfold S6; fun_prop

theorem contDiff_hq : ContDiff ℝ ∞ hq := by unfold hq; fun_prop

theorem pd_hq (x : Pt) (a : Fin 4) : pd hq a x = if a = 0 then 0 else 4 * x a ^ 3 := by
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x).pow 4
  have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x).pow 4
  have h3 := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x).pow 4
  have hF : HasFDerivAt hq _ x := ((h1.add h2).add h3).sub_const 1
  rw [pd, hF.fderiv]
  fin_cases a <;> simp [Pi.single_apply]

noncomputable def sig : Surface mink flat where
  U := Uq
  U_open := isOpen_lt continuous_const contDiff_S6.continuous
  h := hq
  h_smooth := contDiff_hq.contDiffOn
  n := nq
  n_smooth := fun a => by
    by_cases ha : a = 0
    · simp only [nq, ha, if_true]
      exact contDiffOn_const
    · simp only [nq, ha, if_false]
      exact ((contDiff_apply ℝ ℝ a).pow 3).contDiffOn.div
        (contDiff_S6.contDiffOn.sqrt (fun x hx => (show 0 < S6 x from hx).ne'))
        (fun x hx => (Real.sqrt_pos.mpr (show 0 < S6 x from hx)).ne')
  n_unit := fun x hx => by
    have hS : 0 < S6 x := hx
    have hr : Real.sqrt (S6 x) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
    have hsq : Real.sqrt (S6 x) ^ 2 = S6 x := Real.sq_sqrt hS.le
    have e : ∀ i : Fin 4, i ≠ 0 → nq x i = x i ^ 3 / Real.sqrt (S6 x) := fun i hi => by
      simp [nq, hi]
    have e0' : nq x 0 = 0 := by simp [nq]
    rw [mink_ip, e0', e 1 (by decide), e 2 (by decide), e 3 (by decide)]
    field_simp
    rw [hsq]
    unfold S6
    ring
  n_orth := fun x _ => by simp [mink_ip, nq, flat, e0]
  n_normal := fun x hx => by
    have hS : 0 < S6 x := hx
    have hr : Real.sqrt (S6 x) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
    refine ⟨4 * Real.sqrt (S6 x), by positivity, fun a => ?_⟩
    rw [pd_hq, mink_lower]
    by_cases ha : a = 0
    · simp [ha, nq]
    · simp only [ha, if_false, nq]
      field_simp
  subset := fun x hx => by
    obtain ⟨_, hh⟩ := hx
    show 0 < S6 x
    unfold hq at hh
    unfold S6
    by_contra hle
    push Not at hle
    have a1 : 0 ≤ x 1 ^ 6 := by positivity
    have a2 : 0 ≤ x 2 ^ 6 := by positivity
    have a3 : 0 ≤ x 3 ^ 6 := by positivity
    have z1 : x 1 = 0 := pow_eq_zero_iff (n := 6) (by norm_num) |>.mp (by linarith)
    have z2 : x 2 = 0 := pow_eq_zero_iff (n := 6) (by norm_num) |>.mp (by linarith)
    have z3 : x 3 = 0 := pow_eq_zero_iff (n := 6) (by norm_num) |>.mp (by linarith)
    rw [z1, z2, z3] at hh
    norm_num at hh
  compact := by
    apply Metric.isCompact_of_isClosed_isBounded
    · rw [Set.ofPred_and]
      exact (isClosed_eq (continuous_apply 0) continuous_const).inter
        (isClosed_eq contDiff_hq.continuous continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall (0 : Pt)]
      refine ⟨1, fun x hx => ?_⟩
      obtain ⟨hf, hh⟩ := hx
      have hf' : x 0 = 0 := hf
      unfold hq at hh
      have b1 : 0 ≤ x 1 ^ 4 := by positivity
      have b2 : 0 ≤ x 2 ^ 4 := by positivity
      have b3 : 0 ≤ x 3 ^ 4 := by positivity
      have key : ∀ y : ℝ, y ^ 4 ≤ 1 → |y| ≤ 1 := fun y hy => by
        have : |y| ^ 4 ≤ 1 := by rw [pow_abs, abs_of_nonneg (by positivity)]; exact hy
        exact (pow_le_one_iff_of_nonneg (abs_nonneg y) (by norm_num)).mp this
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      fin_cases i
      · simp [hf']
      · exact key _ (by simp; linarith)
      · exact key _ (by simp; linarith)
      · exact key _ (by simp; linarith)

/-! ### The outgoing null geodesic from `(0, 0, 0, 1)` -/

/-- `t ↦ (t, 0, 0, 1 + t)`. -/
def cn (t : ℝ) : Pt := fun a => if a = 0 then t else if a = 3 then 1 + t else 0

/-- `∂₀ + ∂₃`. -/
def l0 : Pt := fun a => if a = 0 then 1 else if a = 3 then 1 else 0

theorem vel_cn (t : ℝ) : vel cn t = l0 := by
  funext a
  fin_cases a <;> simp [vel, cn, l0]

theorem acc_cn (t : ℝ) (a : Fin 4) : acc cn t a = 0 := by
  have h : (fun s => deriv (fun u => cn u a) s) = fun _ => l0 a :=
    funext fun s => congrFun (vel_cn s) a
  simp only [acc, h, deriv_const]

theorem cn_null (T : ℝ) : mink.IsNullGeodesicOn cn (Set.Icc 0 T) := by
  refine ⟨⟨fun a => ?_, fun t _ a => ?_⟩, fun t _ => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · fin_cases a <;> simp [cn] <;> fun_prop
  · simp [acc_cn, mink_chr]
  · simp [vel_cn, mink_ip, l0]
  · rw [vel_cn]
    intro h
    have := congrFun h 0
    simp [l0] at this
  · simp [Spacetime.IsFuture, vel_cn, l0]

theorem cn_start : sig.NormalNullGeodesicAt sig.lplus cn 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [flat, cn]
  · simp [sig, hq, cn]
  · rw [vel_cn]
    funext a
    fin_cases a <;> simp [Surface.lplus, sig, flat, nq, S6, cn, l0, e0]

/-! ### The formal conjugate point at `t = 1` -/

theorem pd_line {g : Pt → ℝ} {b : Fin 4} {x : Pt} (hd : DifferentiableAt ℝ g x) :
    HasDerivAt (fun t : ℝ => g (x + t • Pi.single b (1:ℝ))) (pd g b x) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single b (1:ℝ)) (Pi.single b 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single b (1:ℝ))).const_add x
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)

theorem pd_even (g : Pt → ℝ) (b : Fin 4) (x : Pt)
    (h : ∀ t : ℝ, g (x + (-t) • Pi.single b (1:ℝ)) = g (x + t • Pi.single b (1:ℝ))) :
    pd g b x = 0 := by
  by_cases hd : DifferentiableAt ℝ g x
  · have hφ := pd_line (b := b) hd
    have heven : (fun t : ℝ => g (x + (-t) • Pi.single b (1:ℝ)))
        = fun t => g (x + t • Pi.single b (1:ℝ)) := funext h
    have h0 := deriv_comp_neg (f := fun s : ℝ => g (x + s • Pi.single b (1:ℝ))) (x := 0)
    rw [heven, neg_zero] at h0
    rw [← hφ.deriv]
    linarith
  · simp [pd, fderiv_zero_of_not_differentiableAt hd]

theorem pd_zero_of_line (g : Pt → ℝ) (b : Fin 4) (x : Pt)
    (h : HasDerivAt (fun t : ℝ => g (x + t • Pi.single b (1:ℝ))) 0 0) : pd g b x = 0 := by
  by_cases hd : DifferentiableAt ℝ g x
  · exact (pd_line hd).unique h
  · simp [pd, fderiv_zero_of_not_differentiableAt hd]

theorem pd_lp0 : pd (fun y => sig.lplus y 0) 1 (cn 0) = 0 := by
  have e : (fun y => sig.lplus y 0) = fun _ => (1:ℝ) := by
    funext y
    simp [Surface.lplus, sig, flat, e0, nq]
  rw [e]
  simp [pd]

theorem pd_lp1 : pd (fun y => sig.lplus y 1) 1 (cn 0) = 0 := by
  apply pd_zero_of_line
  have e : (fun t : ℝ => sig.lplus (cn 0 + t • Pi.single 1 (1:ℝ)) 1)
      = fun t => t ^ 3 * (Real.sqrt (t ^ 6 + 1))⁻¹ := by
    funext t
    simp [Surface.lplus, sig, flat, e0, nq, cn, S6, Pi.single_apply, div_eq_mul_inv]
  rw [e]
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 6 + 1)) _ 0 :=
    ((hasDerivAt_pow 6 (0:ℝ)).add_const 1).sqrt (by norm_num)
  have hi := hs.inv (by norm_num)
  have hp := (hasDerivAt_pow 3 (0:ℝ)).mul hi
  convert hp using 1 <;> first | rfl | simp

theorem pd_lp2 : pd (fun y => sig.lplus y 2) 1 (cn 0) = 0 := by
  apply pd_even
  intro t
  simp [Surface.lplus, sig, flat, e0, nq, cn, S6, Pi.single_apply]

theorem pd_lp3 : pd (fun y => sig.lplus y 3) 1 (cn 0) = 0 := by
  apply pd_even
  intro t
  have h6 : (-t) ^ 6 = t ^ 6 := by ring
  simp [Surface.lplus, sig, flat, e0, nq, cn, S6, Pi.single_apply, h6]

theorem pd_lp (a : Fin 4) : pd (fun y => sig.lplus y a) 1 (cn 0) = 0 := by
  fin_cases a
  exacts [pd_lp0, pd_lp1, pd_lp2, pd_lp3]

theorem cn_conj : sig.ConjugateToSurface sig.lplus cn 0 1 := by
  refine ⟨Yj, Yj_jacobi cn, ⟨0, by simp, ?_⟩, ?_, ?_, fun a => ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp [Yj, yj] at this
  · simp [mink_ip, flat, e0, Yj]
  · simp [mink_ip, sig, nq, Yj, cn, S6]
  · have hL : ∀ b, mink.covVec sig.lplus a b (cn 0) * Yj 0 b = 0 := by
      intro b
      by_cases hb : b = 1
      · subst hb
        have hcv : mink.covVec sig.lplus a 1 (cn 0) = 0 := by
          simp only [Spacetime.covVec, mink_chr, zero_mul, Finset.sum_const_zero, add_zero]
          exact pd_lp a
        rw [hcv, zero_mul]
      · simp [Yj, hb]
    simp only [hL, Finset.sum_const_zero, mink_covD]
    by_cases ha : a = 1
    · subst ha
      simpa [Yj] using deriv_yj_zero
    · simp [Yj, ha]
  · funext a
    simp [Yj, yj]

/-! ### `c 2 = (2, 0, 0, 3)` is not in the chronological future of the surface -/

theorem not_chron : cn 2 ∉ mink.chronFuture sig.carrier := by
  rintro ⟨d, t1, ht1, hd, hd0, hdt⟩
  have hdiffI : ∀ a, ∀ x ∈ Set.Ioo 0 t1, DifferentiableAt ℝ (fun s => d s a) x :=
    fun a x hx => ((hd.1 a).contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by norm_num)
  have hmono : StrictMonoOn (fun s => d s 0 - d s 3) (Set.Icc 0 t1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 t1)
    · exact ((hd.1 0).continuousOn).sub ((hd.1 3).continuousOn)
    · intro x hx
      rw [interior_Icc] at hx
      rw [deriv_fun_sub (hdiffI 0 x hx) (hdiffI 3 x hx)]
      obtain ⟨htl, hfu⟩ := hd.2 x (Set.Ioo_subset_Icc_self hx)
      rw [Spacetime.IsTimelike, mink_ip] at htl
      rw [Spacetime.IsFuture] at hfu
      change 0 < vel d x 0 - vel d x 3
      nlinarith [mul_self_nonneg (vel d x 1), mul_self_nonneg (vel d x 2),
        mul_self_nonneg (vel d x 3 - vel d x 0)]
  have hlt := hmono ⟨le_refl 0, ht1.le⟩ ⟨ht1.le, le_refl t1⟩ ht1
  obtain ⟨hf0, hh0⟩ := hd0
  have hf0' : d 0 0 = 0 := hf0
  have hdt0 : d t1 0 = 2 := by rw [hdt]; simp [cn]
  have hdt3 : d t1 3 = 3 := by rw [hdt]; simp [cn]; norm_num
  simp only [hdt0, hdt3, hf0'] at hlt
  have h3 : 1 < d 0 3 := by linarith
  have h34 : 1 < d 0 3 ^ 4 := one_lt_pow₀ h3 (by norm_num)
  have hh0' : d 0 1 ^ 4 + d 0 2 ^ 4 + d 0 3 ^ 4 - 1 = 0 := hh0
  have b1 : 0 ≤ d 0 1 ^ 4 := by positivity
  have b2 : 0 ≤ d 0 2 ^ 4 := by positivity
  linarith

end MRDisC

open MathematicalRelativity in
theorem solution : ¬ (∀ (m : Spacetime) (S : Slice m) (Sig : Surface m S) (c : ℝ → Pt) (T tstar : ℝ)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hgeo : m.IsNullGeodesicOn c (Set.Icc 0 T))
    (hstart : Sig.NormalNullGeodesicAt Sig.lplus c 0)
    (ht : tstar ∈ Set.Ioo (0:ℝ) T)
    (hconj : Sig.ConjugateToSurface Sig.lplus c 0 tstar),
    c T ∈ m.chronFuture Sig.carrier) := by
  intro H
  exact MRDisC.not_chron (H MRDisC.mink MRDisC.flat MRDisC.sig MRDisC.cn 2 1 MRDisC.flat_cauchy
    (MRDisC.cn_null 2) MRDisC.cn_start ⟨by norm_num, by norm_num⟩ MRDisC.cn_conj)

