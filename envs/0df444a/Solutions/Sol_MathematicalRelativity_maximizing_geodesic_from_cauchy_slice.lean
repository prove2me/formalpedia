-- Prove2me | solution 1 for MathematicalRelativity.maximizing_geodesic_from_cauchy_slice
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:49:59.927573+00:00
-- url     : https://prove2.me/submissions/eb342d06-ffeb-44d2-ac3f-6e08713baf66

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

/-! Disproof of e1df1b18 `MathematicalRelativity.maximizing_geodesic_from_cauchy_slice`.

`IsFuture v` is `0 < v 0`. That is a genuine time orientation only when the hypersurfaces
`x⁰ = const` are spacelike, and `time_orient` (`g₀₀ < 0`) does not ensure this. Take Minkowski
space in the skewed linear chart `T = x⁰ + 2x¹`, `X = x¹`, so that
`g = -(dx⁰ + 2dx¹)² + (dx¹)² + (dx²)² + (dx³)²`. Here `∂ₓ¹ = 2∂_T + ∂_X` is timelike, and
some genuinely past-directed timelike vectors have `v⁰ > 0`.

* `S = {T = 0}` with `N = ∂₀ = ∂_T` is a Cauchy surface in the formal sense. Along an
  inextendible causal curve, `T' = v⁰ + 2v¹` never vanishes and so keeps one sign, `σ T` is
  strictly increasing, and `σ T ± xᵃ` are monotone. A bounded `σ T` would force a limit.
* `q = (1, -2, 0, 0)` has `T = -3`. The segment `s ↦ s·q` from the origin is formally future
  timelike, so `q ∈ I⁺(S)` formally.
* A geodesic `c` on `[0, T₀]` from `S` to `q` is a straight segment `q - c 0 = T₀ w`. Its proper
  time is `T₀`, where `T₀² = 9 - (2 + p¹)² - (p²)² - (p³)²` with `p = c 0`, and `v⁰ > 0` forces
  `p¹ > -1/2`. The straight competitor from `(-2X, X, 0, 0) ∈ S` with `X = (p¹ - 1/2)/2`
  (so `-1/2 < X < p¹`) is formally future timelike and has proper time `√(9 - (2+X)²) > T₀`.
  So no geodesic from `S` to `q` maximizes. -/

set_option autoImplicit false

open scoped ContDiff
open Filter Topology

namespace MRDisE

open MathematicalRelativity

/-- Minkowski metric in the skewed linear chart `T = x⁰ + 2x¹`, `X = x¹`, `Y = x²`, `Z = x³`:
`g = -(dx⁰ + 2dx¹)² + (dx¹)² + (dx²)² + (dx³)²`. -/
def Gs : Matrix (Fin 4) (Fin 4) ℝ := !![-1, -2, 0, 0; -2, -3, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- The chart change back to inertial coordinates. -/
def Ps : Matrix (Fin 4) (Fin 4) ℝ := !![1, -2, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Its inverse. -/
def Qs : Matrix (Fin 4) (Fin 4) ℝ := !![1, 2, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def skew : Spacetime where
  g := fun _ i j => Gs i j
  smooth := fun _ _ => contDiff_const
  symm := fun _ i j => by
    fin_cases i <;> fin_cases j <;> simp [Gs]
  lorentz := fun _ => ⟨Ps, Matrix.isUnit_det_of_right_inverse (B := Qs) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Ps, Qs]),
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, Ps, Gs, eta, Matrix.diagonal_apply] <;>
        norm_num⟩
  time_orient := fun _ => by simp [Gs]

theorem skew_ip (x u v : Pt) :
    skew.ip x u v = -(u 0 * v 0) - 2 * (u 0 * v 1) - 2 * (u 1 * v 0) - 3 * (u 1 * v 1)
      + u 2 * v 2 + u 3 * v 3 := by
  simp [Spacetime.ip, skew, Gs, Fin.sum_univ_four]
  ring

theorem skew_chr (a b c : Fin 4) : skew.christoffel a b c = fun _ => 0 := by
  funext x
  simp [Spacetime.christoffel, pd, skew]

/-- `∂₀`, the (genuinely future) unit normal of `T = 0`. -/
def e0 : Pt := fun a => if a = 0 then 1 else 0

/-- Physical time `T = x⁰ + 2x¹`. -/
def fS (x : Pt) : ℝ := x 0 + 2 * x 1

noncomputable def slc : Slice skew where
  f := fS
  f_smooth := by unfold fS; fun_prop
  N := fun _ => e0
  N_smooth := fun _ => contDiff_const
  N_unit := fun x => by simp [skew_ip, e0]
  N_future := fun x => by simp [Spacetime.IsFuture, e0]
  N_normal := fun x => ⟨-1, by norm_num, fun a => by
    have hF : HasFDerivAt fS _ x :=
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x).add
        ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x).const_mul 2)
    rw [pd, hF.fderiv]
    fin_cases a <;> simp [Spacetime.lower, skew, Gs, e0, Fin.sum_univ_four, Pi.single_apply]⟩

/-! ### `T = 0` is a Cauchy surface (for curves of either genuine time orientation) -/

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

theorem skew_cauchy : skew.IsCauchySurface slc.carrier := by
  intro c hc
  obtain ⟨⟨hcd, hcv⟩, hnt, hnb⟩ := hc
  have hCD : ∀ a, ContDiff ℝ 1 (fun s => c s a) := fun a => contDiffOn_univ.mp (hcd a)
  have hdiff : ∀ a, Differentiable ℝ (fun s => c s a) := fun a =>
    (hCD a).differentiable (by norm_num)
  have hvc : ∀ a, Continuous (fun t => vel c t a) := fun a =>
    (hCD a).continuous_deriv (by norm_num)
  set vT : ℝ → ℝ := fun t => vel c t 0 + 2 * vel c t 1 with hvT
  have hvTc : Continuous vT := (hvc 0).add (continuous_const.mul (hvc 1))
  have hbd : ∀ t, vT t ≠ 0 ∧ ∀ i : Fin 4, i ≠ 0 → (vel c t i) ^ 2 ≤ (vT t) ^ 2 := by
    intro t
    obtain ⟨⟨hcaus, hne⟩, _⟩ := hcv t (Set.mem_univ t)
    rw [skew_ip] at hcaus
    have key : (vel c t 1) ^ 2 + (vel c t 2) ^ 2 + (vel c t 3) ^ 2 ≤ (vT t) ^ 2 := by
      simp only [hvT]; nlinarith
    refine ⟨fun h0 => hne ?_, fun i hi => ?_⟩
    · have h0' : vel c t 0 + 2 * vel c t 1 = 0 := h0
      rw [hvT] at key
      simp only [h0'] at key
      have n1 := sq_nonneg (vel c t 1)
      have n2 := sq_nonneg (vel c t 2)
      have n3 := sq_nonneg (vel c t 3)
      have s1 : (vel c t 1) ^ 2 = 0 := by nlinarith
      have s2 : (vel c t 2) ^ 2 = 0 := by nlinarith
      have s3 : (vel c t 3) ^ 2 = 0 := by nlinarith
      have e1 : vel c t 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp s1
      have e2 : vel c t 2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp s2
      have e3 : vel c t 3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp s3
      have e0' : vel c t 0 = 0 := by linarith
      funext i
      fin_cases i
      · exact e0'
      · exact e1
      · exact e2
      · exact e3
    · fin_cases i
      · exact absurd rfl hi
      all_goals
        have n1 := sq_nonneg (vel c t 1)
        have n2 := sq_nonneg (vel c t 2)
        have n3 := sq_nonneg (vel c t 3)
        simp only [Fin.mk_one, Fin.reduceFinMk]
        nlinarith
  have hsign : ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ t, 0 < σ * vT t := by
    rcases lt_or_gt_of_ne (hbd 0).1 with h0 | h0
    · refine ⟨-1, by norm_num, fun t => ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs⟩ : (0:ℝ) ∈ Set.range vT :=
        intermediate_value_univ 0 t hvTc ⟨h0.le, by linarith⟩
      exact (hbd s).1 hs
    · refine ⟨1, by norm_num, fun t => ?_⟩
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs⟩ : (0:ℝ) ∈ Set.range vT :=
        intermediate_value_univ t 0 hvTc ⟨by linarith, h0.le⟩
      exact (hbd s).1 hs
  obtain ⟨σ, hσ, hpos⟩ := hsign
  set x : ℝ → ℝ := fun t => σ * (c t 0 + 2 * c t 1) with hx
  have hxd : ∀ t, HasDerivAt x (σ * vT t) t := fun t =>
    (((hdiff 0 t).hasDerivAt).add (((hdiff 1 t).hasDerivAt).const_mul 2)).const_mul σ
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hxd t).continuousAt
  have hsm : StrictMono x := strictMono_of_deriv_pos fun t => by
    rw [(hxd t).deriv]; exact hpos t
  have hmonoP : ∀ a : Fin 4, a ≠ 0 →
      Monotone (fun t => x t + c t a) ∧ Monotone (fun t => x t - c t a) := by
    intro a ha
    have hb : ∀ t, vel c t a ≤ σ * vT t ∧ -vel c t a ≤ σ * vT t := fun t => by
      have h1 := (hbd t).2 a ha
      have h2 := hpos t
      have h3 : (σ * vT t) ^ 2 = (vT t) ^ 2 := by rw [mul_pow, hσ, one_mul]
      constructor <;> nlinarith
    constructor
    · exact monotone_of_deriv_nonneg
        (fun t => ((hxd t).differentiableAt.add (hdiff a t)))
        (fun t => by
          rw [deriv_fun_add (hxd t).differentiableAt (hdiff a t), (hxd t).deriv]
          change 0 ≤ σ * vT t + vel c t a
          linarith [(hb t).2])
    · exact monotone_of_deriv_nonneg
        (fun t => ((hxd t).differentiableAt.sub (hdiff a t)))
        (fun t => by
          rw [deriv_fun_sub (hxd t).differentiableAt (hdiff a t), (hxd t).deriv]
          change 0 ≤ σ * vT t - vel c t a
          linarith [(hb t).1])
  have hxx : Monotone (fun t => x t + x t) := hsm.monotone.add hsm.monotone
  have hxx' : Monotone (fun t => x t - x t) := fun a b _ => by simp
  have hc0 : ∀ t, c t 0 = σ * x t - 2 * c t 1 := fun t => by
    simp only [hx]
    linear_combination (-(c t 0 + 2 * c t 1)) * hσ
  have hup : ∃ t, 0 ≤ x t := by
    by_contra hcon
    push Not at hcon
    apply hnt
    obtain ⟨Lx, hLx⟩ := conv_top x x hxx hxx' hcon
    obtain ⟨L1, h1⟩ := conv_top x (fun t => c t 1) (hmonoP 1 (by decide)).1
      (hmonoP 1 (by decide)).2 hcon
    obtain ⟨L2, h2⟩ := conv_top x (fun t => c t 2) (hmonoP 2 (by decide)).1
      (hmonoP 2 (by decide)).2 hcon
    obtain ⟨L3, h3⟩ := conv_top x (fun t => c t 3) (hmonoP 3 (by decide)).1
      (hmonoP 3 (by decide)).2 hcon
    have h0 : Tendsto (fun t => c t 0) atTop (𝓝 (σ * Lx - 2 * L1)) :=
      ((hLx.const_mul σ).sub (h1.const_mul 2)).congr (fun t => (hc0 t).symm)
    refine ⟨fun a => if a = 0 then σ * Lx - 2 * L1 else if a = 1 then L1 else
      if a = 2 then L2 else L3, tendsto_pi_nhds.mpr fun a => ?_⟩
    fin_cases a
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hdown : ∃ t, x t ≤ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnb
    obtain ⟨Lx, hLx⟩ := conv_bot x x hxx hxx' hcon
    obtain ⟨L1, h1⟩ := conv_bot x (fun t => c t 1) (hmonoP 1 (by decide)).1
      (hmonoP 1 (by decide)).2 hcon
    obtain ⟨L2, h2⟩ := conv_bot x (fun t => c t 2) (hmonoP 2 (by decide)).1
      (hmonoP 2 (by decide)).2 hcon
    obtain ⟨L3, h3⟩ := conv_bot x (fun t => c t 3) (hmonoP 3 (by decide)).1
      (hmonoP 3 (by decide)).2 hcon
    have h0 : Tendsto (fun t => c t 0) atBot (𝓝 (σ * Lx - 2 * L1)) :=
      ((hLx.const_mul σ).sub (h1.const_mul 2)).congr (fun t => (hc0 t).symm)
    refine ⟨fun a => if a = 0 then σ * Lx - 2 * L1 else if a = 1 then L1 else
      if a = 2 then L2 else L3, tendsto_pi_nhds.mpr fun a => ?_⟩
    fin_cases a
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3
  obtain ⟨t1, ht1⟩ := hup
  obtain ⟨t2, ht2⟩ := hdown
  obtain ⟨t0, ht0⟩ : (0:ℝ) ∈ Set.range x := intermediate_value_univ t2 t1 hxc ⟨ht2, ht1⟩
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  have hmem : ∀ t, c t ∈ slc.carrier ↔ x t = 0 := fun t => by
    show fS (c t) = 0 ↔ σ * (c t 0 + 2 * c t 1) = 0
    simp [fS, hσ0]
  exact ⟨t0, (hmem t0).mpr ht0, fun t ht => hsm.injective (((hmem t).mp ht).trans ht0.symm)⟩

/-! ### Straight competitors from the slice to `q = (1, -2, 0, 0)` -/

/-- The target point `q`; physically `T = -3`, `X = -2`: in the past of the slice. -/
def qE : Pt := fun a => if a = 0 then 1 else if a = 1 then -2 else 0

/-- The straight segment from `(-2X, X, 0, 0)` (on the slice) to `q`, over `s ∈ [0, 1]`. -/
def dd (X s : ℝ) : Pt := fun a =>
  if a = 0 then -2 * X + s * (1 + 2 * X) else if a = 1 then X + s * (-2 - X) else 0

theorem vel_dd (X s : ℝ) :
    vel (dd X) s = fun a => if a = 0 then 1 + 2 * X else if a = 1 then -2 - X else 0 := by
  funext a
  fin_cases a <;> simp [vel, dd]

theorem ip_dd (X s : ℝ) (x : Pt) :
    skew.ip x (vel (dd X) s) (vel (dd X) s) = (2 + X) ^ 2 - 9 := by
  rw [vel_dd, skew_ip]
  simp
  ring

theorem pt_dd (X : ℝ) : skew.properTime (dd X) 0 1 = Real.sqrt (9 - (2 + X) ^ 2) := by
  simp [Spacetime.properTime, ip_dd]

theorem dd_timelike (X : ℝ) (h1 : -1/2 < X) (h2 : (2 + X) ^ 2 < 9) :
    skew.IsTimelikeCurveOn (dd X) (Set.Icc 0 1) := by
  refine ⟨fun a => ?_, fun t _ => ⟨?_, ?_⟩⟩
  · fin_cases a <;> simp [dd] <;> fun_prop
  · rw [Spacetime.IsTimelike, ip_dd]; linarith
  · rw [Spacetime.IsFuture, vel_dd]; simp; linarith

theorem dd_start (X : ℝ) : dd X 0 ∈ slc.carrier := by
  show fS (dd X 0) = 0
  simp [fS, dd]

theorem dd_end (X : ℝ) : dd X 1 = qE := by
  funext a
  fin_cases a <;> simp [dd, qE] <;> ring

theorem q_mem : qE ∈ skew.chronFuture slc.carrier :=
  ⟨dd 0, 1, one_pos, dd_timelike 0 (by norm_num) (by norm_num), dd_start 0, dd_end 0⟩

/-! ### No geodesic from the slice to `q` maximizes -/

theorem no_max (c : ℝ → Pt) (T : ℝ) (hT : 0 < T)
    (hgeo : skew.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T)) (hc0 : c 0 ∈ slc.carrier)
    (hcT : c T = qE) : ¬ slc.MaximizesFromSlice c T := by
  intro hmax
  obtain ⟨⟨⟨hC2, hgeq⟩, htf⟩, hunit⟩ := hgeo
  have hmid : T / 2 ∈ Set.Icc 0 T := ⟨by linarith, by linarith⟩
  have hw1 := hunit _ hmid
  rw [skew_ip] at hw1
  have hw0 : 0 < vel c (T / 2) 0 := (htf _ hmid).2
  have hdisp : ∀ a, c T a - c 0 a = T * vel c (T / 2) a := by
    intro a
    have hIoo : IsOpen (Set.Ioo 0 T) := isOpen_Ioo
    have hCa : ContDiffOn ℝ 2 (fun s => c s a) (Set.Ioo 0 T) :=
      (hC2 a).mono Set.Ioo_subset_Icc_self
    have hD : ContDiffOn ℝ 1 (deriv (fun s => c s a)) (Set.Ioo 0 T) :=
      hCa.deriv_of_isOpen hIoo (by norm_num)
    have hDdiff : DifferentiableOn ℝ (deriv (fun s => c s a)) (Set.Ioo 0 T) :=
      hD.differentiableOn (by norm_num)
    have hDzero : (Set.Ioo 0 T).EqOn (deriv (deriv (fun s => c s a))) 0 := by
      intro t ht
      have h := hgeq t (Set.Ioo_subset_Icc_self ht) a
      simp only [skew_chr, zero_mul, Finset.sum_const_zero, add_zero] at h
      exact h
    have hconst : ∀ t ∈ Set.Ioo 0 T, deriv (fun s => c s a) t = vel c (T / 2) a :=
      fun t ht => hIoo.is_const_of_deriv_eq_zero isPreconnected_Ioo hDdiff hDzero ht
        ⟨by linarith, by linarith⟩
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope (fun s => c s a) hT
      ((hC2 a).continuousOn) (hCa.differentiableOn (by norm_num))
    rw [hconst ξ hξ] at hξeq
    rw [hξeq, sub_zero]
    field_simp
  have hpc : skew.properTime c 0 T = T := by
    unfold Spacetime.properTime
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (fun t ht => by
      rw [Set.uIcc_of_le hT.le] at ht
      simp [hunit t ht])]
    simp
  have hp : c 0 0 + 2 * c 0 1 = 0 := hc0
  have hq0 : c T 0 = 1 := by rw [hcT]; simp [qE]
  have hq1 : c T 1 = -2 := by rw [hcT]; simp [qE]
  have hq2 : c T 2 = 0 := by rw [hcT]; simp [qE]
  have hq3 : c T 3 = 0 := by rw [hcT]; simp [qE]
  have d0 := hdisp 0
  have d1 := hdisp 1
  have d2 := hdisp 2
  have d3 := hdisp 3
  rw [hq0] at d0
  rw [hq1] at d1
  rw [hq2] at d2
  rw [hq3] at d3
  set w0 := vel c (T / 2) 0
  set w1 := vel c (T / 2) 1
  set w2 := vel c (T / 2) 2
  set w3 := vel c (T / 2) 3
  set p1 := c 0 1
  have hTw : T * (w0 + 2 * w1) = -3 := by linear_combination -d0 - 2 * d1 - hp
  have hT2 : T ^ 2 = 9 - (2 + p1) ^ 2 - (c 0 2) ^ 2 - (c 0 3) ^ 2 := by
    have e1 : 2 + p1 = -(T * w1) := by linarith
    have e2 : c 0 2 = -(T * w2) := by linarith
    have e3 : c 0 3 = -(T * w3) := by linarith
    rw [e1, e2, e3]
    linear_combination (T ^ 2) * hw1 + (T * (w0 + 2 * w1) - 3) * hTw
  have hp1 : -1/2 < p1 := by
    have : 0 < T * w0 := mul_pos hT hw0
    linarith
  set X : ℝ := -1/2 + (p1 + 1/2) / 2 with hX
  have hX1 : -1/2 < X := by rw [hX]; linarith
  have hXlt : (2 + X) ^ 2 < (2 + p1) ^ 2 := by
    have h1 : 0 < 2 + X := by linarith
    have h2 : 2 + X < 2 + p1 := by rw [hX]; linarith
    nlinarith
  have hT2pos : 0 < T ^ 2 := by positivity
  have hX9 : (2 + X) ^ 2 < 9 := by nlinarith [sq_nonneg (c 0 2), sq_nonneg (c 0 3)]
  have hle := hmax (dd X) 1 one_pos (dd_timelike X hX1 hX9) (dd_start X)
    (by rw [dd_end, hcT])
  rw [pt_dd, hpc] at hle
  have hlt : T < Real.sqrt (9 - (2 + X) ^ 2) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [sq_nonneg (c 0 2), sq_nonneg (c 0 3)]
  linarith

end MRDisE

open MathematicalRelativity in
theorem solution : ¬ (∀ (m : Spacetime) (S : Slice m) (q : Pt)
    (hcauchy : m.IsCauchySurface S.carrier)
    (hq : q ∈ m.chronFuture S.carrier),
    ∃ (c : ℝ → Pt) (T : ℝ), 0 < T ∧ m.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T) ∧
      S.OrthogonalAt c 0 ∧ c T = q ∧ S.MaximizesFromSlice c T) := by
  intro H
  obtain ⟨c, T, hT, hgeo, horth, hcT, hmax⟩ :=
    H MRDisE.skew MRDisE.slc MRDisE.qE MRDisE.skew_cauchy MRDisE.q_mem
  exact MRDisE.no_max c T hT hgeo horth.1 hcT hmax

