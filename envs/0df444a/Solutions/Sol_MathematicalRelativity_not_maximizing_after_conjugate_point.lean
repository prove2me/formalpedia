-- Prove2me | solution 1 for MathematicalRelativity.not_maximizing_after_conjugate_point
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T11:58:43.879976+00:00
-- url     : https://prove2.me/submissions/fff617d3-b8fa-4169-b7d7-fb2a5fac9d64

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

/-! Disproof of a01ceee1 `MathematicalRelativity.not_maximizing_after_conjugate_point`.

`ConjugateToSlice` and `IsJacobiFieldOn` use `deriv`, which is the two-sided derivative and is
`0` wherever the function is not differentiable. The Jacobi equation and the initial condition
are imposed at the closed endpoint `t = 0`, where the field's values for `t < 0` are free.
So a field with a jump at `0` satisfies the endpoint conditions vacuously.

Counterexample: Minkowski space, the flat slice `x⁰ = 0` with normal `∂₀`, the vertical unit
geodesic `c t = (t, 0, 0, 0)` on `[0, 2]`, and `t* = 1`. The field `Y t = (t - 1) ∂₁` for
`t ≥ 0` and `Y t = 0` for `t < 0` solves `Y'' = 0` on `(0, 1]`. At `0` both `deriv Y` and
`deriv (deriv Y)` are `0` because of the jump, so it is a "Jacobi field" on `[0, 1]`. It is
tangent to the slice at `0`, satisfies `∇Y = ∇_Y N = 0` there, vanishes at `1`, and is nonzero
at `0`. So `c 1` is formally conjugate to the slice.

The vertical line still maximizes proper time from the slice: for any future timelike `d` from
the slice to `(2, 0, 0, 0)`, `√(-⟪d', d'⟫) ≤ (d⁰)'`, so the proper time of `d` is at most
`d⁰(T') - d⁰(0) = 2`, which is the proper time of `c`. -/

set_option autoImplicit false

open scoped ContDiff
open Filter Topology

namespace MRDisA

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

/-- The vertical line `t ↦ (t, 0, 0, 0)`. -/
def vert (t : ℝ) : Pt := fun a => if a = 0 then t else 0

theorem vel_vert (t : ℝ) : vel vert t = e0 := by
  funext a
  fin_cases a <;> simp [vel, vert, e0]

theorem acc_vert (t : ℝ) (a : Fin 4) : acc vert t a = 0 := by
  have h : (fun s => deriv (fun u => vert u a) s) = fun _ => e0 a :=
    funext fun s => congrFun (vel_vert s) a
  simp only [acc, h, deriv_const]

theorem mink_covD (c Y : ℝ → Pt) (t : ℝ) (a : Fin 4) :
    mink.covDAlong c Y t a = deriv (fun s => Y s a) t := by
  simp [Spacetime.covDAlong, mink_chr]

theorem vert_geo (T : ℝ) : mink.IsUnitTimelikeGeodesicOn vert (Set.Icc 0 T) := by
  refine ⟨⟨⟨fun a => ?_, fun t _ a => ?_⟩, fun t _ => ⟨?_, ?_⟩⟩, fun t _ => ?_⟩
  · fin_cases a <;> simp [vert] <;> fun_prop
  · simp [acc_vert, mink_chr]
  · simp [Spacetime.IsTimelike, vel_vert, mink_ip, e0]
  · simp [Spacetime.IsFuture, vel_vert, e0]
  · simp [vel_vert, mink_ip, e0]

theorem vert_orth : flat.OrthogonalAt vert 0 := by
  refine ⟨?_, ?_⟩
  · simp [Slice.carrier, flat, vert]
  · rw [vel_vert]; rfl

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

theorem Yj_jacobi : mink.IsJacobiFieldOn vert Yj (Set.Icc 0 1) := by
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

theorem conj : flat.ConjugateToSlice vert 0 1 := by
  refine ⟨Yj, Yj_jacobi, ⟨0, by simp, ?_⟩, ?_, fun a => ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp [Yj, yj] at this
  · simp [mink_ip, flat, e0, Yj]
  · have hN : ∀ b, mink.covVec flat.N a b (vert 0) = 0 := by
      intro b
      simp [Spacetime.covVec, mink_chr, flat, pd]
    simp only [hN, zero_mul, Finset.sum_const_zero, mink_covD]
    by_cases ha : a = 1
    · subst ha
      simpa [Yj] using deriv_yj_zero
    · simp [Yj, ha]
  · funext a
    simp [Yj, yj]

theorem properTime_vert : mink.properTime vert 0 2 = 2 := by
  simp [Spacetime.properTime, vel_vert, mink_ip, e0]

theorem vert_max : flat.MaximizesFromSlice vert 2 := by
  intro d T' hT' hd hd0 hdT
  rw [properTime_vert]
  have hd0' : d 0 0 = 0 := by simpa [Slice.carrier, flat] using hd0
  have hdT0 : d T' 0 = 2 := by rw [hdT]; simp [vert]
  unfold Spacetime.properTime
  by_cases hint : IntervalIntegrable
      (fun t => √(-(mink.ip (d t) (vel d t) (vel d t)))) MeasureTheory.volume 0 T'
  · have key := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
      (g := fun s => d s 0) (g' := fun s => vel d s 0) hT'.le ((hd.1 0).continuousOn)
      (fun x hx => by
        have hx' : Set.Icc 0 T' ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
        have hda : DifferentiableAt ℝ (fun s => d s 0) x :=
          ((hd.1 0).contDiffAt hx').differentiableAt (by norm_num)
        exact hda.hasDerivAt.hasDerivWithinAt)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT'.le).mp hint)
      (fun x hx => by
        obtain ⟨htl, hfu⟩ := hd.2 x (Set.Ioo_subset_Icc_self hx)
        rw [Spacetime.IsTimelike, mink_ip] at htl
        rw [Spacetime.IsFuture] at hfu
        rw [mink_ip, Real.sqrt_le_iff]
        refine ⟨hfu.le, ?_⟩
        nlinarith [sq_nonneg (vel d x 1), sq_nonneg (vel d x 2), sq_nonneg (vel d x 3)])
    simp only [hd0', hdT0] at key
    linarith
  · rw [intervalIntegral.integral_undef hint]
    norm_num

end MRDisA

open MathematicalRelativity in
theorem solution : ¬ (∀ (m : Spacetime) (S : Slice m) (c : ℝ → Pt) (T tstar : ℝ)
    (hgeo : m.IsUnitTimelikeGeodesicOn c (Set.Icc 0 T))
    (horth : S.OrthogonalAt c 0)
    (ht : tstar ∈ Set.Ioo (0:ℝ) T)
    (hconj : S.ConjugateToSlice c 0 tstar),
    ¬ S.MaximizesFromSlice c T) := by
  intro H
  exact H MRDisA.mink MRDisA.flat MRDisA.vert 2 1 (MRDisA.vert_geo 2) MRDisA.vert_orth
    ⟨by norm_num, by norm_num⟩ MRDisA.conj MRDisA.vert_max

