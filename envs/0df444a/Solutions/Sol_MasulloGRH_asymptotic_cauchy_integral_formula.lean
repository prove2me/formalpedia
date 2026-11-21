-- Prove2me | solution 1 for MasulloGRH.asymptotic_cauchy_integral_formula
-- status  : ACCEPTED   (disprove)
-- author  : @Yi
-- created : 2026-11-21T04:38:00.692579+00:00
-- url     : https://prove2.me/submissions/f2d8666d-1130-4c83-bc02-66ef2b08f198

import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Complex Set Filter MeasureTheory Topology Asymptotics
open scoped ComplexConjugate Topology

namespace MasulloGRH

private noncomputable def nf_tractKernel (z w : ℂ) : ℂ :=
  Complex.exp (2*z*w-(1+w)*Complex.log (1+w))

private noncomputable def nf_tract (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (0:ℝ), nf_tractKernel z (x:ℂ)

private lemma nf_tractRealLog {x : ℝ} (hx : 0 ≤ x) :
    Complex.log (1+(x:ℂ)) = (Real.log (1+x) : ℂ) := by
  simpa using (Complex.ofReal_log (show 0 ≤ 1+x by linarith)).symm

private lemma nf_tractKernel_norm (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖nf_tractKernel z (x : ℂ)‖ = Real.exp (2*z.re*x-(1+x)*Real.log (1+x)) := by
  simp [nf_tractKernel, Complex.norm_exp, nf_tractRealLog hx, Complex.mul_re]

private noncomputable def nf_tractA (M : ℝ) : ℝ := (2*M+3) * Real.exp (2*M+3)

private theorem nf_tract_log_bound {u x M : ℝ} (hu : u ≤ M) (hM : 0 ≤ M) (hx : 0 ≤ x) :
    2*u*x - (1+x)*Real.log (1+x) ≤ nf_tractA M - 2*x := by
  have hlog : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
  have hux : 2*u*x ≤ 2*M*x := by gcongr
  have hA : 0 ≤ nf_tractA M := by dsimp [nf_tractA]; positivity
  by_cases h : 2*M+3 ≤ Real.log (1+x)
  · nlinarith [mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ 1+x)]
  · have hel : 1+x < Real.exp (2*M+3) := (Real.log_lt_iff_lt_exp (by linarith)).mp (lt_of_not_ge h)
    have hh : x ≤ Real.exp (2*M+3) := by linarith
    have h' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*M+3 by linarith)
    dsimp [nf_tractA]
    nlinarith [mul_nonneg (show 0 ≤ 1+x by linarith) hlog]

private theorem nf_tractEnv_integrable (u : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (2*u*x-(1+x)*Real.log (1+x))) (Set.Ioi 0) := by
  let M := |u|
  refine ((integrableOn_exp_neg_Ioi 0).const_mul (Real.exp (nf_tractA M))).mono' ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,Real.abs_exp,←Real.exp_add]
    have hx' : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    exact Real.exp_le_exp.mpr (by dsimp [M]; linarith only [nf_tract_log_bound (le_abs_self u) (abs_nonneg u) hx',hx'])

private theorem nf_tractEnv_tendsto (u : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (2*u*x-(1+x)*Real.log (1+x))) atTop (𝓝 0) := by
  let M := |u|
  have hupper : Tendsto (fun x : ℝ => Real.exp (nf_tractA M) * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (Real.exp (nf_tractA M))
  apply squeeze_zero' (Eventually.of_forall (fun x => (Real.exp_pos _).le)) _ hupper
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  rw [←Real.exp_add]
  exact Real.exp_le_exp.mpr (by dsimp [M]; linarith only [nf_tract_log_bound (le_abs_self u) (abs_nonneg u) hx,hx])

private lemma nf_tractKernel_cont (z : ℂ) :
    ContinuousOn (fun x : ℝ => nf_tractKernel z (x:ℂ)) (Ioi 0) := by
  apply ContinuousOn.congr (f := fun x : ℝ => Complex.exp (2*z*x-(1+x)*(Real.log (1+x):ℂ)))
  · apply Continuous.continuousOn Complex.continuous_exp |>.comp _ (mapsTo_univ ..)
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.mul
      · fun_prop
      · apply Complex.continuous_ofReal.comp_continuousOn
        apply ContinuousOn.log (by fun_prop)
        intro x hx
        have hx' : 0 < x := hx
        linarith
  · intro x hx
    simp [nf_tractKernel,nf_tractRealLog (mem_Ioi.mp hx).le]

private theorem nf_tractKernel_integrable (z : ℂ) :
    IntegrableOn (fun x : ℝ => nf_tractKernel z (x:ℂ)) (Ioi 0) := by
  refine (nf_tractEnv_integrable z.re).mono' ((nf_tractKernel_cont z).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
  exact (nf_tractKernel_norm z (mem_Ioi.mp hx).le).le

private theorem nf_tract_differentiable : Differentiable ℂ nf_tract := by
  intro z
  let M : ℝ := ‖z‖ + 1
  let G : ℂ → ℝ → ℂ := fun q x => (2*(x:ℂ))*nf_tractKernel q x
  have hd (q : ℂ) (x : ℝ) : HasDerivAt (fun v : ℂ => nf_tractKernel v x) (G q x) q := by
    have hh : HasDerivAt (fun v : ℂ => 2*v*(x:ℂ)-(1+(x:ℂ))*Complex.log (1+(x:ℂ))) (2*x) q := by
      convert! ((((hasDerivAt_id q).const_mul 2).mul_const (x:ℂ)).sub_const _) using 1; simp
    simpa [G,nf_tractKernel,mul_comm] using hh.cexp
  have hgb (x : ℝ) (hx : 0 ≤ x) (q : ℂ) (hq : q ∈ Metric.ball z 1) :
      ‖G q x‖ ≤ (2*Real.exp (nf_tractA M)) * Real.exp (-x) := by
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hqm : q.re ≤ M := by
      have hd := norm_sub_norm_le q z
      rw [← dist_eq_norm] at hd
      have hd' := Metric.mem_ball.mp hq
      have hr := Complex.re_le_norm q
      dsimp [M]; linarith
    have hk := Real.exp_le_exp.mpr (nf_tract_log_bound hqm hM hx)
    have hel : x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
    calc
      ‖G q x‖ = 2*x*Real.exp (2*q.re*x-(1+x)*Real.log (1+x)) := by
        simp [G, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
          nf_tractKernel_norm q hx]
      _ ≤ 2*Real.exp x * Real.exp (nf_tractA M - 2*x) := by gcongr
      _ = (2*Real.exp (nf_tractA M)) * Real.exp (-x) := by
        rw [mul_assoc,← Real.exp_add,mul_assoc,← Real.exp_add]
        congr 2; ring
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun q x => nf_tractKernel q (x:ℂ)) (F' := G)
    (bound := fun x : ℝ => (2*Real.exp (nf_tractA M))*Real.exp (-x))
    (Metric.ball_mem_nhds z (show (0:ℝ)<1 by norm_num))
    (Eventually.of_forall (fun q => (nf_tractKernel_cont q).aestronglyMeasurable measurableSet_Ioi))
    (nf_tractKernel_integrable z)
    (show AEStronglyMeasurable (G z) _ from
      (show ContinuousOn (G z) (Ioi 0) from
        (show Continuous (fun x : ℝ => 2*(x:ℂ)) by fun_prop).continuousOn.mul
          (nf_tractKernel_cont z)).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
        exact hgb x (mem_Ioi.mp hx).le)
    ((integrableOn_exp_neg_Ioi 0).const_mul (2*Real.exp (nf_tractA M)))
    (Eventually.of_forall (fun x q _ => hd q x))
  exact hder.2.differentiableAt

private theorem nf_tract_grows : ∀ᶠ u : ℝ in atTop, Real.exp u ≤ ‖nf_tract (u:ℂ)‖ := by
  filter_upwards [eventually_ge_atTop (3 * Real.log 3 + 1)] with u hu
  let f : ℝ → ℝ := fun x => Real.exp (2*u*x-(1+x)*Real.log (1+x))
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] f :=
    Eventually.of_forall (fun x => (Real.exp_pos _).le)
  have hsub : Icc (1:ℝ) 2 ⊆ Ioi 0 := fun x hx => by have := hx.1; change 0 < x; linarith
  have hfi : IntegrableOn f (Ioi 0) := nf_tractEnv_integrable u
  have heq : nf_tract (u:ℂ) = ((∫ x in Ioi (0:ℝ), f x) : ℝ) := by
    rw [nf_tract, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change nf_tractKernel (u:ℂ) (x:ℂ) = ((f x : ℝ) : ℂ)
    rw [nf_tractKernel,nf_tractRealLog (mem_Ioi.mp hx).le]
    dsimp [f]
    simp only [Complex.ofReal_exp, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hconst : (∫ _ in Icc (1:ℝ) 2, Real.exp u) = Real.exp u := by
    norm_num [Real.volume_real_Icc_of_le (show (1:ℝ) ≤ 2 by norm_num)]
  calc
    Real.exp u = ∫ _ in Icc (1:ℝ) 2, Real.exp u := hconst.symm
    _ ≤ ∫ x in Icc (1:ℝ) 2, f x := by
      apply setIntegral_mono_on (integrableOn_const (by simp)) (hfi.mono_set hsub) measurableSet_Icc
      intro x hx
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (1+x) ≤ Real.log 3 :=
        Real.log_le_log (by linarith [hx.1]) (by linarith [hx.2])
      have hB : (1+x)*Real.log (1+x) ≤ 3*Real.log 3 :=
        mul_le_mul (by linarith [hx.2]) hlog (Real.log_nonneg (by linarith [hx.1])) (by norm_num)
      have hu' : 0 ≤ u := by linarith [Real.log_nonneg (show (1:ℝ) ≤ 3 by norm_num)]
      nlinarith [mul_nonneg hu' (show 0 ≤ x-1 by linarith [hx.1])]
    _ ≤ ∫ x in Ioi (0:ℝ), f x :=
      setIntegral_mono_set hfi hpos (Eventually.of_forall hsub)
    _ ≤ ‖nf_tract (u:ℂ)‖ := by rw [heq,Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _


private theorem nf_tract_bound_abs (z : ℂ) (x y : ℝ) (hx : 0 ≤ x) :
    ‖nf_tractKernel z ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      Real.exp (2*z.re*x-(1+x)*Real.log (1+x)) *
        Real.exp (-2*z.im*y+Real.pi/2*|y|) := by
  let w : ℂ := (x : ℂ) + (y : ℂ)*Complex.I
  have hwr : (1 + w).re = 1+x := by simp [w]
  have hwi : (1 + w).im = y := by simp [w]
  have hnorm : 1+x ≤ ‖1+w‖ := hwr ▸ Complex.re_le_norm (1+w)
  have hlog : Real.log (1+x) ≤ Real.log ‖1+w‖ := Real.log_le_log (by linarith) hnorm
  have hlog' := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1+x)
  have harg : |(1+w).arg| ≤ Real.pi/2 := Complex.abs_arg_le_pi_div_two_iff.mpr (by rw [hwr]; linarith)
  have harg' : y*(1+w).arg ≤ Real.pi/2*|y| := by
    calc
      _ ≤ |y*(1+w).arg| := le_abs_self _
      _ = |(1+w).arg| * |y| := by rw [abs_mul,mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right harg (abs_nonneg _)
  change ‖Complex.exp (2*z*w-(1+w)*Complex.log (1+w))‖ ≤ _
  rw [Complex.norm_exp, ← Real.exp_add,Real.exp_le_exp]
  simp only [Complex.sub_re,Complex.mul_re,Complex.log_re,Complex.log_im,hwr,hwi]
  simp [w, Complex.mul_re, Complex.mul_im] at *
  nlinarith

private theorem nf_tract_bound_up (z : ℂ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖nf_tractKernel z ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      Real.exp (2*z.re*x-(1+x)*Real.log (1+x)) *
        Real.exp (-(2*z.im-Real.pi/2)*y) := by
  convert nf_tract_bound_abs z x y hx using 2
  rw [abs_of_nonneg hy]
  congr 1
  ring

private theorem nf_tract_bound_down (z : ℂ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖nf_tractKernel z ((x:ℂ)-(y:ℂ)*Complex.I)‖ ≤
      Real.exp (2*z.re*x-(1+x)*Real.log (1+x)) *
        Real.exp (-(2*(-z.im)-Real.pi/2)*y) := by
  have h := nf_tract_bound_abs z x (-y) hx
  rw [abs_neg,abs_of_nonneg hy] at h
  convert h using 2 <;> push_cast <;> ring_nf

private theorem nf_tract_rect_bound (z : ℂ) (hz : 1 ≤ 2*z.im-Real.pi/2)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖nf_tractKernel z ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      Real.exp (2*z.re*x-(1+x)*Real.log (1+x))*Real.exp (-y) := by
  apply (nf_tract_bound_up z x y hx hy).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hz hy]

private theorem nf_tract_norm_conj (z : ℂ) : ‖nf_tract (star z)‖ = ‖nf_tract z‖ := by
  have h : nf_tract (star z) = conj (nf_tract z) := by
    rw [nf_tract,nf_tract,←integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change Complex.exp _ = conj (Complex.exp _)
    rw [←Complex.exp_conj]
    have hpos : 0 ≤ (1+x) := by linarith [show 0<x from hx]
    have hbase : 1+(x:ℂ) = ((1+x:ℝ):ℂ) := by push_cast; rfl
    rw [hbase,←Complex.ofReal_log hpos]
    congr 1
    simp [map_ofNat]
  rw [h,Complex.norm_conj]



open Complex MeasureTheory Set Filter
open scoped Topology

private theorem nf_partial_major (f : ℝ → ℂ) (g : ℝ → ℝ)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hgi : IntegrableOn g (Ioi 0))
    (hg : ∀ x, 0 ≤ x → 0 ≤ g x) (h : ∀ x, 0 ≤ x → x ≤ R → ‖f x‖ ≤ g x * C) :
    ‖∫ t in 0..R, f t‖ ≤ (∫ t in Ioi 0, g t) * C := by
  rw [intervalIntegral.integral_of_le hR]
  have sub : Ioc 0 R ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
  have hj : IntegrableOn (fun x => g x * C) (Ioc 0 R) := (hgi.mono_set sub).mul_const C
  calc
    _ ≤ ∫ t in Ioc 0 R, g t * C := norm_integral_le_of_norm_le hj
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => h x hx.1.le hx.2)
    _ = (∫ t in Ioc 0 R, g t)*C := integral_mul_const C _
    _ ≤ _ := mul_le_mul_of_nonneg_right (setIntegral_mono_set hgi
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => hg x hx.le) (.of_forall sub)) hC

private theorem nf_rect_identity (z : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in 0..R, nf_tractKernel z (x:ℂ)) =
      (∫ x in 0..R, nf_tractKernel z ((x:ℂ)+(R:ℂ)*I)) -
      I*(∫ y in 0..R, nf_tractKernel z ((R:ℂ)+(y:ℂ)*I)) +
      I*(∫ y in 0..R, nf_tractKernel z ((y:ℂ)*I)) := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (nf_tractKernel z) 0 (⟨R,R⟩ : ℂ) (by
      intro w hw
      have hmem : w.re ∈ Set.uIcc 0 R := hw.1
      have hw0 : 0 ≤ w.re := (Set.uIcc_of_le hR ▸ hmem).1
      have hslit : 1+w ∈ Complex.slitPlane := Or.inl (by simp; linarith)
      have hlog := (Complex.differentiableAt_log hslit).comp w ((differentiableAt_const (c := (1:ℂ))).add differentiableAt_id)
      exact (Complex.differentiableAt_exp.comp w
        (((differentiableAt_const (c := 2*z)).mul differentiableAt_id).sub
        (((differentiableAt_const (c := (1:ℂ))).add differentiableAt_id).mul hlog))).differentiableWithinAt)
  simp only [Complex.zero_re, Complex.zero_im, zero_mul, Complex.ofReal_zero,
    add_zero, zero_add, smul_eq_mul] at hh
  linear_combination hh

private theorem nf_tract_bound_above (z : ℂ) (hz : 1 ≤ 2*z.im - Real.pi/2) :
    ‖nf_tract z‖ ≤ 1 := by
  let E := fun x : ℝ => Real.exp (2*z.re*x - (1+x)*Real.log (1+x))
  let A := ∫ x in Ioi 0, E x
  have hE : IntegrableOn E (Ioi 0) := nf_tractEnv_integrable z.re
  have bnd (R : ℝ) (hR : 0 ≤ R) :
      ‖∫ x in 0..R, nf_tractKernel z (x:ℂ)‖ ≤ A * Real.exp (-R) + E R + 1 := by
    have htop := nf_partial_major
      (fun x : ℝ => nf_tractKernel z ((x:ℂ)+(R:ℂ)*I)) E R (Real.exp (-R)) hR (Real.exp_pos _).le hE
      (fun _ _ => (Real.exp_pos _).le) (fun x hx _ => nf_tract_rect_bound z hz x R hx hR)
    have hright := nf_partial_major
      (fun y : ℝ => nf_tractKernel z ((R:ℂ)+(y:ℂ)*I))
      (fun y => Real.exp (-y)) R (E R) hR (Real.exp_pos _).le (integrableOn_exp_neg_Ioi 0)
      (fun _ _ => (Real.exp_pos _).le) (fun y hy _ => (nf_tract_rect_bound z hz R y hR hy).trans_eq (mul_comm ..))
    have hleft := nf_partial_major (fun y : ℝ => nf_tractKernel z ((y:ℂ)*I))
      (fun y => Real.exp (-y)) R 1 hR zero_le_one (integrableOn_exp_neg_Ioi 0)
      (fun _ _ => (Real.exp_pos _).le) (fun y hy _ => by simpa using nf_tract_rect_bound z hz 0 y le_rfl hy)
    rw [integral_exp_neg_Ioi_zero, one_mul] at hright hleft
    rw [nf_rect_identity z R hR]
    refine (norm_add_le ..).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    gcongr
    refine (norm_sub_le ..).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    exact add_le_add htop hright
  have hbottom := (intervalIntegral_tendsto_integral_Ioi 0 (nf_tractKernel_integrable z) tendsto_id).norm
  have hupper : Tendsto (fun R : ℝ => A * Real.exp (-R) + E R + 1) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := A)).mul (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)).add (nf_tractEnv_tendsto z.re) |>.add_const 1
  exact le_of_tendsto_of_tendsto hbottom hupper ((eventually_ge_atTop 0).mono fun R hR => bnd R hR)


private noncomputable def nf_damped (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  F (-s) * Complex.exp (-(Complex.sqrt (1-s)))

private theorem nf_damped_holo (F : ℂ → ℂ) (h : Differentiable ℂ F) :
    DifferentiableOn ℂ (nf_damped F) {s : ℂ | s.re < 0} := by
  intro s hs
  change s.re < 0 at hs
  have hslit : 1-s ∈ Complex.slitPlane := Or.inl (by simpa using (by linarith : 0 < 1 - s.re))
  have hsqrt : DifferentiableAt ℂ (fun z : ℂ => Complex.sqrt (1-z)) s :=
    (Complex.differentiableAt_sqrt hslit).comp s (by fun_prop)
  exact (((h (-s)).comp s differentiableAt_id.neg).mul
    (Complex.differentiableAt_exp.comp s hsqrt.neg)).differentiableWithinAt

private theorem nf_damped_rapid (F : ℂ → ℂ) (B R : ℝ)
    (hF : ∀ z : ℂ, R ≤ |z.im| → ‖F z‖ ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ,
        s.re ≤ 0 - ε → Y ≤ |s.im| → ‖nf_damped F s‖ ≤ C / |s.im| ^ N := by
  intro ε hε N _
  let A : ℝ := 2^N * ((2*N).factorial : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨1 + |B| * A, by positivity, max R 1, ?_⟩
  intro s hre him
  have hy : 0 < |s.im| := zero_lt_one.trans_le ((le_max_right ..).trans him)
  have hFB : ‖F (-s)‖ ≤ |B| := (hF (-s) (by simpa using ((le_max_left ..).trans him))).trans (le_abs_self B)
  let t := (Complex.sqrt (1-s)).re
  have ht : t = Real.sqrt ((‖1-s‖ + (1-s).re)/2) :=
    Complex.cpow_inv_two_re _
  have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
  have hr0 : 0 ≤ (1-s).re := by simp; linarith
  have hsq : t^2 = (‖1-s‖ + (1-s).re)/2 := by rw [ht,Real.sq_sqrt (by positivity)]
  have hysq : |s.im| ≤ 2*t^2 := by
    have him' : |s.im| ≤ ‖1-s‖ := by simpa using Complex.abs_im_le_norm (1-s)
    linarith
  have htN : t^(2*N) ≤ Real.exp t * ((2*N).factorial : ℝ) :=
    (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp t ht0 (2*N))
  have hdec : |s.im| ^ N ≤ A * Real.exp t := calc
    |s.im| ^ N ≤ (2*t^2)^N := pow_le_pow_left₀ hy.le hysq N
    _ = 2^N * t^(2*N) := by rw [mul_pow, pow_mul]
    _ ≤ 2^N * (Real.exp t * ((2*N).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left htN (by positivity)
    _ = _ := by dsimp [A]; ring
  have hd : ‖nf_damped F s‖ = ‖F (-s)‖ / Real.exp t := by
    simp [nf_damped,Complex.norm_exp,Real.exp_neg,div_eq_mul_inv,t]
  rw [hd]
  apply (le_div_iff₀ (pow_pos hy _)).mpr
  calc
    ‖F (-s)‖ / Real.exp t * |s.im| ^ N ≤ (|B| / Real.exp t) * (A * Real.exp t) :=
      mul_le_mul (div_le_div_of_nonneg_right hFB (Real.exp_pos _).le) hdec (by positivity) (by positivity)
    _ = |B| * A := by field_simp
    _ ≤ _ := by linarith

private theorem nf_damped_grows (F : ℂ → ℂ)
    (hF : ∀ᶠ x : ℝ in atTop, Real.exp x ≤ ‖F (x : ℂ)‖) :
    Tendsto (fun x : ℝ => ‖nf_damped F (-x)‖) atTop atTop := by
  have hhalf : Tendsto (fun x : ℝ => x/2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp hhalf)
  filter_upwards [hF, eventually_ge_atTop (6:ℝ)] with x hFx hx
  have hs : Real.sqrt (1+x) ≤ x/2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ x-6)]
  have hrex : (Complex.sqrt (1 + (x : ℂ))).re = Real.sqrt (1+x) := by
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using (Complex.re_sqrt_ofReal (a := 1+x))
  calc
    Real.exp (x / 2) ≤ Real.exp (x - Real.sqrt (1+x)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp x / Real.exp (Real.sqrt (1+x)) := Real.exp_sub _ _
    _ ≤ ‖F (x : ℂ)‖ / Real.exp (Real.sqrt (1+x)) :=
      div_le_div_of_nonneg_right hFx (Real.exp_pos _).le
    _ = ‖nf_damped F (-x)‖ := by simp [nf_damped,Complex.norm_exp,Real.exp_neg,div_eq_mul_inv,hrex]




private theorem nf_cauchy_left_bound (Φ : ℂ → ℂ) (d : ℝ) (c z : ℂ)
    (hint : VerticalLineIntegrable Φ d) (hz : z.re < d) :
    ‖c * verticalLineIntegral (fun s => Φ s / (s-z)) d‖ ≤
      (‖c‖ * ∫ y : ℝ, ‖Φ (d+y*Complex.I)‖) / (d-z.re) := by
  have hnorm (y : ℝ) : d-z.re ≤ ‖(d : ℂ)+y*Complex.I-z‖ := by
    calc
      d-z.re = ((d : ℂ)+y*Complex.I-z).re := by simp
      _ ≤ _ := Complex.re_le_norm _
  have hb (y : ℝ) : ‖Φ (d+y*Complex.I)/((d : ℂ)+y*Complex.I-z)‖ ≤
      ‖Φ (d+y*Complex.I)‖ / (d-z.re) := by
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hz) (hnorm y)
  have h := norm_integral_le_of_norm_le (hint.norm.div_const (d-z.re)) (.of_forall hb)
  rw [integral_div] at h
  simpa [verticalLineIntegral, norm_mul, mul_div_assoc] using
    mul_le_mul_of_nonneg_left h (norm_nonneg c)

private theorem nf_cauchy_left_decay (Φ : ℂ → ℂ) (d : ℝ) (c : ℂ)
    (hint : VerticalLineIntegrable Φ d)
    (hrep : ∀ z : ℂ, z.re < d →
      c * verticalLineIntegral (fun s => Φ s / (s-z)) d = Φ z) :
    Tendsto (fun x : ℝ => Φ (x : ℂ)) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hden : Tendsto (fun x : ℝ => d-x) atBot atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_left atBot d tendsto_neg_atBot_atTop
  have hlim : Tendsto (fun x : ℝ => (‖c‖ * ∫ y : ℝ, ‖Φ (d+y*Complex.I)‖)/(d-x))
      atBot (𝓝 0) := tendsto_const_nhds.div_atTop hden
  refine squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_lt_atBot d] with x hx
  simpa only [hrep _ (show (x : ℂ).re < d from hx), Complex.ofReal_re] using
    nf_cauchy_left_bound Φ d c (x : ℂ) hint hx

private theorem nf_cauchy_lineL1 (Φ : ℂ → ℂ) (b d : ℝ) (hd : d < b)
    (hc : ContinuousOn Φ {z : ℂ | z.re < b}) (hS : SchwartzOnLeftHalfPlane Φ b) :
    VerticalLineIntegrable Φ d := by
  let F : ℝ → ℂ := fun y => Φ (d+y*Complex.I)
  have hline : Continuous F := by
    apply hc.comp_continuous (f := fun y : ℝ => (d : ℂ) + y*Complex.I)
    · fun_prop
    · intro y
      simpa using hd
  obtain ⟨C,hC,Y,hY⟩ := hS (b-d) (sub_pos.mpr hd) 2 (by norm_num)
  have hB (y : ℝ) (hy : max Y 1 ≤ |y|) :
      ‖F y‖ ≤ (2*C) * ‖(1+y^2)⁻¹‖ := by
    have ht := hY ((d : ℂ)+y*Complex.I) (by simp) (by simpa using (le_max_left Y 1).trans hy)
    have hy1 := (le_max_right Y 1).trans hy
    change ‖Φ _‖ ≤ _
    calc
      _ ≤ C / y^2 := by simpa using ht
      _ ≤ _ := by
        have hy2 : 1 ≤ y^2 := by nlinarith [sq_abs y, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hy1]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity : 0 < y^2) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hy2 hC.le]
  unfold VerticalLineIntegrable
  change Integrable F
  apply hline.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun y : ℝ => (1+y^2)⁻¹) (g' := fun y : ℝ => (1+y^2)⁻¹)
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_le_atBot (-max Y 1)] with y hy
    exact hB y (by linarith [neg_le_abs y])
  · exact integrable_inv_one_add_sq.integrableAtFilter _
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_ge_atTop (max Y 1)] with y hy
    exact hB y (hy.trans (le_abs_self _))
  · exact integrable_inv_one_add_sq.integrableAtFilter _

private theorem nf_cauchy_claim_excludes (hClaim : (∀ (a b : ℝ) (Φ : ℂ → ℂ), a < b → DifferentiableOn ℂ Φ (openStrip a b) →
      UniformlySchwartzOnStrip Φ a b → ∀ ε : ℝ, 0 < ε → a + ε < b - ε → ∀ (N : ℕ) (z : ℂ),
      let g : ℂ → ℂ := fun s => Φ s / (s - z) ^ (N + 1)
      let c : ℂ := (N.factorial : ℂ) / (2 * Real.pi * Complex.I)
      (z ∈ openStrip (a + ε) (b - ε) →
        VerticalLineIntegrable g (a + ε) ∧ VerticalLineIntegrable g (b - ε) ∧
        -(c * verticalLineIntegral g (a + ε)) + c * verticalLineIntegral g (b - ε) =
          iteratedDeriv N Φ z) ∧
      (z ∉ closedStrip (a + ε) (b - ε) →
        VerticalLineIntegrable g (a + ε) ∧ VerticalLineIntegrable g (b - ε) ∧
        -(c * verticalLineIntegral g (a + ε)) + c * verticalLineIntegral g (b - ε) = 0)) ∧
    (∀ (b : ℝ) (Φ : ℂ → ℂ), DifferentiableOn ℂ Φ {s : ℂ | s.re < b} →
      SchwartzOnLeftHalfPlane Φ b → ∀ ε : ℝ, 0 < ε → ∀ (N : ℕ) (z : ℂ),
      let g : ℂ → ℂ := fun s => Φ s / (s - z) ^ (N + 1)
      let c : ℂ := (N.factorial : ℂ) / (2 * Real.pi * Complex.I)
      (z.re < b - ε →
        VerticalLineIntegrable g (b - ε) ∧ c * verticalLineIntegral g (b - ε) = iteratedDeriv N Φ z) ∧
      (b - ε < z.re →
        VerticalLineIntegrable g (b - ε) ∧ c * verticalLineIntegral g (b - ε) = 0)))
    (b : ℝ) (Φ : ℂ → ℂ) (hhol : DifferentiableOn ℂ Φ {s : ℂ | s.re < b})
    (hS : SchwartzOnLeftHalfPlane Φ b) :
    Tendsto (fun x : ℝ => Φ (x : ℂ)) atBot (𝓝 0) := by
  let d := b - 1
  have hdb : d < b := by dsimp [d]; linarith
  let c : ℂ := (1 : ℂ) / (2 * Real.pi * Complex.I)
  apply nf_cauchy_left_decay Φ d c (nf_cauchy_lineL1 Φ b d hdb hhol.continuousOn hS)
  intro z hz
  have hi := ((hClaim.2 b Φ hhol hS 1 (by norm_num) 0 z).1 hz).2
  simpa [c,d] using hi


end MasulloGRH

open MasulloGRH

theorem solution : ¬ (
    (∀ (a b : ℝ) (Φ : ℂ → ℂ), a < b → DifferentiableOn ℂ Φ (openStrip a b) →
      UniformlySchwartzOnStrip Φ a b → ∀ ε : ℝ, 0 < ε → a + ε < b - ε → ∀ (N : ℕ) (z : ℂ),
      let g : ℂ → ℂ := fun s => Φ s / (s - z) ^ (N + 1)
      let c : ℂ := (N.factorial : ℂ) / (2 * Real.pi * Complex.I)
      (z ∈ openStrip (a + ε) (b - ε) →
        VerticalLineIntegrable g (a + ε) ∧ VerticalLineIntegrable g (b - ε) ∧
        -(c * verticalLineIntegral g (a + ε)) + c * verticalLineIntegral g (b - ε) =
          iteratedDeriv N Φ z) ∧
      (z ∉ closedStrip (a + ε) (b - ε) →
        VerticalLineIntegrable g (a + ε) ∧ VerticalLineIntegrable g (b - ε) ∧
        -(c * verticalLineIntegral g (a + ε)) + c * verticalLineIntegral g (b - ε) = 0)) ∧
    (∀ (b : ℝ) (Φ : ℂ → ℂ), DifferentiableOn ℂ Φ {s : ℂ | s.re < b} →
      SchwartzOnLeftHalfPlane Φ b → ∀ ε : ℝ, 0 < ε → ∀ (N : ℕ) (z : ℂ),
      let g : ℂ → ℂ := fun s => Φ s / (s - z) ^ (N + 1)
      let c : ℂ := (N.factorial : ℂ) / (2 * Real.pi * Complex.I)
      (z.re < b - ε →
        VerticalLineIntegrable g (b - ε) ∧ c * verticalLineIntegral g (b - ε) = iteratedDeriv N Φ z) ∧
      (b - ε < z.re →
        VerticalLineIntegrable g (b - ε) ∧ c * verticalLineIntegral g (b - ε) = 0)) ) := by
  intro ho
  let Φ := nf_damped nf_tract
  have hp : SchwartzOnLeftHalfPlane Φ 0 := by
    apply nf_damped_rapid nf_tract 1 (Real.pi+1)
    intro z hz
    rcases le_total 0 z.im with hpos | hneg
    · rw [abs_of_nonneg hpos] at hz
      exact nf_tract_bound_above z (by linarith [Real.pi_pos])
    · rw [abs_of_nonpos hneg] at hz
      rw [← nf_tract_norm_conj z]
      apply nf_tract_bound_above
      simp
      linarith [Real.pi_pos]
  have hvan := nf_cauchy_claim_excludes ho 0 Φ (nf_damped_holo nf_tract nf_tract_differentiable) hp
  have hlim : Tendsto (fun x : ℝ => ‖nf_damped nf_tract (-x)‖) atTop (𝓝 0) := by
    simpa [Φ,Function.comp_def] using (hvan.comp tendsto_neg_atTop_atBot).norm
  exact not_tendsto_atTop_of_tendsto_nhds hlim (nf_damped_grows nf_tract nf_tract_grows)
