-- Prove2me | solution 1 for MaxwellWiki.timeDeriv_div_comm
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:30:26.995827+00:00
-- url     : https://prove2.me/submissions/05915765-94a4-43bc-b451-919d0e1c55f5

import Mathlib
import Definitions.Def_MaxwellWiki_Defs
set_option autoImplicit false
open MaxwellWiki

private theorem space_slice (f : (ℝ × Vec3) → ℝ) (hf : Differentiable ℝ f)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    partialDeriv i (fun y => f (t,y)) x = fderiv ℝ f (t,x) (0, Pi.single i 1) := by
  have hh := (hf (t,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold partialDeriv
  change HasFDerivAt (fun y => f (t,y)) _ x at hh
  rw [hh.fderiv]
  rfl

private theorem time_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × Vec3) → V) (hf : Differentiable ℝ f) (t : ℝ) (x : Vec3) :
    deriv (fun s => f (s,x)) t = fderiv ℝ f (t,x) (1,0) := by
  have hh := (hf (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hh.deriv

private theorem dir_diff (f : (ℝ × Vec3) → ℝ) (hf : ContDiff ℝ 2 f) (v : ℝ × Vec3) :
    Differentiable ℝ (fun p => fderiv ℝ f p v) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem mixed (f : (ℝ × Vec3) → ℝ) (hf : ContDiff ℝ 2 f)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    deriv (fun s => partialDeriv i (fun y => f (s,y)) x) t =
      partialDeriv i (fun y => deriv (fun s => f (s,y)) t) x := by
  have hd := hf.differentiable (by norm_num)
  have hs : (fun s => partialDeriv i (fun y => f (s,y)) x) =
      fun s => fderiv ℝ f (s,x) (0, Pi.single i 1) := funext fun s => space_slice f hd s x i
  have ht : (fun y => deriv (fun s => f (s,y)) t) =
      fun y => fderiv ℝ f (t,y) (1,0) := funext fun y => time_slice f hd t y
  rw [hs, ht, time_slice _ (dir_diff f hf _), space_slice _ (dir_diff f hf _)]
  have hd' := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _),
    fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (1,0) (0,Pi.single i 1)

theorem solution (F : ℝ → Vec3 → Vec3) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (t : ℝ) (x : Vec3) :
    timeDeriv (fun s y => div (F s) y) t x = div (fun y => timeDeriv F t y) x := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun p : ℝ × Vec3 => F p.1 p.2 i) :=
    (contDiff_apply ℝ ℝ i).comp hF
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun s => partialDeriv i (fun y => F s y i) x) t := by
    have he : (fun s => partialDeriv i (fun y => F s y i) x) =
        fun s => fderiv ℝ (fun p : ℝ × Vec3 => F p.1 p.2 i) (s,x) (0,Pi.single i 1) :=
      funext fun s => space_slice _ ((hc i).differentiable (by norm_num)) s x i
    rw [he]
    exact ((dir_diff _ (hc i) _).comp ((differentiable_id).prodMk (differentiable_const x))).differentiableAt
  have htime (y : Vec3) : timeDeriv F t y = fun i => deriv (fun s => F s y i) t := by
    unfold timeDeriv
    apply deriv_pi
    intro i
    exact (((hc i).differentiable (by norm_num)).comp
      (differentiable_id.prodMk (differentiable_const y))).differentiableAt
  change deriv (fun s => ∑ i, partialDeriv i (fun y => F s y i) x) t = _
  rw [deriv_fun_sum (fun i _ => hd i)]
  unfold div
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [htime]
  exact mixed _ (hc i) t x i
