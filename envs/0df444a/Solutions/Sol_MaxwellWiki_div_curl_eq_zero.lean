-- Prove2me | solution 1 for MaxwellWiki.div_curl_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:29:19.532986+00:00
-- url     : https://prove2.me/submissions/1856a553-bbdc-4209-ad66-962a19e8624c

import Mathlib
import Definitions.Def_MaxwellWiki_Defs
set_option autoImplicit false
open MaxwellWiki

private theorem partial_diff (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (partialDeriv i f) := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem partial_sub (f g : Vec3 → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Vec3) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  unfold partialDeriv
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

private theorem partial_comm (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Vec3) : partialDeriv i (partialDeriv j f) x = partialDeriv j (partialDeriv i f) x := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  unfold partialDeriv
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (Pi.single i 1) (Pi.single j 1)

theorem solution (F : Vec3 → Vec3) (hF : ContDiff ℝ 2 F) (x : Vec3) :
    div (curl F) x = 0 := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => F y i) := (contDiff_apply ℝ ℝ i).comp hF
  change partialDeriv 0 (fun y => partialDeriv 1 (fun z => F z 2) y - partialDeriv 2 (fun z => F z 1) y) x +
    (partialDeriv 1 (fun y => partialDeriv 2 (fun z => F z 0) y - partialDeriv 0 (fun z => F z 2) y) x +
    (partialDeriv 2 (fun y => partialDeriv 0 (fun z => F z 1) y - partialDeriv 1 (fun z => F z 0) y) x + 0)) = 0
  rw [partial_sub _ _ (partial_diff _ (hc 2) 1) (partial_diff _ (hc 1) 2),
    partial_sub _ _ (partial_diff _ (hc 0) 2) (partial_diff _ (hc 2) 0),
    partial_sub _ _ (partial_diff _ (hc 1) 0) (partial_diff _ (hc 0) 1)]
  rw [partial_comm _ (hc 2) 0 1, partial_comm _ (hc 1) 0 2, partial_comm _ (hc 0) 1 2]
  ring
