-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:23.237835+00:00
-- url     : https://prove2.me/submissions/b2f374cc-80cd-4d3f-8895-30615b9592b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped SchwartzMap ContDiff
namespace GlobalTheory.SchwartzTranslate
private theorem fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : V) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : V → F), ContDiff ℝ ∞ g →
      ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by
  induction n with
  | zero =>
    intro F _ _ g hg x m
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ g hg x m
    have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    have hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y)
        = fun y => fderiv ℝ (fderiv ℝ g) y a := by
      funext y
      ext w
      rw [fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]
      simp
      have h2le : minSmoothness ℝ 2 ≤ ∞ := by simp; exact WithTop.coe_le_coe.mpr le_top
      exact (ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a
    simp_rw [iteratedFDeriv_succ_apply_right]
    rw [fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]
    simp
    rw [ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]
end GlobalTheory.SchwartzTranslate
end

set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzTranslate
namespace GlobalTheory.SchwartzTranslate
theorem _root_.solution {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m :=
  fun g hg x m => fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m
end GlobalTheory.SchwartzTranslate
