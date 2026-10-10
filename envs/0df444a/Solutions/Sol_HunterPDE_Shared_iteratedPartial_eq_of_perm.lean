-- Prove2me | solution 1 for HunterPDE.Shared.iteratedPartial_eq_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:18:44.018722+00:00
-- url     : https://prove2.me/submissions/9c8dca56-69b0-4de5-8fe1-f78c69943f85

import Theorems.Thm_HunterPDE_Shared_contDiffOn_iteratedPartial
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem solution {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {l t : List (Fin n)} (hp : l.Perm t) : Set.EqOn (iteratedPartial u l) (iteratedPartial u t) s := by
  induction hp with
  | nil => intro x hx; rfl
  | @cons i l t hp ih =>
    intro x hx
    exact congrArg (fun L => L (EuclideanSpace.single i 1))
      ((ih.eventuallyEq_of_mem (hs.mem_nhds hx)).fderiv_eq (𝕜 := ℝ))
  | swap i j l =>
    intro x hx
    have h := (HunterPDE.Shared.contDiffOn_iteratedPartial hs hu l x hx).contDiffAt (hs.mem_nhds hx)
    have hd := h.fderiv_right (m := ∞) (by simp)
    have hi := hd.differentiableAt (by simp)
    have hj := h.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
    change fderiv ℝ (fun z => fderiv ℝ (iteratedPartial u l) z (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single j 1) =
      fderiv ℝ (fun z => fderiv ℝ (iteratedPartial u l) z (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1)
    simp only [fderiv_clm_apply hi (differentiableAt_const _), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    exact hj _ _
  | trans hp hq ih ihq => exact ih.trans ihq
