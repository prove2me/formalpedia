-- Prove2me | solution 1 for GlobalTheory.HCA.contDiffOn_dw_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:59.074999+00:00
-- url     : https://prove2.me/submissions/2c951f15-112b-4434-b370-9dbcf48d0e03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
namespace GlobalTheory.HCA
open MeasureTheory in
open scoped ContDiff BoundedContinuousFunction Topology in
private lemma exists_dir_dw_cons_eq_fderiv {d : ℕ} (j : Fin d) :
    ∃ e : _root_.ZetaZeros.D.EllReg.E d, ∀ (w : List (Fin d)) (f : _root_.ZetaZeros.D.EllReg.E d → ℂ) (x : _root_.ZetaZeros.D.EllReg.E d),
      _root_.ZetaZeros.D.EllReg.dw (j :: w) f x = fderiv ℝ (_root_.ZetaZeros.D.EllReg.dw w f) x e :=
  ⟨EuclideanSpace.single j 1, fun _ _ _ => rfl⟩
end GlobalTheory.HCA
end

set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
open MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
namespace GlobalTheory.HCA
namespace _root_.GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (_root_.ZetaZeros.D.EllReg.E d)} (hU : IsOpen U) (w : List (Fin d))
    (u : _root_.ZetaZeros.D.EllReg.E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) : ContDiffOn ℝ ∞ (_root_.ZetaZeros.D.EllReg.dw w u) U := by
  induction w with
  | nil => exact hu
  | cons j w ih =>
    obtain ⟨e, he⟩ := exists_dir_dw_cons_eq_fderiv j
    have h : _root_.ZetaZeros.D.EllReg.dw (j :: w) u = fun x => fderiv ℝ (_root_.ZetaZeros.D.EllReg.dw w u) x e := funext (he w u)
    rw [h]
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
end _root_.GlobalTheory.HCA
end GlobalTheory.HCA
