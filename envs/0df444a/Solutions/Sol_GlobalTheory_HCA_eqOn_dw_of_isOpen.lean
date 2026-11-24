-- Prove2me | solution 1 for GlobalTheory.HCA.eqOn_dw_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:04.77169+00:00
-- url     : https://prove2.me/submissions/a8753531-2f38-4d14-9d09-75896b955faf

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
    (u v : _root_.ZetaZeros.D.EllReg.E d → ℂ) (h : Set.EqOn u v U) : Set.EqOn (_root_.ZetaZeros.D.EllReg.dw w u) (_root_.ZetaZeros.D.EllReg.dw w v) U := by
  induction w with
  | nil => exact h
  | cons j w ih =>
    obtain ⟨e, he⟩ := exists_dir_dw_cons_eq_fderiv j
    intro x hx
    rw [he, he, (ih.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq]
end _root_.GlobalTheory.HCA
end GlobalTheory.HCA
