-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_int_vecMul_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:18:47.186015+00:00
-- url     : https://prove2.me/submissions/60b32ae4-c9a9-4b14-b8aa-f310b3c45a44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MinkowskiLinearForms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Theorems.Thm_GlobalTheory_MinkowskiLinearForms_minkowski_linear_forms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open MeasureTheory Module Submodule NumberField Matrix
namespace GlobalTheory.HermClass
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.det ≠ 0) {t : ℝ} (ht : 0 < t) (h : |A.det| < t ^ Fintype.card ι) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ j, |∑ i, (z i : ℝ) * A i j| < t := by
  first
  | exact @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms
  | (apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MinkowskiLinearForms.minkowski_linear_forms ..)
end GlobalTheory.HermClass
