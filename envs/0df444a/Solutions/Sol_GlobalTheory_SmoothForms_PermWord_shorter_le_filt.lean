-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.shorter_le_filt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:14.62788+00:00
-- url     : https://prove2.me/submissions/8b523123-593e-44c8-ac1c-bb323fa5ccd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_wd_ofFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution (E : Fin n → Fin n → A) (d : ℕ) : shorter E d ≤ filt E d := by
  rw [shorter, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  refine Submodule.mem_iSup_of_mem l.length (Submodule.mem_iSup_of_mem hl ?_)
  refine ⟨Matrix.single (fun a => (l.get a).1) (fun a => (l.get a).2) 1, ?_⟩
  conv_rhs => rw [← List.ofFn_get l]
  rw [show (List.ofFn l.get) = List.ofFn fun a => ((l.get a).1, (l.get a).2) from rfl, wd_ofFn]
  simp only [wordMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (fun a => (l.get a).1), Finset.sum_eq_single (fun a => (l.get a).2)]
  · simp
  · intro K _ hK
    rw [Matrix.single_apply_of_col_ne _ _ hK.symm, zero_smul]
  · simp
  · intro I _ hI
    refine Finset.sum_eq_zero fun K _ => ?_
    rw [Matrix.single_apply_of_row_ne hI.symm, zero_smul]
  · simp
end GlobalTheory.SmoothForms.PermWord
