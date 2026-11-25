-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:50.018795+00:00
-- url     : https://prove2.me/submissions/edec2277-f542-403f-b7f1-c3a2a8bbe153

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_eq_one
import Theorems.Thm_GroundTheory_Automorphic_Measures_transvection_mem_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (t : Matrix.TransvectionStruct ι F)
    (h : t.toMatrix.det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) = 1 := by
  classical
  obtain ⟨i, j, hij, c⟩ := t
  have h1 : ∀ d : F, (Matrix.transvection i j d).det ≠ 0 := fun d => by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact one_ne_zero
  let T : F → GL ι F := fun d => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h1 d)
  have hT : ∀ d d', T d * T d' = T (d + d') := fun d d' => by
    ext : 1
    simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.transvection_mul_transvection_same (h := hij)]
  have hT1 : distribHaarChar (ι → F) (glEquiv (T 1)) = 1 := by
    have hinv : (T 1)⁻¹ = T (-1) := by
      rw [inv_eq_iff_mul_eq_one, hT, add_neg_cancel]
      ext : 1
      simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    refine distribHaarChar_glEquiv_eq_one (fun a b => ?_) (fun a b => ?_)
    · exact transvection_mem_integer (Subring.one_mem _) a b
    · rw [hinv]
      exact transvection_mem_integer (Subring.neg_mem _ (Subring.one_mem _)) a b
  change distribHaarChar (ι → F) (glEquiv (T c)) = 1
  by_cases hc : c = 0
  · have : T c = 1 := by
      ext : 1
      simp [T, hc, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [this, map_one, map_one]
  let d : ι → F := Function.update 1 i c
  have hd : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simpa [d] using hc
    · simp [d, hk]
  let Dg : GL ι F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
  have hM : Matrix.transvection i j c * Matrix.diagonal d =
      Matrix.diagonal d * Matrix.transvection i j 1 := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, d]
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai; simp [Ne.symm hij]
      · simp [hai, Ne.symm hai]
    · by_cases hai : a = i
      · subst hai
        by_cases hbj : b = j
        · subst hbj; simp [hab, Ne.symm hij]
        · simp [hab, Ne.symm hbj]
      · simp [hab, hai, Ne.symm hai]
  have hcomm : T c * Dg = Dg * T 1 := by
    ext : 1
    simpa [T, Dg, Matrix.GeneralLinearGroup.mkOfDetNeZero] using hM
  have key := congrArg (fun g => distribHaarChar (ι → F) (glEquiv g)) hcomm
  simp only [map_mul, hT1, mul_one] at key
  have hpos : distribHaarChar (ι → F) (glEquiv Dg) ≠ 0 := distribHaarChar_pos.ne'
  rw [mul_comm] at key
  exact (mul_eq_left₀ hpos).1 key
end GroundTheory.Automorphic.Measures
