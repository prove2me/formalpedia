-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.exists_unit_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:23.394752+00:00
-- url     : https://prove2.me/submissions/6c330588-6f39-4310-9fd2-fee55deb4394

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_det_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace GlobalTheory.AdaptedChain
theorem _root_.solution {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) :
    ∃ f : ι → I, V.v (Matrix.of fun c' c => U c (f c')).det = 0 := by
  by_contra hcon
  push_neg at hcon
  have h1 : (Matrix.of fun c' => ∑ x, w x c' • (fun c => U c x) : Matrix ι ι C) = 1 := by
    ext c' c
    simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [show (if c' = c then (1 : C) else 0) = if c = c' then 1 else 0 by simp [eq_comm], ← h]
    simp only [mul_comm]
  have h2 : (1 : C) = ∑ f : ι → I, (∏ c', w (f c') c') * (Matrix.of fun c' c => U c (f c')).det := by
    have e := (Matrix.detRowAlternating (n := ι) (R := C)).toMultilinearMap.map_sum
      (fun c' x => w x c' • (fun c => U c x))
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul] at e
    have e1 : (Matrix.of fun c' => ∑ x, w x c' • (fun c => U c x) : Matrix ι ι C).det = 1 := by
      rw [h1, Matrix.det_one]
    rw [← e1]
    exact e
  have h3 : (0 : WithTop ℝ) < V.v (1 : C) := by
    rw [h2]
    refine V.v.map_lt_sum WithTop.zero_ne_top fun f _ => ?_
    rw [V.v.map_mul]
    have a1 : V.Ge 0 (∏ c', w (f c') c') := VF.Ge.prod fun c _ => hw _ _
    have a2 : V.Ge 0 (Matrix.of fun c' c => U c (f c')).det := det_int _ fun _ _ => hU _ _
    have a3 : (0 : WithTop ℝ) < V.v (Matrix.of fun c' c => U c (f c')).det :=
      lt_of_le_of_ne a2 (hcon f).symm
    exact lt_of_lt_of_le a3 (le_add_of_nonneg_left a1)
  simp at h3
end GlobalTheory.AdaptedChain
