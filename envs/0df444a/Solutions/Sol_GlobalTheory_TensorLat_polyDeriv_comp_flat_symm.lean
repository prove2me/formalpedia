-- Prove2me | solution 1 for GlobalTheory.TensorLat.polyDeriv_comp_flat_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:10.890414+00:00
-- url     : https://prove2.me/submissions/f581aa17-0291-4977-bd41-6cf101e7af2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
open Classical
namespace GlobalTheory.TensorLat
theorem _root_.solution (P : MvPolynomial (Letter n dim) ℂ)
    (F : (Fin n → Vsp dim) → ℂ) (v : Fin n → Vsp dim) :
    polyDeriv P (fun l => EuclideanSpace.single l 1) (F ∘ flat.symm) (flat v) =
      polyDeriv P dir F v := by
  have hd : ∀ l : Letter n dim,
      (flat (n := n) (ι := Idx dim)).symm (EuclideanSpace.single l 1) = dir l := fun l => by
    rw [← flat_dir, ContinuousLinearEquiv.symm_apply_apply]
  have hit : ∀ (i : ℕ) (x : EuclideanSpace ℂ (Fin n × Idx dim)),
      iteratedFDeriv ℂ i (F ∘ (flat (n := n) (ι := Idx dim)).symm) x =
        (iteratedFDeriv ℂ i F ((flat (n := n) (ι := Idx dim)).symm x)).compContinuousLinearMap
          fun _ => ((flat (n := n) (ι := Idx dim)).symm :
            EuclideanSpace ℂ (Fin n × Idx dim) →L[ℂ] (Fin n → Vsp dim)) := by
    intro i x
    have h := (flat (n := n) (ι := Idx dim)).symm.iteratedFDerivWithin_comp_right F
      (uniqueDiffOn_univ (𝕜 := ℂ)) (x := x) (Set.mem_univ _) i
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using h
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [hit, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, hd]
end GlobalTheory.TensorLat
