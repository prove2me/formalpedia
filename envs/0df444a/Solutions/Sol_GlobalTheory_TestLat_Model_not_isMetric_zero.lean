-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.not_isMetric_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:41.314634+00:00
-- url     : https://prove2.me/submissions/d1ffe641-23b1-4319-a15a-047f0283998f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
namespace GlobalTheory.TestLat.Model
theorem _root_.solution (X : InfinitePlace K → Matrix (Fin 1) (Fin 1) ℂ) : ¬ IsMetric (0 : Matrix (Fin 1) (Fin 1) K) X := by
  intro h
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨h1, h2⟩ := h v
  have h3 := congrArg Matrix.det h2
  have h4 : (X v)⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ h1).ne_zero
  rw [Matrix.det_mul, Matrix.det_conjTranspose] at h3
  simp only [Matrix.map_zero _ (map_zero _), Matrix.det_zero, mul_eq_zero, star_eq_zero, or_self] at h3
  exact h4 h3
end GlobalTheory.TestLat.Model
