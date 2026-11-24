-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.kerL_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:17.158953+00:00
-- url     : https://prove2.me/submissions/47effe23-cd5b-4f18-9d0f-4d228d645add

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_WeilProd_trace_split
import Theorems.Thm_GlobalTheory_JR_WeilProd_splitL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
    (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) :
    A.kerL ψ x y' y = A₁.kerL ψ (eK x).1 (eL y').1 (eL y).1 * A₂.kerL ψ (eK x).2 (eL y').2 (eL y).2 := by
  have h := (splitL A A₁ A₂ eK eL hS (star y' * y)).2
  rw [map_mul eL, hS.2.2] at h
  simp only [Et.kerL, Et.psiK]
  rw [trace_split A A₁ A₂ eK, AddChar.map_add_eq_mul, map_mul, h]
  rfl
end GlobalTheory.JR.WeilProd
