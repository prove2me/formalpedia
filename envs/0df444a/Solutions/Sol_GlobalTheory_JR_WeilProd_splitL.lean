-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.splitL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:34.538149+00:00
-- url     : https://prove2.me/submissions/7279ca7c-f730-4d9b-af9c-2c1042214e8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


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
    (hS : IsSplitting A A₁ A₂ eK eL) (y : A.L) :
    eK (A.NL y) = (A₁.NL (eL y).1, A₂.NL (eL y).2) ∧
      eK (Algebra.trace A.K A.L y) = (Algebra.trace A₁.K A₁.L (eL y).1, Algebra.trace A₂.K A₂.L (eL y).2) := by
  obtain ⟨-, i₁, n₁, t₁, -⟩ := Et.quadratic_structure F E A₁
  obtain ⟨-, i₂, n₂, t₂, -⟩ := Et.quadratic_structure F E A₂
  obtain ⟨-, -, n, t, -⟩ := Et.quadratic_structure F E A
  obtain ⟨hK, -, hst⟩ := hS
  have e1 := hK (A.NL y)
  rw [n, map_mul, hst] at e1
  have e2 := hK (Algebra.trace A.K A.L y)
  rw [t, map_add, hst] at e2
  refine ⟨Prod.ext (i₁ ?_) (i₂ ?_), Prod.ext (i₁ ?_) (i₂ ?_)⟩
  · rw [n₁]; simpa using (congrArg Prod.fst e1).symm
  · rw [n₂]; simpa using (congrArg Prod.snd e1).symm
  · rw [t₁]; simpa using (congrArg Prod.fst e2).symm
  · rw [t₂]; simpa using (congrArg Prod.snd e2).symm
end GlobalTheory.JR.WeilProd
