-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.prod_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:31:21.717832+00:00
-- url     : https://prove2.me/submissions/7076fe3b-0c2b-4433-8511-26390d5416d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayleyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedInvolutionFieldEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyOverExtIntegralReductionPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaLocalOddResidueOfLieAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial
variable {K K' : UQ}
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (B₁ B₂ : InvAlg K) (hi₁ : IsIntegral K.O B₁.g) (hi₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g := by
  obtain ⟨p₁, hp₁, e₁⟩ := hi₁
  obtain ⟨p₂, hp₂, e₂⟩ := hi₂
  refine ⟨p₁ * p₂, hp₁.mul hp₂, ?_⟩
  rw [← aeval_def] at e₁ e₂ ⊢
  have h1 : (aeval (B₁.prod B₂).g (p₁ * p₂)).1 = aeval B₁.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  have h2 : (aeval (B₁.prod B₂).g (p₁ * p₂)).2 = aeval B₂.g (p₁ * p₂) :=
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.prod B₂).g (p₁ * p₂)).symm
  refine Prod.ext ?_ ?_
  · rw [h1, map_mul, e₁, zero_mul]; rfl
  · rw [h2, map_mul, e₂, mul_zero]; rfl
end GlobalTheory.UnitLemma.Unr
