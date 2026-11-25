-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrAny.prod_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:00.030974+00:00
-- url     : https://prove2.me/submissions/84ff6b2e-95c2-43f0-97d6-60cf2dd497b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedBaseChangeLatticeCountEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyOverExtIntegralReductionPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardResidueFieldLocalOrderUnitaryProdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnramifiedEmbeddingOfInvolutionAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaLocalAnyResidueCharOfLieAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrAny
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable {K K' : UQ}
namespace GlobalTheory.UnitLemma.UnrAny
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
end GlobalTheory.UnitLemma.UnrAny
