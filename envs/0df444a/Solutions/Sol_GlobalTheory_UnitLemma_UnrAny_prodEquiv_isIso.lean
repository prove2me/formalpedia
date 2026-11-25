-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrAny.prodEquiv_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:17.446559+00:00
-- url     : https://prove2.me/submissions/341f29da-e22f-4fd0-b106-6a335d1a18af

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
theorem _root_.solution (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩
end GlobalTheory.UnitLemma.UnrAny
