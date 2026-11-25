-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.prodEquiv_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:54.961243+00:00
-- url     : https://prove2.me/submissions/da9d569f-9614-4c20-8e24-6394e4595d4c

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
theorem _root_.solution (φ : K.E →+* K'.E) (B₁ B₂ : InvAlg K) (ψ : K'.E →+* (B₁.prod B₂).A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E (B₁.prod B₂).A e) (hσ : ∀ e, (B₁.prod B₂).σ (ψ e) = ψ (K'.c e)) :
    Orbit.IsIso (prodEquiv φ B₁ B₂ ψ hψ hσ) :=
  ⟨fun _ => rfl, rfl⟩
end GlobalTheory.UnitLemma.Unr
