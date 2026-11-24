-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_frame_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:55.58907+00:00
-- url     : https://prove2.me/submissions/d41c4cf6-9daa-4664-947d-b402ceda2483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_mul
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_norm
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_prod
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_plus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S →
    (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧
    (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧
    (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧
    (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  intro K B ι _ _ e π S h
  exact ⟨fun I x y hx hy => chi_mul B h.1.1.toOrthogonalIdempotents I hx hy, fun I w hw => chi_norm B h.1 I hw,
    fun I J _ hJ => chi_prod B h I J hJ, fun y hy => chi_plus B h.1 hy⟩
end GlobalTheory.UnitLemma.Desc
