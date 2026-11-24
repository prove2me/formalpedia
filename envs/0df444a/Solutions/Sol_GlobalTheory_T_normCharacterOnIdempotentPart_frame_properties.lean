-- Prove2me | solution 1 for GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:25.722801+00:00
-- url     : https://prove2.me/submissions/df7a4ee4-2238-43d7-a919-02a4b72a385e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFramePropertiesStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_frame_props


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A) (S : Finset ι), IsFrame B e π S → (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧ (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧ (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧ (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_frame_props | exact GlobalTheory.UnitLemma.Desc.chi_frame_props | (intros; apply GlobalTheory.UnitLemma.Desc.chi_frame_props <;> assumption)
end _root_.GlobalTheory.T
