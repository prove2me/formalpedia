-- Prove2me | solution 1 for GlobalTheory.T.unitLemma_residually_unipotent_via_cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:15.985806+00:00
-- url     : https://prove2.me/submissions/f61f21f6-151e-40ec-b030-c6352f458470

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayleyStatement
import Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_identity_of_residually_unipotent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ, algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 → (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧ Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | exact GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent | (intros; apply GlobalTheory.UnitLemma.CayleyCase.identity_of_residually_unipotent <;> assumption)
end _root_.GlobalTheory.T
