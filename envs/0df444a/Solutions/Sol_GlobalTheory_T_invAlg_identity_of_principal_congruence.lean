-- Prove2me | solution 1 for GlobalTheory.T.invAlg_identity_of_principal_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:20:31.515212+00:00
-- url     : https://prove2.me/submissions/276e1ef8-2196-4e55-9d42-c4acd409968a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruenceStatement
import Theorems.Thm_GlobalTheory_UnitLemma_CongruenceCayley_identity_of_principal_congruence


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
theorem _root_.solution : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a → ∀ B₁ B₂ : InvAlg K, (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 → (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | exact GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence | (intros; apply GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence <;> assumption)
end _root_.GlobalTheory.T
