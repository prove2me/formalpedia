-- Prove2me | solution 1 for GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:07.15455+00:00
-- url     : https://prove2.me/submissions/fb03e8ce-5afa-4f53-8f7b-e3a143a73929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximalStatement
import Theorems.Thm_GlobalTheory_Izumi_exists_dominating_eq_mul_of_not_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  first | exact @GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | exact GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span | (intros; apply GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span <;> assumption)
end _root_.GlobalTheory.T
