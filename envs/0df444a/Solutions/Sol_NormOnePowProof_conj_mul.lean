-- Prove2me | solution 1 for NormOnePowProof.conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:58.629808+00:00
-- url     : https://prove2.me/submissions/b22f5d56-7a26-406d-b281-d0f92b377a45

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
import Theorems.Thm_NormOnePowProof_map_mem_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]
namespace NormOnePowProof
theorem _root_.solution (c : E →+* E) (hc : ∀ x, c (c x) = x) {A A' B B' : Submodule (𝓞 E) E}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) (hB' : ∀ x, x ∈ B' ↔ c x ∈ A') :
    ∀ x, x ∈ B * B' ↔ c x ∈ A * A' := by
  intro x
  constructor
  · intro hx
    exact map_mem_mul c (fun p hp => (hB p).1 hp) (fun p hp => (hB' p).1 hp) x hx
  · intro hx
    have := map_mem_mul c (fun p hp => (hB (c p)).2 (by rwa [hc]))
      (fun p hp => (hB' (c p)).2 (by rwa [hc])) (c x) hx
    rwa [hc] at this
end NormOnePowProof
