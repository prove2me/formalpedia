-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:35.9601+00:00
-- url     : https://prove2.me/submissions/a6aed2e4-af4c-4db2-97d4-dc295dfdb4d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_dominating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (q : Ideal S) [q.IsPrime] (hq : q ≠ maximalIdeal S) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : S →+* O),
      RingHom.ker φ = q ∧ IsLocalHom φ := by
  have hl : IsLocalRing (S ⧸ q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hm : IsLocalHom (Ideal.Quotient.mk q) := .of_surjective _ Ideal.Quotient.mk_surjective
  have hf : ¬ IsField (S ⧸ q) := fun h =>
    hq (eq_maximalIdeal (Ideal.Quotient.maximal_of_isField q h))
  obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating (S ⧸ q) hf
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    φ.comp (Ideal.Quotient.mk q), ?_, RingHom.isLocalHom_comp _ _⟩
  rw [RingHom.ker_comp_of_injective _ h1, Ideal.mk_ker]
end GlobalTheory
