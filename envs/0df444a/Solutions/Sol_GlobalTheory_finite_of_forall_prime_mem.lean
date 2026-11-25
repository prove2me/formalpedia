-- Prove2me | solution 1 for GlobalTheory.finite_of_forall_prime_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:53.09633+00:00
-- url     : https://prove2.me/submissions/702c2b05-9d62-42cf-b028-0d1a5692d671

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_finite_of_isHausdorff_of_finite_quotient
import Theorems.Thm_GlobalTheory_prime_eq_bot_or_maximalIdeal_of_forall_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
namespace GlobalTheory
theorem _root_.solution {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra R B] [Finite (B ⧸ maximalIdeal B)] {f : B} (hf : f ≠ 0)
    (H : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → f ∈ P)
    (h0 : (maximalIdeal R).map (algebraMap R B) ≠ ⊥)
    (h1 : (maximalIdeal R).map (algebraMap R B) ≠ ⊤) : Module.Finite R B := by
  set J := (maximalIdeal R).map (algebraMap R B) with hJ
  have hrad : maximalIdeal B ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun q hq => ?_
    rcases prime_eq_bot_or_maximalIdeal_of_forall_mem hf H hq.2 with h | h
    · exact absurd (le_bot_iff.mp (h ▸ hq.1)) h0
    · exact h.ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal B)) n
  haveI : Finite (B ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)
  haveI : IsHausdorff J B := IsHausdorff.of_isLocalRing _ _ h1
  haveI : IsHausdorff (maximalIdeal R) B := IsHausdorff.map_algebraMap_iff.mp this
  haveI : Finite (B ⧸ (maximalIdeal R • ⊤ : Submodule R B)) := by
    rw [Ideal.smul_top_eq_map]
    exact ‹Finite (B ⧸ J)›
  exact finite_of_isHausdorff_of_finite_quotient (maximalIdeal R) B
end GlobalTheory
