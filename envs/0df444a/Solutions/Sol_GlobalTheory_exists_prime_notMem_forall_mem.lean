-- Prove2me | solution 1 for GlobalTheory.exists_prime_notMem_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:53:26.676323+00:00
-- url     : https://prove2.me/submissions/f63b28ce-acda-4647-8388-7d445371adb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt

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
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A] {f : A}
    {q : Ideal A} (hq : q.IsPrime) (hf : f ∉ q) : ∃ Q : Ideal A, Q.IsPrime ∧ f ∉ Q ∧
      ∀ P : Ideal (A ⧸ Q), P.IsPrime → P ≠ ⊥ → Ideal.Quotient.mk Q f ∈ P := by
  obtain ⟨Q, hQ, hmax⟩ := set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
    {Q : Ideal A | Q.IsPrime ∧ f ∉ Q} ⟨q, hq, hf⟩
  refine ⟨Q, hQ.1, hQ.2, fun P hP hP0 => ?_⟩
  by_contra h
  refine hmax (P.comap (Ideal.Quotient.mk Q)) ⟨Ideal.IsPrime.comap _, h⟩ ?_
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff P).mp hP0
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine SetLike.lt_iff_le_and_exists.mpr ⟨fun a ha => ?_, x, hx,
    fun hxQ => hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr hxQ)⟩
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact P.zero_mem
end GlobalTheory
