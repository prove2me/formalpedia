-- Prove2me | solution 1 for GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:30:45.259826+00:00
-- url     : https://prove2.me/submissions/643bd956-b85b-4770-9aeb-553632cda593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Theorems.Thm_GlobalTheory_CNorm_mem_span_singleton_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_NormIntegers_isAdicComplete_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∀ t : v.adicCompletionIntegers F, Valued.v (t : v.adicCompletion F) < 1 → IsAdicComplete (Ideal.span {t}) (v.adicCompletionIntegers F)) ∧ ∀ (t : v.adicCompletionIntegers F) (e : ℕ), Valued.v (t : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {t}) = Ideal.absNorm v.asIdeal ^ e := by
  intro F _ _ v
  refine ⟨fun t ht => ?_, fun t e ht => ?_⟩
  · refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) ?_
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
    · rw [Ne, Ideal.span_singleton_eq_top,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact ht.ne
  · have ht0 : Valued.v (t : v.adicCompletion F) ≠ 0 := by rw [ht]; exact WithZero.exp_ne_zero
    let f : 𝓞 F →+* v.adicCompletionIntegers F ⧸ Ideal.span {t} :=
      (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    have hs : Function.Surjective f := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le v (a := (y : v.adicCompletion F)) y.2 e
      refine ⟨s, ?_⟩
      change Ideal.Quotient.mk _ _ = _
      rw [eq_comm, Ideal.Quotient.eq, mem_span_singleton_adicCompletionIntegers v ht0, ht]
      exact hs
    have hk : RingHom.ker f = v.asIdeal ^ e := by
      ext s
      rw [RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = _ ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton_adicCompletionIntegers v ht0, ht,
        HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, hk, ← map_pow,
      Ideal.absNorm_apply, Submodule.cardQuot_apply]
end GlobalTheory.CNorm
