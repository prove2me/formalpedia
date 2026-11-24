-- Prove2me | solution 1 for GlobalTheory.CompleteDVR.exists_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:52.797809+00:00
-- url     : https://prove2.me/submissions/c0f26e8b-9c9d-4e2a-805c-4605b76dd704

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
import Theorems.Thm_GlobalTheory_CompleteDVR_exists_place_le
import Theorems.Thm_GlobalTheory_CompleteDVR_ne_top_of_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_NormIntegers_isAdicComplete_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR
namespace GlobalTheory.CompleteDVR
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V],
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : V →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  intro F _ _ V _
  obtain ⟨la, hla⟩ := exists_place_le V
  have hV : (la.valuation F).valuationSubring = V :=
    ValuationSubring.eq_of_le_of_ne_top _ hla (ne_top_of_isDiscreteValuationRing V)
  subst hV
  have hc : IsAdicComplete (maximalIdeal (la.adicCompletionIntegers F)) (la.adicCompletionIntegers F) := by
    refine NormIntegers.isAdicComplete_of_fg (C := la.adicCompletion F) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : la.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let φ : (la.valuation F).valuationSubring →+* la.adicCompletionIntegers F :=
    ((FinitePlace.embedding la).comp (la.valuation F).valuationSubring.subtype).codRestrict _ (fun x => by
      rw [RingHom.comp_apply, mem_adicCompletionIntegers, ValuationSubring.coe_subtype,
        FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
      exact (Valuation.mem_valuationSubring_iff _ _).1 x.2)
  refine ⟨la.adicCompletionIntegers F, inferInstance, inferInstance, inferInstance, hc, φ, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((FinitePlace.embedding la).injective (congrArg Subtype.val h))
  · refine ⟨fun a ha => ?_⟩
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one] at ha
    have h1 : la.valuation F (a : F) = 1 := by
      rw [← valuedAdicCompletion_eq_valuation']
      exact ha
    exact (Valuation.valuationSubring.integers (la.valuation F)).isUnit_iff_valuation_eq_one.2 h1
end GlobalTheory.CompleteDVR
