-- Prove2me | solution 1 for GlobalTheory.Nef.isFF_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:38.437285+00:00
-- url     : https://prove2.me/submissions/14eb4754-321f-4d82-aa5e-d91874ed8e1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldOneVariableTranscendentalFiniteAndE
import Theorems.Thm_GlobalTheory_Nef_finiteDimensional_adjoin_of_trdeg_le_one
import Theorems.Thm_GlobalTheory_Nef_essFiniteType_trdeg_of_isFF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open IntermediateField
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [Field F] [Algebra k F], IsFF k F →
    (∀ x : F, Transcendental k x → FiniteDimensional k⟮x⟯ F) ∧
    ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k E := by
  intro k F _ _ _ h
  obtain ⟨hfg, htr⟩ := essFiniteType_trdeg_of_isFF h
  refine ⟨fun x hx => finiteDimensional_adjoin_of_trdeg_le_one htr x hx, ?_⟩
  intro E _ _ _ _ _
  have hfgE : Algebra.EssFiniteType k E := Algebra.EssFiniteType.comp k F E
  have h0 : Algebra.trdeg F E = 0 := trdeg_eq_zero_iff.mpr inferInstance
  have htrE : Algebra.trdeg k E ≤ 1 := by
    rw [← trdeg_add_eq k F, h0, add_zero]; exact htr
  obtain ⟨t, ht, _⟩ := h
  have ht' : Transcendental k (algebraMap F E t) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr ht
  exact ⟨algebraMap F E t, ht', finiteDimensional_adjoin_of_trdeg_le_one htrE _ ht'⟩
end GlobalTheory.Nef
