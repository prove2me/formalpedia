-- Prove2me | solution 1 for GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:07.436835+00:00
-- url     : https://prove2.me/submissions/9a5bac91-947f-439c-9b11-ef80b6b5436b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiser
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AdicCompletionValuationMapUniformiserStatement
import Theorems.Thm_GlobalTheory_adicCompletion_valuation_map_uniformiser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  first | exact @GlobalTheory.adicCompletion_valuation_map_uniformiser | exact GlobalTheory.adicCompletion_valuation_map_uniformiser | (intros; apply GlobalTheory.adicCompletion_valuation_map_uniformiser <;> assumption)
end _root_.GlobalTheory.T
