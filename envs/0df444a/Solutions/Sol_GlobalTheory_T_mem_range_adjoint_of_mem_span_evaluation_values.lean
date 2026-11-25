-- Prove2me | solution 1 for GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:48.497198+00:00
-- url     : https://prove2.me/submissions/00101ebc-7fe7-443d-b1bc-9b788c073afc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemRangeAdjointOfMemSpanEvaluationValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemRangeAdjointOfMemSpanEvaluationValuesStatement
import Theorems.Thm_GlobalTheory_ChainOnto_value_of_adjoint_of_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  first | exact @GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | exact GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | (intros; apply GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span <;> assumption)
end _root_.GlobalTheory.T
