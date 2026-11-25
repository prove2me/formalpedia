-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:27.748737+00:00
-- url     : https://prove2.me/submissions/40dac571-365b-46ba-8bff-33dfed3f774f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_mem_unitGL_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_algebraMap_le_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_continuous_algebraMap_of_lt_one
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_continuous_linearMap
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_map_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution : PositivityTheory.Rg.Tf.Loc.D0a := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ _
  obtain ⟨π, h1, hmax⟩ := hun
  have h0 : valuation E (algebraMap k E π) ≠ 0 := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation E)
    intro h
    have := hmax r hr1
    rw [h] at this
    exact hr0 ((Valuation.zero_iff _).1 (le_antisymm this zero_le'))
  have hcont := continuous_algebraMap_of_lt_one h0 h1
  haveI : ContinuousSMul k E := continuousSMul_of_algebraMap k E hcont
  have hc : ∀ τ : E ≃ₐ[k] E, Continuous τ := fun τ => continuous_linearMap τ.toLinearMap
  have hval := value_map_eq hc h0 h1 hmax
  have hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k := by
    intro a
    have := value_algebraMap_le_iff (E := E) a 1
    simpa [Valuation.mem_integer_iff] using this
  refine ⟨hval, hint, ?_, ?_, hcont, ?_⟩
  · intro n g
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hint _) (forall₂_congr fun i j => hint _)
  · intro τ n g
    have hτ : ∀ x : E, τ x ∈ intO E ↔ x ∈ intO E := by
      intro x
      simp only [Valuation.mem_integer_iff, hval]
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hτ _) (forall₂_congr fun i j => hτ _)
  · intro n
    exact Continuous.units_map _ (continuous_id.matrix_map hcont)
end GlobalTheory.CompanionTheory.UnramDict
