-- Prove2me | solution 1 for GroundTheory.LocalField.valuation_algEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:35.279723+00:00
-- url     : https://prove2.me/submissions/34d6e9de-1945-49f9-91cb-cb67023d3dfa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Theorems.Thm_GroundTheory_LocalField_valuation_map_lt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by

  have key : ∀ (τ : L ≃ₐ[K] L) (y : L), ¬ valuation L (τ y) < valuation L y := by
    intro τ y h
    have hpow : ∀ m : ℕ, valuation L ((τ ^ (m + 1)) y) < valuation L y := by
      intro m
      induction m with
      | zero => simpa using h
      | succ m ih =>
        rw [pow_succ', AlgEquiv.mul_apply]
        exact ((valuation_map_lt_iff τ.toAlgHom _ _).mpr ih).trans h
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (orderOf_pos τ).ne'
    have := hpow m
    rw [← Nat.succ_eq_add_one, ← hm, pow_orderOf_eq_one, AlgEquiv.one_apply] at this
    exact this.false
  rcases lt_trichotomy (valuation L (σ x)) (valuation L x) with h | h | h
  · exact (key σ x h).elim
  · exact h
  · refine (key σ.symm (σ x) ?_).elim
    simpa using h
end GroundTheory.LocalField
