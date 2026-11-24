-- Prove2me | solution 1 for GlobalTheory.HCA.solSet_closed_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:29:24.082798+00:00
-- url     : https://prove2.me/submissions/704e9d4a-7d20-4649-bd90-174df4f36323

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Theorems.Thm_GlobalTheory_HCA_SolSub_integrable_tr
import Theorems.Thm_GlobalTheory_HCA_zero_mem_solSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory.HCA.SolSub
namespace GlobalTheory.HCA
theorem _root_.solution :
    ∀ (d : ℕ) (ι : Type) (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) →
      IsClosed (solSet P U) ∧ ∃ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U := by
  intro d ι P U hU ha
  have hint : ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
      Integrable (P.tr i φ) := fun i φ h => integrable_tr P hU ha i h.1 h.2.1 h.2.2
  have key : ∀ u : U →ᵇ ℂ, u ∈ solSet P U ↔
      ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        pair hU (P.tr i φ) (hint i φ h) u = 0 := by
    intro u
    constructor
    · intro hu i φ h
      exact hu i φ h.1 h.2.1 h.2.2
    · intro hu i φ h1 h2 h3
      exact hu i φ ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have : solSet P U = ⋂ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        {u | pair hU (P.tr i φ) (hint i φ h) u = 0} := by
      ext u; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact key u
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun h =>
      isClosed_eq (pair hU (P.tr i φ) (hint i φ h)).continuous continuous_const
  · refine ⟨{ carrier := solSet P U, add_mem' := ?_, zero_mem' := zero_mem_solSet P U, smul_mem' := ?_ }, rfl⟩
    · intro u v hu hv
      rw [key] at hu hv ⊢
      intro i φ h
      rw [map_add, hu i φ h, hv i φ h, add_zero]
    · intro c u hu
      rw [key] at hu ⊢
      intro i φ h
      rw [map_smul, hu i φ h, smul_zero]
end GlobalTheory.HCA
