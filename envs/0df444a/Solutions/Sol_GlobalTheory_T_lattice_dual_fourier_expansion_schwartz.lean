-- Prove2me | solution 1 for GlobalTheory.T.lattice_dual_fourier_expansion_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:21:23.200736+00:00
-- url     : https://prove2.me/submissions/059acaae-cd61-487b-8ec9-3cf65d8e7f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartz
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeDualFourierExpansionSchwartzStatement
import Theorems.Thm_GlobalTheory_periodisation_hasSum_fourier_bilinForm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap V ℂ),
    ∃ c : V → ℂ, (∀ N : ℕ, Summable (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        ‖c μ‖ * (1 + ‖(μ : V)‖) ^ N)) ∧
      ∀ x : V, HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} =>
        c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) (∑' l : Λ, f (x + l)) := by
  first | exact @GlobalTheory.periodisation_hasSum_fourier_bilinForm | exact GlobalTheory.periodisation_hasSum_fourier_bilinForm | (intros; apply GlobalTheory.periodisation_hasSum_fourier_bilinForm <;> assumption)
end _root_.GlobalTheory.T
