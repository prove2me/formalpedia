-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.round_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:55.910388+00:00
-- url     : https://prove2.me/submissions/fe2d17ce-ba54-48f9-a387-3cdaa028325d

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
namespace GlobalTheory.CompareIterDegree
theorem _root_.solution {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (g : ℝ → ℤ) (hm : Monotone g)
    (h2 : ∀ x, g (x + 2) = g x + 2) (h0 : g 0 = 0) :
    GapTwo (fun c => -(g (μ s - μ c) : ℝ)) ∧ ∀ c, c ≠ s → 0 < (μ s - μ c) * g (μ s - μ c) := by
  have key : ∀ x y : ℝ, x + 2 ≤ y → (g x : ℝ) + 2 ≤ g y := fun x y hxy => by
    have := hm hxy
    rw [h2] at this
    exact_mod_cast this
  refine ⟨fun a b hab => ?_, fun c hc => ?_⟩
  · rcases le_abs.1 (hg a b hab) with h | h
    · have := key (μ s - μ a) (μ s - μ b) (by linarith)
      exact le_abs.2 (Or.inl (by linarith))
    · have := key (μ s - μ b) (μ s - μ a) (by linarith)
      exact le_abs.2 (Or.inr (by linarith))
  · rcases le_abs.1 (hg s c hc.symm) with h | h
    · have := key 0 (μ s - μ c) (by linarith)
      rw [h0] at this
      exact mul_pos (by linarith) (by push_cast at this; linarith)
    · have := key (μ s - μ c) 0 (by linarith)
      rw [h0] at this
      exact mul_pos_of_neg_of_neg (by linarith) (by push_cast at this; linarith)
end GlobalTheory.CompareIterDegree
