-- Prove2me | solution 1 for OAI.Problem346.zero_of_upward_grid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:13:37.89123+00:00
-- url     : https://prove2.me/submissions/94a4cdfb-e2c6-46f1-ac76-4d8e8eee9eb7

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/GridCancellation.lean:L9-L52
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.zero_of_upward_grid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap

-- ---- from OAI.RepresentationTheory.FoulkesHowe.GridCancellation ----
namespace OAI

open scoped BigOperators

namespace Problem346

/-- Reverse induction over a finite rectangular grid.  A zero at its upper corner
propagates to every point when a one-coordinate upward step can be cancelled. -/
theorem zero_of_upward_grid {ι M : Type*} [Fintype ι] [DecidableEq ι] [Zero M]
    (r : ℕ) (F : (ι → ℕ) → M)
    (hend : F (fun _ => r) = 0)
    (hstep : ∀ (c : ι → ℕ), (∀ i, c i ≤ r) → ∀ i, c i < r →
      F (Function.update c i (c i + 1)) = 0 → F c = 0)
    (c : ι → ℕ) (hc : ∀ i, c i ≤ r) : F c = 0 := by
  classical
  have aux : ∀ n : ℕ, ∀ c : ι → ℕ, (∀ i, c i ≤ r) →
      (∑ i, (r - c i)) = n → F c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc hn
      by_cases htop : ∀ i, c i = r
      · have heq : c = fun _ => r := funext htop
        simpa only [heq] using hend
      · push Not at htop
        obtain ⟨i, hi⟩ := htop
        have hir : c i < r := lt_of_le_of_ne (hc i) hi
        apply hstep c hc i hir
        let c' := Function.update c i (c i + 1)
        have hc' : ∀ j, c' j ≤ r := by
          intro j
          by_cases hji : j = i
          · subst j
            simp only [c', Function.update_self]
            omega
          · simpa only [c', Function.update_of_ne hji] using hc j
        have hlt : (∑ j, (r - c' j)) < n := by
          rw [← hn]
          apply Finset.sum_lt_sum
          · intro j hj
            by_cases hji : j = i
            · subst j
              simp only [c', Function.update_self]
              omega
            · simp only [c', Function.update_of_ne hji, le_refl]
          · refine ⟨i, Finset.mem_univ i, ?_⟩
            simp only [c', Function.update_self]
            omega
        exact ih _ hlt c' hc' rfl
  exact aux _ c hc rfl

end Problem346

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.zero_of_upward_grid := @_root_.OAI.Problem346.zero_of_upward_grid
