-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.l1_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:34:40.949544+00:00
-- url     : https://prove2.me/submissions/51675e8d-0a0e-4c05-947c-d326c2f19167

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
theorem _root_.solution {A : Type} (a b : A →₀ ℂ) : l1 (a + b) ≤ l1 a + l1 b := by
  classical
  have e : ∀ c : A →₀ ℂ, c.support ⊆ a.support ∪ b.support →
      l1 c = ∑ ν ∈ a.support ∪ b.support, ‖c ν‖ := fun c hc =>
    sum_subset hc fun ν _ hν => by simp [Finsupp.notMem_support_iff.1 hν]
  rw [e _ Finsupp.support_add, e a subset_union_left, e b subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun ν _ => norm_add_le _ _
end GlobalTheory.CompareIterDegree
