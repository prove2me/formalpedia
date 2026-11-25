-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.gapOne_of_regInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:16:02.821226+00:00
-- url     : https://prove2.me/submissions/e56ded62-8686-43f1-83dd-20132c29e72e

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
theorem _root_.solution {n : ℕ} {μ : Fin n → ℝ} (h : RegInt μ) : ∀ a b, a ≠ b → 1 ≤ |μ a - μ b| := by
  intro a b hab
  obtain ⟨m, hm⟩ := h.2 a b
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hab (h.1 (by simpa [sub_eq_zero] using hm))
  rw [hm]
  exact_mod_cast Int.one_le_abs hm0
end GlobalTheory.CompareIterDegree
