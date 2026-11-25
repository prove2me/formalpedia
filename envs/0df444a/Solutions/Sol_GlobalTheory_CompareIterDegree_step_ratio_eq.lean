-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.step_ratio_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:23:46.619182+00:00
-- url     : https://prove2.me/submissions/92328825-4e15-44b8-afd4-a47a96d561c8

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
import Theorems.Thm_GlobalTheory_CompareIterDegree_fdeg_ratio
import Theorems.Thm_GlobalTheory_CompareIterDegree_gapOne_of_regInt
import Theorems.Thm_GlobalTheory_CompareIterDegree_sub_single

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
theorem _root_.solution {n : ℕ} {μ : Fin n → ℝ} (h : RegInt μ) (s : Fin n) :
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + 1 - μ c) / (μ s - μ c) ∧
    fdegHC (μ - Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s - 1 - μ c) / (μ s - μ c) := by
  refine ⟨fdeg_ratio μ s 1 (by simp) (gapOne_of_regInt h), ?_⟩
  rw [sub_single, fdeg_ratio μ s (-1) (by simp) (gapOne_of_regInt h)]
  simp only [← sub_eq_add_neg]
end GlobalTheory.CompareIterDegree
