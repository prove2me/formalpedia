-- Prove2me | solution 1 for GlobalTheory.CompareIterDegree.weaken_consts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:25.854028+00:00
-- url     : https://prove2.me/submissions/d9d3c46a-0f89-4279-abfd-bc0104fdd416

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    1 / (4 * (n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ∧ (n : ℝ) ≤ Real.exp 1 * n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨one_div_le_one_div_of_le (by linarith) (by nlinarith), ?_⟩
  have := Real.add_one_le_exp (1 : ℝ)
  nlinarith
end GlobalTheory.CompareIterDegree
