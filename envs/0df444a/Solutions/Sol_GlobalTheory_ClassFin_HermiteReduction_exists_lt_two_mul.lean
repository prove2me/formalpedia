-- Prove2me | solution 1 for GlobalTheory.ClassFin.HermiteReduction.exists_lt_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:27:49.803797+00:00
-- url     : https://prove2.me/submissions/2317d944-b4ce-442c-a3b9-c21d787fd2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HermiteReduction
namespace GlobalTheory.ClassFin.HermiteReduction
theorem _root_.solution {S : Type} [Nonempty S] (f : S → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ s, c ≤ f s) :
    ∃ s, ∀ t, f s < 2 * f t := by
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have hm : c ≤ ⨅ s, f s := le_ciInf hf
  have hlt : ⨅ s, f s < 2 * ⨅ s, f s := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨s, fun t => hs.trans_le (by linarith [ciInf_le hbdd t])⟩
end GlobalTheory.ClassFin.HermiteReduction
