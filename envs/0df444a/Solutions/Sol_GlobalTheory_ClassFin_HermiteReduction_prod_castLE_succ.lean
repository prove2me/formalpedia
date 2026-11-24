-- Prove2me | solution 1 for GlobalTheory.ClassFin.HermiteReduction.prod_castLE_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:12.441343+00:00
-- url     : https://prove2.me/submissions/2220ebfc-f5fe-4ccd-a0d9-882a07f351da

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
theorem _root_.solution {N : ℕ} (f : Fin N → ℝ) (p q : Fin N) (hq : (q : ℕ) = p + 1) (h : (q : ℕ) ≤ N) :
    ∏ i : Fin q, f (Fin.castLE h i) = (∏ l ∈ Finset.univ.filter (· < p), f l) * f p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hq h ⊢
  subst hq
  rw [Fin.prod_univ_castSucc]
  congr 1
  refine Finset.prod_bij (fun i _ => Fin.castLE h i.castSucc) ?_ ?_ ?_ ?_
  · intro i _
    simp [Fin.lt_def]
  · intro i _ j _ hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  · intro l hl
    have hl' : (l : ℕ) < p := by simpa [Fin.lt_def] using hl
    exact ⟨⟨l, hl'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl
end GlobalTheory.ClassFin.HermiteReduction
