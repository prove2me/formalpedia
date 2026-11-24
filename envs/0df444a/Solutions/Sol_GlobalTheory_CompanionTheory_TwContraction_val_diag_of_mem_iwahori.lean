-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.val_diag_of_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:05.955955+00:00
-- url     : https://prove2.me/submissions/a8bfc9da-4fcd-478a-94b7-ee4cd1b0eaf5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_det_sub_prod_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_mem_unitGL_entries
import Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_val_det_of_mem_unitGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution {c : GL (Fin n) F} (hc : c ∈ iwahori (m := n) F) (i : Fin n) :
    valuation F ((c : Matrix (Fin n) (Fin n) F) i i) = 1 := by
  have h1 := val_det_sub_prod_lt (c : Matrix (Fin n) (Fin n) F) (mem_unitGL_entries hc.1) hc.2
  have hd := val_det_of_mem_unitGL hc.1
  have h2 : valuation F (∏ i, (c : Matrix (Fin n) (Fin n) F) i i) = 1 := by
    rw [← hd]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd, Valuation.map_sub_swap]
    exact h1
  rw [map_prod] at h2
  exact (Finset.prod_eq_one_iff_of_le_one' fun r _ => mem_unitGL_entries hc.1 r r).1 h2 i (Finset.mem_univ i)
end GlobalTheory.CompanionTheory.TwContraction
