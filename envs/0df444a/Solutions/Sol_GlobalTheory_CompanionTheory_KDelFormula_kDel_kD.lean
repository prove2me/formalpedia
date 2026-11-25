-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KDelFormula.kDel_kD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:05.04002+00:00
-- url     : https://prove2.me/submissions/0fa4c7ab-eb77-48ac-b6d0-c1864b9407de

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_kD_vecCons
import Theorems.Thm_PositivityTheory_Rg_Cz_kDel_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KDelFormula
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace GlobalTheory.CompanionTheory.KDelFormula
theorem _root_.solution {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ}
    (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P) :
    kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) -
      ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by
  rw [kDel_apply]
  simp only [kD_vecCons, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.KDelFormula
