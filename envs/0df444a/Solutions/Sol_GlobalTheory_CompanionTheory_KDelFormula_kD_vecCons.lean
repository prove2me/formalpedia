-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KDelFormula.kD_vecCons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:33.811899+00:00
-- url     : https://prove2.me/submissions/413132f0-932a-42fa-a9bd-32da48584bfb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_removeNth_succ_vecCons
import Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_map_vecCons_removeNth
import Theorems.Thm_PositivityTheory_Rg_Cz_kD_apply


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
theorem _root_.solution (T : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (x : P)
    (Y : Fin q → P) :
    kD T η (Matrix.vecCons x Y) =
      T x (η Y) - ∑ t, T (Y t) (η (Function.update Y t x)) := by
  have hs : ∀ t : ℕ, ((-1 : ℤ) ^ (t + 1) * (-1) ^ t) = -1 := fun t => by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨t, by ring⟩
  cases q with
  | zero =>
    rw [kD_apply, Fin.sum_univ_succ]
    simp [Fin.removeNth_zero]
  | succ n =>
    rw [kD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp [Fin.removeNth_zero]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.val_succ, Matrix.cons_val_succ, removeNth_succ_vecCons, map_vecCons_removeNth,
        map_zsmul, smul_smul, hs, neg_one_zsmul]
end GlobalTheory.CompanionTheory.KDelFormula
