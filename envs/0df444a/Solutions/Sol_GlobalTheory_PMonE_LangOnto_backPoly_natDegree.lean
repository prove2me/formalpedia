-- Prove2me | solution 1 for GlobalTheory.PMonE.LangOnto.backPoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:05.790823+00:00
-- url     : https://prove2.me/submissions/f67f9a46-12f1-48fc-8312-a70fc684dabd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_zero
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
namespace GlobalTheory.PMonE.LangOnto
theorem _root_.solution {k : Type*} [Field k] {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (c : ℕ → k) :
    ∀ j, 1 ≤ (backPoly q n c j).natDegree := by
  intro j
  induction j with
  | zero => simp [backPoly_zero]
  | succ j ih =>
    have h1 : (C (c (n - j)) * X : k[X]).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      simp
    have h2 : 2 ≤ (backPoly q n c j ^ q).natDegree := by
      rw [natDegree_pow]; nlinarith
    rw [backPoly_succ, natDegree_sub_eq_left_of_natDegree_lt (by omega)]
    omega
end GlobalTheory.PMonE.LangOnto
