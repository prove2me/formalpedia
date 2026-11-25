-- Prove2me | solution 1 for GlobalTheory.DeligneSerre.norm_eigen_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:57.724732+00:00
-- url     : https://prove2.me/submissions/99c81b06-3c77-4690-843e-cdb75765630a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre
import Theorems.Thm_GlobalTheory_EigenvalueNormAtMostOne_norm_eigenvalue_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.DeligneSerre
namespace GlobalTheory.DeligneSerre
theorem _root_.solution (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by
  first
  | (rename_i h_1 h_3; revert l h_1 O h_3 emb hle n N c μ hc hN; exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one)
  | exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one ..)
end GlobalTheory.DeligneSerre
