-- Prove2me | solution 1 for GlobalTheory.DeligneSerre.norm_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:14.075578+00:00
-- url     : https://prove2.me/submissions/e0195a7d-c731-4b7d-a15d-d0a65ac39f25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixExistsCommonEigenvectorMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatricesIntertwiningOfSemilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegralHeckeEigensystemDeligneSerre

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
theorem _root_.solution (K : Type) [NormedField K] [IsAlgClosed K] (n : ℕ)
    (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ μ : K, (∃ c : Fin n → K, c ≠ 0 ∧ N *ᵥ c = μ • c) → ‖μ‖ = 1) : ‖N.det‖ = 1 := by
  have hroot : ∀ μ ∈ N.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    apply h
    have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
    have hr := (Polynomial.mem_roots hne).1 hμ
    rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hr
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  rw [Matrix.det_eq_prod_roots_charpoly]
  revert hroot
  generalize N.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    rw [Multiset.prod_cons, norm_mul, hs a (Multiset.mem_cons_self a s),
      ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]
end GlobalTheory.DeligneSerre
