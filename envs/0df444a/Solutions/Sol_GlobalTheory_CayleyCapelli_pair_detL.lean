-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.pair_detL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:17.39944+00:00
-- url     : https://prove2.me/submissions/e4352e88-47e1-4fb3-b45c-cb5dfecdf52b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Theorems.Thm_GlobalTheory_CayleyCapelli_list_rename
import Theorems.Thm_GlobalTheory_DetPowPairing_pair_list


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution (n : ℕ) (P : MvPolynomial (PVar n) C) (Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * detL C n) (rename Sum.inl Q) = pair P (rename Sum.inl (cayOp n C Q)) := by
  have hσ : ∀ τ : Equiv.Perm (Fin n), pair (P * ∏ i, (X (Sum.inl (τ i, i)) : MvPolynomial (PVar n) C))
      (rename Sum.inl Q) = pair P (rename Sum.inl (cayMono n C τ Q)) := by
    intro τ
    have h1 := pair_list (C := C) (fun j : Fin n => (Sum.inl (τ j, j) : PVar n)) (List.finRange n) P
      (rename Sum.inl Q)
    have h2 := list_rename (C := C) (Sum.inl : Fin n × Fin n → PVar n) Sum.inl_injective
      (fun j : Fin n => (τ j, j)) (List.finRange n) Q
    rw [Fin.prod_univ_def, h1, h2]
    rfl
  rw [detL, Matrix.det_apply', Finset.mul_sum, map_sum, LinearMap.sum_apply, cayOp, LinearMap.sum_apply,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.smul_apply, map_zsmul, map_zsmul, ← hσ τ, mul_left_comm, ← zsmul_eq_mul, map_zsmul,
    LinearMap.smul_apply]
  rfl
end GlobalTheory.CayleyCapelli
