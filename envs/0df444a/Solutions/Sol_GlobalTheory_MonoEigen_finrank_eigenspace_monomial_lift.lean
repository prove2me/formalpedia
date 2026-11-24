-- Prove2me | solution 1 for GlobalTheory.MonoEigen.finrank_eigenspace_monomial_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:12:45.017625+00:00
-- url     : https://prove2.me/submissions/1bafbb9a-057a-4980-bfc8-a2cbfeab9e2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinrankEigenspaceMonomialMatrixLift
import Theorems.Thm_GlobalTheory_MonoEigen_finrank_eq_card
import Theorems.Thm_GlobalTheory_MonoEigen_mem_eigenspace_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.MonoEigen
namespace GlobalTheory.MonoEigen
theorem _root_.solution :
    ∀ (k : Type) [Field k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → ∀ μ : k, μ ≠ 0 → Module.finrank k (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then c j else 0)) μ) = Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Matrix.of fun i j => if i = σ j then θ (c j) else 0)) (θ μ)) := by
  intro k _ θ hθ n σ c hc μ hμ
  have hmul : θ μ * θ μ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
  have hθμ : θ μ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hinv : (θ μ)⁻¹ = θ μ⁻¹ := inv_eq_of_mul_eq_one_right hmul
  rw [finrank_eq_card σ (fun j => c j * μ⁻¹) _ (mem_eigenspace_iff σ c μ hμ),
    finrank_eq_card σ (fun j => θ (c j) * (θ μ)⁻¹) _
      (mem_eigenspace_iff σ (fun j => θ (c j)) (θ μ) hθμ)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  refine and_congr_right fun _ => forall_congr' fun m => imp_congr_right fun _ => ?_
  have h1 : orbProd σ (fun j => θ (c j) * (θ μ)⁻¹) m j
      = θ (orbProd σ (fun j => c j * μ⁻¹) m j) := by
    simp only [orbProd, map_prod, map_mul, hinv]
  have h2 : orbProd σ (fun j => c j * μ⁻¹) m j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc _) (inv_ne_zero hμ)
  rw [h1]
  constructor
  · intro h; rw [h, map_one]
  · intro h
    exact hθ _ _ h2 one_ne_zero (by rw [h, map_one])
end GlobalTheory.MonoEigen
