-- Prove2me | solution 1 for GlobalTheory.KSp.pr_diag_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:15.232973+00:00
-- url     : https://prove2.me/submissions/5163140b-93b2-46bb-8f4a-5ee38bb8ae24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingDiagonalNorm
import Theorems.Thm_GlobalTheory_KSp_pr_eq_half_trace_mat
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_norm
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (u : Matrix α α E) (D' : α → F) (a : Matrix ν ν E) (D : ν → F), Q = u * diagonal (fun i => algebraMap F E (D' i)) * (u.map c)ᵀ → ∀ x : Matrix α ν E, 2⁻¹ * pr c Q x (x * (a * diagonal (fun j => algebraMap F E (D j)) * (a.map c)ᵀ)) = ∑ i, ∑ j, (2⁻¹ * D' i * D j) * Algebra.norm F ((uᵀ * x * a) i j) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q _ u D' a D hQu x
  have hc : ∀ z, c (c z) = z := hE.invol
  have hmm : ∀ {m n : Type} (M : Matrix m n E), (M.map c).map c = M := fun M => by ext i j; simp [hc]
  have hd : ∀ {m : Type} [Fintype m] [DecidableEq m] (d : m → F),
      (diagonal (fun i => algebraMap F E (d i))).map c = diagonal (fun i => algebraMap F E (d i)) := by
    intro m _ _ d; ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  set dD' := diagonal (fun i => algebraMap F E (D' i))
  set dD := diagonal (fun j => algebraMap F E (D j))
  set Y := uᵀ * x * a with hY
  have hQT : Qᵀ = u.map c * dD' * uᵀ := by
    rw [hQu, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]
  have hbs : ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ = a * dD * (a.map c)ᵀ * (x.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul,
      transpose_mul, hd, diagonal_transpose, transpose_map, hmm, ← transpose_map, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rfl
  have hYs : (Y.map c)ᵀ = (a.map c)ᵀ * (x.map c)ᵀ * u.map c := by
    rw [hY, Matrix.map_mul (f := c), Matrix.map_mul (f := c), transpose_mul, transpose_mul, transpose_map,
      transpose_transpose]
    simp only [Matrix.mul_assoc]
  have htr : Matrix.trace (Qᵀ * (x * ((x * (a * dD * (a.map c)ᵀ)).map c)ᵀ)) = Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) := by
    rw [hQT, hbs, hYs, hY]
    rw [show u.map c * dD' * uᵀ * (x * (a * dD * (a.map c)ᵀ * (x.map c)ᵀ)) =
      u.map c * (dD' * uᵀ * x * a * dD * (a.map c)ᵀ * (x.map c)ᵀ) by simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (dD' * Y * dD * (Y.map c)ᵀ) =
      algebraMap F E (∑ i, ∑ j, D' i * D j * Algebra.norm F (Y i j)) := by
    simp only [Matrix.trace, diag_apply, mul_apply, dD', dD, diagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, transpose_apply, map_apply,
      map_sum, map_mul, hE.algebraMap_norm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨b, -, -⟩ := hE.basis
  haveI : Module.Free F E := Module.Free.of_basis b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  have hfin : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [pr_eq_half_trace_mat, htr, hsum, Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat,
    inv_mul_cancel_left₀ (two_ne_zero : (2 : F) ≠ 0), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.KSp
