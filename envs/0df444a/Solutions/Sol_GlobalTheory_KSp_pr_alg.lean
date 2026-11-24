-- Prove2me | solution 1 for GlobalTheory.KSp.pr_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:16.526902+00:00
-- url     : https://prove2.me/submissions/c1901cbc-61aa-46fa-a58e-35f742fe95c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicProperties
import Theorems.Thm_GlobalTheory_KSp_pr_eq_trace
import Theorems.Thm_GlobalTheory_KSp_trace_single_pair
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
noncomputable section
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.invol
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E, prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      simp only [Matrix.trace, diag, mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc, hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.basis
    haveI : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      simp [mul_apply, map_sum, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]
end GlobalTheory.KSp
