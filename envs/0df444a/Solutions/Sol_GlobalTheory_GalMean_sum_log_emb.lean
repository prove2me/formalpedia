-- Prove2me | solution 1 for GlobalTheory.GalMean.sum_log_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:41.9568+00:00
-- url     : https://prove2.me/submissions/7f15144b-924c-44bf-a983-bbc206843244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open IntermediateField
namespace GlobalTheory.GalMean
theorem _root_.solution (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [NumberField L] (β : ℂ) (hβ : β ∈ L)
    (h0 : β ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ Module.finrank ℚ L = m * (minpoly ℚ β).natDegree ∧
      ∑ τ : L →+* ℂ, Real.log ‖τ ⟨β, hβ⟩‖ = m * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by
  set b : L := ⟨β, hβ⟩
  have hint : IsIntegral ℚ b := .of_finite ℚ b
  have hmin : minpoly ℚ b = minpoly ℚ β := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ L ℂ) Subtype.val_injective b
    exact this.symm
  have h2 := Algebra.norm_eq_norm_adjoin ℚ b
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ b) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen,
      IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  set m := Module.finrank ℚ⟮b⟯ L
  refine ⟨m, Module.finrank_pos, ?_, ?_⟩
  · rw [← Module.finrank_mul_finrank ℚ ℚ⟮b⟯ L, IntermediateField.adjoin.finrank hint, hmin, mul_comm]
  · have hN : |Algebra.norm ℚ b| = |(minpoly ℚ β).coeff 0| ^ m := by
      rw [h2, abs_pow]; erw [h3]; rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ b
    have hne : ∀ τ : L →+* ℂ, ‖τ b‖ ≠ 0 := fun τ => by
      rw [norm_ne_zero_iff]; exact (map_ne_zero τ).2 (fun h => h0 (congrArg Subtype.val h))
    rw [← Real.log_prod (fun τ _ => hne τ), ← norm_prod]
    have e : ∏ τ : L →+* ℂ, τ b = ∏ σ : L →ₐ[ℚ] ℂ, σ b :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun τ => rfl)
    rw [e, ← hprod, eq_ratCast, Complex.norm_ratCast]
    rw [show |((Algebra.norm ℚ b : ℚ) : ℝ)| = (((|Algebra.norm ℚ b|) : ℚ) : ℝ) by push_cast; rfl, hN]
    push_cast
    rw [Real.log_pow]
end GlobalTheory.GalMean
