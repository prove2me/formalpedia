-- Prove2me | solution 1 for GlobalTheory.CyclicNormCheck.local_norm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:17.181553+00:00
-- url     : https://prove2.me/submissions/94658bdd-eddf-4ef8-ba5a-7db10ce2d960

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_one_tmul_eq
import Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_pos_of_not_extends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck
namespace GlobalTheory.CyclicNormCheck
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Algebra F ℝ] [CharZero F]
    [Module.Finite F E] (hσ : ¬ ∃ τ : E →+* ℝ, τ.comp (algebraMap F E) = algebraMap F ℝ)
    (y : ℝ ⊗[F] E) : 0 ≤ Algebra.norm ℝ y := by
  classical
  let b := Module.finBasis F E
  let B := b.baseChange ℝ
  let f : (Fin (Module.finrank F E) → ℝ) → ℝ := fun t => Algebra.norm ℝ (∑ i, t i • B i)
  have hf : Continuous f := by
    have : f = fun t => (∑ i, t i • Algebra.leftMulMatrix B (B i)).det := by
      funext t
      simp only [f]
      rw [Algebra.norm_eq_matrix_det B, map_sum]
      simp only [map_smul]
    rw [this]
    exact Continuous.matrix_det (by fun_prop)
  have hd : DenseRange (Pi.map fun (_ : Fin (Module.finrank F E)) (q : ℚ) => (q : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hall : ∀ t, 0 ≤ f t := by
    intro t
    refine hd.induction_on t (isClosed_le continuous_const hf) fun q => ?_
    have he : (∑ i, Pi.map (fun (_ : Fin (Module.finrank F E)) (q : ℚ) => (q : ℝ)) q i • B i)
        = (1 : ℝ) ⊗ₜ[F] (∑ i, (q i : F) • b i) := by
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul ℝ (q i : F), map_ratCast]
      simp [B]
    simp only [f]
    rw [he, norm_one_tmul_eq]
    by_cases h0 : (∑ i, (q i : F) • b i) = 0
    · rw [h0, Algebra.norm_zero, map_zero]
    · exact (norm_pos_of_not_extends _ hσ h0).le
  have := hall (B.repr y)
  simpa only [f, B.sum_repr] using this
end GlobalTheory.CyclicNormCheck
