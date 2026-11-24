-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Short.one_le_norm_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:03.616963+00:00
-- url     : https://prove2.me/submissions/7833a8c9-5744-4720-9b52-9f3267031370

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short
namespace GlobalTheory.SmoothForms.Short
theorem _root_.solution {E : Type} [Field E] [NumberField E] {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (haT : house a ≤ T) (ψ : E →+* ℂ) : 1 ≤ ‖ψ a‖ * T ^ finrank ℚ E := by
  classical
  have h1 : (1 : ℝ) ≤ ∏ φ : E →+* ℂ, ‖φ a‖ := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ a) _ (fun _ => rfl)] at h
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Algebra.norm_ne_zero_iff (R := ℚ)).2 h0 (by rw [← hm, map_zero])
    rw [← norm_prod, ← h, ← hm]
    simp only [algebraMap_int_eq, eq_intCast, eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ψ)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (Finset.prod_le_prod (g := fun _ => T) (fun _ _ => norm_nonneg _)
    fun φ _ => (norm_le_pi_norm (canonicalEmbedding E a) φ).trans haT).trans ?_
  rw [Finset.prod_const, ← Embeddings.card E ℂ]
  exact pow_le_pow_right₀ hT (Finset.card_le_univ _)
end GlobalTheory.SmoothForms.Short
