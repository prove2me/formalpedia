-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.aPart_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:43.501668+00:00
-- url     : https://prove2.me/submissions/56389375-3400-4245-b5f9-4ecf0ed1d29e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_summable_norm_rpow
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_inv_natPow_rpow_neg_half_even_eq_pow
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_rpow_le_add
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_prod_latPt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory.HeckeTwo.APart
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (GlobalTheory.HeckeTwo.aPart 𝔞) GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by
  intro F _ _ _ 𝔞
  set P : Quotient (unitRel (latM 𝔞)) → ℂ := fun c => ∏ τ : Emb F, latPt 0 ((c.out.1 : F), (0 : F)) τ with hP
  have hP0 : ∀ c, P c ≠ 0 := fun c => by
    simp only [hP, prod_latPt_zero]
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero
    · exact_mod_cast (Algebra.norm_ne_zero_iff).2 c.out.2.2
  set K : ℝ := ‖(2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F)‖ with hK
  have hK0 : 0 < K := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact norm_pos_iff.2 (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hπ) I_ne_zero))
  have hnP : ∀ c, ‖P c‖ = K * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := fun c => by
    simp only [hP, prod_latPt_zero, norm_mul, hK]
    congr 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∀ t : ℝ, 1 < t → Summable fun c => ‖P c‖ ^ (-t) := fun t ht =>
    ((summable_norm_rpow (latM 𝔞) ht).mul_left (K ^ (-t))).congr fun c => by
      rw [hnP, Real.mul_rpow hK0.le (abs_nonneg _)]
  have hnorm : ∀ c σ, ‖eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))‖ = ‖P c‖⁻¹ ^ 2 * ‖P c‖ ^ (-2 * σ.re) := fun c σ => by
    show ‖(P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)‖ = _
    rw [norm_mul, norm_pow, norm_inv, norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 (hP0 c))]
    simp
  intro σ₀ hσ₀
  have hσ₀' : -1 / 2 < σ₀.re := hσ₀
  set r : ℝ := (σ₀.re - 1 / 2) / 2 with hr
  set R : ℝ := σ₀.re + 1 with hR
  set U : Set ℂ := {σ | r < σ.re} ∩ {σ | σ.re < R} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hmem : σ₀ ∈ U := ⟨by show r < σ₀.re; rw [hr]; linarith, by show σ₀.re < R; rw [hR]; linarith⟩
  have hd : DifferentiableOn ℂ (fun σ => ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 ((c.out.1 : F), (0 : F))) U := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun c => ‖P c‖⁻¹ ^ 2 * (‖P c‖ ^ (-2 * r) + ‖P c‖ ^ (-2 * R))) ?_ ?_ hU ?_
    · refine ((hsum (2 + 2 * r) (by rw [hr]; linarith)).add (hsum (2 + 2 * R) (by rw [hR]; linarith))).congr
        fun c => ?_
      have hx := norm_pos_iff.2 (hP0 c)
      rw [inv_natPow_rpow_neg_half_even_eq_pow hx, inv_natPow_rpow_neg_half_even_eq_pow hx]
      ring
    · intro c σ _
      show DifferentiableWithinAt ℂ (fun σ => (P c)⁻¹ ^ 2 * ((‖P c‖ : ℝ) : ℂ) ^ (-2 * σ)) U σ
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.const_mul ?_ _)
      refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
      exact_mod_cast (norm_pos_iff.2 (hP0 c)).ne'
    · intro c σ hσ
      rw [hnorm]
      have hx := norm_pos_iff.2 (hP0 c)
      gcongr
      exact rpow_le_add hx hσ.1.le hσ.2.le
  exact (hd.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt
end GlobalTheory.HeckeTwo
