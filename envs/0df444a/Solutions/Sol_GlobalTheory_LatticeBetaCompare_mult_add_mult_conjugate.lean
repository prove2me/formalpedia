-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.mult_add_mult_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:48.384498+00:00
-- url     : https://prove2.me/submissions/d927cea3-0558-4317-be99-7cffe52dab2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution (τ : E →+* ℂ) :
    Dw.mult τ + Dw.mult (ComplexEmbedding.conjugate τ) = Dw.p + Dw.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h2 : starRingEnd ℂ (τ (H.rt : E)) = -τ (H.rt : E) := by
    generalize τ (H.rt : E) = z at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at hre him
    have h0 : z.re = 0 := by
      by_contra h
      have : z.im = 0 := mul_left_cancel₀ h (by linarith)
      rw [this] at hre
      nlinarith
    apply Complex.ext <;> simp [h0]
  have h3 : H.rt0 ≠ -H.rt0 := fun h => by
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have := H.sqrt_neg_disc_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  simp only [Datum.mult, ComplexEmbedding.conjugate_coe_eq, h2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · rw [h, if_pos rfl, if_neg h3.symm]
  · rw [h, neg_neg, if_pos rfl, if_neg h3.symm, add_comm]
end GlobalTheory.LatticeBetaCompare
