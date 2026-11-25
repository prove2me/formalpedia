-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.norm_reflexNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:20.432132+00:00
-- url     : https://prove2.me/submissions/81aed9ed-c41b-4c6c-9dcd-1f38f07349ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_mult_add_mult_conjugate
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
theorem _root_.solution (γ : E) (s : c.F →+* ℂ) :
    ‖s (reflexNorm Dw c γ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ (Dw.p + Dw.q) := by
  have h1 : ∀ σ : E →+* ℂ, ‖s (embF c (ComplexEmbedding.conjugate σ) γ)‖ = ‖s (embF c σ γ)‖ := fun σ => by
    have e : embF c (ComplexEmbedding.conjugate σ) γ = embF c σ (IsCMField.complexConj E γ) :=
      Subtype.ext (IsCMField.complexEmbedding_complexConj E σ γ).symm
    have := IsCMField.complexEmbedding_complexConj E (s.comp (embF c σ)) γ
    rw [e]
    exact (congrArg norm this).trans (Complex.norm_conj _)
  have h2 : ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult σ =
      ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ ^ Dw.mult (ComplexEmbedding.conjugate σ) := by
    rw [← Equiv.prod_comp (ComplexEmbedding.involutive_conjugate E).toPerm]
    simp only [Function.Involutive.coe_toPerm, h1]
  have h3 : |(Algebra.norm ℚ γ : ℝ)| = ∏ σ : E →+* ℂ, ‖s (embF c σ γ)‖ := by
    have hb : Function.Bijective fun σ : E →+* ℂ => s.comp (embF c σ) :=
      Finite.injective_iff_bijective.1 fun σ τ h => RingHom.ext fun x =>
        congrArg Subtype.val (s.injective (DFunLike.congr_fun h x))
    rw [← norm_prod, Fintype.prod_bijective _ hb (fun σ => s (embF c σ γ)) (fun σ => σ γ) fun _ => rfl,
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun σ : E →+* ℂ => σ γ) (fun σ : E →ₐ[ℚ] ℂ => σ γ) fun _ => rfl,
      ← Algebra.norm_eq_prod_embeddings]
    simp
  rw [reflexNorm, map_prod, norm_prod, h3, sq]
  simp only [map_pow, norm_pow]
  nth_rewrite 2 [h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun σ _ => by rw [← pow_add, mult_add_mult_conjugate]
end GlobalTheory.LatticeBetaCompare
