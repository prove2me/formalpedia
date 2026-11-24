-- Prove2me | solution 1 for GlobalTheory.HeightLower.exists_pos_le_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:56.729991+00:00
-- url     : https://prove2.me/submissions/64838a87-b397-4179-b740-874c1e6ba4cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsMaximalMinorNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormDetSubmatrixSqLeDetGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanLeNormMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrame
import Theorems.Thm_GlobalTheory_LatBasis_exists_basis_mem
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_span_ne_zero
import Theorems.Thm_GlobalTheory_det_re_mono_of_posSemidef
import Theorems.Thm_GlobalTheory_exists_maximal_minor_ne_zero_of_linearIndependent
import Theorems.Thm_GlobalTheory_gram_det_mul_le
import Theorems.Thm_GlobalTheory_norm_det_submatrix_sq_le_det_gram
import Theorems.Thm_GlobalTheory_relIndex_span_le_norm_minor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightLower
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightLower
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  intro r X d hd x hx
  obtain ⟨C, hC, hCle⟩ := GlobalTheory.relIndex_span_le_norm_minor r X
  have hω : ∀ τ : X.Ψ, ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (M : Matrix (Fin r) ι ℂ), ((mat x τ * M)ᴴ * (mat x τ * M)).det.re ≤ ω * (Mᴴ * M).det.re :=
    fun τ => GlobalTheory.gram_det_mul_le GlobalTheory.det_re_mono_of_posSemidef r (mat x τ)
  choose ω hω1 hωle using hω
  have hΩ : 0 < ∏ τ, ω τ := Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hω1 τ)
  refine ⟨1 / (C * ∏ τ, ω τ), by positivity, fun W => ?_⟩
  obtain ⟨w, hwi, hwΛ, hspan⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, he, hδ⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hwi
  have hdW := hd x hx _ w hwi hwΛ
  rw [hspan] at hdW
  rw [hdW]
  have hI0 := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X _ w hwi hwΛ
  have hIle := hCle _ w hwi hwΛ e he hδ
  rw [hspan] at hI0 hIle
  set I := ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex
    (X.Λ.toAddSubgroup ⊓ W.toAddSubgroup)) with hIdef
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI0

  have key : ∀ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      ω τ * (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ)
    have h1 := hωle τ _ ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h1
    have h2 := GlobalTheory.norm_det_submatrix_sq_le_det_gram (Fin r) _
      (Matrix.of fun k a => τ.1 (w a k)) e he
    have h3 : ((Matrix.of fun k a => τ.1 (w a k)).submatrix e id).det =
        τ.1 (Matrix.of fun k a => w a (e k)).det := by
      rw [RingHom.map_det]
      congr 1
    rw [h3] at h2
    exact h2.trans h1
  have hprod : ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      (∏ τ, ω τ) * ∏ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ => key τ)
  rw [div_le_div_iff₀ (by positivity) hIpos, one_mul]
  calc (I : ℝ) ≤ C * _ := hIle
    _ ≤ C * ((∏ τ, ω τ) * _) := mul_le_mul_of_nonneg_left hprod hC.le
    _ = _ := by ring
end GlobalTheory.HeightLower
