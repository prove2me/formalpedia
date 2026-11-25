-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:42.835453+00:00
-- url     : https://prove2.me/submissions/00a0ccf6-27fe-4a11-b8f4-608cc714629c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_one_le_prod
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution (h : IsType Ψ) {m D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E}
    {H : CM Ψ m m} (h0 : G.det ≠ 0) (hG : Den D G⁻¹) (hH : IsMaj Ψ G H) :
    ∏ τ, ‖(H τ).det‖ ≤ ∏ _τ : Ψ, (D : ℝ) ^ m := by
  have ha : IsIntegral ℤ ((D : E) • G⁻¹).det := IsIntegral.det hG
  have hd : ((D : E) • G⁻¹).det = (D : E) ^ m * (G.det)⁻¹ := by simp
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 := one_le_prod h ha (by rw [hd]; exact mul_ne_zero (pow_ne_zero _ hD') (inv_ne_zero h0))
  refine (le_mul_of_one_le_right (Finset.prod_nonneg fun _ _ => norm_nonneg _) h1).trans_eq ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h2 := congrArg (fun A => ‖Matrix.det A‖) (hH τ).2
  have h3 : (G.map τ.1).det = τ.1 G.det := (RingHom.map_det _ _).symm
  have h4 : 0 < ‖τ.1 G.det‖ := by simpa using h0
  simp only [det_mul, det_nonsing_inv, Ring.inverse_eq_inv', h3, norm_mul, norm_inv] at h2
  have h5 : ‖(H τ).det‖ = ‖τ.1 G.det‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) h4.le]
    field_simp at h2
    exact h2
  rw [hd, h5]
  simp only [map_mul, map_pow, map_natCast, map_inv₀, norm_mul, norm_pow, norm_inv,
    Complex.norm_natCast]
  field_simp
end GlobalTheory.SW.MinkowskiProductBounds
