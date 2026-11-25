-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.gram_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:13.032964+00:00
-- url     : https://prove2.me/submissions/fdd9a177-005a-4d4a-8630-35e3ef454a7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_fac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution {m : ℕ} {H G : Matrix (Fin m) (Fin m) ℂ} (hH : H.PosDef) (hG : Gᴴ = G)
    (h0 : G.det ≠ 0) (hm : H * G⁻¹ * H = G) (x y : Fin m → ℂ) {C : ℝ}
    (hx : (x ⬝ᵥ H *ᵥ star x).re ≤ C) (hy : (y ⬝ᵥ H *ᵥ star y).re ≤ C) :
    ‖x ⬝ᵥ G *ᵥ star y‖ ≤ C := by
  obtain ⟨B, -, h2, h3⟩ := fac hH
  have hG' : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG]
  have h4' : ∀ y, x ⬝ᵥ G *ᵥ y = (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ y := fun y => by
    rw [← dotProduct_mulVec, mulVec_mulVec, hm]
  have h5 : (x ᵥ* (H * G⁻¹)) ⬝ᵥ H *ᵥ star (x ᵥ* (H * G⁻¹)) = x ⬝ᵥ H *ᵥ star x := by
    rw [← h4', star_vecMul, mulVec_mulVec, conjTranspose_mul, hG', hH.1.eq,
      mul_nonsing_inv_cancel_left _ _ h0.isUnit]
  rw [← h5, h3] at hx
  rw [h3] at hy
  rw [h4', h2]
  refine (norm_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖WithLp.toLp 2 (y ᵥ* B)‖ - ‖WithLp.toLp 2 ((x ᵥ* (H * G⁻¹)) ᵥ* B)‖)]
end GlobalTheory.SW.MinkowskiProductBounds
