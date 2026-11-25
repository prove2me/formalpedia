-- Prove2me | solution 1 for GlobalTheory.SW.IsType.prod_det_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:23.915655+00:00
-- url     : https://prove2.me/submissions/fdc5b5a5-f536-4ca1-bb63-f7cd31a26f22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_IsType_prod_univ
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot


attribute [local simp] GlobalTheory.SW.rowEmb_apply

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
namespace IsType
theorem _root_.solution {E m n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype m]
    [Fintype n] [DecidableEq n] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (W : Matrix n m E) :
    ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det =
      (((∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 : ℝ) : ℂ) := by
  rw [hΨ.prod_univ, ← Finset.prod_pow, ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : W.map (ComplexEmbedding.conjugate τ.1) * (W.map (ComplexEmbedding.conjugate τ.1))ᴴ =
      (W.map τ.1 * (W.map τ.1)ᴴ)ᵀ := by
    ext i j
    simp [mul_apply, mul_comm]
  have h2 : (((W.map τ.1 * (W.map τ.1)ᴴ).det.re : ℝ) : ℂ) = (W.map τ.1 * (W.map τ.1)ᴴ).det :=
    conj_eq_iff_re.1 (by
      rw [← RCLike.star_def, ← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose])
  rw [h1, det_transpose, ofReal_pow, h2, sq]
end IsType
end GlobalTheory.SW
