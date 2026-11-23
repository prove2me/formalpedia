-- Prove2me | solution 1 for GlobalTheory.SW.HAct.norm_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:54.528357+00:00
-- url     : https://prove2.me/submissions/c72eaddc-4012-4bcd-a9ab-14b2d5d74677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) : ‖τ γ.det‖ = 1 := by
  have h2 := congrArg det (map_mem τ h)
  have hJ : (Matrix.J (Fin N) ℂ).det ≠ 0 := (Matrix.isUnit_det_J (Fin N) ℂ).ne_zero
  have hd : (γ.map τ).det = τ γ.det := (RingHom.map_det τ γ).symm
  rw [det_mul, det_mul, det_conjTranspose, hd] at h2
  have h3 : conj (τ γ.det) * τ γ.det = 1 := by
    apply mul_left_cancel₀ hJ
    rw [Complex.star_def] at h2
    linear_combination h2
  have h4 := congrArg norm h3
  rw [norm_mul, Complex.norm_conj, norm_one] at h4
  nlinarith [norm_nonneg (τ γ.det)]
end GlobalTheory.SW.HAct
