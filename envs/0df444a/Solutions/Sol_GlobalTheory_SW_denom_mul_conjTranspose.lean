-- Prove2me | solution 1 for GlobalTheory.SW.denom_mul_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:02.011573+00:00
-- url     : https://prove2.me/submissions/5e836fcf-cd32-4c2b-9d10-e1b36e9a904b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose

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
open GlobalTheory GlobalTheory.SW
variable {N : ℕ}
namespace GlobalTheory.SW
theorem _root_.solution (C D X : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hX : X.IsHermitian) (δ : ℝ) :
    (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ =
      (C * X + D) * (C * X + D)ᴴ + ((δ : ℂ) ^ 2) • (C * Cᴴ) := by
  have h1 : D * Cᴴ = C * Dᴴ := by simpa using h.eq
  have h2 : star (I * δ : ℂ) = -(I * δ) := by simp
  have h3 : (δ : ℂ) ^ 2 = -((I * δ) * (I * δ)) := by
    have : I * δ * (I * δ) = (I * I) * (δ : ℂ) ^ 2 := by ring
    rw [this, I_mul_I]; ring
  rw [h3]
  generalize (I * δ : ℂ) = t at h2 ⊢
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, conjTranspose_one, hX.eq, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1]
  module
end GlobalTheory.SW
