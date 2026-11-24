-- Prove2me | solution 1 for GlobalTheory.SW.HAct.im_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:06.948685+00:00
-- url     : https://prove2.me/submissions/36331fad-7b82-4ac5-8879-57fe1045adf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_im_eq

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
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (C * Z + D)ᴴ * imH ((A * Z + B) * (C * Z + D)⁻¹) * (C * Z + D) = imH Z := by
  rw [← im_eq h1 h2 h3 h4 Z]
  generalize A * Z + B = P
  generalize C * Z + D = Q at hQ ⊢
  have hi : Q⁻¹ * Q = 1 := nonsing_inv_mul Q (Ne.isUnit hQ)
  have e1 : P * Q⁻¹ * Q = P := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have e2 : Qᴴ * (P * Q⁻¹)ᴴ = Pᴴ := by rw [← conjTranspose_mul, e1]
  rw [imH, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, e2, Matrix.mul_assoc,
    e1]
end GlobalTheory.SW.HAct
