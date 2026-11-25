-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.ge_of_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:33.157849+00:00
-- url     : https://prove2.me/submissions/8b20d55f-962f-495e-bc05-255b8e1f6b2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {N : ℕ}
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {Y M : Matrix (Fin N) (Fin N) ℂ} (hY : Y.PosSemidef) (hM : Mᴴ = M)
    (h : Y * M = 1) {T : ℝ} (hT : 0 < T)
    (hle : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef) :
    (Y - ((T⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  have h' : M * Y = 1 := mul_eq_one_comm.1 h
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have p1 := hY.conjTranspose_mul_mul_same (1 - ((T⁻¹ : ℝ) : ℂ) • M)
  have p2 := hle.smul (a := ((T⁻¹ ^ 2 : ℝ) : ℂ)) (by exact_mod_cast sq_nonneg T⁻¹)
  convert p1.add p2 using 1
  have hc : star ((T⁻¹ : ℝ) : ℂ) = ((T⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM, hc]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h, h', smul_sub, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring
end GlobalTheory.SW.Reduct
