-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.im_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:22.574976+00:00
-- url     : https://prove2.me/submissions/58983dfd-bc2e-40c6-9f85-f665883df32b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisBdd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.EisBdd
theorem _root_.solution {W : Matrix (Fin N) (Fin N) ℂ} (h : (imH W).PosSemidef) (v : Fin N → ℂ) :
    0 ≤ (v ⬝ᵥ W *ᵥ star v).im := by
  have h1 := h.re_dotProduct_nonneg (star v)
  have h2 : v ⬝ᵥ Wᴴ *ᵥ star v = conj (v ⬝ᵥ W *ᵥ star v) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, conjTranspose_apply, map_sum, map_mul,
      Pi.star_apply, Complex.star_def, conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [star_star, imH, smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub, h2,
    Complex.sub_conj, smul_eq_mul] at h1
  have h3 : (2 * I)⁻¹ * (((2 * (v ⬝ᵥ W *ᵥ star v).im : ℝ) : ℂ) * I) =
      ((v ⬝ᵥ W *ᵥ star v).im : ℂ) := by
    push_cast; field_simp
  rw [h3] at h1
  simpa using h1
end GlobalTheory.SW.EisBdd
