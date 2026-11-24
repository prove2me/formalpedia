-- Prove2me | solution 1 for GlobalTheory.SW.Emb.cor_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:17.843121+00:00
-- url     : https://prove2.me/submissions/52a96ddc-3712-4a7d-9074-f412dbb9a83c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
import Theorems.Thm_GlobalTheory_SW_Emb_cor_mul
import Theorems.Thm_GlobalTheory_SW_Emb_cor_one

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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
namespace GlobalTheory.SW.Emb
theorem _root_.solution (A : Matrix (Fin N) (Fin N) ℂ) (h : A.det ≠ 0) : (cor 1 A)⁻¹ = cor 1 A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [cor_mul, one_mul, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h), cor_one]
end GlobalTheory.SW.Emb
