-- Prove2me | solution 1 for GlobalTheory.SW.Cusp.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:09.798133+00:00
-- url     : https://prove2.me/submissions/5d0a64ad-0847-4540-97b8-94af37363dfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilActionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelOperatorHermitianEisensteinSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SwdTendstoZeroAtCusps
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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Cusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Cusp
theorem _root_.solution (v : Fin (N + 1) → E) (hv : v ≠ 0) :
    ∃ a b : Matrix (Fin (N + 1)) (Fin (N + 1)) E, b * a = 1 ∧ a *ᵥ v = Pi.single 0 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  let b : Matrix (Fin (N + 1)) (Fin (N + 1)) E :=
    ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).submatrix id (Equiv.swap 0 i)
  have hd : ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) E).updateCol i v).det = v i := by
    rw [← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hb : IsUnit b.det := by
    rw [Matrix.det_permute', hd]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.2 hi)
    exact (Equiv.Perm.sign (Equiv.swap 0 i)).isUnit.map (Int.castRingHom E)
  have hbv : b *ᵥ Pi.single 0 1 = v := by
    ext k; simp [b]
  refine ⟨b⁻¹, b, Matrix.mul_nonsing_inv b hb, ?_⟩
  rw [← hbv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul b hb, Matrix.one_mulVec]
end GlobalTheory.SW.Cusp
