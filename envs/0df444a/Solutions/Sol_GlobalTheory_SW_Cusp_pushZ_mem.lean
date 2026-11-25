-- Prove2me | solution 1 for GlobalTheory.SW.Cusp.pushZ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:11.709592+00:00
-- url     : https://prove2.me/submissions/692aba95-d6cb-42fb-b36b-5f8fe8fd8d9c

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
import Theorems.Thm_GlobalTheory_IsSiegel_smul
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
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (v : Fin N → E) {t : ℝ}
    (ht : 0 ≤ t) : pushZ Ψ Z v t ∈ Hn Ψ N := by
  intro τ
  have e : imH (pushZ Ψ Z v t τ) = imH (Z τ) +
      (t : ℂ) • vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) := by
    ext i j
    simp [imH, pushZ, vecMulVec_apply, Matrix.conjTranspose_apply]
    field_simp
    linear_combination (-2 * (t : ℂ) * τ.1 (v i) * conj (τ.1 (v j))) * I_sq
  rw [e]
  exact (hZ τ).add_posSemidef
    ((Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht))
end GlobalTheory.SW.Cusp
