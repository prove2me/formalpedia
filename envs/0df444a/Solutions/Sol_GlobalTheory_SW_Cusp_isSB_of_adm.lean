-- Prove2me | solution 1 for GlobalTheory.SW.Cusp.isSB_of_adm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:34.201513+00:00
-- url     : https://prove2.me/submissions/0bace69d-8761-4510-9d3d-c804fe00b76e

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
import Theorems.Thm_GlobalTheory_SW_Cusp_exists_den
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_UU
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den
import Theorems.Thm_GlobalTheory_SW_Model_one_mem_UU
import Theorems.Thm_GlobalTheory_SW_NearPrim_exists_den
import Theorems.Thm_GlobalTheory_SW_Parab_exists_den
import Theorems.Thm_GlobalTheory_T_weil_action_level_supNorm_uniform_in_lattice


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Cusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
namespace GlobalTheory.SW.Cusp
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ}
    {φ : Fam E n N} (hφ : admitted M R φ) : ∀ Λ ∈ Vset E n M, IsSB (φ Λ) := by
  intro Λ hΛ
  obtain ⟨c, hc, hd⟩ := exists_den (1 : M2 E N)
  obtain ⟨_, _, -, h⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hφ.pos.2
  exact (h M Λ hΛ 1 Base.one_mem_UU hd (φ Λ) ⟨hφ.supp Λ hΛ, hφ.per Λ hΛ⟩).1
end GlobalTheory.SW.Cusp
