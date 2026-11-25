-- Prove2me | solution 1 for GlobalTheory.SW.SwdAut.add_mem_Hn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:34.743865+00:00
-- url     : https://prove2.me/submissions/dc6e5ef6-54c7-459b-aa7d-a4ce702084e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
import Theorems.Thm_GlobalTheory_SW_Base_ccT_map


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SwdAut
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
namespace GlobalTheory.SW.SwdAut
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : (fun τ => Z τ + β.map τ.1 : CM Ψ N N) ∈ Hn Ψ N := by
  intro τ
  have : imH (Z τ + β.map τ.1) = imH (Z τ) := by
    unfold imH
    rw [conjTranspose_add, ← Base.ccT_map, hβ, add_sub_add_right_eq_sub]
  change (imH (Z τ + β.map τ.1)).PosDef
  rw [this]; exact hZ τ
end GlobalTheory.SW.SwdAut
