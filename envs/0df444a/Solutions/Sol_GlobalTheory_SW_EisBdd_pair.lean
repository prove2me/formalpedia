-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:47:13.604607+00:00
-- url     : https://prove2.me/submissions/6f90d56a-1cd8-40ef-8b82-d18b53ccede1

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
import Theorems.Thm_GlobalTheory_SW_Base_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_Model_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_Parab_blocks
import Theorems.Thm_GlobalTheory_SW_TransComp_blocks
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
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
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) (τ : Ψ) :
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).IsHermitian ∧
    (γ.toBlocks₂₁.map τ.1 * (γ.toBlocks₂₁.map τ.1)ᴴ +
      γ.toBlocks₂₂.map τ.1 * (γ.toBlocks₂₂.map τ.1)ᴴ).PosDef ∧
    (hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det ≠ 0 := by
  have h1 := HAct.map_mem τ.1 (HAct.group_part h).2.2.1
  rw [HAct.map_ccT, HAct.map_blocks, fromBlocks_conjTranspose] at h1
  have h2 := (HAct.blocks h1).2.2.2
  rw [conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2
  have h3 := (((unitary_act_halfSpace E Ψ N γ h).2 _ (Base.I_mem_Hn Ψ)).1 τ).1
  refine ⟨?_, ?_, h3⟩
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, h2]
  · have h4 := PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h3)))
    refine (congrArg PosDef ?_).mp h4
    simp only [hDen, Matrix.mul_smul, Matrix.mul_one, conjTranspose_add, conjTranspose_smul,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, smul_add, smul_smul, h2, Complex.star_def,
      conj_I]
    rw [show -I * I = 1 by simp, one_smul, neg_smul]
    abel
end GlobalTheory.SW.EisBdd
