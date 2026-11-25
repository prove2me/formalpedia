-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.approx_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:02.508165+00:00
-- url     : https://prove2.me/submissions/e00506a5-ad65-4163-9d0e-7cc2b94fe563

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
import Theorems.Thm_GlobalTheory_SW_EisBdd_approx_entry
import Theorems.Thm_GlobalTheory_SW_Base_isIntegral_cc
import Theorems.Thm_GlobalTheory_SW_Base_map_cc
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
theorem _root_.solution (hΨ : IsType Ψ) : ∃ K : ℝ, ∀ Z : CM Ψ N N,
    ∃ β : Matrix (Fin N) (Fin N) E, ccT β = β ∧ IntM β ∧
      ∀ (τ : Ψ) a b, ‖((Z τ - β.map τ.1) + (Z τ - β.map τ.1)ᴴ) a b‖ ≤ K := by
  obtain ⟨K, hK⟩ := approx_entry hΨ
  refine ⟨4 * K, fun Z => ?_⟩
  choose y hy hyK using fun a b : Fin N => hK fun τ => (Z τ a b + conj (Z τ b a)) / 4
  refine ⟨Matrix.of fun a b => y a b + cc (y b a), ?_, fun a b => (hy a b).add
    (Base.isIntegral_cc (hy b a)), fun τ a b => ?_⟩
  · ext a b; simp [ccT, cc, add_comm]
  · have e : ((Z τ - (Matrix.of fun a b => y a b + cc (y b a)).map τ.1) +
        (Z τ - (Matrix.of fun a b => y a b + cc (y b a)).map τ.1)ᴴ) a b =
        2 * ((Z τ a b + conj (Z τ b a)) / 4 - τ.1 (y a b)) +
        2 * conj ((Z τ b a + conj (Z τ a b)) / 4 - τ.1 (y b a)) := by
      simp [Base.map_cc, Matrix.conjTranspose_apply, map_ofNat]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_two]
    linarith [hyK a b τ, hyK b a τ]
end GlobalTheory.SW.EisBdd
