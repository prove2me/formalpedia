-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.isSB_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:29:35.784386+00:00
-- url     : https://prove2.me/submissions/ce05ca2f-201e-454b-bd47-809c605ce809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
omit [IsCMField E]
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    IsSB (φ + ψ) := by
  obtain ⟨R, hR, h1, h2⟩ := hφ
  obtain ⟨S, hS, h3, h4⟩ := hψ
  have k : ∀ (m : ℕ) (y : Matrix (Fin n) (Fin N) E), IntM y → IntM ((m : E) • y) :=
    fun m y hy i j => (isIntegral_natCast (R := ℤ) m).mul (hy i j)
  refine ⟨R * S, by positivity, fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases h : φ x = 0
    · rw [Pi.add_apply, h, zero_add] at hx
      rw [Nat.cast_mul, mul_smul]; exact k _ _ (h3 x hx)
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact k _ _ (h1 x h)
  · have e1 := h2 x _ (k S y hy)
    have e2 := h4 x _ (k R y hy)
    rw [smul_smul] at e1 e2
    rw [Pi.add_apply, Pi.add_apply, Nat.cast_mul, e1, mul_comm, e2]
end GlobalTheory.SW.WeilAdm
