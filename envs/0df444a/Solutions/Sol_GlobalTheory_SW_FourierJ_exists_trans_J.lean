-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.exists_trans_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:26.189815+00:00
-- url     : https://prove2.me/submissions/0cb068e8-790e-424e-b28e-3bfa5fb7a7df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_level_mul
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_level
import Theorems.Thm_GlobalTheory_SW_FourierJ_plancherel
import Theorems.Thm_GlobalTheory_SW_FourierJ_trans_J

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    Even (Fintype.card κ) → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ →
      IsSB (ω φ) ∧ TransS (Matrix.J ι ℚ) φ (ω φ) ∧
        ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by
  intro κ ι _ _ _ ⟨p, hp⟩
  refine ⟨fun φ y => I ^ (Fintype.card ι * p) * ft φ y, fun φ ⟨R, hR, h⟩ =>
    ⟨⟨R, hR, ft_level hR h _⟩, trans_J hp hR h, fun φ' ⟨S, hS, h'⟩ => ?_⟩⟩
  refine plancherel (Nat.mul_pos hR hS) (level_mul h S) (by rw [mul_comm]; exact level_mul h' R) _ ?_
  rw [map_pow, ← mul_pow]; simp
end GlobalTheory.SW.FourierJ
