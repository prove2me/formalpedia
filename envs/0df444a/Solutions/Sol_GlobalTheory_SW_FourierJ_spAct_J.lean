-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.spAct_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:12.364423+00:00
-- url     : https://prove2.me/submissions/e9d18309-abf4-46bd-90af-7c7765e33103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_spDen_J

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
theorem _root_.solution [DecidableEq ι] (τ : Matrix ι ι ℂ) : spAct (Matrix.J ι ℚ) τ = -τ⁻¹ := by
  have h1 : qm (-1 : Matrix ι ι ℚ) = -1 := by
    ext i j; simp [qm, Matrix.one_apply]; split_ifs <;> simp
  have h0 : qm (0 : Matrix ι ι ℚ) = 0 := by ext i j; simp [qm]
  rw [spAct, spDen_J]
  simp [Matrix.J, h1, h0]
end GlobalTheory.SW.FourierJ
