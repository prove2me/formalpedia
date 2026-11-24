-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.intM_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:07.322454+00:00
-- url     : https://prove2.me/submissions/02b92069-f2c3-490d-948b-9fdac83dfdd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_intM_iff
import Theorems.Thm_GlobalTheory_SW_HaarLevel_intM_iff


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
theorem _root_.solution {R : ℕ} (hR : 0 < R) (n : κ → ι → Fin (R * R)) : IntM ((R : ℚ) • rep R n) := by
  refine (intM_iff _).2 ⟨fun k i => ((n k i : ℕ) : ℤ), ?_⟩
  have : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  ext k i; simp [rep, zm]; field_simp
end GlobalTheory.SW.FourierJ
