-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.level_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:10.61826+00:00
-- url     : https://prove2.me/submissions/97ac2569-0125-48ef-bce2-4dffb70cf1ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_add_left
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_smul_swap
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_pr_int
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_add


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
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) {y : Matrix κ ι ℚ}
    (hy : IntM ((R : ℚ) • y)) : HasLevel R fun x => φ x * ech (pr x y) := by
  refine ⟨fun x hx => h.1 x (left_ne_zero_of_mul hx), fun x z hz => ?_⟩
  simp only
  rw [h.2 x z hz, pr_add_left, ech_add, pr_smul_swap, ech_pr_int hz hy, mul_one]
end GlobalTheory.SW.FourierJ
