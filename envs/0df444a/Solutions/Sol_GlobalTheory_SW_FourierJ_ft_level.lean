-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ft_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:59:01.738482+00:00
-- url     : https://prove2.me/submissions/52012a62-807d-44bd-9f49-f94faf4030c2

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
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_comm
import Theorems.Thm_GlobalTheory_SW_FourierJ_pr_smul_swap
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_pr_int
import Theorems.Thm_GlobalTheory_SW_FourierJ_ft_supp
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
theorem _root_.solution {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) (c : ℂ) :
    HasLevel R fun y => c * ft φ y := by
  refine ⟨fun y hy => ft_supp hR h y (right_ne_zero_of_mul hy), fun y z hz => ?_⟩
  simp only [ft]
  congr 2
  ext x
  by_cases hx : φ x = 0
  · simp [hx]
  · rw [pr_comm, pr_add_left, ech_add, pr_smul_swap, ech_pr_int hz (h.1 x hx), mul_one, pr_comm]
end GlobalTheory.SW.FourierJ
