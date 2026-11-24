-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.ft_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:00.954813+00:00
-- url     : https://prove2.me/submissions/ce128a06-41de-4796-849c-804eeb135bb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_level_ch
import Theorems.Thm_GlobalTheory_T_schwartzBruhatIntegral_eq_sum_residueRepresentatives


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
theorem _root_.solution [DecidableEq κ] [DecidableEq ι] {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι ℚ → ℂ}
    (h : HasLevel R φ) {y : Matrix κ ι ℚ} (hy : IntM ((R : ℚ) • y)) :
    ft φ y = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
      ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ech (pr (rep R n) y) :=
  GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives κ ι R _ hR (level_ch h hy)
end GlobalTheory.SW.FourierJ
