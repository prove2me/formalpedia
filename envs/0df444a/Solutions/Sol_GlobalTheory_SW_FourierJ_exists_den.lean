-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:35.016802+00:00
-- url     : https://prove2.me/submissions/dd6d7531-05e1-4fce-bae8-1f72caa583bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar

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
theorem _root_.solution (y : Matrix κ ι ℚ) : ∃ S : ℕ, 0 < S ∧ IntM ((S : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => (y p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨d, hd⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  have : (((∏ p : κ × ι, (y p.1 p.2).den : ℕ) : ℚ) • y) k i = ((d * (y k i).num : ℤ) : ℚ) := by
    rw [hd, Matrix.smul_apply, smul_eq_mul]; push_cast
    rw [← Rat.den_mul_eq_num]; ring
  rw [this]
  exact isIntegral_algebraMap (R := ℤ) (x := d * (y k i).num)
end GlobalTheory.SW.FourierJ
