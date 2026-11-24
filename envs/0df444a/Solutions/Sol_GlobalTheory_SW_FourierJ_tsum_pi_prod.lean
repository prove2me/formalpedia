-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.tsum_pi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:52.636008+00:00
-- url     : https://prove2.me/submissions/ec25968e-6ac8-4170-afed-4541ecbc8799

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_prodsum_fin

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
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution : ∀ (κ α : Type) [Fintype κ] (f : κ → α → ℂ), (∀ k, Summable fun a => ‖f k a‖) → (Summable fun m : κ → α => ‖∏ k, f k (m k)‖) ∧ ∑' m : κ → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  intro κ α _ f hf
  set e := (Fintype.equivFin κ).symm
  obtain ⟨h1, h2⟩ := prodsum_fin α _ (fun k => f (e k)) fun k => hf _
  have h : ∀ m : Fin (Fintype.card κ) → α, ∏ k, f k ((e.arrowCongr (Equiv.refl α)) m k) =
      ∏ k, f (e k) (m k) := by
    intro m; rw [← e.prod_comp]; simp
  constructor
  · rw [← (e.arrowCongr (Equiv.refl α)).summable_iff]
    simpa only [Function.comp_def, h] using h1
  · rw [← (e.arrowCongr (Equiv.refl α)).tsum_eq, ← e.prod_comp, ← h2]
    simp only [h]
end GlobalTheory.SW.FourierJ
