-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.prodsum_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:10.491045+00:00
-- url     : https://prove2.me/submissions/6c9968f1-27d6-4c9e-8a99-a40cbd8d2918

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
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution (α : Type) (n : ℕ) (f : Fin n → α → ℂ) (hf : ∀ k, Summable fun a => ‖f k a‖) :
    (Summable fun m : Fin n → α => ‖∏ k, f k (m k)‖) ∧
      ∑' m : Fin n → α, ∏ k, f k (m k) = ∏ k, ∑' a, f k a := by
  induction n with
  | zero => exact ⟨Summable.of_finite, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun k => f k.succ) fun k => hf _
    have e : ∀ q : α × (Fin n → α), ∏ k, f k ((Fin.consEquiv fun _ => α) q k) =
        f 0 q.1 * ∏ k : Fin n, f k.succ (q.2 k) := by
      intro q; rw [Fin.prod_univ_succ]; rfl
    constructor
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).summable_iff]
      have := (hf 0).mul_norm h1
      simpa only [Function.comp_def, e] using this
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => α).tsum_eq, Fin.prod_univ_succ, ← h2,
        tsum_mul_tsum_of_summable_norm (hf 0) h1]
      simp only [e]
end GlobalTheory.SW.FourierJ
