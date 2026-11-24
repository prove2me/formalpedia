-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.tsum_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:26:02.127869+00:00
-- url     : https://prove2.me/submissions/d7b4517f-2bec-4cbe-b798-e8608c3e172c

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
theorem _root_.solution {R : ℕ} (hR : 0 < R) {ψ : Matrix κ ι ℚ → ℂ} (h : HasLevel R ψ)
    (G : Matrix κ ι ℚ → ℂ) :
    ∑' y, ψ y * G y = ∑' m : κ → ι → ℤ, ψ ((R : ℚ)⁻¹ • zm m) * G ((R : ℚ)⁻¹ • zm m) := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hinj : Function.Injective fun m : κ → ι → ℤ => (R : ℚ)⁻¹ • zm m := by
    intro m m' hm
    ext k i
    have := congrFun (congrFun hm k) i
    simpa [zm, hR.ne'] using this
  refine (hinj.tsum_eq (f := fun y => ψ y * G y) ?_).symm
  intro y hy
  obtain ⟨m, hm⟩ := (intM_iff _).1 (h.1 y (left_ne_zero_of_mul hy))
  exact ⟨m, by simp only [← hm, smul_smul, inv_mul_cancel₀ hR0, one_smul]⟩
end GlobalTheory.SW.FourierJ
