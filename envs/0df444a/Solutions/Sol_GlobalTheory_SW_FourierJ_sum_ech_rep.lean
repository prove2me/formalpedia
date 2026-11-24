-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.sum_ech_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:15.861181+00:00
-- url     : https://prove2.me/submissions/49fe89c8-e21f-4749-9620-d362fcb6bc8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_orth_one
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_sum


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
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ), 0 < R → ∀ a b : κ → ι → Fin (R * R), ∑ n : κ → ι → Fin (R * R), ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) = if a = b then ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι)) ^ 2 else 0 := by
  intro κ ι _ _ _ _ R hR a b
  have h : ∀ n : κ → ι → Fin (R * R), ech (∑ k, (rep R a k - rep R b k) ⬝ᵥ rep R n k) =
      ∏ k, ∏ i, ech ((((a k i : ℕ) : ℚ) / R - ((b k i : ℕ) : ℚ) / R) *
        (((n k i : ℕ) : ℚ) / R)) := by
    intro n; simp only [dotProduct, ech_sum]; rfl
  simp only [h]
  rw [← Fintype.prod_sum (fun k (v : ι → Fin (R * R)) => ∏ i, ech ((((a k i : ℕ) : ℚ) / R -
    ((b k i : ℕ) : ℚ) / R) * (((v i : ℕ) : ℚ) / R)))]
  have h2 : ∀ k, ∑ v : ι → Fin (R * R), ∏ i, ech ((((a k i : ℕ) : ℚ) / R -
      ((b k i : ℕ) : ℚ) / R) * (((v i : ℕ) : ℚ) / R)) =
      ∏ i, if a k i = b k i then (R : ℂ) ^ 2 else 0 := by
    intro k
    rw [← Fintype.prod_sum (fun i (v : Fin (R * R)) => ech ((((a k i : ℕ) : ℚ) / R -
      ((b k i : ℕ) : ℚ) / R) * (((v : ℕ) : ℚ) / R)))]
    simp only [orth_one hR]
  simp only [h2]
  split_ifs with hab
  · simp [hab, ← pow_mul]; ring_nf
  · obtain ⟨k, hk⟩ := Function.ne_iff.1 hab
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hk
    exact Finset.prod_eq_zero (Finset.mem_univ k)
      (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi))
end GlobalTheory.SW.FourierJ
