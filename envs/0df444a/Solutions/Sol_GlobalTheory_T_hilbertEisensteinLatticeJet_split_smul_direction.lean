-- Prove2me | solution 1 for GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:21:53.287977+00:00
-- url     : https://prove2.me/submissions/ec6b71b6-7137-4be3-9626-aeef8e6ac7e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSplitSmulDirection
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeJetSplitSmulDirectionStatement
import Theorems.Thm_GlobalTheory_HilbFam_jet_split_smul_direction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_smul_direction | exact GlobalTheory.HilbFam.jet_split_smul_direction | (intros; apply GlobalTheory.HilbFam.jet_split_smul_direction <;> assumption)
end _root_.GlobalTheory.T
