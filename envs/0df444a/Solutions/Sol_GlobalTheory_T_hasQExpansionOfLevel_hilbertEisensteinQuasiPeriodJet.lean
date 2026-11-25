-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:11.435901+00:00
-- url     : https://prove2.me/submissions/14c89fa6-db61-4b17-b434-b9847d945c4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelHilbertEisensteinQuasiPeriod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
import Theorems.Thm_GlobalTheory_HilbFam_ExpH_hasQ_hfun


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (c : ℕ → ℂ), 0 < N → Even k → IsCoef k 𝔞 𝔟 a₀ a → HasLevel N (split 𝔞 𝔟 x) → HasQ N Ch c → HasQ N (hfun k (split 𝔞 𝔟 x) κ Ch) (fun n ↦ PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by
  first | exact @GlobalTheory.HilbFam.ExpH.hasQ_hfun | exact GlobalTheory.HilbFam.ExpH.hasQ_hfun | (intros; apply GlobalTheory.HilbFam.ExpH.hasQ_hfun <;> assumption)
end _root_.GlobalTheory.T
