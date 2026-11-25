-- Prove2me | solution 1 for GlobalTheory.T.snc_resolution_regular_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:34:44.092155+00:00
-- url     : https://prove2.me/submissions/e410eccd-1506-4f5a-bd02-a4035352d0a4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_isRegularLocalRing_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart <;> assumption)
end _root_.GlobalTheory.T
