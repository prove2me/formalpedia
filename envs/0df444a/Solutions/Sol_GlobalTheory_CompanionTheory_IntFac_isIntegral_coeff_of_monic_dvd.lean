-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:24.528651+00:00
-- url     : https://prove2.me/submissions/0c8b5142-8621-475f-b0ad-a28f65108353

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IntFac
namespace GlobalTheory.CompanionTheory.IntFac
theorem _root_.solution (A : Type) [CommRing A] [Algebra ℂ A] (F G : A[X])
    (hF : F.Monic) (hG : G.Monic) (hd : G ∣ F) (h : ∀ k, IsIntegral ℂ (F.coeff k)) (k : ℕ) :
    IsIntegral ℂ (G.coeff k) := by
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
    (f := algebraMap (integralClosure ℂ A) A) (p := F)
    ((lifts_iff_coeff_lifts F).mpr fun n => ⟨⟨F.coeff n, h n⟩, rfl⟩) hF
  have hd' : G ∣ q.map (algebraMap (integralClosure ℂ A) A) := by
    rw [hq]
    exact hd
  exact isIntegral_trans _ (isIntegral_coeff_of_dvd q G hqm hG hd' k)
end GlobalTheory.CompanionTheory.IntFac
