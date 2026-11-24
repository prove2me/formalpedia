-- Prove2me | solution 1 for GlobalTheory.LatticeMean.setAverage_eq_of_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:44:00.296802+00:00
-- url     : https://prove2.me/submissions/a1ad0516-52cc-49f2-95ac-0a3ab9c96369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SetAverageProdFundamentalDomainPlaneLatticePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeMean
namespace GlobalTheory.LatticeMean
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (A : AddSubgroup V) [Countable A] (f : V → ℝ)
    (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z) (P : Set V) (hP : IsAddFundamentalDomain A P μ) :
    ⨍ z in Classical.epsilon (fun Fd : Set V => IsAddFundamentalDomain A Fd μ), f z ∂μ
      = ⨍ z in P, f z ∂μ := by
  have hE := Classical.epsilon_spec (p := fun Fd : Set V => IsAddFundamentalDomain A Fd μ) ⟨P, hP⟩
  rw [setAverage_eq, setAverage_eq, hE.setIntegral_eq hP (fun g x => hf g g.2 x),
    measureReal_def, measureReal_def, hE.measure_eq hP]
end GlobalTheory.LatticeMean
