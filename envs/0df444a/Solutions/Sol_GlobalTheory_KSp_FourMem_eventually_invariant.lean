-- Prove2me | solution 1 for GlobalTheory.KSp.FourMem.eventually_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:25:54.106555+00:00
-- url     : https://prove2.me/submissions/c45f836b-083d-464e-8e4d-7bb2091d8435

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourMem
namespace GlobalTheory.KSp.FourMem
theorem _root_.solution {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
end GlobalTheory.KSp.FourMem
