-- Prove2me | solution 1 for GlobalTheory.CosetSumShift.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:04.598579+00:00
-- url     : https://prove2.me/submissions/61d21b75-6150-4562-aaf6-a6528c639c77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariant
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
open GlobalTheory GlobalTheory.CosetSumShift
namespace GlobalTheory.CosetSumShift
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)),
    (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) →
    ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) →
    ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by
  intro k _ _ _ _ n _ r R S hS huniq F hF a ha
  classical
  have hadd : ∀ {s : kˣ} {x y : n → k}, x ∈ box n s → y ∈ box n s → x + y ∈ box n s :=
    fun hx hy i _ => add_mem_cball (hx i trivial) (hy i trivial)
  have hneg : ∀ {s : kˣ} {x : n → k}, x ∈ box n s → -x ∈ box n s :=
    fun hx i _ => neg_mem_cball (hx i trivial)
  have hzero : (0 : n → k) ∈ box n r := fun i _ => by simp [cball]
  have hmem : ∀ b ∈ S, a + b ∈ box n R := fun b hb => hadd ha (hS b hb)
  choose! c hc using fun b (hb : b ∈ S) => (huniq (a + b) (hmem b hb)).exists
  have hF' : ∀ b ∈ S, F (a + b) = F (c b) := by
    intro b hb
    have := hF _ (hc b hb).2 (c b)
    rwa [add_sub_cancel] at this
  have hinj : ∀ x ∈ S, ∀ y ∈ S, c x = c y → x = y := by
    intro x hx y hy h
    have e : x - y = (a + x - c x) + -(a + y - c y) := by rw [h]; abel
    have h1 : x - y ∈ box n r := e ▸ hadd (hc x hx).2 (hneg (hc y hy).2)
    obtain ⟨z, -, huq⟩ := huniq x (hS x hx)
    exact (huq x ⟨hx, by simpa using hzero⟩).trans (huq y ⟨hy, h1⟩).symm
  have himg : S.image c = S := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      exact (hc b hb).1
    · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
  rw [Finset.sum_congr rfl hF', ← Finset.sum_image hinj, himg]
end GlobalTheory.CosetSumShift
