-- Prove2me | solution 1 for GlobalTheory.isTest_nhds_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:22.914838+00:00
-- url     : https://prove2.me/submissions/a7913c45-5b7e-48d3-81ca-a88e3f502c61

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ),
    IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  intro X _ _ _ f hf
  obtain ⟨hlc, hcs⟩ := hf
  have hK : IsCompact (tsupport f) := hcs
  have key : ∀ᶠ u in 𝓝 (0 : X), ∀ y ∈ tsupport f, f (y + u) = f y := by
    refine hK.eventually_forall_of_forall_eventually (P := fun u y => f (y + u) = f y) ?_
    intro y _
    have hy : ∀ᶠ z in 𝓝 y, f z = f y := (IsLocallyConstant.iff_eventually_eq f).1 hlc y
    have hc : Filter.Tendsto (fun p : X × X => p.2 + p.1) (𝓝 ((0 : X), y)) (𝓝 y) := by
      have hcont : Continuous fun p : X × X => p.2 + p.1 := continuous_snd.add continuous_fst
      have := hcont.tendsto ((0 : X), y)
      simpa only [add_zero] using this
    have h2 : Filter.Tendsto (fun p : X × X => p.2) (𝓝 ((0 : X), y)) (𝓝 y) :=
      (continuous_snd.tendsto ((0 : X), y))
    filter_upwards [hc.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have hneg : Filter.Tendsto (fun u : X => -u) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : X))
  refine ⟨{u | ∀ y ∈ tsupport f, f (y + u) = f y} ∩ (fun u : X => -u) ⁻¹' {u | ∀ y ∈ tsupport f, f (y + u) = f y},
    Filter.inter_mem key (hneg key), ?_⟩
  rintro x u ⟨h1, h2⟩
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  by_cases hxu : x + u ∈ tsupport f
  · have := h2 (x + u) hxu
    simp only [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]
end GlobalTheory
