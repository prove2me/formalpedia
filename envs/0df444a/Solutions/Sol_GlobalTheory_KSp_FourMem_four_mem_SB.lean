-- Prove2me | solution 1 for GlobalTheory.KSp.FourMem.four_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:13.982242+00:00
-- url     : https://prove2.me/submissions/c7fe6765-20da-4f66-8aef-5150ec1a35ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhat
import Theorems.Thm_GlobalTheory_KSp_FourMem_eventually_invariant

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
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  intro X _ _ _ _ h μ _ e he φ hφ
  haveI := h.grp
  haveI := h.t2
  haveI := h.lc
  haveI := h.sc
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_invariant hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold four
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.add, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold four
    rw [sub_mul, h1, one_mul, sub_self]
end GlobalTheory.KSp.FourMem
