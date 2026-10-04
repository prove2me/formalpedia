-- Prove2me | solution 1 for LeblSCV.Pseudoconvex.sup_subharmonic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:52:33.696456+00:00
-- url     : https://prove2.me/submissions/555450e4-1a45-4d7b-a71c-0dc2ff94c925

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsSubharmonicOn

set_option autoImplicit false

namespace LeblSCV.Pseudoconvex.P0ed6bfcc

open LeblSCV.Pseudoconvex

theorem sup_comparison {ι : Type*} (U : Set ℂ) (f : ι → ℂ → EReal)
    (hf : ∀ α, IsSubharmonicOn (f α) U)
    (hne : ∀ z ∈ U, (⨆ α, f α z) ≠ ⊤)
    (husc : UpperSemicontinuousOn (fun z => ⨆ α, f α z) U) :
    IsSubharmonicOn (fun z => ⨆ α, f α z) U := by
  refine ⟨husc, hne, ?_⟩
  intro a r hr hsub g hg hgh hle x hx
  refine iSup_le (fun α => ?_)
  exact (hf α).2.2 a r hr hsub g hg hgh
    (fun y hy => le_trans (le_iSup (fun β => f β y) α) (hle y hy)) x hx

theorem finite_usc {ι : Type*} [Finite ι] (U : Set ℂ) (f : ι → ℂ → EReal)
    (hf : ∀ α, IsSubharmonicOn (f α) U) :
    UpperSemicontinuousOn (fun z => ⨆ α, f α z) U := by
  intro x hx y hy
  rcases isEmpty_or_nonempty ι with h | h
  · exact Filter.Eventually.of_forall (fun x' => by
      have : (⨆ α, f α x') = (⨆ α, f α x) := by simp
      simp only
      rw [this]; exact hy)
  · have H : ∀ α, ∀ᶠ x' in nhdsWithin x U, f α x' < y := fun α =>
      (hf α).1 x hx y (lt_of_le_of_lt (le_iSup (fun β => f β x) α) hy)
    filter_upwards [Filter.eventually_all.2 H] with x' hx'
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun α => f α x')
    show (⨆ α, f α x') < y
    rw [← hi]
    exact hx' i

theorem finite_ne_top {ι : Type*} [Finite ι] (U : Set ℂ) (f : ι → ℂ → EReal)
    (hf : ∀ α, IsSubharmonicOn (f α) U) :
    ∀ z ∈ U, (⨆ α, f α z) ≠ ⊤ := by
  intro z hz
  rcases isEmpty_or_nonempty ι with h | h
  · simp
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun α => f α z)
    rw [← hi]
    exact (hf i).2.1 z hz

end LeblSCV.Pseudoconvex.P0ed6bfcc

open LeblSCV.Pseudoconvex in
theorem solution {ι : Type*} (U : Set ℂ) (hU : IsOpen U) (f : ι → ℂ → EReal)
    (hf : ∀ α, IsSubharmonicOn (f α) U) :
    (Finite ι → IsSubharmonicOn (fun z => ⨆ α, f α z) U) ∧
    ((∀ z ∈ U, (⨆ α, f α z) ≠ ⊤) → UpperSemicontinuousOn (fun z => ⨆ α, f α z) U →
      IsSubharmonicOn (fun z => ⨆ α, f α z) U) := by
  refine ⟨fun hfin => ?_, fun hne husc => ?_⟩
  · have := hfin
    exact LeblSCV.Pseudoconvex.P0ed6bfcc.sup_comparison U f hf
      (LeblSCV.Pseudoconvex.P0ed6bfcc.finite_ne_top U f hf)
      (LeblSCV.Pseudoconvex.P0ed6bfcc.finite_usc U f hf)
  · exact LeblSCV.Pseudoconvex.P0ed6bfcc.sup_comparison U f hf hne husc
