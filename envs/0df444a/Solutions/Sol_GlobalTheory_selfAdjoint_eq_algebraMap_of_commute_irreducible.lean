-- Prove2me | solution 1 for GlobalTheory.selfAdjoint_eq_algebraMap_of_commute_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:32:47.581665+00:00
-- url     : https://prove2.me/submissions/085d1044-f097-458b-9c43-0040638a78a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointEqAlgebraMapOfCommuteIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (π g)) :
    ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · refine ⟨0, ?_⟩
    ext u
    simp [Subsingleton.elim u 0]
  obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have hsub : ∀ s ∈ spectrum ℝ A, s = r := by
    intro s hs
    by_contra hne
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ spectrum ℝ A, ∃ b ∈ spectrum ℝ A, a < b := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨s, hs, r, hr, h⟩
      · exact ⟨r, hr, s, hs, h⟩
    set c : ℝ := (a + b) / 2 with hc_def
    set f : ℝ → ℝ := fun x => max (c - x) 0 with hf_def
    set k : ℝ → ℝ := fun x => max (x - c) 0 with hk_def
    have hfk : (fun x => k x * f x) = (0 : ℝ → ℝ) := by
      funext x
      simp only [Pi.zero_apply, hf_def, hk_def]
      rcases le_total x c with h | h
      · rw [max_eq_right (by linarith : x - c ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : c - x ≤ 0), mul_zero]
    have hprod : cfc k A * cfc f A = 0 := by
      rw [← cfc_mul k f A, hfk, cfc_zero]
    have hF : cfc f A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := f) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) ha
      simp only [Pi.zero_apply, hf_def] at this
      have : c - a ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hK : cfc k A ≠ 0 := by
      intro h0
      have := (eqOn_of_cfc_eq_cfc (f := k) (g := 0) (a := A) (h0.trans (cfc_zero ℝ A).symm)) hb
      simp only [Pi.zero_apply, hk_def] at this
      have : b - c ≤ 0 := by
        rw [← this]; exact le_max_left _ _
      linarith
    have hcomm : ∀ g, Commute (cfc k A) (π g) := fun g => (hc g).cfc_real k
    let S : Submodule ℂ H := LinearMap.ker (cfc k A).toLinearMap
    have hS : S = ⊥ ∨ S = ⊤ := by
      refine hirr S ?_ ?_
      · exact (cfc k A).isClosed_ker
      · intro g u hu
        have hu' : cfc k A u = 0 := hu
        show cfc k A (π g u) = 0
        have := congrArg (fun T : H →L[ℂ] H => T u) (hcomm g).eq
        simp only [ContinuousLinearMap.mul_apply] at this
        rw [this, hu', map_zero]
    rcases hS with hS | hS
    · apply hF
      ext v
      have hv : cfc f A v ∈ S := by
        show cfc k A (cfc f A v) = 0
        rw [← ContinuousLinearMap.mul_apply, hprod, ContinuousLinearMap.zero_apply]
      rw [hS, Submodule.mem_bot] at hv
      simpa using hv
    · apply hK
      ext v
      have hv : v ∈ S := hS ▸ Submodule.mem_top
      have hv' : cfc k A v = 0 := hv
      rw [ContinuousLinearMap.zero_apply]
      exact hv'
  refine ⟨r, ?_⟩
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A).symm
    _ = cfc (fun _ : ℝ => r) A := cfc_congr (fun s hs => hsub s hs)
    _ = algebraMap ℝ (H →L[ℂ] H) r := cfc_const r A
end GlobalTheory
