-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_eq_sum_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:00.337502+00:00
-- url     : https://prove2.me/submissions/030eef8b-f9f2-41c9-b195-3e2dcc7751a2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_principalPart
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_principalPart
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_regularPart
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_principalPart_add_regularPart
import Theorems.Thm_GroundTheory_Global_Elliptic_notMem_rectBoundary_of_mem_Ioo
import Theorems.Thm_GroundTheory_Global_Elliptic_rectBoundary_subset
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_add
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_congr
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_eq_zero_of_differentiable_on_off_countable
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_finset_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {z w : ℂ} (S : Finset ℂ)
    (hS : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hmero : ∀ p ∈ S, MeromorphicAt f p)
    (hana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], u ∉ S → AnalyticAt ℂ f u) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  set F : ℂ → ℂ := fun u ↦ f u - ∑ q ∈ S, principalPart f q u with hF
  set E : ℂ → ℂ → ℂ := fun p u ↦ regularPart f p u - ∑ q ∈ S.erase p, principalPart f q u
    with hE
  set G : ℂ → ℂ := fun u ↦ if u ∈ S then E u u else F u with hG
  have hFE : ∀ p ∈ S, ∀ u, u ≠ p → F u = E p u := by
    intro p hp u hu
    simp only [hF, hE]
    rw [eq_principalPart_add_regularPart f p hu, ← Finset.add_sum_erase S _ hp]
    ring
  have hEana : ∀ p ∈ S, AnalyticAt ℂ (E p) p := by
    intro p hp
    exact (analyticAt_regularPart (hmero p hp)).sub
      (Finset.analyticAt_fun_sum _ fun q hq ↦
        analyticAt_principalPart f (Finset.ne_of_mem_erase hq).symm)
  have hGana : ∀ u ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], AnalyticAt ℂ G u := by
    intro u hu
    by_cases huS : u ∈ S
    · have hnhds : ((S.erase u : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 u :=
        (S.erase u).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine (hEana u huS).congr ?_
      filter_upwards [hnhds] with v hv
      simp only [hG]
      rcases eq_or_ne v u with rfl | hvu
      · simp [huS]
      · have hvS : v ∉ S := fun h ↦ hv (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu, h⟩))
        rw [if_neg hvS, hFE u huS v hvu]
    · have hnhds : ((S : Set ℂ))ᶜ ∈ 𝓝 u :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using huS)
      have hFana : AnalyticAt ℂ F u :=
        (hana u hu huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
          analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))
      refine hFana.congr ?_
      filter_upwards [hnhds] with v hv
      have hvS : v ∉ S := by simpa using hv
      simp only [hG, if_neg hvS]
  have hSb : ∀ p ∈ S, p ∉ rectBoundary z w := fun p hp ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    exact notMem_rectBoundary_of_mem_Ioo
      ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hbK : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := rectBoundary_subset
  have hG0 : rectIntegral G z w = 0 := by
    apply rectIntegral_eq_zero_of_differentiable_on_off_countable G z w ∅ countable_empty
    · exact fun u hu ↦ (hGana u hu).continuousAt.continuousWithinAt
    · intro u hu
      apply (hGana u _).differentiableAt
      have h' := hu.1
      rw [mem_reProdIm] at h' ⊢
      exact ⟨Ioo_subset_Icc_self h'.1, Ioo_subset_Icc_self h'.2⟩
  have hGF : rectIntegral G z w = rectIntegral F z w := by
    apply rectIntegral_congr
    intro u hu
    have huS : u ∉ S := fun h ↦ hSb u h hu
    simp only [hG, if_neg huS]
  have hPc : ∀ q ∈ S, ContinuousOn (principalPart f q) (rectBoundary z w) := fun q hq u hu ↦
    (analyticAt_principalPart f (fun (h : u = q) ↦ hSb q hq (h ▸ hu))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (rectBoundary z w) := fun u hu ↦ by
    have huS : u ∉ S := fun h ↦ hSb u h hu
    exact ((hana u (hbK hu) huS).sub (Finset.analyticAt_fun_sum _ fun q hq ↦
      analyticAt_principalPart f (fun h ↦ huS (h ▸ hq)))).continuousAt.continuousWithinAt
  have hsplit : rectIntegral f z w =
      rectIntegral F z w + ∑ q ∈ S, rectIntegral (principalPart f q) z w := by
    rw [← rectIntegral_finset_sum S hPc, ← rectIntegral_add hFc (continuousOn_finsetSum S hPc)]
    congr 1
    funext u
    simp only [hF]
    ring
  rw [hsplit, ← hGF, hG0, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hS q hq
  exact rectIntegral_principalPart f h1 h2 h3 h4
end GroundTheory.Global.Elliptic
