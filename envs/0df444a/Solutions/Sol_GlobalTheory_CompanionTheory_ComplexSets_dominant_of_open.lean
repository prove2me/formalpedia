-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.dominant_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:23.170831+00:00
-- url     : https://prove2.me/submissions/d2814d3f-5ab7-4e25-9c48-a10f13f6120a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_equation_not_vanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_not_eventually_prod_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
variable {σ : Type} [Fintype σ]
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution {ι : Type} [Fintype ι] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    {S W : Set (σ → ℂ)} {w : σ → ℂ} (Y : ι → Set (σ → ℂ))
    (hopen : ∀ x ∈ S, ∀ V ∈ 𝓝 x, A '' (S ∩ V) ∈ 𝓝 (A x))
    (hYan : ∀ i, IsAnalyticNear (Y i) w) (hYirr : ∀ i, GermIrreducibleAt (Y i) w)
    (hno : ∀ i j, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j)
    (hW : W ∈ 𝓝 w) (hS : S ∩ W = (⋃ i, Y i) ∩ W) (i : ι)
    (h : (Fin d → ℂ) → ℂ) (hh : AnalyticAt ℂ h (A w))
    (hv : ∀ᶠ z in 𝓝 w, z ∈ Y i → h (A z) = 0) :
    ∀ᶠ y in 𝓝 (A w), h y = 0 := by
  classical
  have hsep : ∀ j, ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (j ≠ i →
      (∀ᶠ z in 𝓝 w, z ∈ Y j → φ z = 0) ∧ ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → φ z = 0) := by
    intro j
    by_cases hj : j = i
    · exact ⟨fun _ => 1, analyticAt_const, fun h' => absurd hj h'⟩
    · obtain ⟨φ, h1, h2, h3⟩ := exists_equation_not_vanishing (hYan j) (hno i j (Ne.symm hj))
      exact ⟨φ, h1, fun _ => ⟨h2, h3⟩⟩
  choose φ hφan hφ using hsep
  have hΦan : AnalyticAt ℂ (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) w :=
    by simpa only [Finset.prod_fn] using Finset.analyticAt_prod (Finset.univ.erase i) fun j _ => hφan j
  have hΦne : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → ∏ j ∈ Finset.univ.erase i, φ j z = 0 :=
    not_eventually_prod_eq_zero (hYirr i) φ _ (fun j _ => hφan j)
      (fun j hj => (hφ j (Finset.ne_of_mem_erase hj)).2)
  have hΦY : ∀ᶠ z in 𝓝 w, ∀ j, j ≠ i → z ∈ Y j → ∏ j ∈ Finset.univ.erase i, φ j z = 0 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun z h' => absurd hj h'
    · filter_upwards [(hφ j hj).1] with z hz _ hzj
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (hz hzj)
  obtain ⟨ε, hε, hhb⟩ := hh.exists_ball_analyticOnNhd
  have hcont : ∀ᶠ z in 𝓝 w, ContinuousAt (fun z => ∏ j ∈ Finset.univ.erase i, φ j z) z :=
    hΦan.eventually_analyticAt.mono fun z hz => hz.continuousAt
  have hAball : ∀ᶠ z in 𝓝 w, A z ∈ Metric.ball (A w) ε :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hgood := hcont.and (hΦY.and (hv.and (hAball.and (show ∀ᶠ z in 𝓝 w, z ∈ W from hW))))
  have hfreq := Filter.not_eventually.mp hΦne
  obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually hgood.eventually_nhds).exists
  push_neg at hx1
  obtain ⟨hxY, hxΦ⟩ := hx1
  obtain ⟨hxc, -, -, hxA, hxW⟩ := hx2.self_of_nhds
  have hxS : x ∈ S := by
    have hx' : x ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.mpr ⟨i, hxY⟩, hxW⟩
    rw [← hS] at hx'
    exact hx'.1
  have hV := hx2.and (hxc.eventually_ne hxΦ)
  have himg := hopen x hxS _ hV
  have hzero : ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    filter_upwards [himg] with y hy
    obtain ⟨z, ⟨hzS, ⟨⟨-, hzY, hzh, -, hzW⟩, hzΦ⟩⟩, rfl⟩ := hy
    have hz' : z ∈ (⋃ j, Y j) ∩ W := by rw [← hS]; exact ⟨hzS, hzW⟩
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz'.1
    by_cases hji : j = i
    · rw [hji] at hzj
      exact hzh hzj
    · exact absurd (hzY j hji hzj) hzΦ
  have hEq := hhb.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected hxA hzero
  filter_upwards [Metric.ball_mem_nhds (A w) hε] with y hy
  exact hEq hy
end GlobalTheory.CompanionTheory.ComplexSets
