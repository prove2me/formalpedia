-- Prove2me | solution 1 for OAI.C0Absorption.disjoint_supports_signed_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:23:59.947113+00:00
-- url     : https://prove2.me/submissions/3784d57c-66fa-4592-8d87-43c78b52051c

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology
theorem h41_lip_local {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {B : Set E} (hB : Convex ℝ B) {f : B → Y} {K : ℝ≥0}
    (hf : Continuous f)
    (hloc : ∀ x, ∀ᶠ y in nhds x, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  classical
  by_cases hne : IsEmpty B
  · exact LipschitzWith.of_dist_le_mul (fun x _ => (hne.false x).elim)
  rw [not_isEmpty_iff] at hne
  obtain ⟨b⟩ := hne
  let F : E → Y := fun x => if h : x ∈ B then f ⟨x, h⟩ else f b
  have hres : B.restrict F = f := by
    funext x; simp [F, Set.restrict, x.2]
  have hFc : ContinuousOn F B := by
    rw [continuousOn_iff_continuous_restrict]; change Continuous (B.restrict F); rw [hres]; exact hf
  have hFl : ∀ x ∈ B, ∀ᶠ y in nhdsWithin x B, dist (F x) (F y) ≤ K * dist x y := by
    intro x hx
    rw [← map_nhds_subtype_val ⟨x, hx⟩, Filter.eventually_map]
    filter_upwards [hloc ⟨x, hx⟩] with y hy
    simpa [F, hx, y.2, Subtype.dist_eq] using hy
  have : LipschitzWith K (B.restrict F) := (lipschitzOn_convex_of_local hB hFc hFl).to_restrict
  rwa [hres] at this

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : Set E} (hB : Convex ℝ B)
    {ι : Type*} [Fintype ι] (f : ι → B → ℝ) (K : ℝ≥0)
    (hf : ∀ i, LipschitzWith K (f i))
    (hdisj : Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j))))
    (ε : ι → ℝ) (hε : ∀ i, |ε i| = 1) :
    LipschitzWith K (fun x => ∑ i, ε i * f i x) := by
  classical
  have hcont : Continuous (fun x => ∑ i, ε i * f i x) := by
    have := fun i => (hf i).continuous
    fun_prop
  apply h41_lip_local hB hcont
  intro x
  by_cases hx : ∃ i, x ∈ tsupport (f i)
  · obtain ⟨i, hi⟩ := hx
    have hopen : IsOpen (⋂ j ∈ (Finset.univ.erase i), (tsupport (f j))ᶜ) :=
      isOpen_biInter_finset (fun j _ => (isClosed_tsupport _).isOpen_compl)
    have hmem : x ∈ ⋂ j ∈ (Finset.univ.erase i), (tsupport (f j))ᶜ := by
      simp only [Set.mem_iInter, Finset.mem_erase]
      intro j ⟨hj, _⟩ hxj
      exact Set.disjoint_left.1 (hdisj hj) hxj hi
    have hloc : ∀ z ∈ ⋂ j ∈ (Finset.univ.erase i), (tsupport (f j))ᶜ,
        ∑ j, ε j * f j z = ε i * f i z := by
      intro z hz
      rw [Finset.sum_eq_single i]
      · intro j _ hj
        simp only [Set.mem_iInter, Finset.mem_erase] at hz
        rw [image_eq_zero_of_notMem_tsupport (hz j ⟨hj, Finset.mem_univ _⟩), mul_zero]
      · simp
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rw [hloc x hmem, hloc y hy, Real.dist_eq, ← mul_sub, abs_mul, hε i, one_mul, ← Real.dist_eq]
    exact (hf i).dist_le_mul x y
  · push_neg at hx
    have hopen : IsOpen (⋂ j ∈ (Finset.univ : Finset ι), (tsupport (f j))ᶜ) :=
      isOpen_biInter_finset (fun j _ => (isClosed_tsupport _).isOpen_compl)
    have hmem : x ∈ ⋂ j ∈ (Finset.univ : Finset ι), (tsupport (f j))ᶜ := by
      simp only [Set.mem_iInter]; intro j _; exact hx j
    have hz : ∀ z ∈ ⋂ j ∈ (Finset.univ : Finset ι), (tsupport (f j))ᶜ, ∑ j, ε j * f j z = 0 := by
      intro z hz
      simp only [Set.mem_iInter] at hz
      exact Finset.sum_eq_zero (fun j _ => by rw [image_eq_zero_of_notMem_tsupport (hz j (Finset.mem_univ _)), mul_zero])
    filter_upwards [hopen.mem_nhds hmem] with y hy
    rw [hz x hmem, hz y hy, dist_self]; positivity

