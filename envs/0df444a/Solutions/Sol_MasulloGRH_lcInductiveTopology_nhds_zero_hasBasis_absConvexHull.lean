-- Prove2me | solution 1 for MasulloGRH.lcInductiveTopology_nhds_zero_hasBasis_absConvexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:07:33.433652+00:00
-- url     : https://prove2.me/submissions/65b4b247-68b0-49ac-902c-f1da3454e2e5

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_lcInductiveTopology_nhds_zero_hasBasis_absConvexHull

open MasulloGRH

universe u v w

section

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The real convex hull of a circled (balanced over `ℂ`) set is circled. -/
theorem balanced_convexHull_real {s : Set E} (hs : Balanced ℂ s) :
    Balanced ℂ (convexHull ℝ s) := by
  suffices h : Convex ℝ {x : E | ∀ a : ℂ, ‖a‖ ≤ 1 → a • x ∈ convexHull ℝ s} by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ h hx a ha
    exact fun y hy a ha => subset_convexHull ℝ s (hs ha hy)
  intro x hx y hy b c hb hc hbc a ha
  rw [smul_add, smul_comm a b, smul_comm a c]
  exact convex_convexHull ℝ s (hx a ha) (hy a ha) hb hc hbc

variable {ι : Type v} {X : ι → Type w} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, TopologicalSpace (X a)]

omit [∀ a, TopologicalSpace (X a)] in
/-- Each image `f a '' U a` lies in the absolutely convex hull of the union of the images. -/
theorem image_subset_hull (f : ∀ a, X a →ₗ[ℂ] E) (U : ∀ a, Set (X a)) (a : ι) :
    f a '' U a ⊆ convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) :=
  (Set.subset_iUnion (fun a => f a '' U a) a).trans
    ((subset_balancedHull ℂ).trans (subset_convexHull ℝ _))

omit [∀ a, TopologicalSpace (X a)] in
/-- The hull is monotone in the family `U`. -/
theorem hull_mono (f : ∀ a, X a →ₗ[ℂ] E) {U V : ∀ a, Set (X a)} (h : ∀ a, U a ⊆ V a) :
    convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) ⊆
      convexHull ℝ (balancedHull ℂ (⋃ a, f a '' V a)) :=
  convexHull_mono (balancedHull_mono (Set.iUnion_mono fun a => Set.image_mono (h a)))

/-- If the images of the `f a` span `E`, the absolutely convex hull of the union of the images of
`0`-neighbourhoods is absorbent. -/
theorem absorbent_hull [Nonempty ι] [∀ a, ContinuousSMul ℂ (X a)]
    (f : ∀ a, X a →ₗ[ℂ] E) (hspan : ⨆ a, LinearMap.range (f a) = ⊤)
    (U : ∀ a, Set (X a)) (hU : ∀ a, U a ∈ 𝓝 (0 : X a)) :
    Absorbent ℝ (convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) := by
  have hsub := image_subset_hull f U
  have h0 : (0 : E) ∈ convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) := by
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact hsub a ⟨0, mem_of_mem_nhds (hU a), map_zero _⟩
  have hconv : Convex ℝ (convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) :=
    convex_convexHull ℝ _
  -- every vector is moved into the hull by all sufficiently small real scalars
  have key : ∀ x : E, ∀ᶠ c : ℝ in 𝓝 0,
      c • x ∈ convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) := by
    intro x
    have hx : x ∈ ⨆ a, LinearMap.range (f a) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun a => LinearMap.range (f a))
      (motive := fun x => ∀ᶠ c : ℝ in 𝓝 0,
        c • x ∈ convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) hx ?_ ?_ ?_
    · -- vectors in the image of one `f a`
      rintro a _ ⟨y, rfl⟩
      have ht : Filter.Tendsto (fun c : ℝ => (c : ℂ) • y) (𝓝 0) (𝓝 (0 : X a)) := by
        have hc : Continuous fun c : ℝ => (c : ℂ) • y :=
          Complex.continuous_ofReal.smul continuous_const
        have := hc.tendsto 0
        simpa using this
      filter_upwards [ht (hU a)] with c hc
      refine hsub a ⟨(c : ℂ) • y, hc, ?_⟩
      rw [map_smul]
      exact Complex.coe_smul c (f a y)
    · -- the zero vector
      refine Filter.Eventually.of_forall fun c => ?_
      rw [smul_zero]
      exact h0
    · -- sums
      intro x y hx hy
      have ht : Filter.Tendsto (fun c : ℝ => 2 * c) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun c : ℝ => 2 * c := continuous_const.mul continuous_id
        have := hc.tendsto 0
        simpa using this
      filter_upwards [ht.eventually hx, ht.eventually hy] with c hcx hcy
      have hmem := hconv hcx hcy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
      have heq : (1 / 2 : ℝ) • (2 * c) • x + (1 / 2 : ℝ) • (2 * c) • y = c • (x + y) := by
        rw [smul_smul, smul_smul, smul_add]
        have h2 : (1 / 2 : ℝ) * (2 * c) = c := by ring
        rw [h2]
      rw [← heq]
      exact hmem
  intro x
  rw [absorbs_iff_eventually_nhds_zero h0]
  filter_upwards [key x] with c hc
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hc

/-- The absolutely convex hull of the union of the images of `0`-neighbourhoods is a
neighbourhood of `0` for the locally convex inductive topology. -/
theorem hull_mem_nhds [Nonempty ι] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)]
    (f : ∀ a, X a →ₗ[ℂ] E) (hspan : ⨆ a, LinearMap.range (f a) = ⊤)
    (U : ∀ a, Set (X a)) (hU : ∀ a, U a ∈ 𝓝 (0 : X a)) :
    convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) ∈
      @nhds E (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)}) 0 := by
  have hsub := image_subset_hull f U
  have habs := absorbent_hull f hspan U hU
  have hbal : Balanced ℂ (convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) :=
    balanced_convexHull_real (balancedHull.balanced _)
  have hconv : Convex ℝ (convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) :=
    convex_convexHull ℝ _
  -- the gauge of the hull, and the topology it defines
  let p : Seminorm ℂ E := gaugeSeminorm hbal hconv habs
  let P : SeminormFamily ℂ E PUnit.{u + 1} := fun _ => p
  let t' : TopologicalSpace E := P.moduleFilterBasis.topology
  have hW : @WithSeminorms ℂ E PUnit.{u + 1} _ _ _ P t' :=
    @WithSeminorms.mk ℂ E _ _ _ _ P t' rfl
  -- every `f a` is continuous for the gauge topology
  have hcont : ∀ a, @Continuous (X a) E _ t' (f a) := by
    intro a
    let _ : TopologicalSpace E := t'
    refine WithSeminorms.continuous_of_continuous_comp hW (f a) fun _ => ?_
    refine Seminorm.continuous' (r := 1) ?_
    refine Filter.mem_of_superset (hU a) fun x hx => ?_
    rw [Seminorm.mem_closedBall_zero]
    exact gauge_le_one_of_mem (hsub a ⟨x, hx, rfl⟩)
  have hmem : t' ∈ {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)} :=
    ⟨⟨PUnit.{u + 1}, ⟨PUnit.unit⟩, P, hW⟩, hcont⟩
  -- the hull contains the open unit ball of its gauge
  have h1 : convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a)) ∈ @nhds E t' 0 := by
    let _ : TopologicalSpace E := t'
    have hball : p.ball 0 1 ∈ 𝓝 (0 : E) := by
      have := hW.hasBasis_zero_ball.mem_of_mem
        (i := (({PUnit.unit} : Finset PUnit.{u + 1}), (1 : ℝ))) one_pos
      simpa [P] using this
    refine Filter.mem_of_superset hball fun x hx => ?_
    rw [Seminorm.mem_ball_zero] at hx
    exact setOfPred_gauge_lt_one_subset_self hconv habs.zero_mem habs hx
  exact nhds_mono (sInf_le hmem) h1

end

end Sol_MasulloGRH_lcInductiveTopology_nhds_zero_hasBasis_absConvexHull

open MasulloGRH
open Sol_MasulloGRH_lcInductiveTopology_nhds_zero_hasBasis_absConvexHull

theorem solution (E : Type*) [AddCommGroup E]
    [Module ℂ E] {ι : Type*} [Nonempty ι] (X : ι → Type*) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, TopologicalSpace (X a)] [∀ a, IsTopologicalAddGroup (X a)]
    [∀ a, ContinuousSMul ℂ (X a)] (f : ∀ a, X a →ₗ[ℂ] E)
    (hspan : ⨆ a, LinearMap.range (f a) = ⊤) :
    (@nhds E (sInf {t | IsLocallyConvexTopology E t ∧ ∀ a, @Continuous (X a) E _ t (f a)})
        0).HasBasis
      (fun U : ∀ a, Set (X a) => ∀ a, U a ∈ 𝓝 (0 : X a))
      (fun U => convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) := by
  -- the hulls form a filter basis
  have hB : Filter.IsBasis (fun U : ∀ a, Set (X a) => ∀ a, U a ∈ 𝓝 (0 : X a))
      (fun U => convexHull ℝ (balancedHull ℂ (⋃ a, f a '' U a))) := by
    refine ⟨⟨fun _ => Set.univ, fun _ => Filter.univ_mem⟩, ?_⟩
    intro U V hU hV
    refine ⟨fun a => U a ∩ V a, fun a => Filter.inter_mem (hU a) (hV a), ?_⟩
    exact Set.subset_inter (hull_mono f fun a => Set.inter_subset_left)
      (hull_mono f fun a => Set.inter_subset_right)
  have key : @nhds E (sInf {t | IsLocallyConvexTopology E t ∧
      ∀ a, @Continuous (X a) E _ t (f a)}) 0 = hB.filter := by
    apply le_antisymm
    · -- every hull is a neighbourhood of `0`
      rw [hB.hasBasis.ge_iff]
      intro U hU
      exact hull_mem_nhds f hspan U hU
    · -- every neighbourhood of `0` for a member of the family contains a hull
      rw [nhds_sInf]
      refine le_iInf₂ fun t ht => ?_
      obtain ⟨⟨κ, _, q, hq⟩, hf⟩ := ht
      let _ : TopologicalSpace E := t
      rw [hB.hasBasis.le_basis_iff hq.hasBasis_zero_ball]
      rintro ⟨s, r⟩ hr
      have hV : (s.sup q).ball 0 r ∈ 𝓝 (0 : E) := hq.hasBasis_zero_ball.mem_of_mem hr
      refine ⟨fun a => f a ⁻¹' (s.sup q).ball 0 r, fun a => ?_, ?_⟩
      · have ht : Filter.Tendsto (f a) (𝓝 0) (𝓝 (0 : E)) := by
          have := (hf a).tendsto 0
          rwa [map_zero] at this
        exact ht hV
      · refine convexHull_min ?_ (Seminorm.convex_ball _ _ _)
        refine (Seminorm.balanced_ball_zero _ _).balancedHull_subset_of_subset ?_
        exact Set.iUnion_subset fun a => Set.image_preimage_subset _ _
  rw [key]
  exact hB.hasBasis
