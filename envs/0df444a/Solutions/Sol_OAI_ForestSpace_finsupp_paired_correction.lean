-- Prove2me | solution 1 for OAI.ForestSpace.finsupp_paired_correction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:41:43.810146+00:00
-- url     : https://prove2.me/submissions/958635ee-a822-4a0b-a1f2-044cc29e38d2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Paired.lean:L303-L349
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.finsupp_paired_correction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Theorems.Thm_OAI_ForestSpace_paired_finite_test_correction

-- ---- from OAI.Analysis.ForestSpace.Paired ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePaired
variable {V : Type} [Fintype V] [PartialOrder V]

end FinitePaired

section FiniteRestriction
variable {V : Type} [PartialOrder V]

 theorem IsSegment.subtype {S B : Finset V} (hS : IsSegment S) :
    IsSegment (S.subtype (· ∈ B)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_subtype.mp ha) b (mem_subtype.mp hb)
  · intro a ha b hb c hac hcb
    exact mem_subtype.mpr (hS.2 a (mem_subtype.mp ha) b (mem_subtype.mp hb) c hac hcb)

 theorem IsSegment.image_subtype {B : Finset V} (hB : IsLowerSet (B : Set V))
    {S : Finset B} (hS : IsSegment S) : IsSegment (S.image Subtype.val) := by
  constructor
  · intro a ha b hb
    obtain ⟨a, ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := mem_image.mp hb
    exact hS.1 a ha' b hb'
  · intro a ha b hb c hac hcb
    obtain ⟨a, ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := mem_image.mp hb
    have hcB : c ∈ B := hB hcb b.property
    exact mem_image.mpr ⟨⟨c,hcB⟩, hS.2 a ha' b hb' ⟨c,hcB⟩ hac hcb, rfl⟩

omit [PartialOrder V] in
 theorem segSum_image_subtype [PartialOrder V] {B : Finset V} (u : V → ℝ) (S : Finset B) :
    segSum u (S.image Subtype.val) = segSum (fun v : B => u v) S := by
  exact sum_image (fun a ha b hb hab => Subtype.val_injective hab)

omit [PartialOrder V] in
 theorem segSum_subtype [PartialOrder V] {B S : Finset V} {u : V → ℝ} (hu : SupportedOn u (B : Set V)) :
    segSum (fun v : B => u v) (S.subtype (· ∈ B)) = segSum u S := by
  change (∑ v ∈ S.subtype (· ∈ B), u v) = ∑ v ∈ S, u v
  rw [sum_subtype_eq_sum_filter]
  exact sum_subset (filter_subset _ _) (by
    intro v hv hv'
    exact hu v (by change v ∉ B; simpa only [mem_filter, hv, true_and] using hv'))

 theorem TestBound.restrict_subtype {B : Finset V} (hB : IsLowerSet (B : Set V))
    {u : V → ℝ} {C : ℝ} (hu : TestBound u C) :
    TestBound (fun v : B => u v) C := by
  intro ι inst S hS hd
  have hh := hu ι inst (fun i => (S i).image Subtype.val)
    (fun i => (hS i).image_subtype hB) (by
      intro i j hij
      exact (Finset.disjoint_image Subtype.val_injective).mpr (hd hij))
  simpa only [segSum_image_subtype] using hh

 theorem TestBound.of_restrict {B : Finset V} {u : V → ℝ} {C : ℝ}
    (hu : SupportedOn u (B : Set V)) (hb : TestBound (fun v : B => u v) C) :
    TestBound u C := by
  intro ι inst S hS hd
  have hh := hb ι inst (fun i => (S i).subtype (· ∈ B))
    (fun i => (hS i).subtype) (by
      intro i j hij
      apply disjoint_left.mpr
      intro v hvi hvj
      exact disjoint_left.mp (hd hij) (mem_subtype.mp hvi) (mem_subtype.mp hvj))
  simpa only [segSum_subtype hu] using hh

omit [PartialOrder V] in
 theorem finiteExtension_supported [PartialOrder V] (B : Finset V) (u : B → ℝ) :
    SupportedOn (finiteExtension B u) (B : Set V) := by
  intro v hv
  simp [finiteExtension, show v ∉ B from hv]

 theorem finiteExtension_testBound {B : Finset V} {u : B → ℝ} {C : ℝ}
    (hu : TestBound u C) : TestBound (finiteExtension B u) C := by
  apply TestBound.of_restrict (finiteExtension_supported B u)
  simpa only [finiteExtension_apply] using hu

/-- The finite-support corrected tests on an arbitrary finite-ancestor forest.
No assertion about the full dual having dense finite coordinates is used. -/
 theorem finsupp_paired_correction (hF : ForestOrder V)
    (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : V →₀ ℝ)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : V →₀ ℝ, SupportedOn c Hᶜ ∧ TestBound c 1 ∧
      TestBound (f + s • (c + k)) (1 + 12 * s ^ 2) ∧
      TestBound (f + s • (c - k)) (1 + 12 * s ^ 2) := by
  obtain ⟨B,hB,hBl⟩ := exists_finite_lower_hull hAnc (f.support ∪ k.support)
  have hfB : SupportedOn f (B : Set V) := by
    intro v hv
    by_contra hvf
    exact hv (hB (mem_union_left _ (Finsupp.mem_support_iff.mpr hvf)))
  have hkB : SupportedOn k (B : Set V) := by
    intro v hv
    by_contra hvk
    exact hv (hB (mem_union_right _ (Finsupp.mem_support_iff.mpr hvk)))
  let HB : Set B := {v | (v : V) ∈ H}
  have hHB : IsLowerSet HB := fun _ _ hab hb => hH hab hb
  obtain ⟨c,hcH,hc₁,hcp,hcm⟩ := paired_finite_test_correction
    (V := B) (fun a b c hac hbc => hF a b c hac hbc) HB hHB (fun v : B => f v) (fun v : B => k v)
    (fun v hv => hf v hv) (fun v hv => hk v (by
      exact not_not.mpr hv))
    (hf₁.restrict_subtype hBl) (hk₁.restrict_subtype hBl) s hs
  refine ⟨finiteExtension B c, ?_, finiteExtension_testBound hc₁, ?_, ?_⟩
  · intro v hv
    by_cases hvB : v ∈ B
    · have hh := hcH ⟨v,hvB⟩ (by
        change v ∈ H; simpa only [Set.mem_compl_iff, not_not] using hv)
      simpa [finiteExtension, hvB] using hh
    · exact finiteExtension_supported B c v hvB
  · apply TestBound.of_restrict (B := B)
      (u := (f + s • (finiteExtension B c + k) : V →₀ ℝ))
    · intro v hv
      simp [hfB v hv, hkB v hv, finiteExtension_supported B c v hv]
    · change TestBound (fun v : B => f v + s * (c v + k v)) (1 + 12 * s ^ 2) at hcp
      simpa only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, finiteExtension_apply] using hcp
  · apply TestBound.of_restrict (B := B)
      (u := (f + s • (finiteExtension B c - k) : V →₀ ℝ))
    · intro v hv
      simp [hfB v hv, hkB v hv, finiteExtension_supported B c v hv]
    · change TestBound (fun v : B => f v + s * (c v - k v)) (1 + 12 * s ^ 2) at hcm
      simpa only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, finiteExtension_apply] using hcm

end FiniteRestriction

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.finsupp_paired_correction := @_root_.OAI.ForestSpace.finsupp_paired_correction
