-- Prove2me | solution 1 for OAI.RuledApproximation.glue_finite_local_covers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:50:51.920032+00:00
-- url     : https://prove2.me/submissions/d5419d78-dfca-471e-9cdb-65592dd2d205

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean:L124-L162
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.glue_finite_local_covers. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Theorems.Thm_OAI_RuledApproximation_compact_cut_integral

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma HasFiniteCover.empty (shape : Cylinder → Prop) {A : ℝ} (hA : 0 ≤ A) :
    HasFiniteCover shape ∅ A := by
  refine ⟨0, Fin.elim0, by intro i; exact i.elim0, by simp, ?_⟩
  simpa [familyArea] using hA

lemma HasFiniteCover.union {shape : Cylinder → Prop} {S T : Set Space} {A B : ℝ}
    (hS : HasFiniteCover shape S A) (hT : HasFiniteCover shape T B) :
    HasFiniteCover shape (S ∪ T) (A + B) := by
  obtain ⟨n, C, hC, hSC, hcostC⟩ := hS
  obtain ⟨m, D, hD, hTD, hcostD⟩ := hT
  refine ⟨n + m, Fin.addCases C D, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hC j
    · simpa using hD j
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hSC hx)
      exact mem_iUnion.mpr ⟨i.castAdd m, by simpa using hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hTD hx)
      exact mem_iUnion.mpr ⟨j.natAdd n, by simpa using hj⟩
  · simpa [familyArea, Fin.sum_univ_add] using add_le_add hcostC hcostD

lemma physicalRuled_union (h L : ℝ) (v : Plane → Plane) (S T : Set Plane) :
    physicalRuled h (S ∪ T) v L = physicalRuled h S v L ∪ physicalRuled h T v L := by
  ext z
  simp only [physicalRuled, mem_ofPred_eq, mem_union]
  aesop

lemma physicalRuled_empty (h L : ℝ) (v : Plane → Plane) : physicalRuled h ∅ v L = ∅ := by
  simp [physicalRuled]

/-- Finite gluing over regular open patches. Only the patch frontiers must be null;
 there is deliberately no restriction on the label set's own frontier. -/
theorem glue_finite_local_covers {shape : Cylinder → Prop} (h L : ℝ) (v : Plane → Plane)
    (F : Plane → ℝ) {A : ℝ}
    {ι : Type*} (s : Finset ι) (O U : ι → Set Plane)
    (hO : ∀ i ∈ s, IsOpen (O i)) (hOU : ∀ i ∈ s, closure (O i) ⊆ U i)
    (hnull : ∀ i ∈ s, volume (frontier (O i)) = 0)
    (hlocal : ∀ i ∈ s, ∀ Q : Set Plane, IsCompact Q → Q ⊆ U i →
      ∀ eps : ℝ, 0 < eps → HasFiniteCover shape (physicalRuled h Q v L)
        (A * (∫ p in Q, F p) + eps))
    {K : Set Plane} (hK : IsCompact K) (hF : IntegrableOn F K)
    (hcover : K ⊆ ⋃ i ∈ s, O i) {eps : ℝ} (heps : 0 < eps) :
    HasFiniteCover shape (physicalRuled h K v L) (A * (∫ p in K, F p) + eps) := by
  classical
  induction s using Finset.induction_on generalizing K eps with
  | empty =>
    have hKe : K = ∅ := by simpa using hcover
    rw [hKe, physicalRuled_empty]
    simpa using HasFiniteCover.empty shape heps.le
  | @insert i s hi ih =>
    have hOi := hO i (by simp)
    obtain ⟨h₁, h₂, hun, hint⟩ := compact_cut_integral hK hOi (hnull i (by simp)) hF
    have hc₁ := hlocal i (by simp) _ h₁
      (inter_subset_right.trans (hOU i (by simp))) (eps / 2) (half_pos heps)
    have hsub : K \ O i ⊆ ⋃ j ∈ s, O j := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx.1)
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact False.elim (hx.2 hxj)
      · exact mem_iUnion₂.mpr ⟨j, hj, hxj⟩
    have hc₂ := ih (fun j hj => hO j (by simp [hj]))
      (fun j hj => hOU j (by simp [hj])) (fun j hj => hnull j (by simp [hj]))
      (fun j hj => hlocal j (by simp [hj])) h₂ (hF.mono_set sdiff_subset)
      hsub (half_pos heps)
    have hc := hc₁.union hc₂
    rw [← physicalRuled_union, ← hun] at hc
    convert hc using 1
    rw [hint]
    ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.glue_finite_local_covers := @_root_.OAI.RuledApproximation.glue_finite_local_covers
