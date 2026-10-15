-- Prove2me | solution 1 for OAI.RuledApproximation.HasFiniteCover.open_enlarge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:59:49.357381+00:00
-- url     : https://prove2.me/submissions/efdf38a4-2e24-4866-b775-f7f76a12d1ca

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SpecializedCover.lean:L37-L59
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.HasFiniteCover.open_enlarge. The node keeps its source
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
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Theorems.Thm_OAI_RuledApproximation_exists_nice_outer_integral

-- ---- from OAI.Geometry.RuledCovering.SpecializedCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma IsParallelogram.isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Set E} (hP : IsParallelogram P) : IsCompact P := by
  obtain ⟨c, u, v, _, rfl⟩ := hP
  have hc : IsCompact ((fun z : ℝ × ℝ => c + z.1 • u + z.2 • v) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  convert hc using 1
  ext x
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨(s,t), ⟨hs,ht⟩, rfl⟩
  · rintro ⟨⟨s,t⟩, ⟨hs,ht⟩, rfl⟩
    exact ⟨s,hs,t,ht,rfl⟩

lemma Cylinder.enlarge_open {C : Cylinder} (hC : C.parallelogram) {eps : ℝ} (heps : 0 < eps) :
    ∃ D : Cylinder, D.openBounded ∧ C.carrier ⊆ D.carrier ∧ D.area < C.area + eps := by
  obtain ⟨O, hOo, hOb, hCO, _, _, hOI⟩ := exists_nice_outer_integral
    hC.isCompact isOpen_univ (subset_univ _) (continuous_const : Continuous (fun _ => (1 : ℝ)))
    (fun _ => zero_le_one) heps
  refine ⟨⟨C.axis, C.unit_axis, O⟩, ⟨hOo,hOb,hOo.measurableSet⟩, ?_, ?_⟩
  · rintro x ⟨b,hb,t,hx⟩
    exact ⟨b,hCO hb,t,hx⟩
  · change volume.real O < volume.real C.base + eps
    simpa only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one] using hOI

/-- Compact parallelogram covers admit bounded open perpendicular bases with any
additional positive error. No portion of the closed ruled family is discarded. -/
lemma HasFiniteCover.open_enlarge {S : Set Space} {A eps : ℝ}
    (hc : HasFiniteCover Cylinder.parallelogram S A) (heps : 0 < eps) :
    HasFiniteCover Cylinder.openBounded S (A+eps) := by
  classical
  obtain ⟨n,C,hC,hcov,hcost⟩ := hc
  have hd : 0 < eps / (n+1 : ℝ) := div_pos heps (by positivity)
  choose D hD hCD harea using fun i => Cylinder.enlarge_open (hC i) hd
  refine ⟨n,D,hD,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i,hCD i hi⟩
  · change (∑ i, (D i).area) ≤ A+eps
    calc
      _ ≤ ∑ i, ((C i).area + eps/(n+1 : ℝ)) := Finset.sum_le_sum (fun i _ => (harea i).le)
      _ = familyArea C + n * (eps/(n+1 : ℝ)) := by simp [familyArea, Finset.sum_add_distrib]
      _ ≤ A + eps := by
        have hn : 0 < (n+1 : ℝ) := by positivity
        have hne : (n : ℝ) * (eps/(n+1 : ℝ)) ≤ eps := by
          rw [← mul_div_assoc, div_le_iff₀ hn]
          nlinarith
        exact add_le_add hcost hne

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.HasFiniteCover.open_enlarge := @_root_.OAI.RuledApproximation.HasFiniteCover.open_enlarge
