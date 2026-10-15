-- Prove2me | solution 1 for OAI.ForestSpace.exists_head_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:53:13.57362+00:00
-- url     : https://prove2.me/submissions/9b9018e4-d78d-4bc7-891d-8a537d5b9755

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Projections.lean:L167-L183
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.exists_head_approx. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections

-- ---- from OAI.Analysis.ForestSpace.Projections ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Projections
variable {V : Type} [PartialOrder V]

 theorem norm_Q_le (H : Set V) (hH : IsLowerSet H) (x : FullDual V) : ‖Q H hH x‖ ≤ ‖x‖ := by
  apply (Q H hH x).opNorm_le_bound (norm_nonneg _)
  intro u
  exact (x.le_opNorm (tailJ H hH u)).trans
    (mul_le_mul_of_nonneg_left (norm_tailJ_le H hH u) (norm_nonneg _))

 theorem P_eStar (H : Set V) (hH : IsLowerSet H) (v : V) :
    P H hH (eStar v) = if v ∈ H then eStar v else 0 := by
  apply ContinuousLinearMap.ext
  intro u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (P H hH (eStar v)).continuous (map_continuous _)) ?_
  intro f
  by_cases hv : v ∈ H <;> simp [hv]

 theorem finite_span_support {z : FullDual V}
    (hz : z ∈ Submodule.span ℝ (Set.range (eStar (V := V)))) :
    ∃ S : Finset V, ∀ H : Finset V, ∀ hH : IsLowerSet (H : Set V),
      S ⊆ H → P (H : Set V) hH z = z := by
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  refine ⟨c.support, ?_⟩
  intro H hH hSH
  change P (H : Set V) hH (∑ v ∈ c.support, c v • eStar v) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_smul, P_eStar, ite_eq_left (show v ∈ (H : Set V) from hSH hv)]

/-- Coordinate density plus tail contractivity gives arbitrarily close finite
ancestral heads in the general coordinate completion. -/
 theorem exists_head_approx (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (x : X V) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset V, ∃ hH : IsLowerSet (H : Set V), ‖x - PX H hH x‖ < ε := by
  have hx : (x : FullDual V) ∈ closure
      (Submodule.span ℝ (Set.range (eStar (V := V))) : Set (FullDual V)) := x.property
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp hx ε hε
  obtain ⟨S,hS⟩ := finite_span_support hz
  obtain ⟨H,hSH,hH⟩ := exists_finite_lower_hull hAnc S
  have hzP := hS H hH hSH
  have hzQ : Q (H : Set V) hH z = 0 := by rw [Q_eq_sub, hzP, sub_self]
  have hn := norm_Q_le (H : Set V) hH ((x : FullDual V)-z)
  rw [map_sub, hzQ, sub_zero, Q_eq_sub] at hn
  refine ⟨H,hH, ?_⟩
  change ‖(x : FullDual V) - P (H : Set V) hH x‖ < ε
  exact hn.trans_lt (by simpa only [dist_eq_norm] using hclose)

end Projections

section CoordinateStructure
variable {V : Type} [PartialOrder V]

end CoordinateStructure

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.exists_head_approx := @_root_.OAI.ForestSpace.exists_head_approx
