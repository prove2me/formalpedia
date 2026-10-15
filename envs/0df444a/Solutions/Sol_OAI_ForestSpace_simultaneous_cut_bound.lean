-- Prove2me | solution 1 for OAI.ForestSpace.simultaneous_cut_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:36:48.644422+00:00
-- url     : https://prove2.me/submissions/09b62abc-10cf-446b-a5a0-2cd86b19fdcf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Paired.lean:L119-L158
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.simultaneous_cut_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired

-- ---- from OAI.Analysis.ForestSpace.Segments ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {V : Type} [PartialOrder V]

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

omit [PartialOrder V] in
 theorem SupportedOn.segSum_filter [PartialOrder V] {u : V → ℝ} {H : Set V} (hu : SupportedOn u H)
    (S : Finset V) : segSum u (S.filter (· ∈ H)) = segSum u S := by
  classical
  simp only [segSum, Finset.sum_filter]
  apply sum_congr rfl
  intro v hv
  split_ifs with hh
  · rfl
  · exact (hu v hh).symm

end Geometry

end

end ForestSpace

end OAI

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

omit [Fintype V] [PartialOrder V] in
/-- All suffix cuts can be charged to one disjoint segment test of the head. -/
 theorem simultaneous_cut_bound [Fintype V] [PartialOrder V] {H : Set V} {f : V → ℝ}
    (hf : SupportedOn f H) (hf₁ : TestBound f 1)
    {ι : Type} [Fintype ι] (S L : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hL : ∀ i, L i ⊆ (S i).filter (· ∈ H))
    (hseg : ∀ i, IsSegment (L i))
    (hdiff : ∀ i, IsSegment ((S i).filter (· ∈ H) \ L i)) :
    (∑ i, ((segSum f (S i) - segSum f (L i)) ^ 2 + segSum f (L i) ^ 2)) ≤ 1 := by
  let P : ι → Finset V := fun i => (S i).filter (· ∈ H)
  let pieces : ι × Bool → Finset V := fun p => if p.2 then L p.1 else P p.1 \ L p.1
  have hpseg : ∀ p, IsSegment (pieces p) := by
    rintro ⟨i, b⟩
    cases b
    · exact hdiff i
    · exact hseg i
  have hpsub : ∀ p, pieces p ⊆ S p.1 := by
    rintro ⟨i, b⟩
    cases b
    · exact sdiff_subset.trans (filter_subset _ _)
    · exact (hL i).trans (filter_subset _ _)
  have hpdis : Pairwise (fun p q => Disjoint (pieces p) (pieces q)) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact sdiff_disjoint
      · exact disjoint_sdiff
      · exact (hne rfl).elim
    · exact (hd hij).mono (hpsub (i,b)) (hpsub (j,c))
  have hb := hf₁ (ι × Bool) inferInstance pieces hpseg hpdis
  have he : ∀ i, segSum f (P i \ L i) = segSum f (S i) - segSum f (L i) := by
    intro i
    have ht : segSum f (P i \ L i) + segSum f (L i) = segSum f (P i) := sum_sdiff (hL i)
    have ht' : segSum f (P i) = segSum f (S i) := hf.segSum_filter (S i)
    linarith
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, pieces, Bool.false_eq_true,
    ↓reduceIte, he, add_comm] using hb

end FinitePaired

section FiniteRestriction
variable {V : Type} [PartialOrder V]

end FiniteRestriction

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.simultaneous_cut_bound := @_root_.OAI.ForestSpace.simultaneous_cut_bound
