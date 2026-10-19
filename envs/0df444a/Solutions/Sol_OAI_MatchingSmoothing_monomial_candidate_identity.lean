-- Prove2me | solution 1 for OAI.MatchingSmoothing.monomial_candidate_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:25:04.233001+00:00
-- url     : https://prove2.me/submissions/4ca31088-a023-44c4-8cf3-e5110148a340

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PartialColorings.lean:L125-L145
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.monomial_candidate_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings

-- ---- from OAI.Combinatorics.MatchingPSD.EdgeMonomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
namespace Pairing
variable {V : Type u_1}

lemma mem_edgeSupport (l : List (V × V)) (v : V) :
    v ∈ edgeSupport l ↔ ∃ e ∈ l, v = e.1 ∨ v = e.2 := by
  simp only [edgeSupport, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e, he, Or.inr rfl⟩
  · rintro ⟨e, he, h | h⟩
    · exact Or.inl ⟨e, he, h.symm⟩
    · exact Or.inr ⟨e, he, h.symm⟩

lemma edgeMonomial_eq_indicator (l : List (V × V)) (M : Pairing V) :
    edgeMonomial l M = if ContainsList M l then 1 else 0 := by
  induction l with
  | nil => simp [edgeMonomial, ContainsList]
  | cons e l ih =>
    simp only [edgeMonomial, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih]
    simp only [ContainsList, List.mem_cons, forall_eq_or_imp, edgeCoord]
    split_ifs <;> simp_all

lemma contains_partner_support {M : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) {v : V} (hv : v ∈ edgeSupport l) :
    M.1 v ∈ edgeSupport l := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he]
    exact (mem_edgeSupport l e.2).mpr ⟨e, he, Or.inr rfl⟩
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he)]
    exact (mem_edgeSupport l e.1).mpr ⟨e, he, Or.inl rfl⟩

lemma contains_agree_support {M N : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) (hn : ContainsList N l) {v : V}
    (hv : v ∈ edgeSupport l) : M.1 v = N.1 v := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he, hn e he]
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he),
      (partner_eq_iff N e.1 e.2).mp (hn e he)]

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ColorAverage
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PartialColorings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorCounting
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma candidate_sum (z : V → C) (U : Finset V) (c : C × C) (M : Pairing V)
    (hU : ∀ v, M.1 v ∈ U ↔ v ∈ U) :
    ∑ e ∈ candidateEdges z U c, Pairing.edgeCoord e M =
      ∑ v ∈ (Finset.univ \ U), if z v = c.1 ∧ z (M.1 v) = c.2 then (1:ℝ) else 0 := by
  rw [candidateEdges, Finset.sum_filter]
  change (∑ e : V × V, if e.1 ∉ U ∧ e.2 ∉ U ∧ e.1 ≠ e.2 ∧
      z e.1 = c.1 ∧ z e.2 = c.2 then Pairing.edgeCoord e M else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]
  have hpoint (v : V) :
      (∑ w : V, if v ∉ U ∧ w ∉ U ∧ v ≠ w ∧ z v = c.1 ∧ z w = c.2
        then Pairing.edgeCoord (v,w) M else 0) =
      if v ∉ U then (if z v = c.1 ∧ z (M.1 v) = c.2 then 1 else 0) else 0 := by
    rw [Finset.sum_eq_single (M.1 v)]
    · by_cases hv : v ∈ U <;> by_cases ha : z v = c.1 <;>
        by_cases hb : z (M.1 v) = c.2 <;>
        simp [Pairing.edgeCoord, hU v, (M.partner_ne v).symm, hv, ha, hb]
    · intro w _ hw
      simp [Pairing.edgeCoord, Ne.symm hw]
    · simp
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun v => v ∉ U) = Finset.univ \ U := by ext; simp
  rw [hfilter, Finset.sum_sdiff_eq_sub (Finset.subset_univ U)]

lemma monomial_candidate_identity (z : V → C) (l : List (V × V)) (c : C × C)
    (M₀ : Pairing V) (h₀ : Pairing.ContainsList M₀ l) :
    Pairing.edgeMonomial l * (∑ e ∈ candidateEdges z (Pairing.edgeSupport l) c,
      Pairing.edgeCoord e) =
    Pairing.edgeMonomial l * (tableCoordinate z c -
      (∑ v ∈ Pairing.edgeSupport l,
        if z v = c.1 ∧ z (M₀.1 v) = c.2 then (1:ℝ) else 0) • 1) := by
  funext M
  by_cases hm : Pairing.ContainsList M l
  · simp only [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, ite_eq_left hm, one_mul,
      Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [candidate_sum z (Pairing.edgeSupport l) c M (fun v => ⟨
      fun hv => by simpa using Pairing.contains_partner_support hm hv,
      fun hv => Pairing.contains_partner_support hm hv⟩)]
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
    unfold tableCoordinate
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [Pairing.contains_agree_support hm h₀ hv]
  · simp [Pi.mul_apply, Pairing.edgeMonomial_eq_indicator, hm]

end ColorCounting
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.monomial_candidate_identity := @_root_.OAI.MatchingSmoothing.monomial_candidate_identity
