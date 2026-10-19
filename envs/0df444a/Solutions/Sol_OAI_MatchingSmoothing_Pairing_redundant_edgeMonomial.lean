-- Prove2me | solution 1 for OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:23:31.149313+00:00
-- url     : https://prove2.me/submissions/ea38bb24-6096-4cf7-9311-c201be6ec3c3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/EdgeMonomials.lean:L66-L81
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial. The node keeps its source
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

lemma contains_agree_support {M N : Pairing V} {l : List (V × V)}
    (hm : ContainsList M l) (hn : ContainsList N l) {v : V}
    (hv : v ∈ edgeSupport l) : M.1 v = N.1 v := by
  obtain ⟨e, he, rfl | rfl⟩ := (mem_edgeSupport l v).mp hv
  · rw [hm e he, hn e he]
  · rw [(partner_eq_iff M e.1 e.2).mp (hm e he),
      (partner_eq_iff N e.1 e.2).mp (hn e he)]

lemma redundant_edgeMonomial {M : Pairing V} {e : V × V} {l : List (V × V)}
    (he : M.1 e.1 = e.2) (hm : ContainsList M l)
    (hv : e.1 ∈ edgeSupport l ∨ e.2 ∈ edgeSupport l) :
    edgeMonomial (e::l) = edgeMonomial l := by
  funext N
  simp only [edgeMonomial_eq_indicator]
  congr 1
  simp only [ContainsList, List.mem_cons, forall_eq_or_imp]
  apply propext
  refine and_iff_right_of_imp ?_
  intro hn
  change ContainsList N l at hn
  rcases hv with hv | hv
  · exact (contains_agree_support hn hm hv).trans he
  · apply (partner_eq_iff N e.1 e.2).mpr
    exact (contains_agree_support hn hm hv).trans ((partner_eq_iff M e.1 e.2).mp he)

end Pairing

section ColorAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ColorAverage
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial := @_root_.OAI.MatchingSmoothing.Pairing.redundant_edgeMonomial
