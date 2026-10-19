-- Prove2me | solution 1 for OAI.MatchingSmoothing.lowDegree_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:26:54.213543+00:00
-- url     : https://prove2.me/submissions/4cd9abc5-3f52-46ae-a5b7-259be84de910

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/ColorPolynomials.lean:L113-L135
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.lowDegree_lift. The node keeps its source
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

-- ---- from OAI.Combinatorics.MatchingPSD.ColorPolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ColorPolynomials
variable {V : Type u_1} {C : Type u_2} [Fintype V]

end ColorPolynomials

section Substitution
variable {E : Type u_3} {I : Type u_4} {X : Type u_5} {Y : Type u_6}

lemma lowDegree_lift (x : E → X → ℝ) (d : ℕ) (f : X → ℝ)
    (hf : f ∈ lowDegree x d) :
    ∃ P ∈ lowDegree (fun e (v : E → ℝ) => v e) d,
      ∀ a, f a = P (fun e => x e a) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    refine ⟨(l.map (fun e (v : E → ℝ) => v e)).prod,
      Submodule.subset_span ⟨l, hl, rfl⟩, ?_⟩
    intro a
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply]
      rw [ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) hl)]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨P, hP, hp⟩ := hf
    obtain ⟨Q, hQ, hq⟩ := hg
    exact ⟨P+Q, Submodule.add_mem _ hP hQ, fun a => by simp [hp a, hq a]⟩
  | smul c f _ hf =>
    obtain ⟨P, hP, hp⟩ := hf
    exact ⟨c • P, Submodule.smul_mem _ c hP, fun a => by simp [hp a]⟩

end Substitution
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.lowDegree_lift := @_root_.OAI.MatchingSmoothing.lowDegree_lift
