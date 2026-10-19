-- Prove2me | solution 1 for OAI.MatchingSmoothing.predicateAverage_of_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:30:17.202978+00:00
-- url     : https://prove2.me/submissions/6ff996ac-f500-423a-8b58-9751d490c962

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TablePolynomials.lean:L38-L52
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.predicateAverage_of_constant. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials

-- ---- from OAI.Combinatorics.MatchingPSD.TablePolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

lemma predicateAverage_of_constant (P : X → Prop) (c : ℝ) (hP : ∃ x, P x)
    (f : X → ℝ) (hf : ∀ x, P x → f x = c) : predicateAverage P f = c := by
  classical
  have : Nonempty {x // P x} := ⟨⟨hP.choose, hP.choose_spec⟩⟩
  rw [predicateAverage_apply]
  have hs : (∑ x, if P x then f x else 0) = Fintype.card {x // P x} * c := by
    calc
      _ = ∑ x ∈ Finset.univ.filter P, f x := (Finset.sum_filter _ _).symm
      _ = ∑ _x ∈ Finset.univ.filter P, c := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hf x (Finset.mem_filter.mp hx).2
      _ = _ := by simp [Fintype.card_subtype]
  rw [hs]
  exact mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

end TablePolynomial
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.predicateAverage_of_constant := @_root_.OAI.MatchingSmoothing.predicateAverage_of_constant
