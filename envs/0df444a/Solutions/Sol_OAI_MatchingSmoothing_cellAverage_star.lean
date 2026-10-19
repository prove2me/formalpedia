-- Prove2me | solution 1 for OAI.MatchingSmoothing.cellAverage_star
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:46:42.186256+00:00
-- url     : https://prove2.me/submissions/88bed28f-5380-4bd0-9859-a12de5697abb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CellAverages.lean:L32-L60
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.cellAverage_star. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages

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

-- ---- from OAI.Combinatorics.MatchingPSD.PermutationSmoothing ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
lemma predicateAverage_eq_expect (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = 𝔼 x : {x // P x}, f x.1 := by
  rw [predicateAverage_apply, Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

end Averages

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.GlobalGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ThreeCellGeometry
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C]

end ThreeCellGeometry

section GlobalExtension
variable {D : Type u_5} {C : Type u_6} {I : Type u_7} [DecidableEq I]

lemma extendLocal_sum (i : I) (M : Pairing D) (N : I → Pairing C) :
    extendLocal i (Pairing.sum M (N i)) (fun j => N j.1) =
      Pairing.sum M (Pairing.cellwise N) := by
  apply Pairing.ext
  intro v
  obtain ⟨v,rfl⟩ := (localSplitEquiv (D := D) (C := C) i).surjective v
  simp only [extendLocal, Pairing.transport_apply, Equiv.symm_apply_apply]
  cases v with
  | inl v =>
    cases v with
    | inl d => rfl
    | inr c => rfl
  | inr jc => rfl

end GlobalExtension
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellAverages ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
section CellAverages
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

lemma expect_pair_product {X : Type u_5} {Y : Type u_6} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    (𝔼 p : X × Y, f p) = 𝔼 x : X, 𝔼 y : Y, f (x,y) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

lemma cellAverage_star (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (x : ℝ) :
    cellAverage i f ![x,0,0] =
      𝔼 M : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x},
        𝔼 N : I → Pairing C, f (Pairing.sum M.1 (Pairing.cellwise N)) := by
  classical
  rw [cellAverage, predicateAverage_eq_expect]
  have he := Fintype.expect_equiv (starFiberEquiv (A := A) (B := B) (C := C) x)
    (fun p => extensionAverage i f (Pairing.sum p.1.1 p.2))
    (fun p => extensionAverage i f p.1) (fun _ => rfl)
  calc
    _ = 𝔼 p : {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x} × Pairing C,
        extensionAverage i f (Pairing.sum p.1.1 p.2) := by
          convert he.symm using 1
          congr 1
          ext; simp
    _ = _ := ?_
  rw [expect_pair_product]
  apply Finset.expect_congr rfl
  intro M _
  simp only [extensionAverage]
  calc
    _ = 𝔼 p : Pairing C × ({j : I // j ≠ i} → Pairing C),
        f (extendLocal i (Pairing.sum M.1 p.1) p.2) := by
      convert (expect_pair_product (fun p : Pairing C × ({j : I // j ≠ i} → Pairing C) =>
        f (extendLocal i (Pairing.sum M.1 p.1) p.2))).symm using 1
    _ = _ := (Fintype.expect_equiv (Equiv.piSplitAt i (fun _ : I => Pairing C))
      (fun N => f (Pairing.sum M.1 (Pairing.cellwise N)))
      (fun p => f (extendLocal i (Pairing.sum M.1 p.1) p.2))
      (fun N => by rw [Equiv.piSplitAt_apply, extendLocal_sum])).symm

end CellAverages
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.cellAverage_star := @_root_.OAI.MatchingSmoothing.cellAverage_star
