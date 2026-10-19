-- Prove2me | solution 1 for OAI.MatchingSmoothing.triple_pairing_five
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:43:18.151841+00:00
-- url     : https://prove2.me/submissions/94f9aff1-1284-456d-996f-52074babc91c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AdmissiblePoints.lean:L9-L27
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.triple_pairing_five. The node keeps its source
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

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingFibers ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_transport (e : A ≃ B) (z : B → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c (Pairing.transport e M) = tableCoordinate (z ∘ e) c M := by
  unfold tableCoordinate
  rw [← e.sum_comp (fun b => if z b = c.1 ∧ z ((Pairing.transport e M).1 b) = c.2 then (1:ℝ) else 0)]
  simp only [Pairing.transport_apply, Equiv.symm_apply_apply, Function.comp_apply]

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

end MatchingSmoothing.Pairing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AdmissibleTables ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ColorTransport
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
omit [Fintype C] in
lemma colorEquiv_spec (f : A → C) (g : B → C) (h : histogram f = histogram g) (a : A) :
    g (colorEquiv f g h a) = f a := by
  exact (Fintype.equivOfCardEq (congrFun h (f a)) ⟨a,rfl⟩).property
end ColorTransport

lemma edgeColor_histogram (E : Fin 6 → ℕ) : histogram (edgeColor E) = endpointSizes E := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases c <;> simp [edgeColor, endpointSizes, typePair, Fin.sum_univ_succ] <;> ring

lemma edgeColor_cross (E : Fin 6 → ℕ) (i : Fin 3) :
    crossCoordinate (edgeColor E) i (standardPairing (H := TypedEdges E)) =
      (![E 1,E 2,E 4] i : ℝ) := by
  simp only [crossCoordinate, tableCoordinate, Fintype.sum_prod_type,
    Fintype.sum_sigma, Fintype.sum_bool]
  fin_cases i <;> simp [crossPair, standardPairing, edgeColor, typePair, Fin.sum_univ_succ]

lemma exists_pairing_of_endpoints {V : Type u_4} [Fintype V]
    (z : V → Fin 3) (E : Fin 6 → ℕ) (hz : histogram z = endpointSizes E) :
    ∃ M : Pairing V, ∀ i : Fin 3, crossCoordinate z i M = (![E 1,E 2,E 4] i : ℝ) := by
  let e := colorEquiv (edgeColor E) z ((edgeColor_histogram E).trans hz.symm)
  have he : z ∘ e = edgeColor E := funext (colorEquiv_spec _ _ _)
  refine ⟨Pairing.transport e standardPairing, ?_⟩
  intro i
  rw [crossCoordinate, tableCoordinate_transport, he]
  exact edgeColor_cross E i

lemma tripleColor_histogram (s : ℕ) :
    histogram (@tripleColor s) = ![2*s+1,2*s+1,2*s] := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  fin_cases c <;> simp [tripleColor, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_mul]; ring

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AdmissiblePoints ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma triple_pairing_five {s : ℕ} (hs : 1 ≤ s) (j : Fin 5) :
    ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
      (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Fin 3 → ℝ) := by
  have hex (E : Fin 6 → ℕ) (he : endpointSizes E = ![2*s+1,2*s+1,2*s]) :
      ∃ M : Pairing (TripleVertices s), crossVector tripleColor M =
        (fun i => (![E 1,E 2,E 4] i : ℝ)) := by
    obtain ⟨M,hM⟩ := exists_pairing_of_endpoints tripleColor E (by rw [tripleColor_histogram, he])
    exact ⟨M,funext hM⟩
  fin_cases j
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s,0,s] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,0,1,s,1,s-1] (by ext i; fin_cases i <;> simp [endpointSizes]; omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,3,0,s-1,0,s] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s-1,1,2,s,0,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩
  · obtain ⟨M,hM⟩ := hex ![s,1,0,s-1,2,s-1] (by ext i; fin_cases i <;> simp [endpointSizes] <;> omega)
    exact ⟨M,by rw [hM]; ext i; fin_cases i <;> simp⟩

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.triple_pairing_five := @_root_.OAI.MatchingSmoothing.triple_pairing_five
