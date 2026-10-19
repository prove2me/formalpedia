-- Prove2me | solution 1 for OAI.MatchingSmoothing.table_eq_iff_cross
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:37:48.930346+00:00
-- url     : https://prove2.me/submissions/e48666f4-1375-4789-9f44-8b18914c1bae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableGeometry.lean:L42-L62
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.table_eq_iff_cross. The node keeps its source
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
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

end Pairing
end MatchingSmoothing

end OAI

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

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma table_relabel (p : Equiv.Perm V) (M : Pairing V) (f : V → Fin 3) :
    (relabel p M).table f = M.table (f ∘ p) := by
  funext t
  unfold table
  congr 1
  have he : (fun v => threeEdgeType (f v, f ((relabel p M).1 v))) ∘ p =
      (fun v => threeEdgeType ((f ∘ p) v, (f ∘ p) (M.1 v))) := by
    funext v
    simp only [Function.comp_apply, relabel_apply]
    rw [Equiv.Perm.inv_def, p.symm_apply_apply]
  rw [← he, histogram_comp_perm]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma tableCoordinate_symm (z : V → C) (a b : C) :
    tableCoordinate z (a,b) = tableCoordinate z (b,a) := by
  funext M
  unfold tableCoordinate
  rw [← Equiv.sum_comp M.1 (fun v => if z v = b ∧ z (M.1 v) = a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  simp [M.partner_partner, and_comm]

lemma tableCoordinate_row_sum [Fintype C] (z : V → C) (a : C) :
    ∑ b, tableCoordinate z (a,b) = (histogram z a : ℝ) • 1 := by
  classical
  funext M
  simp only [Finset.sum_apply, tableCoordinate, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [Finset.sum_comm, histogram_cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : z v = a
  · simp [ha]
  · simp [ha]

lemma tableCoordinate_diagonal [Fintype C] (z : V → C) (a : C) :
    tableCoordinate z (a,a) = (histogram z a : ℝ) • 1 -
      ∑ b ∈ Finset.univ.erase a, tableCoordinate z (a,b) := by
  classical
  rw [← tableCoordinate_row_sum]
  rw [eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ a)

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

lemma tableCoordinate_relabel (z : H × Bool → Fin 3) (c : Fin 3 × Fin 3)
    (p : Equiv.Perm (H × Bool)) (M : Pairing (H × Bool)) :
    tableCoordinate z c (Pairing.relabel p M) = tableCoordinate (z ∘ p) c M := by
  classical
  unfold tableCoordinate
  apply Fintype.sum_equiv p.symm
  intro v
  split_ifs <;> simp_all [Function.comp_apply, Pairing.relabel_apply]

lemma three_order_indicator (a b x y : Fin 3) :
    (if x=a ∧ y=b then (1:ℝ) else 0) + (if y=a ∧ x=b then (1:ℝ) else 0) =
      (if a=b then 2 else 1) *
      (if threeEdgeType (x,y) = threeEdgeType (a,b) then (1:ℝ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [threeEdgeType, Fin.ext_iff]

lemma standard_tableCoordinate (z : H × Bool → Fin 3) (a b : Fin 3) :
    tableCoordinate z (a,b) standardPairing =
      (if a=b then (2:ℝ) else 1) * (threeTable z (threeEdgeType (a,b)) : ℝ) := by
  classical
  simp only [tableCoordinate, Fintype.sum_prod_type, Fintype.sum_bool,
    standardPairing, Equiv.prodCongr_apply]
  change (∑ i, ((if z (i,true)=a ∧ z (i,false)=b then (1:ℝ) else 0) +
    (if z (i,false)=a ∧ z (i,true)=b then (1:ℝ) else 0))) = _
  calc
    _ = ∑ i, (if a=b then (2:ℝ) else 1) *
        (if threeEdgeType (z (i,false),z (i,true)) = threeEdgeType (a,b) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_comm] using three_order_indicator a b (z (i,false)) (z (i,true))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (histogram_cast_sum (threeEdgeType ∘ pairColorEquiv z) _).symm

lemma tableCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (a b : Fin 3) :
    tableCoordinate z (a,b) M =
      (if a=b then (2:ℝ) else 1) * (M.table z (threeEdgeType (a,b)) : ℝ) := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  rw [tableCoordinate_relabel, Pairing.table_relabel, standardPairing_table,
    standard_tableCoordinate]

lemma crossCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (i : Fin 3) :
    crossCoordinate z i M = (M.table z (threeEdgeType (crossPair i)) : ℝ) := by
  rw [crossCoordinate, tableCoordinate_eq_table]
  have hne : (crossPair i).1 ≠ (crossPair i).2 := by fin_cases i <;> decide
  rw [ite_eq_right hne, one_mul]

end TableRelation
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TableGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma coordinates_eq_of_cross_eq {V : Type u_3} [Fintype V]
    (z : V → Fin 3) (M N : Pairing V)
    (h : crossVector z M = crossVector z N) : ∀ a b, tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
  have hb (a b : Fin 3) (hab : a ≠ b) : tableCoordinate z (a,b) M = tableCoordinate z (a,b) N := by
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b
    all_goals first | exact (hab rfl).elim | exact h0 | exact h1 | exact h2 |
      rwa [tableCoordinate_symm]
  intro a b
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb'
    exact hb a b hb'.symm
  · exact hb a b hab

lemma table_eq_iff_cross {H : Type u_4} [Fintype H] [DecidableEq H]
    (z : H × Bool → Fin 3) (M N : Pairing (H × Bool)) :
    M.table z = N.table z ↔ crossVector z M = crossVector z N := by
  constructor
  · intro h
    funext i
    simp only [crossVector, crossCoordinate_eq_table, h]
  · intro h
    have hh := coordinates_eq_of_cross_eq z M N h
    have get (a b : Fin 3) : M.table z (threeEdgeType (a,b)) = N.table z (threeEdgeType (a,b)) := by
      have he := hh a b
      rw [tableCoordinate_eq_table, tableCoordinate_eq_table] at he
      split_ifs at he <;> exact_mod_cast (by linarith : (M.table z (threeEdgeType (a,b)) : ℝ) = N.table z (threeEdgeType (a,b)))
    funext i
    fin_cases i
    · exact get 0 0
    · exact get 0 1
    · exact get 0 2
    · exact get 1 1
    · exact get 1 2
    · exact get 2 2

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.table_eq_iff_cross := @_root_.OAI.MatchingSmoothing.table_eq_iff_cross
