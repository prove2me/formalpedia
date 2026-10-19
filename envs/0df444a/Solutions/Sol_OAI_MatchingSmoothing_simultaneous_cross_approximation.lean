-- Prove2me | solution 1 for OAI.MatchingSmoothing.simultaneous_cross_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:41:13.130988+00:00
-- url     : https://prove2.me/submissions/da6718df-000d-4ff7-9195-f7c86f4c8b0e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CrossSelection.lean:L9-L67
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.simultaneous_cross_approximation. The node keeps its source
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
import Theorems.Thm_OAI_MatchingSmoothing_simultaneous_table_approximation
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table
import Theorems.Thm_OAI_MatchingSmoothing_table_eq_iff_cross

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
lemma predicateAverage_equiv (e : X ≃ Y) (P : X → Prop) (Q : Y → Prop)
    (he : ∀ x, P x ↔ Q (e x)) (f : Y → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage Q f := by
  classical
  have hc : Fintype.card {x // P x} = Fintype.card {y // Q y} :=
    Fintype.card_congr (e.subtypeEquiv he)
  rw [predicateAverage_apply, predicateAverage_apply, hc]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Function.comp_apply, he])

end Averages

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingFibers ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

lemma transport_relabel (e : A ≃ B) (p : Equiv.Perm A) (M : Pairing A) :
    transport e (relabel p M) = relabel (e.symm.trans (p.trans e)) (transport e M) := by
  ext b
  simp only [transport_apply, relabel_apply, Equiv.Perm.inv_def,
    Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

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

-- ---- from OAI.Combinatorics.MatchingPSD.TableGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma crossVector_transport {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W]
    (e : V ≃ W) (z : W → Fin 3) (M : Pairing V) :
    crossVector z (Pairing.transport e M) = crossVector (z ∘ e) M := by
  funext i
  exact tableCoordinate_transport e z (crossPair i) M

lemma histogram_comp_equiv {V : Type u_7} {W : Type u_8} {C : Type u_9} [Fintype V] [Fintype W] [DecidableEq C]
    (z : W → C) (e : V ≃ W) : histogram (z ∘ e) = histogram z := by
  funext c
  apply Fintype.card_congr
  exact e.subtypeEquiv (fun _ => Iff.rfl)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CrossSelection ----
namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma simultaneous_cross_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (V G I T : Type) [Fintype V] [Fintype G] [Group G] [Fintype I] [Fintype T]
      (_e : V ≃ Vertices h) (z : I → V → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing V)
      (lift : I → Equiv.Perm V → G)
      (g : I → G → Pairing V → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) -
            P i (crossVector (z i) (M i t)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_table_approximation K
  refine ⟨d,H,hd,?_⟩
  intro h hh V G I T _ _ _ _ _ e z hz M lift g hcov B hB
  let ev := Pairing.transportEquiv e.symm
  let z' := fun i => z i ∘ e.symm
  let M' := fun i t => Pairing.transport e (M i t)
  let lift' := fun i (p : Equiv.Perm (Vertices h)) => lift i (e.trans (p.trans e.symm))
  let g' := fun i a N => g i a (ev N)
  have hc (i : I) (a : G) (p : Equiv.Perm (Vertices h)) :
      g' i (a * lift' i p) = fun N => g' i a (Pairing.relabel p N) := by
    funext N
    change g i (a * lift' i p) (ev N) = _
    rw [hcov]
    change g i a (Pairing.relabel (e.trans (p.trans e.symm)) (Pairing.transport e.symm N)) =
      g i a (Pairing.transport e.symm (Pairing.relabel p N))
    rw [Pairing.transport_relabel]
    rfl
  obtain ⟨a,P,hP,hbound⟩ := hmain h hh G I T z'
    (fun i c => by
      have he : histogram (z' i) = histogram (z i) := histogram_comp_equiv (z i) e.symm
      rw [he]
      exact hz i c)
    M' lift' g' hc B (fun i a N => hB i a (ev N))
  refine ⟨a,P,hP,?_⟩
  have hvec (i : I) (t : T) : crossVector (z' i) (M' i t) = crossVector (z i) (M i t) := by
    rw [crossVector_transport]
    have he : z' i ∘ e = z i := by funext v; simp [z']
    rw [he]
  have hav (i : I) (t : T) :
      predicateAverage (fun N => N.table (z' i) = (M' i t).table (z' i)) (g' i a) =
        predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) := by
    apply predicateAverage_equiv ev
    intro N
    rw [table_eq_iff_cross, hvec]
    change _ ↔ crossVector (z i) (Pairing.transport e.symm N) = _
    rw [crossVector_transport]
  have htvec (i : I) (t : T) :
      (fun c => ((M' i t).table (z' i) (threeEdgeType (crossPair c)) : ℝ)) =
        crossVector (z i) (M i t) := by
    rw [← hvec]
    funext c
    exact (crossCoordinate_eq_table _ _ _).symm
  simpa only [hav, htvec] using hbound

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.simultaneous_cross_approximation := @_root_.OAI.MatchingSmoothing.simultaneous_cross_approximation
