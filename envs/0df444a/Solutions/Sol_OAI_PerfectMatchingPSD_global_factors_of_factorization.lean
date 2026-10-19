-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.global_factors_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:20:51.307095+00:00
-- url     : https://prove2.me/submissions/27b936b5-ce7b-4840-9e04-0fcca541d93c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Padding.lean:L59-L88
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.global_factors_of_factorization. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding
import Theorems.Thm_OAI_PerfectMatchingPSD_cut_degree_identity
import Theorems.Thm_OAI_PerfectMatchingPSD_exists_normalized_factors

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

lemma transport_perm (p : Equiv.Perm A) (M : Pairing A) : transport p M = relabel p M := rfl

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

-- ---- from OAI.Combinatorics.MatchingPSD.CutGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma globalCutColor_card (s q : ℕ) (y : Fin q → Bool) :
    Fintype.card {v : GlobalVertices s q // globalCutColor y v = true} =
      2*s+1 + Fintype.card {i : Fin q // y i = true} * (2*s) := by
  classical
  have hc (V : Type) [Fintype V] (f : V → Bool) :
      Fintype.card {v // f v = true} = histogram f true := by
    simp only [Fintype.card_subtype, histogram]
  rw [hc, hc]
  apply Nat.cast_injective (R := ℝ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    histogram_cast_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, globalCutColor,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, mul_zero, add_zero, Finset.sum_add_distrib, Finset.sum_mul,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : y i = true <;> simp [h]
  ring

lemma globalCutColor_odd (s q : ℕ) (y : Fin q → Bool) :
    Odd (Fintype.card {v : GlobalVertices s q // globalCutColor y v = true}) := by
  rw [globalCutColor_card]
  exact ⟨s+Fintype.card {i : Fin q // y i = true}*s, by ring⟩

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingConversion ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing
attribute [local instance] Classical.propDecidable

lemma pairingEdge_cross {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (v : Fin n) (hv : v ∈ U) (hp : M.1 v ∉ U) : Crosses U (pairingEdge M v) := by
  unfold pairingEdge
  split_ifs <;> simp [Crosses, hv, hp]

lemma cross_edge_inside {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n))
    (e : Edge n) (he : e ∈ (fromPairing M).1) (hc : Crosses U e) :
    ∃ v : Fin n, (v ∈ U ∧ M.1 v ∉ U) ∧ pairingEdge M v = e := by
  have hm := (mem_fromPairing M e).mp he
  rcases hc with hc | hc
  · refine ⟨e.1.1,⟨hc.1,?_⟩,(eq_pairingEdge M e hm _ (Or.inl rfl)).symm⟩
    simpa only [hm] using hc.2
  · refine ⟨e.1.2,⟨hc.2,?_⟩,(eq_pairingEdge M e hm _ (Or.inr rfl)).symm⟩
    simpa only [← hm, M.partner_partner] using hc.1

lemma pairingEdge_inside_injective {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    Function.Injective (fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} => pairingEdge M v.1) := by
  intro v w h
  apply Subtype.ext
  have hv := pairingEdge_incident M v.1
  have hw := pairingEdge_incident M w.1
  change pairingEdge M v.1 = pairingEdge M w.1 at h
  rw [← h] at hw
  rcases hv with hv | hv <;> rcases hw with hw | hw
  · exact hv.symm.trans hw
  · have hm := pairingEdge_mem M v.1
    rw [hv,hw] at hm
    exact False.elim (v.2.2 (hm ▸ w.2.1))
  · have hm := pairingEdge_mem M v.1
    rw [hw,hv] at hm
    exact False.elim (w.2.2 (hm ▸ v.2.1))
  · exact hv.symm.trans hw

lemma crossingCount_fromPairing {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    crossingCount U (fromPairing M) = Fintype.card {v : Fin n // v ∈ U ∧ M.1 v ∉ U} := by
  classical
  rw [crossingCount, ← Fintype.card_coe]
  symm
  apply Fintype.card_of_bijective (f := fun v : {v : Fin n // v ∈ U ∧ M.1 v ∉ U} =>
    (⟨pairingEdge M v.1,by simp [pairingEdge_mem, pairingEdge_cross M U v.1 v.2.1 v.2.2]⟩ :
      {e // e ∈ (fromPairing M).1.filter (Crosses U)}))
  constructor
  · intro v w h
    exact pairingEdge_inside_injective M U (congrArg Subtype.val h)
  · intro e
    obtain ⟨v,hv,he⟩ := cross_edge_inside M U e.1 (Finset.mem_filter.mp e.2).1 (Finset.mem_filter.mp e.2).2
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩

lemma crossingCount_tableCoordinate {n : ℕ} (M : Pairing (Fin n)) (U : Finset (Fin n)) :
    (crossingCount U (fromPairing M) : ℝ) =
      tableCoordinate (fun v => decide (v ∈ U)) (true,false) M := by
  rw [crossingCount_fromPairing]
  simp [tableCoordinate, Fintype.card_subtype, Finset.sum_boole]

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.NormalizedFactors ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma perfectMatching_nonempty {n : ℕ} (hn : Even n) : Nonempty (PerfectMatching n) := by
  classical
  obtain ⟨k,hk⟩ := hn
  let e : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  exact ⟨fromPairing (Pairing.transport e standardPairing)⟩

lemma slack_le_vertices {n : ℕ} (hn : 1 ≤ n) (i : Row n) (M : PerfectMatching n) :
    slack i M ≤ (n:ℝ) := by
  rcases i with e | U
  · simp only [slack]
    split_ifs
    · exact_mod_cast hn
    · positivity
  · have hd := cut_degree_identity U.1 M
    have hcard : U.1.card ≤ n := by simpa using Finset.card_le_univ U.1
    have hc : crossingCount U.1 M ≤ n := by omega
    have hc' : (crossingCount U.1 M : ℝ) ≤ n := by exact_mod_cast hc
    change (crossingCount U.1 M : ℝ)-1 ≤ (n:ℝ)
    linarith

lemma normalized_factorization {n r : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) :
    ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
      (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
      (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ i M, (A i*B M).trace = slack i M) ∧
      (∀ i, (A i).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) := by
  classical
  have := perfectMatching_nonempty hn
  rcases hfac with ⟨A,B,hA,hB,hpair⟩
  obtain ⟨A',B',hA',hB',hpair',htrA,htrB⟩ := exists_normalized_factors A B hA hB (n:ℝ)
    (fun i M => by rw [← hpair]; exact slack_le_vertices hnpos i M)
  exact ⟨A',B',hA',hB',fun i M => (hpair' i M).trans (hpair i M).symm,
    htrA,by simpa using htrB⟩

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Padding ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma colorCut_slack {n : ℕ} {V : Type u_2} [Fintype V]
    (e : V ≃ Fin n) (z : V → Bool) (hz : Odd (Fintype.card {v // z v = true}))
    (M : Pairing V) :
    slack (Sum.inr (colorCut e z hz)) (fromPairing (Pairing.transport e M)) =
      tableCoordinate z (true,false) M - 1 := by
  classical
  rw [slack, crossingCount_tableCoordinate, tableCoordinate_transport]
  congr 2
  funext v
  simp [colorCut]

lemma true_card_comp_equiv {V : Type u_3} {W : Type u_4} [Fintype V] [Fintype W]
    (z : V → Bool) (e : W ≃ V) :
    Fintype.card {w // z (e w) = true} = Fintype.card {v // z v = true} :=
  Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

lemma true_card_sum_false {V : Type u_5} {W : Type u_6} [Fintype V] [Fintype W] (z : V → Bool) :
    Fintype.card {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} =
      Fintype.card {v : V // z v = true} := by
  classical
  let e : {v : V ⊕ W // Sum.elim z (fun _ => false) v = true} ≃ {v : V // z v = true} :=
    { toFun := fun v => match v with
        | ⟨Sum.inl a,h⟩ => ⟨a,h⟩
        | ⟨Sum.inr _,h⟩ => nomatch h
      invFun := fun v => ⟨Sum.inl v.1,v.2⟩
      left_inv := by
        rintro ⟨v,h⟩
        cases v with
        | inl v => rfl
        | inr v => exact False.elim (Bool.false_ne_true h)
      right_inv := by intro v; rfl }
  exact Fintype.card_congr e

lemma tableCoordinate_false {V : Type u_7} [Fintype V] (M : Pairing V) :
    tableCoordinate (fun _ : V => false) (true,false) M = 0 := by
  simp [tableCoordinate]

lemma global_factors_of_factorization {n r s q : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) {W : Type} [Fintype W]
    (e : (GlobalVertices s q ⊕ W) ≃ Fin n) (MW : Pairing W) :
    ∃ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ a y, (Q a y).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) ∧
      ∀ a y M, (Q a y * B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M - 1 := by
  classical
  obtain ⟨A,B,hA,hB,hpair,htrA,htrB⟩ := normalized_factorization hn hnpos hfac
  let z (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) : GlobalVertices s q ⊕ W → Bool :=
    Sum.elim (globalCutColor y ∘ a.symm) (fun _ => false)
  have hz (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) :
      Odd (Fintype.card {v // z a y v = true}) := by
    rw [true_card_sum_false]
    change Odd (Fintype.card {v // globalCutColor y (a.symm v) = true})
    rw [true_card_comp_equiv]
    exact globalCutColor_odd s q y
  let U (a : Equiv.Perm (GlobalVertices s q)) (y : Fin q → Bool) := colorCut e (z a y) (hz a y)
  refine ⟨fun a y => A (Sum.inr (U a y)),
    fun M => B (fromPairing (Pairing.transport e (Pairing.sum M MW))),
    fun a y => hA _, fun M => hB _, fun a y => htrA _, fun M => htrB _, ?_⟩
  intro a y M
  rw [hpair, colorCut_slack, tableCoordinate_sum, tableCoordinate_false, add_zero]
  congr 1
  rw [← Pairing.transport_perm, tableCoordinate_transport]
  congr 1
  ext v
  simp

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.global_factors_of_factorization := @_root_.OAI.PerfectMatchingPSD.global_factors_of_factorization
