-- Prove2me | solution 1 for LeanPool.Vizing.no_three_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:47.13456+00:00
-- url     : https://prove2.me/submissions/227df503-ebdc-4ea8-a45e-ad06d385f5f9

module
public import Definitions.Def_LeanPool_Vizing_Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Definitions.Def_LeanPool_Vizing_Endpoints
public import Theorems.Thm_LeanPool_Vizing_degree_toSimpleGraph_le
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open LeanPool LeanPool.Vizing
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]
namespace LeanPool.Vizing
theorem _root_.solution {H : SimpleGraph V} [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z ≤ 2) {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : H.degree u ≤ 1) (hv : H.degree v ≤ 1) (hw : H.degree w ≤ 1)
    (h1 : H.Reachable u v) (h2 : H.Reachable u w) : False := by
  classical
  set Cp := H.connectedComponentMk u with hCp
  have humem : u ∈ Cp := rfl
  have hvmem : v ∈ Cp := (ConnectedComponent.sound h1.symm : _)
  have hwmem : w ∈ Cp := (ConnectedComponent.sound h2.symm : _)
  set K := Cp.toSimpleGraph with hK
  have hKconn : K.Connected := Cp.connected_toSimpleGraph
  set u' : ↥Cp := ⟨u, humem⟩ with hu'
  set v' : ↥Cp := ⟨v, hvmem⟩ with hv'
  set w' : ↥Cp := ⟨w, hwmem⟩ with hw'
  have hdegK : ∀ z : ↥Cp, K.degree z ≤ H.degree z.1 := fun z => degree_toSimpleGraph_le Cp z
  set N := Fintype.card ↥Cp with hN
  set T : Finset ↥Cp := {u', v', w'} with hT
  have hTcard : T.card = 3 := by
    rw [hT, Finset.card_insert_of_notMem (by simp [hu', hv', hw', Subtype.ext_iff, huv, huw]),
      Finset.card_insert_of_notMem (by simp [hv', hw', Subtype.ext_iff, hvw]),
      Finset.card_singleton]
  have hN3 : 3 ≤ N := by
    rw [hN, ← Finset.card_univ, ← hTcard]
    exact Finset.card_le_card (Finset.subset_univ T)
  have hsum : ∑ z : ↥Cp, K.degree z ≤ 2 * N - 3 := by
    have hsplit : ∑ z ∈ T, K.degree z + ∑ z ∈ (Finset.univ \ T), K.degree z
        = ∑ z : ↥Cp, K.degree z := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.subset_univ T)
    have hT' : ∑ z ∈ T, K.degree z ≤ 3 := by
      calc ∑ z ∈ T, K.degree z ≤ ∑ _z ∈ T, 1 := by
            refine Finset.sum_le_sum ?_
            intro z hz
            rw [hT] at hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl
            · exact le_trans (hdegK _) hu
            · exact le_trans (hdegK _) hv
            · exact le_trans (hdegK _) hw
        _ = 3 := by simp [hTcard]
    have hR : ∑ z ∈ (Finset.univ \ T), K.degree z ≤ 2 * (N - 3) := by
      calc ∑ z ∈ (Finset.univ \ T), K.degree z ≤ ∑ _z ∈ (Finset.univ \ T), 2 :=
            Finset.sum_le_sum fun z _ => le_trans (hdegK z) (hdeg z.1)
        _ = 2 * (N - 3) := by
            rw [Finset.sum_const, Finset.card_univ_sdiff, smul_eq_mul, hTcard, mul_comm, ← hN]
    omega
  have hhand : ∑ z : ↥Cp, K.degree z = 2 * #K.edgeFinset :=
    K.sum_degrees_eq_twice_card_edges
  have hedges : N ≤ #K.edgeFinset + 1 := by
    have hc := hKconn.card_vert_le_card_edgeSet_add_one
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← hN,
      ← Set.toFinset_card, ← edgeFinset] at hc
  omega
end LeanPool.Vizing
