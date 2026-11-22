-- Prove2me | solution 1 for Lean4LPD.PauliString.card_cover_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:10:14.226973+00:00
-- url     : https://prove2.me/submissions/9b9b3d8b-5107-4542-98f2-1bb3d1e214b0

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_IsLayer_disjoint_of_mem
public import Theorems.Thm_Lean4LPD_PauliString_mem_hitting
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul


attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.cover_nil

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}
namespace Lean4LPD.PauliString
theorem _root_.solution (hL : IsLayer kh L) (hkh : 1 ≤ kh) (S : Finset (Fin n)) :
    (cover L S).card ≤ kh * S.card := by
  set U := (hitting L S).biUnion support with hUdef
  have hdisj : ∀ x ∈ hitting L S, ∀ y ∈ hitting L S, x ≠ y →
      Disjoint (support x ∩ S) (support y ∩ S) := by
    intro x hx y hy hxy
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (hL.disjoint_of_mem (mem_hitting.1 hx).1 (mem_hitting.1 hy).1 hxy))
  -- each firing generator consumes at least one site of `S ∩ U`
  have hcount : (hitting L S).card ≤ (S ∩ U).card := by
    have hcard : ((hitting L S).biUnion fun G => support G ∩ S).card
        = ∑ G ∈ hitting L S, (support G ∩ S).card :=
      Finset.card_biUnion hdisj
    have hsub : ((hitting L S).biUnion fun G => support G ∩ S) ⊆ S ∩ U := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨G, hG, hiG⟩ := hi
      rw [Finset.mem_inter] at hiG
      exact Finset.mem_inter.2 ⟨hiG.2, Finset.subset_biUnion_of_mem support hG hiG.1⟩
    calc (hitting L S).card
        = ∑ _G ∈ hitting L S, 1 := by simp
      _ ≤ ∑ G ∈ hitting L S, (support G ∩ S).card :=
          Finset.sum_le_sum fun G hG => Finset.card_pos.2 (mem_hitting.1 hG).2
      _ = ((hitting L S).biUnion fun G => support G ∩ S).card := hcard.symm
      _ ≤ (S ∩ U).card := Finset.card_le_card hsub
  have hUcard : U.card ≤ (hitting L S).card * kh :=
    Finset.card_biUnion_le_card_mul _ _ _ fun G hG => hL.weight_le G (mem_hitting.1 hG).1
  have hsplit : (S \ U).card + (S ∩ U).card = S.card := Finset.card_sdiff_add_card_inter S U
  calc (cover L S).card
      = ((S \ U) ∪ U).card := by rw [cover, ← hUdef, Finset.sdiff_union_self_eq_union]
    _ ≤ (S \ U).card + U.card := Finset.card_union_le _ _
    _ ≤ (S \ U).card + (hitting L S).card * kh := by omega
    _ ≤ (S \ U).card + (S ∩ U).card * kh := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right kh hcount) _
    _ ≤ (S \ U).card * kh + (S ∩ U).card * kh :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hkh) _
    _ = ((S \ U).card + (S ∩ U).card) * kh := by ring
    _ = kh * S.card := by rw [hsplit]; ring
end Lean4LPD.PauliString
