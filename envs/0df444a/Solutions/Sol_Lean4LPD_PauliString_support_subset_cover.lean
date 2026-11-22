-- Prove2me | solution 1 for Lean4LPD.PauliString.support_subset_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:23.995041+00:00
-- url     : https://prove2.me/submissions/bd7517ac-7627-4d41-806a-a65ee57c9ef8

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Theorems.Thm_Lean4LPD_PauliString_support_mul_subset
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_inter_support_nonempty_of_sympForm
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_cover_subset_cons
public import Theorems.Thm_Lean4LPD_PauliString_cover_subset_cover_cons
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
theorem _root_.solution : ∀ {L : List (PauliString n)},
    (L.Pairwise fun G H => Disjoint (support G) (support H)) →
    ∀ {p q : PauliString n}, q ∈ oneLayer L p → support q ⊆ cover L (support p) := by
  intro L
  induction L with
  | nil =>
    intro _ p q hq
    rw [oneLayer_nil, Finset.mem_singleton] at hq
    subst hq
    simp
  | cons G Gs ih =>
    intro hpw p q hq
    rw [List.pairwise_cons] at hpw
    rw [oneLayer_cons, Finset.mem_biUnion] at hq
    obtain ⟨p', hp', hq'⟩ := hq
    have hsub := ih hpw.2 hq'
    have hcase : p' = p ∨ (sympForm G p = 1 ∧ p' = phaseMul 1 (G * p)) := by
      rw [branch] at hp'
      split at hp'
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
        rcases hp' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨by assumption, rfl⟩
      · rw [Finset.mem_singleton] at hp'
        exact Or.inl hp'
    rcases hcase with rfl | ⟨hanti, rfl⟩
    · exact hsub.trans (cover_subset_cons G Gs _)
    · refine hsub.trans (cover_subset_cover_cons hpw.1 ?_ ?_)
      · exact inter_support_nonempty_of_sympForm hanti
      · rw [support_phaseMul]
        exact (support_mul_subset G p).trans (by rw [Finset.union_comm])
end Lean4LPD.PauliString
