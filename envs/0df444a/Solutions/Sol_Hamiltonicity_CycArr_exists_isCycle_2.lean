-- Prove2me | solution 2 for Hamiltonicity.CycArr.exists_isCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:53:19.688021+00:00
-- url     : https://prove2.me/submissions/d29fd1b6-d25b-4864-80b4-98c59f6f5263

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_support_walkOf
public import Theorems.Thm_Hamiltonicity_edges_walkOf
public import Theorems.Thm_Hamiltonicity_length_walkOf

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (h : CycArr G m f) :
    ∃ c : G.Walk (f 0) (f 0), c.IsCycle ∧ c.length = m := by
  have hm := h.three_le
  have hend : f (m - 1 + 1) = f 0 := by
    rw [show m - 1 + 1 = 0 + m by omega, h.periodic]
  let p := (walkOf G (fun i => f (i + 1)) (fun i => h.adj (i + 1)) (m - 1)).copy rfl hend
  refine ⟨Walk.cons (h.adj 0) p, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    constructor
    · rw [Walk.isPath_def, Walk.support_copy, support_walkOf]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj hij
      simp only [List.mem_range] at hi hj
      rw [h.eq_iff] at hij
      have := Nat.ModEq.add_right_cancel' 1 hij
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    · rw [Walk.edges_copy, edges_walkOf]
      simp only [List.mem_map, List.mem_range, not_exists, not_and]
      intro i hi he
      rw [Sym2.eq_iff] at he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := h.inj _ _ (by omega) (by omega) h1
        omega
      · have := h.inj _ _ (by omega) (by omega) h1
        have h3 : i = 0 := by omega
        subst h3
        have := h.inj _ _ (by omega) (by omega) h2
        omega
  · simp only [Walk.length_cons, p, Walk.length_copy, length_walkOf]
    omega
end Hamiltonicity.CycArr
