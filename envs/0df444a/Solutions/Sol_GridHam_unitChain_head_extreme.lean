-- Prove2me | solution 1 for GridHam.unitChain_head_extreme
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:35.153717+00:00
-- url     : https://prove2.me/submissions/ae1ada01-bb4e-4533-a57f-fa6fb60bea26

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
public import Theorems.Thm_GridHam_unitStepChain_intermediate

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (a : ℕ) (rest : List ℕ) (k : ℕ)
    (hnd : (a :: rest).Nodup) (hch : unitStepChain (a :: rest) = true)
    (hcov : ∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) :
    a = k ∨ a = k + rest.length := by
  have ha := (hcov a).mp (by simp)
  by_cases h1 : a = k
  · exact Or.inl h1
  by_cases h2 : a = k + rest.length
  · exact Or.inr h2
  exfalso
  cases rest with
  | nil =>
    have hl : ([] : List ℕ).length = 0 := rfl
    omega
  | cons b rest' =>
    have hc' : (unitStepB a b && unitStepChain (b :: rest')) = true := by
      simpa [unitStepChain] using hch
    simp at hc'
    obtain ⟨_, hcl⟩ := hc'
    obtain ⟨hanot, _⟩ := List.nodup_cons.mp hnd
    have hlo : a - 1 ∈ b :: rest' := by
      have hm := (hcov (a - 1)).mpr ⟨by omega, by omega⟩
      rcases List.mem_cons.mp hm with h | h
      · exfalso; omega
      · exact h
    have hhi : a + 1 ∈ b :: rest' := by
      have hm := (hcov (a + 1)).mpr ⟨by omega, by omega⟩
      rcases List.mem_cons.mp hm with h | h
      · exfalso; omega
      · exact h
    exact hanot (unitStepChain_intermediate (b :: rest') hcl (a - 1) (a + 1) hlo hhi a
      (Or.inl ⟨by omega, by omega⟩))
end GridHam
