-- Prove2me | solution 1 for GridHam.unitChain_last_of_head_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:17:05.58879+00:00
-- url     : https://prove2.me/submissions/da44136f-3d8d-42d5-ad77-719ff76fd556

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution :
    ∀ (rest : List ℕ) (a k : ℕ), (a :: rest).Nodup → unitStepChain (a :: rest) = true →
      (∀ y, y ∈ a :: rest ↔ k ≤ y ∧ y ≤ k + rest.length) → a = k + rest.length →
      (a :: rest).getLast? = some k := by
  intro rest
  induction rest with
  | nil =>
    intro a k _ _ _ hak
    rw [hak]
    rfl
  | cons b rest' ih =>
    intro a k hnd hch hcov hak
    have hc' : (unitStepB a b && unitStepChain (b :: rest')) = true := by
      simpa [unitStepChain] using hch
    simp at hc'
    obtain ⟨hstepB, hcl⟩ := hc'
    have hstep : a + 1 = b ∨ b + 1 = a := by
      unfold unitStepB at hstepB
      by_contra hcon
      simp [hcon] at hstepB
    obtain ⟨hanot, hndt⟩ := List.nodup_cons.mp hnd
    have hl : (b :: rest').length = rest'.length + 1 := rfl
    have hbr := (hcov b).mp (by simp)
    have hbk : b = k + rest'.length := by rcases hstep with h | h <;> omega
    have hcov' : ∀ y, y ∈ b :: rest' ↔ k ≤ y ∧ y ≤ k + rest'.length := by
      intro y
      constructor
      · intro hy
        have h1 := (hcov y).mp (List.mem_cons.mpr (Or.inr hy))
        have h2 : y ≠ a := by
          intro hya
          rw [hya] at hy
          exact hanot hy
        exact ⟨by omega, by omega⟩
      · intro hy
        have h1 := (hcov y).mpr ⟨by omega, by omega⟩
        rcases List.mem_cons.mp h1 with h | h
        · exfalso; omega
        · exact h
    have hgl : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
    rw [hgl, ih b k hndt hcl hcov' hbk]
end GridHam
