-- Prove2me | solution 1 for GridHam.unitStepChain_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:16:26.761881+00:00
-- url     : https://prove2.me/submissions/21f72184-3fcb-4fa6-b2c7-99db8cd70054

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution :
    ∀ (q : List ℕ), unitStepChain q = true →
      ∀ x y, x ∈ q → y ∈ q →
        ∀ z, (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x) → z ∈ q := by
  intro q
  induction q with
  | nil => intro _ x y hx; simp at hx
  | cons a l ih =>
    intro hchain x y hx hy z hz
    cases l with
    | nil =>
      have hxa : x = a := by simpa using hx
      have hya : y = a := by simpa using hy
      rw [hxa, hya] at hz
      have hza : z = a := by rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      simp [hza]
    | cons b rest =>
      have hc' : (unitStepB a b && unitStepChain (b :: rest)) = true := by
        simpa [unitStepChain] using hchain
      simp at hc'
      obtain ⟨hstepB, hchainRest⟩ := hc'
      have hstep : a + 1 = b ∨ b + 1 = a := by
        unfold unitStepB at hstepB
        by_contra hcon
        simp [hcon] at hstepB
      -- Key sub-fact: for any w in the tail and z' between a and w, z' is in
      -- the whole list (a :: b :: rest).
      have key : ∀ w, w ∈ (b :: rest) →
          ∀ z', (a ≤ z' ∧ z' ≤ w) ∨ (w ≤ z' ∧ z' ≤ a) → z' ∈ (a :: b :: rest) := by
        intro w hw z' hz'
        have hbmem : b ∈ (b :: rest) := by simp
        by_cases hzb : (b ≤ z' ∧ z' ≤ w) ∨ (w ≤ z' ∧ z' ≤ b)
        · exact List.mem_cons.mpr (Or.inr (ih hchainRest b w hbmem hw z' hzb))
        · have hz'eq : z' = a := by
            rcases hstep with hab | hab <;> rcases hz' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          simp [hz'eq]
      rcases List.mem_cons.mp hx with hxa | hxr
      · rw [hxa] at hz
        rcases List.mem_cons.mp hy with hya | hyr
        · rw [hya] at hz
          have hza : z = a := by rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          simp [hza]
        · exact key y hyr z hz
      · rcases List.mem_cons.mp hy with hya | hyr
        · rw [hya] at hz
          have hz' : (a ≤ z ∧ z ≤ x) ∨ (x ≤ z ∧ z ≤ a) := by
            rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl ⟨h1, h2⟩
          exact key x hxr z hz'
        · exact List.mem_cons.mpr (Or.inr (ih hchainRest x y hxr hyr z hz))
end GridHam
