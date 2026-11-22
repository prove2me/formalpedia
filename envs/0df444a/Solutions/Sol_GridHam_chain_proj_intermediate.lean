-- Prove2me | solution 1 for GridHam.chain_proj_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:09:14.455904+00:00
-- url     : https://prove2.me/submissions/d6f6c837-5159-45a7-aeff-0141f985082a

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
public import Definitions.Def_GridHam_Necessity

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution (f : Coord → ℕ)
    (hf : ∀ a b, Adjacent a b → f a ≤ f b + 1 ∧ f b ≤ f a + 1) :
    ∀ (l : List Coord), chainAdjacent l = true →
      ∀ a ∈ l, ∀ b ∈ l, ∀ z, f a ≤ z → z ≤ f b → ∃ c ∈ l, f c = z := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x rest ih =>
    intro hch a ha b hb z hz1 hz2
    cases rest with
    | nil =>
      have hax : a = x := by simpa using ha
      have hbx : b = x := by simpa using hb
      rw [hax] at hz1
      rw [hbx] at hz2
      exact ⟨x, by simp, by omega⟩
    | cons y rest' =>
      have hc' : (adjacentB x y && chainAdjacent (y :: rest')) = true := by
        simpa [chainAdjacent] using hch
      simp at hc'
      obtain ⟨hxy, hcl⟩ := hc'
      have hadj : Adjacent x y := by
        unfold adjacentB at hxy
        by_contra hcon
        simp [hcon] at hxy
      have hstep := hf x y hadj
      have lift : ∀ c, c ∈ y :: rest' → c ∈ x :: y :: rest' :=
        fun c hc => List.mem_cons.mpr (Or.inr hc)
      have hymem : y ∈ y :: rest' := by simp
      have key : ∀ w ∈ y :: rest', ∀ z',
          ((f x ≤ z' ∧ z' ≤ f w) ∨ (f w ≤ z' ∧ z' ≤ f x)) →
          ∃ c ∈ x :: y :: rest', f c = z' := by
        intro w hw z' hz'
        by_cases h1 : f y ≤ z' ∧ z' ≤ f w
        · obtain ⟨c, hc, hfc⟩ := ih hcl y hymem w hw z' h1.1 h1.2
          exact ⟨c, lift c hc, hfc⟩
        · by_cases h2 : f w ≤ z' ∧ z' ≤ f y
          · obtain ⟨c, hc, hfc⟩ := ih hcl w hw y hymem z' h2.1 h2.2
            exact ⟨c, lift c hc, hfc⟩
          · exact ⟨x, by simp, by omega⟩
      rcases List.mem_cons.mp ha with hax | har
      · rcases List.mem_cons.mp hb with hbx | hbr
        · rw [hax] at hz1
          rw [hbx] at hz2
          exact ⟨x, by simp, by omega⟩
        · rw [hax] at hz1
          exact key b hbr z (Or.inl ⟨hz1, hz2⟩)
      · rcases List.mem_cons.mp hb with hbx | hbr
        · rw [hbx] at hz2
          exact key a har z (Or.inr ⟨hz1, hz2⟩)
        · obtain ⟨c, hc, hfc⟩ := ih hcl a har b hbr z hz1 hz2
          exact ⟨c, lift c hc, hfc⟩
end GridHam
