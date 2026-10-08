-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:35.239166+00:00
-- url     : https://prove2.me/submissions/b3a2ba73-1b41-47cd-85a1-7f2a033e9d76

import Theorems.Thm_MonotoneCompStatics_QSMChar_lemma_four_point

theorem solution {X : Type*} [Lattice X] (f : X → ℝ) :
    MonotoneCompStatics.Monotonicity.QuasiSupermodularOn f Set.univ ↔
      ∃ g : ℝ → X → X → ℝ, (∀ x₁ x₂, StrictMono (fun r => g r x₁ x₂)) ∧
        ∀ x₁ x₂, Supermodularity.Monotonicity.SupermodularOn (fun x => g (f x) x₁ x₂)
          {x₁, x₂, x₁ ⊔ x₂, x₁ ⊓ x₂} := by
  classical
  constructor
  · intro hf
    have hlocal (x y : X) : ∃ h : ℝ → ℝ, StrictMono h ∧
        Supermodularity.Monotonicity.SupermodularOn (h ∘ f)
          {x, y, x ⊔ y, x ⊓ y} := by
      apply MonotoneCompStatics.QSMChar.lemma_four_point f x y
      intro u _ v _
      exact hf (Set.mem_univ u) (Set.mem_univ v)
    choose h hh hs using hlocal
    refine ⟨fun r x y => h x y r, hh, ?_⟩
    intro x y
    simpa only [Function.comp_def] using hs x y
  · rintro ⟨g, hg, hs⟩
    intro x _ y _
    have hxy := hs x y (x := x) (by simp) (y := y) (by simp)
    constructor
    · intro h
      apply (hg x y).le_iff_le.mp
      have hm := (hg x y).monotone h
      linarith
    · intro h
      apply (hg x y).lt_iff_lt.mp
      have hm := hg x y h
      linarith

#print axioms solution
