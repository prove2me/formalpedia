-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.strongPower_cohomomorphism_of_cohomomorphism
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:21.427399+00:00
-- url     : https://prove2.me/submissions/ddeba6bd-dd61-4ad8-8de7-2f285e56efdd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Clique
import Definitions.Def_GroupTheoreticShannonCapacity_Defs
import Definitions.Def_GroupTheoreticShannonCapacity_Basic

set_option autoImplicit true
open GroupTheoreticShannonCapacity
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hf : ∀ u v, u ≠ v → ¬G.Adj u v → f u ≠ f v ∧ ¬H.Adj (f u) (f v))
    (n : ℕ) :
    let fn := fun x : Fin n → V => fun i => f (x i)
    ∀ x y, x ≠ y → ¬(strongPower G n).Adj x y →
      fn x ≠ fn y ∧ ¬(strongPower H n).Adj (fn x) (fn y) := by
  intro fn x y hxy hnadj
  -- x ≠ y and not adjacent in G^⊠n means there exists i such that x i ≠ y i and ¬G.Adj (x i) (y i)
  simp only [strongPower] at hnadj ⊢
  -- Not adjacent means: ¬(x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i))
  have hnadj' : ∃ i, x i ≠ y i ∧ ¬G.Adj (x i) (y i) := by
    by_contra h
    push_neg at h
    -- h : ∀ i, x i ≠ y i → G.Adj (x i) (y i)
    apply hnadj
    constructor
    · exact hxy
    · intro i
      by_cases heq : x i = y i
      · left; exact heq
      · right; exact h i heq
  obtain ⟨i, hne_i, hnadj_i⟩ := hnadj'
  have hf_i := hf (x i) (y i) hne_i hnadj_i
  constructor
  · -- fn x ≠ fn y
    intro heq
    have : f (x i) = f (y i) := congrFun heq i
    exact hf_i.1 this
  · -- ¬(strongPower H n).Adj (fn x) (fn y)
    intro ⟨hfne, hadj⟩
    have hi := hadj i
    cases hi with
    | inl heq => exact hf_i.1 heq
    | inr hadj_i => exact hf_i.2 hadj_i
end GroupTheoreticShannonCapacity
