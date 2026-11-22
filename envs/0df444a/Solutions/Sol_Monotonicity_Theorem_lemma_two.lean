-- Prove2me | solution 1 for Monotonicity_Theorem.lemma_two
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:47:47.890825+00:00
-- url     : https://prove2.me/submissions/33276da5-a235-4fe6-a9ed-6e6025fa0f13

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
import Theorems.Thm_Monotonicity_Theorem_uniform_pattern_window3
import Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_above_above2
import Theorems.Thm_Monotonicity_Theorem_decreasing_of_uniform_above_below2
import Theorems.Thm_Monotonicity_Theorem_increasing_of_uniform_below_above2
import Theorems.Thm_Monotonicity_Theorem_decreasing_of_uniform_below_below2
open Monotonicity_Theorem

theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (hI : Set.Infinite I)
    (hinj : ∀ x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (∀ x, openInterval a b x → I x) ∧
      ((∀ x (hxI : I x) y (hyI : I y), openInterval a b x → openInterval a b y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∨
       (∀ x (hxI : I x) y (hyI : I y), openInterval a b x → openInterval a b y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) := by
  obtain ⟨a0, b0, hlt0, hsub0⟩ :=
    Monotonicity_Theorem.infinite_definable_set_contains_interval2 M I f.domain_mem hI
  obtain ⟨a, b, hlt, hsub, hpat⟩ :=
    Monotonicity_Theorem.uniform_pattern_window3 M f hinj hsub0 hlt0
  have hsubI : ∀ x, openInterval a b x → I x :=
    fun x hx => hsub0 (hsub x hx)
  cases hpat with
  | inl h =>
    obtain ⟨a2, b2, hlt2, hsub2, hinc⟩ :=
      Monotonicity_Theorem.increasing_of_uniform_above_above2 M f hinj hsubI hlt h
    exact ⟨a2, b2, hlt2, hsub2, Or.inl hinc⟩
  | inr h =>
    cases h with
    | inl h =>
      obtain ⟨a2, b2, hlt2, hsub2, hdec⟩ :=
        Monotonicity_Theorem.decreasing_of_uniform_above_below2 M f hinj hsubI hlt h
      exact ⟨a2, b2, hlt2, hsub2, Or.inr hdec⟩
    | inr h =>
      cases h with
      | inl h =>
        obtain ⟨a2, b2, hlt2, hsub2, hinc⟩ :=
          Monotonicity_Theorem.increasing_of_uniform_below_above2 M f hinj hsubI hlt h
        exact ⟨a2, b2, hlt2, hsub2, Or.inl hinc⟩
      | inr h =>
        obtain ⟨a2, b2, hlt2, hsub2, hdec⟩ :=
          Monotonicity_Theorem.decreasing_of_uniform_below_below2 M f hinj hsubI hlt h
        exact ⟨a2, b2, hlt2, hsub2, Or.inr hdec⟩
