-- Prove2me | solution 1 for NarrowDNF.Activation.sameAtom_of_active_subset_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:28.083219+00:00
-- url     : https://prove2.me/submissions/c5b81b94-7a65-4981-9587-b455b5ce6c9b

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

section


/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF





namespace Activation
variable {ι : Type*} [DecidableEq ι]











omit [DecidableEq ι] in
private theorem mem_active_of_fires {J : Activation ι} {S : Finset ι} {x : Cube ι}
    (h : J.fires S x) {i : ι} (hi : i ∈ S) : i ∈ J.active x := ⟨S, hi, h⟩









end Activation
end NarrowDNF


end

open NarrowDNF
variable {ι : Type*} [DecidableEq ι]
open NarrowDNF
open NarrowDNF.Activation
omit [DecidableEq ι] in
/-- Locality reconstructs a complete atom from labels on any common superset
of both active unions. This is the elementary recovery fact used below. -/
theorem solution {J : Activation ι} {x y : Cube ι}
    {B : Set ι} (hx : J.active x ⊆ B) (hy : J.active y ⊆ B)
    (hxy : ∀ i ∈ B, x i = y i) : J.SameAtom x y := by
  have forward : ∀ S, J.fires S x → J.fires S y := by
    intro S hS
    apply (J.locality S x y ?_).mp hS
    intro i hi
    exact hxy i (hx (mem_active_of_fires hS hi))
  have backward : ∀ S, J.fires S y → J.fires S x := by
    intro S hS
    apply (J.locality S y x ?_).mp hS
    intro i hi
    exact (hxy i (hy (mem_active_of_fires hS hi))).symm
  constructor
  · ext i
    constructor
    · rintro ⟨S, hi, hS⟩
      exact ⟨S, hi, forward S hS⟩
    · rintro ⟨S, hi, hS⟩
      exact ⟨S, hi, backward S hS⟩
  · intro i hi
    exact hxy i (hx hi)
