-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.nontrivial_positive_composition_cut_code
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:10:58.868007+00:00
-- url     : https://prove2.me/submissions/8388ad65-10a7-4ff4-82f3-09f6b9486f08

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fin.Embedding

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) (hq : 0 < q) (hk : 0 < k) (hqne : q ≠ 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  -- Realize a positive tuple as Mathlib's list-based composition.
  let toComposition : {a // a ∈ logMajorantCompositions q k} → Composition k :=
    fun a =>
      { blocks := List.ofFn a.val
        blocks_pos := by
          intro i hi
          obtain ⟨j, hj⟩ := (List.mem_ofFn' a.val i).mp hi
          rw [← hj]
          exact (Finset.mem_filter.mp a.property).2.1 j
        blocks_sum := by
          rw [List.sum_ofFn]
          exact (Finset.mem_filter.mp a.property).2.2 }
  have hcomp : Function.Injective toComposition := by
    intro a b hab
    apply Subtype.ext
    apply List.ofFn_injective
    exact congrArg Composition.blocks hab
  -- The standard cut equivalence records the proper boundaries minus one.
  let cuts : Composition k ≃ Finset (Fin (k - 1)) :=
    (compositionEquiv k).trans (compositionAsSetEquiv k)
  let inclusion : Fin (k - 1) ↪ Fin k := Fin.castLEEmb (Nat.sub_le k 1)
  refine ⟨fun a => (cuts (toComposition a)).map inclusion, ?_⟩
  intro a b hab
  apply hcomp
  apply cuts.injective
  exact (Finset.map_injective inclusion) hab
