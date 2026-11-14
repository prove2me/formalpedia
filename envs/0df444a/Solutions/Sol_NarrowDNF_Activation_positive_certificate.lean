-- Prove2me | solution 1 for NarrowDNF.Activation.positive_certificate
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:02:35.501631+00:00
-- url     : https://prove2.me/submissions/bccf81cc-770a-4e4f-8a71-21a6587392da

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
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



omit [DecidableEq ι] in
private theorem zeroOutside_le (J : Activation ι) (x : Cube ι) : J.zeroOutside x ≤ x := by
  classical
  intro i
  simp only [zeroOutside]
  split <;> simp_all

omit [DecidableEq ι] in
private theorem zeroOutside_sameAtom {J : Activation ι} (hJ : J.Increasing) (x : Cube ι) :
    J.SameAtom x (J.zeroOutside x) := by
  classical
  have hf : ∀ S, J.fires S x ↔ J.fires S (J.zeroOutside x) := by
    intro S
    constructor
    · intro hS
      apply (J.locality S x (J.zeroOutside x) ?_).mp hS
      intro i hi
      simp [zeroOutside, mem_active_of_fires hS hi]
    · exact hJ S (J.zeroOutside_le x)
  constructor
  · ext i
    simp only [active, Set.mem_setOf_eq]
    exact exists_congr fun S => and_congr_right fun _ => hf S
  · intro i hi
    simp [zeroOutside, hi]



end Activation
end NarrowDNF


end

open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι] in
/-- The exact positive certificate in Lemma 4.1: the positive labels in the
active union force acceptance at every larger extension. -/
theorem solution {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : ∀ i ∈ J.active x, x i = true → y i = true) : u y = true := by
  classical
  have hzero : u (J.zeroOutside x) = true :=
    (hm x (J.zeroOutside x) (zeroOutside_sameAtom hJ x)).symm.trans hx
  have hle : J.zeroOutside x ≤ y := by
    intro i
    by_cases hi : i ∈ J.active x
    · by_cases hxi : x i = true
      · simp [zeroOutside, hi, hxi, hy i hi hxi]
      · have hfalse : x i = false := Bool.eq_false_iff.mpr hxi
        simp [zeroOutside, hi, hfalse]
    · simp [zeroOutside, hi]
  have := hu hle
  cases huy : u y
  · rw [hzero, huy] at this
    exact False.elim ((by decide : ¬(true ≤ false)) this)
  · rfl
