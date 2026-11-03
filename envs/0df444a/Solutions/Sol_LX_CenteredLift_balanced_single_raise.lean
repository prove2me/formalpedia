-- Prove2me | solution 1 for LX.CenteredLift.balanced_single_raise
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T19:47:08.08522+00:00
-- url     : https://prove2.me/submissions/453a542c-e028-4892-814a-a3bd14021114

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u



theorem ite_eq_right {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : ¬ p) :
    (if p then a else b) = b := if_neg h

end LX

namespace List
universe u

end List

/-
The following proof is adapted from Mathlib, copyright (c) 2026 Seewoo Lee,
licensed under Apache 2.0. Source revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Order/Floor/BigOperators.lean, lines 28-45.
-/
namespace Int
open scoped BigOperators


end Int

end

section
/-!
The L/R/X Cayley graph on `Equiv.Perm (Fin n)`. Right multiplication acts
on positions: `L` rotates the list to the left, `R` to the right, and `X`
exchanges its first two entries. The extended diameter avoids the convention
that a disconnected graph has natural-valued diameter zero.
-/
namespace LX.Core



















@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_cons {n : ℕ} [NeZero n] (a : Letter) (w : List Letter) :
    eval (n := n) (a :: w) = a.eval * eval w := by simp [eval]

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by simp [eval]






end LX.Core

end

section
/-! Signed affine crossing data obtained from an actual balanced phase lift.
The row-sum identity is proved from bijectivity of endpoint residues. -/
namespace LX.Core.AffineLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cast_eq_of_modEq {a b : ℤ} (h : Int.ModEq (n : ℤ) a b) :
    (a : Fin n) = (b : Fin n) := by
  apply Fin.ext
  rw [Fin.val_intCast, Fin.val_intCast]
  exact congrArg Int.toNat h




















@[simp] theorem crossing_self (d : Fin n → ℤ) (i : Fin n) : crossing d i i = 0 := by
  simp [crossing, crossingNumerator]









end LX.Core.AffineLift

end

section
/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LX.Core.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift



variable {n : ℕ} [NeZero n]















@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]


end LX.Core.PhysicalModel

end

section
/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing



variable {n : ℕ} [NeZero n]
































theorem cast_eq_iff_modEq (a b : ℤ) :
    (a : Fin n) = (b : Fin n) ↔ Int.ModEq (n : ℤ) a b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_intCast] at hh
    have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hn0),
      Int.toNat_of_nonneg (Int.emod_nonneg b hn0)] at hi
    exact hi
  · exact AffineLift.cast_eq_of_modEq




end LX.Core.LiftedModel

end

namespace LX.CenteredLift
end LX.CenteredLift
open LX
open LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A balanced lift above the lower edge differs from a strip
representative of mass at least -n in at most one raised coordinate. -/
theorem solution (m : ℕ) (d e : Fin n → ℤ)
    (hd : ∑ i,d i=0) (hlo : ∀ i,-(m : ℤ) ≤ d i)
    (he : ∀ i,-(m : ℤ) ≤ e i ∧ e i < (n : ℤ)-m)
    (hres : ∀ i,(d i : Fin n)=(e i : Fin n))
    (hs : -(n : ℤ) ≤ ∑ i,e i) : d=e ∨ ∃ a,d=raiseAt e a := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  let δ : Fin n → ℤ := fun i => d i-e i
  have hgap (i : Fin n) : δ i=0 ∨ (n : ℤ) ≤ δ i := by
    have hmod := (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp (hres i).symm
    obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hmod
    change δ i=(n : ℤ)*k at hk
    have hδ : -(n : ℤ) < δ i := by have := hlo i; have := he i; dsimp [δ]; omega
    have hk0 : 0 ≤ k := by
      by_contra hnot
      have hm := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (le_of_lt hn)
      nlinarith
    by_cases hkz : k=0
    · left; simp [hk,hkz]
    · right
      have hm := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) (le_of_lt hn)
      nlinarith
  have hnonneg (i : Fin n) : 0 ≤ δ i := by have := hgap i; omega
  have htotal : (∑ i,δ i) ≤ (n : ℤ) := by
    simp only [δ,Finset.sum_sub_distrib,hd]
    omega
  by_cases hz : ∀ i,δ i=0
  · left; funext i; have := hz i; dsimp [δ] at this; omega
  · obtain ⟨a,ha⟩ := not_forall.mp hz
    have hamin := (hgap a).resolve_left ha
    have hale := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hnonneg i)
      (Finset.mem_univ a)
    have hea : δ a=n := by omega
    have herase := Finset.sum_erase_add (s := Finset.univ) (f := δ) (Finset.mem_univ a)
    have hrest : (∑ i ∈ Finset.univ.erase a,δ i) ≤ 0 := by omega
    right
    refine ⟨a,?_⟩
    funext i
    by_cases hi : i=a
    · subst i; simp only [raiseAt,ite_true]; dsimp [δ] at hea; omega
    · have hile := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ.erase a) => hnonneg j)
        (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
      simp only [raiseAt,ite_eq_right hi,Nat.cast_zero,add_zero]
      have hzi : δ i=0 := by have := hnonneg i; omega
      dsimp only [δ] at hzi
      omega
