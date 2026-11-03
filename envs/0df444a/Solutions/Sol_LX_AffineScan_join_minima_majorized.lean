-- Prove2me | solution 1 for LX.AffineScan.join_minima_majorized
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:33:40.173876+00:00
-- url     : https://prove2.me/submissions/1eb49c83-c63c-4340-900d-57df2ac1bd02

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
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_Graph
import Definitions.Def_LX_JoinMinimumPair
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.AffineScan
end LX.AffineScan
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

section
/-! Compatibility aliases for core if-then-else lemmas renamed after Lean 4.33.1.
The source proof bodies use the newer names; these aliases preserve their types.
-/
namespace LX
universe u

theorem ite_eq_left {α : Sort u} {p : Prop} {inst : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h

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
namespace LX.Core



@[simp] theorem Letter.eval_inverse {n : ℕ} [NeZero n] (c : Letter) :
    c.inverse.eval (n := n) = (c.eval)⁻¹ := by
  cases c <;> simp [inverse, Letter.eval, L, R, X]








end LX.Core

end

section
/-! Directed LX words. No inverse generator is included in the alphabet.
The target bound is a proposition, not an axiom or an assumed estimate. -/
namespace LX









@[simp] theorem eval_nil {n : ℕ} [NeZero n] : eval (n := n) [] = 1 := rfl

@[simp] theorem eval_append {n : ℕ} [NeZero n] (u v : List Letter) :
    eval (n := n) (u ++ v) = eval u * eval v := by
  simp [eval]





























end LX

end

section
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]



theorem join_minima_balance (d : Fin n → ℤ) (u v : Fin n) (hb : ∑ i,d i=0) :
    ∑ i,joinMinima d u v i=0 := by
  simp [joinMinima,Finset.sum_add_distrib,Finset.sum_sub_distrib,hb]

theorem join_minima_subset_sum (d : Fin n → ℤ) (u v : Fin n) (S : Finset (Fin n)) :
    (∑ i ∈ S,joinMinima d u v i)=(∑ i ∈ S,d i)-(S.card : ℤ)+
      (if u ∈ S then 1 else 0)+(if v ∈ S then (n : ℤ)-1 else 0) := by
  simp [joinMinima,Finset.sum_add_distrib,Finset.sum_sub_distrib]










end LX.AffineScan

end

namespace LX.AffineScan
end LX.AffineScan
open LX
open LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Full majorization is preserved. The potentially increasing subsets are
paid by deleting the one or two known minimum coordinates before applying the
original subset inequality. -/
theorem solution (d : Fin n → ℤ) (u v : Fin n) (hne : u ≠ v)
    (hb : ∑ i,d i=0) (hm : Majorized d) (h : ℕ) (hn : n=2*h+3)
    (hu : d u= -(h : ℤ)) (hv : d v= -(h : ℤ)) :
    Majorized (joinMinima d u v) := by
  intro S
  have hs := join_minima_subset_sum d u v S
  have hn' : (n : ℤ)=2*(h : ℤ)+3 := by exact_mod_cast hn
  have hk0 : (0 : ℤ) ≤ S.card := Nat.cast_nonneg _
  by_cases hvs : v ∈ S
  · by_cases hus : u ∈ S
    · by_cases hfull : S=Finset.univ
      · subst S
        rw [join_minima_balance d u v hb]
        simp
      · have hue : u ∈ S.erase v := Finset.mem_erase.mpr ⟨hne,hus⟩
        have he1 := Finset.sum_erase_add S d hvs
        have he2 := Finset.sum_erase_add (S.erase v) d hue
        rw [hu] at he2
        rw [hv] at he1
        have hk2 : 2 ≤ S.card := by
          have hc := Finset.card_pos.mpr (show (S.erase v).Nonempty from ⟨u,hue⟩)
          rw [Finset.card_erase_of_mem hvs] at hc
          omega
        have hcard : ((S.erase v).erase u).card=S.card-2 := by
          rw [Finset.card_erase_of_mem hue,Finset.card_erase_of_mem hvs]
          omega
        have hm' := hm ((S.erase v).erase u)
        rw [hcard,Nat.cast_sub hk2] at hm'
        norm_num only [Nat.cast_ofNat] at hm'
        have hkn : S.card < n := by
          have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S,hfull⟩)
          simpa using hc
        have hkn' : (S.card : ℤ) ≤ (n : ℤ)-1 := by omega
        rw [hs,ite_eq_left hus,ite_eq_left hvs]
        nlinarith
    · have he := Finset.sum_erase_add S d hvs
      rw [hv] at he
      have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨v,hvs⟩
      have hm' := hm (S.erase v)
      rw [Finset.card_erase_of_mem hvs,Nat.cast_sub hk] at hm'
      norm_num only [Nat.cast_ofNat] at hm'
      rw [hs,ite_eq_right hus,ite_eq_left hvs]
      nlinarith
  · have hm' := hm S
    rw [hs,ite_eq_right hvs]
    by_cases hus : u ∈ S
    · rw [ite_eq_left hus]
      have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨u,hus⟩
      nlinarith
    · rw [ite_eq_right hus]
      nlinarith
