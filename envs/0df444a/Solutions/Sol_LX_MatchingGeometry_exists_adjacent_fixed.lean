-- Prove2me | solution 1 for LX.MatchingGeometry.exists_adjacent_fixed
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:38:10.8213+00:00
-- url     : https://prove2.me/submissions/aa7168a0-5213-4e4a-ab92-4756345f6f6d

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
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LinearMatchingGeometry
import Definitions.Def_LX_NestedMatchingGeometry
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric
import Theorems.Thm_LX_Core_FiniteCuts_noncrossing_pair_interior
import Theorems.Thm_LX_MatchingGeometry_no_separated_pairs
import Theorems.Thm_LX_MatchingGeometry_pair_contains_gap_two

namespace LX
end LX
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.MatchingGeometry
end LX.MatchingGeometry

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
namespace LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



variable [NeZero n]

theorem eq_add_of_value_add (i j : Fin n) (k : ℕ) (h : i.val+k=j.val) : i+(k : Fin n)=j := by
  have he := congrArg (fun t : ℕ => (t : Fin n)) h
  simpa only [Nat.cast_add,Fin.cast_val_eq_self] using he








end LX.MatchingGeometry

end

namespace LX.MatchingGeometry
end LX.MatchingGeometry
open LX
open LX.MatchingGeometry
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}
variable [NeZero n]

/-- A noncrossing matching with at least two pairs, no cyclic adjacent pair,
and at most one cyclic gap-two pair must have adjacent fixed positions. -/
theorem solution (q : State n) (hinv : Function.Involutive q)
    (hnc : LX.Core.FiniteCuts.NoncrossingPairs q) (hsize : 4 ≤ q.support.card)
    (hnoadj : ∀ i : Fin n,q i ≠ i+1)
    (hunique : ∀ i j : Fin n,q i=i+2 → q j=j+2 → i=j) :
    ∃ i : Fin n,q i=i ∧ q (i+1)=i+1 := by
  classical
  by_contra hnone
  have hnofix (i : Fin n) (hi : q i=i) : q (i+1) ≠ i+1 := by
    intro hj
    exact hnone ⟨i,hi,hj⟩
  have hnoadj' (i : Fin n) : i.val+1 ≠ (q i).val := by
    intro hh
    exact hnoadj i (eq_add_of_value_add i (q i) 1 hh).symm
  have hnofix' (i j : Fin n) (hij : i.val+1=j.val) (hi : q i=i) : q j ≠ j := by
    have he : i+1=j := eq_add_of_value_add i j 1 hij
    rw [← he]
    exact hnofix i hi
  have hsep := no_separated_pairs q hinv hnc hnoadj hnofix hunique
  let P := q.support
  have hP : P.Nonempty := Finset.card_pos.mp (by change 0 < q.support.card; omega)
  let a := P.min' hP
  let c := P.max' hP
  have haP : a ∈ q.support := Finset.min'_mem P hP
  have hcP : c ∈ q.support := Finset.max'_mem P hP
  have hamin (x : Fin n) (hx : x ∈ q.support) : a.val ≤ x.val := Finset.min'_le P x hx
  have hcmax (x : Fin n) (hx : x ∈ q.support) : x.val ≤ c.val := Finset.le_max' P x hx
  have hna : q a ≠ a := Equiv.Perm.mem_support.mp haP
  have hnc' : q c ≠ c := Equiv.Perm.mem_support.mp hcP
  have hqaP : q a ∈ q.support := Equiv.Perm.apply_mem_support.mpr haP
  have hqcP : q c ∈ q.support := Equiv.Perm.apply_mem_support.mpr hcP
  have hab : a.val < (q a).val := by
    have hh := hamin (q a) hqaP
    have he : (q a).val ≠ a.val := fun he => hna (Fin.ext he)
    omega
  have hpac : q a=c := by
    have hbc := hcmax (q a) hqaP
    by_contra he
    have hbc' : (q a).val < c.val := by
      have hne : (q a).val ≠ c.val := fun hh => he (Fin.ext hh)
      omega
    have hqc : (q c).val < c.val := by
      have hh := hcmax (q c) hqcP
      have hne : (q c).val ≠ c.val := fun hh => hnc' (Fin.ext hh)
      omega
    have hqca : a.val < (q c).val := by
      have hh := hamin (q c) hqcP
      have hne : q c ≠ a := by
        intro h
        have hi := hinv c
        rw [h] at hi
        exact he hi
      have hnev : (q c).val ≠ a.val := fun hh => hne (Fin.ext hh)
      omega
    have hqcb : q c ≠ q a := by intro h; have := q.injective h; subst c; omega
    have hqcbv : (q c).val ≠ (q a).val := fun hh => hqcb (Fin.ext hh)
    by_cases hlt : (q a).val < (q c).val
    · exact hsep a (q a) (q c) c hab hlt hqc rfl (hinv c)
    · exact hnc a (q c) (q a) c hqca (by omega) hbc' rfl (hinv c)
  have hpca : q c=a := by rw [← hpac]; exact hinv a
  have hac : a.val < c.val := by rwa [hpac] at hab
  have hbefore (x : Fin n) (hx : x.val < a.val) : q x=x := by
    by_contra hh
    have hb := hamin x (Equiv.Perm.mem_support.mpr hh)
    omega
  have hafter (x : Fin n) (hx : c.val < x.val) : q x=x := by
    by_contra hh
    have hb := hcmax x (Equiv.Perm.mem_support.mpr hh)
    omega
  have hn4 : 4 ≤ n := by
    have hh := q.support.card_le_univ
    simp only [Fintype.card_fin] at hh
    omega
  have hzero : (0 : Fin n).val=0 := rfl
  have hone : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have ha1 : a.val ≤ 1 := by
    by_contra hh
    have h0 := hbefore 0 (by omega)
    have h1 := hbefore 1 (by omega)
    exact hnofix 0 h0 (by simpa using h1)
  have hc2 : n ≤ c.val+2 := by
    by_contra hh
    let x : Fin n := ⟨c.val+1,by omega⟩
    let y : Fin n := ⟨c.val+2,by omega⟩
    have hx := hafter x (by dsimp [x]; omega)
    have hy := hafter y (by dsimp [y]; omega)
    exact hnofix' x y rfl hx hy
  have hout0 : ¬ (a.val=0 ∧ c.val+1=n) := by
    rintro ⟨ha0,hclast⟩
    have he : c+1=a := by
      have hh := congrArg (fun k : ℕ => (k : Fin n)) hclast
      have ha0' : a=0 := Fin.ext ha0
      simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one,Fin.natCast_self,ha0'] using hh
    exact hnoadj c (hpca.trans he.symm)
  have hout2 : ¬ (a.val=1 ∧ c.val+2=n) := by
    rintro ⟨haone,hcnear⟩
    let z : Fin n := ⟨n-1,by omega⟩
    have hz := hafter z (by dsimp [z]; omega)
    have h0 := hbefore 0 (by omega)
    have he : z+1=0 := by
      have hh := congrArg (fun k : ℕ => (k : Fin n)) (show z.val+1=n by dsimp [z]; omega)
      simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one,Fin.natCast_self] using hh
    exact hnofix z hz (by simpa only [he] using h0)
  have houter : c.val+2=n+a.val := by have := c.isLt; omega
  have houterPair : q c=c+2 := by
    have hh := congrArg (fun k : ℕ => (k : Fin n)) houter
    have he : c+2=a := by simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_ofNat,Fin.natCast_self,zero_add] using hh
    exact hpca.trans he.symm
  have hex : ∃ x ∈ q.support,x ≠ a ∧ x ≠ c := by
    by_contra hnot
    have hsub : q.support ⊆ {a,c} := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton]
      by_contra hh
      push Not at hh
      exact hnot ⟨x,hx,hh.1,hh.2⟩
    have hs := Finset.card_le_card hsub
    have ht : ({a,c} : Finset (Fin n)).card ≤ 2 := by
      by_cases he : a=c <;> simp [he]
    omega
  obtain ⟨x,hxP,hxa,hxc⟩ := hex
  have hax : a.val < x.val := by
    have hh := hamin x hxP
    have hne : x.val ≠ a.val := fun he => hxa (Fin.ext he)
    omega
  have hxc' : x.val < c.val := by
    have hh := hcmax x hxP
    have hne : x.val ≠ c.val := fun he => hxc (Fin.ext he)
    omega
  have hinside := LX.Core.FiniteCuts.noncrossing_pair_interior q hinv hnc a c x hax hxc' hpac
  have hnx : (q x).val ≠ x.val := fun he => (Equiv.Perm.mem_support.mp hxP) (Fin.ext he)
  have hleaf : ∃ u v : Fin n,v.val < c.val ∧ u.val+2=v.val ∧ q u=v := by
    by_cases hlt : x.val < (q x).val
    · obtain ⟨u,v,_,hv,he,hu⟩ := pair_contains_gap_two q hinv hnc hnoadj' hnofix' x (q x) hlt rfl
      exact ⟨u,v,by omega,he,hu⟩
    · obtain ⟨u,v,_,hv,he,hu⟩ := pair_contains_gap_two q hinv hnc hnoadj' hnofix' (q x) x (by omega) (hinv x)
      exact ⟨u,v,by omega,he,hu⟩
  obtain ⟨u,v,hvc,huv,hpu⟩ := hleaf
  have he := hunique u c (hpu.trans (eq_add_of_value_add u v 2 huv).symm) houterPair
  have heval := congrArg Fin.val he
  omega
