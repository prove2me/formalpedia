-- Prove2me | solution 1 for LX.Core.ZeroGap.swap_distinct_orbits_same_cycle
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:29:29.708333+00:00
-- url     : https://prove2.me/submissions/09584fc1-9bd8-4181-83b2-0d9307f281dc

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

namespace LX.Core
end LX.Core
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap

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

namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
open LX
open LX.Core
open LX.Core.ZeroGap
variable {n : ℕ}

/-- A transposition between two different orbits puts its endpoints in one orbit. -/
theorem solution (p : State n) (a b : Fin n)
    (hnot : ¬p.SameCycle a b) : (Equiv.swap a b*p).SameCycle a b := by
  classical
  have hret : ∃ k : ℕ, 0 < k ∧ (p^k) b=b :=
    ⟨orderOf p,orderOf_pos p,by simp⟩
  let k := Nat.find hret
  have hk : 0 < k ∧ (p^k) b=b := Nat.find_spec hret
  have hne (j : ℕ) (hj : 0 < j) (hjk : j < k) : (p^j) b ≠ b := by
    intro he
    have hh := Nat.find_min hret hjk
    exact hh ⟨hj,he⟩
  have hna (j : ℕ) : (p^j) b ≠ a := by
    intro he
    apply hnot
    have hs : p.SameCycle b ((p^j) b) := (Equiv.Perm.SameCycle.refl p b).pow_right
    exact (he ▸ hs).symm
  let q := Equiv.swap a b*p
  have heq : ∀ j < k, (q^j) b=(p^j) b := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hp := ih (by omega)
      rw [pow_succ',Equiv.Perm.mul_apply,hp]
      change Equiv.swap a b (p ((p^j) b)) = (p^(j+1)) b
      have he : p ((p^j) b) = (p^(j+1)) b := by rw [pow_succ',Equiv.Perm.mul_apply]
      rw [he]
      exact Equiv.swap_apply_of_ne_of_ne (hna _) (hne _ (by omega) hj)
  have hlast : (q^k) b=a := by
    have he : k=(k-1)+1 := by omega
    rw [he,pow_succ',Equiv.Perm.mul_apply,heq (k-1) (by omega)]
    change Equiv.swap a b (p ((p^(k-1)) b)) = a
    have hp : p ((p^(k-1)) b)=b := by
      rw [← Equiv.Perm.mul_apply,← pow_succ',← he]
      exact hk.2
    rw [hp,Equiv.swap_apply_right]
  have hs : q.SameCycle b ((q^k) b) := (Equiv.Perm.SameCycle.refl q b).pow_right
  exact (hlast ▸ hs).symm
