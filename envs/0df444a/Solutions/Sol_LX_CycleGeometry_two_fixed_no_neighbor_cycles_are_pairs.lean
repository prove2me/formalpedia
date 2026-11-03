-- Prove2me | solution 1 for LX.CycleGeometry.two_fixed_no_neighbor_cycles_are_pairs
-- status  : ACCEPTED   (prove)
-- author  : @chaos-ghost
-- created : 2026-11-02T20:49:24.147904+00:00
-- url     : https://prove2.me/submissions/1dce70fb-fe96-4504-aa13-52cd93e7c51f

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
import Definitions.Def_LX_FiniteCutLoad
import Definitions.Def_LX_FiniteDescentRank
import Definitions.Def_LX_FiniteInversionBalance
import Definitions.Def_LX_FiniteWindow
import Definitions.Def_LX_FixedCountReflection
import Definitions.Def_LX_Graph
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_PrunedLift
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_TwoWindowCycleDefect
import Definitions.Def_LX_WordMetric
import Definitions.Def_LX_ZeroGapComponentCounting
import Definitions.Def_LX_ZeroGapCycleRoots
import Definitions.Def_LX_ZeroGapEventGeometry
import Theorems.Thm_LX_CycleGeometry_cycle_factor_gap_fixed

namespace Int
end Int
namespace LX
end LX
namespace LX.AnchoredPhases
end LX.AnchoredPhases
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.BufferProgram
end LX.Core.BufferProgram
namespace LX.Core.FiniteCuts
end LX.Core.FiniteCuts
namespace LX.Core.FiniteGaps
end LX.Core.FiniteGaps
namespace LX.Core.FiniteWindow
end LX.Core.FiniteWindow
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PeriodicBuffer
end LX.Core.PeriodicBuffer
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.PrunedLift
end LX.Core.PrunedLift
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace LX.Core.ZeroGap
end LX.Core.ZeroGap
namespace LX.CycleGeometry
end LX.CycleGeometry
namespace LX.EventGeometry
end LX.EventGeometry
namespace List
end List

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
/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}



















@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i



@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl







end LX.Core.FiniteWindow

end

section
/-! Cycle representatives and fixed points give a root cover of the sorting
event graph; all cycles inside the packet can share one root. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]



theorem cycle_root_mem {q : State n} (hq : q.IsCycle) : cycleRoot q ∈ q.support := by
  classical
  have hne := hq.nonempty_support
  simp only [cycleRoot,dif_pos hne]
  exact Finset.min'_mem _ _

theorem cycle_root_same_cycle {g q : State n} (hq : q ∈ g.cycleFactorsFinset)
    {i : Fin n} (hi : i ∈ q.support) : g.SameCycle (cycleRoot q) i := by
  classical
  have hroot : cycleRoot q ∈ q.support := cycle_root_mem (q := q) (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
  have he : q=g.cycleOf i := Equiv.Perm.cycle_is_cycleOf (f := g) (c := q) hi hq
  have hroot' : cycleRoot q ∈ (g.cycleOf i).support := by rw [← he]; exact hroot
  exact ((Equiv.Perm.mem_support_cycleOf_iff (f := g) (x := i) (y := cycleRoot q)).mp hroot').1.symm








end LX.Core.ZeroGap

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]









@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp




















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem inversion_indicator_self (p : State n) (i : Fin n) :
    inversionIndicator p i i=0 := by simp [inversionIndicator]















end LX.Core.FiniteCuts

end

section
namespace LX.Core.FiniteCuts
open scoped Fin.NatCast Fin.CommRing
variable {n : ℕ}



@[simp] theorem mem_fixedPositions (p : State n) (i : Fin n) :
    i ∈ fixedPositions p ↔ p i=i := by simp [fixedPositions]









end LX.Core.FiniteCuts

end

section
/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LX.Core.PrunedLift
open scoped BigOperators
variable {n : ℕ}



@[simp] theorem permutation_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    permutation p S hS i=if i ∈ S then p i else i := rfl

@[simp] theorem permutation_symm_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    (permutation p S hS).symm i=if i ∈ S then p.symm i else i := rfl

end LX.Core.PrunedLift

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
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]













@[simp] theorem mem_endpoints (events : List (Event n)) (i : Fin n) :
    i ∈ endpoints events ↔ ∃ e ∈ events, i=e.1 ∨ i=e.2 := by
  simp [endpoints]






end LX.Core.ZeroGap

end

namespace LX.CycleGeometry
end LX.CycleGeometry
open LX
open LX.CycleGeometry
open scoped BigOperators
open LX.Core.FiniteCuts LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

/-- With the cut at a fixed point, two fixed positions cannot fill two
nonempty internal gaps of a longer cycle. Consequently every cycle is a
pair whenever neighboring physical positions lie in different cycles. -/
theorem solution (q : State n) (hq : cycleDefect q=0)
    (hzero : q 0=0) (hfixed : (fixedPositions q).card ≤ 2)
    (hsep : ∀ i j : Fin n,i.val+1=j.val → ¬q.SameCycle i j) :
    ∀ g ∈ q.cycleFactorsFinset,g.support.card=2 := by
  classical
  have hunit (i : Fin n) : |_root_.LX.Core.FiniteCuts.displacement q i| ≠ 1 := by
    intro hh
    have hs : q.SameCycle i (q i) := (Equiv.Perm.SameCycle.refl q i).apply_right
    unfold _root_.LX.Core.FiniteCuts.displacement at hh
    rw [abs_eq_max_neg] at hh
    have hc : i.val+1=(q i).val ∨ (q i).val+1=i.val := by omega
    rcases hc with hc | hc
    · exact hsep i (q i) hc hs
    · exact hsep (q i) i hc hs.symm
  intro g hg
  have hsize := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1.two_le_card_support
  by_contra hnot
  have hthree : 3 ≤ g.support.card := by omega
  let S := g.support
  have hS : S.Nonempty := Finset.card_pos.mp (by dsimp [S]; omega)
  let a := S.min' hS
  have ha : a ∈ S := Finset.min'_mem S hS
  have hS1 : (S.erase a).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem ha]
    dsimp [S]
    omega)
  let b := (S.erase a).min' hS1
  have hb1 : b ∈ S.erase a := Finset.min'_mem _ _
  have hb : b ∈ S := (Finset.mem_erase.mp hb1).2
  have hba : b ≠ a := (Finset.mem_erase.mp hb1).1
  have hS2 : ((S.erase a).erase b).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hb1,Finset.card_erase_of_mem ha]
    dsimp [S]
    omega)
  let c := ((S.erase a).erase b).min' hS2
  have hc2 : c ∈ (S.erase a).erase b := Finset.min'_mem _ _
  have hc1 : c ∈ S.erase a := (Finset.mem_erase.mp hc2).2
  have hc : c ∈ S := (Finset.mem_erase.mp hc1).2
  have hcb : c ≠ b := (Finset.mem_erase.mp hc2).1
  have hab : a.val < b.val := by
    have hlo : a.val ≤ b.val := Finset.min'_le S b hb
    have hne : b.val ≠ a.val := fun h => hba (Fin.ext h)
    omega
  have hbc : b.val < c.val := by
    have hlo : b.val ≤ c.val := Finset.min'_le (S.erase a) c hc1
    have hne : c.val ≠ b.val := fun h => hcb (Fin.ext h)
    omega
  have hgapAB (i : Fin n) (hai : a.val < i.val) (hib : i.val < b.val) : i ∉ g.support := by
    intro hi
    have hia : i ≠ a := by intro h; have := congrArg Fin.val h; omega
    have hm : i ∈ S.erase a := Finset.mem_erase.mpr ⟨hia,hi⟩
    have hh : b.val ≤ i.val := Finset.min'_le (S.erase a) i hm
    omega
  have hgapBC (i : Fin n) (hbi : b.val < i.val) (hic : i.val < c.val) : i ∉ g.support := by
    intro hi
    have hia : i ≠ a := by intro h; have := congrArg Fin.val h; omega
    have hib : i ≠ b := by intro h; have := congrArg Fin.val h; omega
    have hm : i ∈ (S.erase a).erase b := Finset.mem_erase.mpr ⟨hib,Finset.mem_erase.mpr ⟨hia,hi⟩⟩
    have hh : c.val ≤ i.val := Finset.min'_le ((S.erase a).erase b) i hm
    omega
  have habCycle : q.SameCycle a b := (cycle_root_same_cycle hg ha).symm.trans (cycle_root_same_cycle hg hb)
  have hbcCycle : q.SameCycle b c := (cycle_root_same_cycle hg hb).symm.trans (cycle_root_same_cycle hg hc)
  have hab2 : a.val+1 < b.val := by
    have hne : a.val+1 ≠ b.val := fun he => hsep a b he habCycle
    omega
  have hbc2 : b.val+1 < c.val := by
    have hne : b.val+1 ≠ c.val := fun he => hsep b c he hbcCycle
    omega
  obtain ⟨u,hau,hub,hu⟩ := cycle_factor_gap_fixed q g hq hunit hg a b ha hb hab2 hgapAB
  obtain ⟨v,hbv,hvc,hv⟩ := cycle_factor_gap_fixed q g hq hunit hg b c hb hc hbc2 hgapBC
  have hz : (0 : Fin n) ∈ fixedPositions q := (mem_fixedPositions _ _).mpr hzero
  have hcard : ((fixedPositions q).erase 0).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hz]
    omega
  have hum : u ∈ (fixedPositions q).erase 0 := Finset.mem_erase.mpr ⟨by
    intro h; rw [h,Fin.val_zero] at hau; omega,(mem_fixedPositions _ _).mpr hu⟩
  have hvm : v ∈ (fixedPositions q).erase 0 := Finset.mem_erase.mpr ⟨by
    intro h; rw [h,Fin.val_zero] at hbv; omega,(mem_fixedPositions _ _).mpr hv⟩
  have he := Finset.card_le_one.mp hcard u hum v hvm
  have hh := congrArg Fin.val he
  omega
