-- Prove2me | solution 1 for OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:07:06.51023+00:00
-- url     : https://prove2.me/submissions/dd12a444-3c49-4f33-8661-c0f97035bad7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/PairPhases.lean:L95-L109
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases

-- ---- from OAI.Combinatorics.Hamiltonian.TriangleSystem ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

namespace State

variable {T} {X : Set V}

end State

theorem indexDelta_third : ∀ i j : Fin 3, i ≠ j →
    indexDelta (thirdIndex i j) j - indexDelta i j =
      2 * indexDelta i (thirdIndex i j) := by decide

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

end
end Barnette.Network

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.CycleReversal ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

namespace OppositeCycle

variable {T} {s r : T.State X} (C : T.OppositeCycle s)

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette.TriangleSystem

open Fin.NatCast

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V} {s : T.State X}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

theorem reverse_ne (r : T.State X) (hrs : T.Partner r s) : C.reverse r hrs ≠ r := by
  intro h
  have heq := congrFun (congrArg Subtype.val h) (C.face 0)
  change C.changedCorners r (C.face 0) = r.val (C.face 0) at heq
  rw [C.changedCorners_image] at heq
  have hne : r.val (C.face 0) ≠ s.val (C.face 0) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  exact (thirdIndex_distinct _ _ hne).1 heq

end OppositeCycle

namespace OppositeCycle

variable (C : T.OppositeCycle s)

theorem reversal_involutive : Function.Involutive C.reversal := by
  intro r
  apply Subtype.ext
  exact C.reverse_reverse r.val r.property

theorem reversal_ne (r : T.Partners s) : C.reversal r ≠ r := by
  intro h
  exact C.reverse_ne r.val r.property (congrArg Subtype.val h)

end OppositeCycle
end Barnette.TriangleSystem

end OAI

-- ---- from OAI.Combinatorics.Hamiltonian.PairPhases ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Paired states, permutation cycle classes, and phase cancellation. -/

namespace Barnette

theorem phase_add_six (n : ℤ) : phase (n + 6) = -phase n := by
  unfold phase
  have h : (n + 6) / 3 = n / 3 + 2 := by omega
  rw [h, zpow_add₀ Complex.I_ne_zero]
  norm_num

theorem phase_sub_six (n : ℤ) : phase (n - 6) = -phase n := by
  have h := phase_add_six (n - 6)
  rw [sub_add_cancel] at h
  exact neg_eq_iff_eq_neg.mp h.symm

namespace TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

namespace OppositeCycle

variable {s : T.State X} (C : T.OppositeCycle s)

theorem reverse_rawIndexSum_diff [Fintype A] (r : T.State X) (hrs : T.Partner r s) :
    rawIndexSum (C.reverse r hrs) s - rawIndexSum r s = 2 * C.cyclicDelta r := by
  classical
  rw [rawIndexSum, rawIndexSum, ← Finset.sum_sub_distrib]
  let h (t : A) := indexDelta ((C.reverse r hrs).val t) (s.val t) -
    indexDelta (r.val t) (s.val t)
  change ∑ t, h t = _
  calc
    ∑ t, h t = ∑ t ∈ C.faceSet, h t := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t _ ht
      have hnot : t ∉ Set.range C.face := fun h => ht ((C.mem_faceSet t).mpr h)
      simp only [h, reverse_val, changedCorners, ite_eq_right hnot, sub_self]
    _ = ∑ t ∈ C.faceSet,
        2 * indexDelta (r.val t) (thirdIndex (r.val t) (s.val t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hrst : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      change indexDelta (C.changedCorners r t) (s.val t) -
        indexDelta (r.val t) (s.val t) = _
      rw [changedCorners, ite_eq_left ((C.mem_faceSet t).mp ht)]
      exact indexDelta_third _ _ hrst
    _ = ∑ i, 2 * indexDelta (r.val (C.face i))
        (thirdIndex (r.val (C.face i)) (s.val (C.face i))) := by
      unfold faceSet
      apply Finset.sum_image
      exact C.face.injective.injOn
    _ = 2 * C.cyclicDelta r := by rw [cyclicDelta, Finset.mul_sum]

theorem reverse_phase [Fintype A] (r : T.State X) (hrs : T.Partner r s)
    (hdisk : C.cyclicDelta r = 3 ∨ C.cyclicDelta r = -3) :
    phase (rawIndexSum (C.reverse r hrs) s) = -phase (rawIndexSum r s) := by
  have hdiff := C.reverse_rawIndexSum_diff r hrs
  rcases hdisk with h | h
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s + 6 := by omega
    rw [heq, phase_add_six]
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s - 6 := by omega
    rw [heq, phase_sub_six]

theorem fixed_second_state_cancels [Fintype A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hdisk : ∀ r : T.Partners s, C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (weight : M) : (∑ r : T.Partners s, phase (rawIndexSum r.val s) • weight) = 0 := by
  classical
  apply Finset.sum_ninvolution C.reversal
  · intro r
    change phase (rawIndexSum r.val s) • weight +
      phase (rawIndexSum (C.reverse r.val r.property) s) • weight = 0
    rw [C.reverse_phase r.val r.property (hdisk r), neg_smul, add_neg_cancel]
  · intro r _
    exact C.reversal_ne r
  · intro r
    exact Finset.mem_univ _
  · intro r
    exact C.reversal_involutive r

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette

variable {A : Type*}

end Barnette

namespace Barnette.TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

namespace Pair

end Pair
end Barnette.TriangleSystem

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.TriangleSystem OAI.Barnette.TriangleSystem.OppositeCycle


theorem solution : type_of% @_root_.OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels := @_root_.OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels
