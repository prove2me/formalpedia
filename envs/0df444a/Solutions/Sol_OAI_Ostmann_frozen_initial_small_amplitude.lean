-- Prove2me | solution 1 for OAI.Ostmann.frozen_initial_small_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:35:44.053228+00:00
-- url     : https://prove2.me/submissions/0a07175a-50f8-47a0-878d-843266c4b59f

import Mathlib
import Definitions.Def_OAIQ095D008

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferArithmetic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic separation of diagonal and transferred terms -/

namespace Ostmann

theorem large_prime_factors_coprime_frequency (H : ℕ) (v : ℤ) (hv : v ≠ 0)
    (hlarge : ∀ q, q.Prime → q ∣ H → v.natAbs < q) : H.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro q hq hqH hqv
  exact (not_le_of_gt (hlarge q hq hqH))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hv) hqv)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_inversion {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x = ∑ a : ZMod p, additiveFourier f a * ZMod.stdAddChar (a * x) := by
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at hinv
  calc
    f x = (p : ℂ)⁻¹ * ∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a := by
      simpa only [smul_eq_mul] using hinv.symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [additiveFourier]
      ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AffineAction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Identifying the Fourier matrix of the affine action

The finite matrix from `AffineFourier` is the action of
`F(t) ↦ ∑ c(a,b) F(at+b)` on nonzero additive frequencies.
-/

namespace Ostmann

open scoped BigOperators

theorem additiveFourier_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => c * f x) a = c * additiveFourier f a := by
  simp only [additiveFourier_apply, mul_assoc]
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourierBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two local Fourier bounds in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem additiveFourier_twice {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) :
    additiveFourier (additiveFourier f) a = (q : ℂ)⁻¹ * f (-a) := by
  rw [additiveFourier_apply]
  congr 1
  have hi := additiveFourier_inversion f (-a)
  simpa only [mul_neg] using hi.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.Follows.root {σ : Type*} {n : ℕ} {T : MovingSlotData σ n}
    {t : FrequencyTree ℤ n} (h : T.Follows t) : T.frequency = frequencyRoot n t := by
  cases T with
  | leaf => exact h
  | node => exact h.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.frequencies_isCoprime {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (x : ℤ) :
    T.Frequencies (fun s => IsCoprime x s) ↔ IsCoprime x T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [Frequencies, frequencyProduct, IsCoprime.mul_right_iff, ihL, ihR, and_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit bridge between equivalent finite enumerations -/

namespace Ostmann

theorem finite_univ_canonical {A : Type*} [Finite A] (F : Fintype A) :
    @Finset.univ A F = @Finset.univ A (Fintype.ofFinite A) := by
  cases Subsingleton.elim F (Fintype.ofFinite A)
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotFieldBridge
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full original support as local guards in the sampled recursion

All current-state coprimalities and all descendant-frequency unit tests are
retained. This puts the existing fully supported coefficient into the local
recursion form, without conditioning any internal sample prior.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_node {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (l r : MovingSlotData σ n) (XL XR : ℕ) :
    let T := MovingSlotData.node s CL CR u l r
    let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
    movingFullSupport value outside T XL XR ↔
      movingLocalSupport value outside ⟨n + 1, T, XL, XR⟩ ∧
      movingFullSupport value outside l p XL ∧ movingFullSupport value outside r p XR := by
  simp only [movingFullSupport, movingLocalSupport, movingFullOutsidePairwise, movingNaturalGiantUnits]
  tauto

theorem movingSlotCutoff_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E) x s v w =
      if movingLocalSupport value outside x then
        movingSlotCutoff value childBound pivotBound E x s v w else 0 := by
  unfold movingSlotCutoff movingGuardedExtra
  split_ifs <;> rfl

/-- The fully supported original history coefficient equals the recursive
coefficient with the literal local support test at each node and leaf. -/
theorem movingSupportedWeight_recursive {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E))
      n ⟨n, T, XL, XR⟩ t =
        movingSupportedWeight value outside T XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n ⟨n, T, XL, XR⟩ t) := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutg := movingSlotCutoff value childBound pivotBound (movingGuardedExtra value outside E)
  induction T generalizing XL XR with
  | leaf s regular => rfl
  | @node n s CL CR u l r hl hr =>
      let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u l r, XL, XR⟩
      let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      let p := (MovingSlotData.step s CL CR u l r false).naturalPivot value XL XR
      have hp : P / MovingSlotReversal.naturalProduct value u = p := by
        simp only [P, p, historyPivot, sys, movingSlotSystem, x, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, MovingSlotReversal.naturalPivot, MovingSlotData.step,
          movingGiantPivot, Nat.mul_one, ← hT.1, ← hT.2.1.root, ← hT.2.2.root]
      by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node sys _ cutg n x t P hv]
        change (cutg x t.1 _ _ : ℂ) *
            recursiveTransferWeight sys _ cutg n ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ t.2.1 *
            star (recursiveTransferWeight sys _ cutg n ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ t.2.2) = _
        rw [hp, hl t.2.1 hT.2.1 p XL, hr t.2.2 hT.2.2 p XR]
        have hg := movingSlotCutoff_guarded value outside childBound pivotBound E x
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        change cutg x t.1 _ _ = if movingLocalSupport value outside x then cut x t.1 _ _ else 0 at hg
        rw [hg]
        unfold movingSupportedWeight
        have hs := movingFullSupport_node value outside s CL CR u l r XL XR
        dsimp only at hs
        rw [hs]
        rw [recursiveTransferWeight_node sys F cut n x t P hv]
        have hleft : sys.leftState x P =
            ⟨n, l, P / MovingSlotReversal.naturalProduct value u, XL⟩ := rfl
        have hright : sys.rightState x P =
            ⟨n, r, P / MovingSlotReversal.naturalProduct value u, XR⟩ := rfl
        rw [hleft, hright, hp]
        by_cases hA : movingLocalSupport value outside x <;>
          by_cases hB : movingFullSupport value outside l p XL <;>
          by_cases hC : movingFullSupport value outside r p XR
        all_goals dsimp only [x, p] at hA hB hC ⊢
        all_goals simp only [hA, hB, hC, and_true, and_false,
          ite_true, if_true, ite_false, if_false, Complex.ofReal_zero, zero_mul, mul_zero, star_zero]
        rfl
      · have hz₁ : recursiveTransferWeight sys (movingGuardedLeaf value outside F) cutg
            (n + 1) x t = 0 := by simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
          simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
        rw [hz₁, hz₂]
        unfold movingSupportedWeight
        split_ifs <;> rfl

theorem movingFrequencySkeleton_frequencyTree (σ : Type*) (n : ℕ)
    (t : FrequencyTree ℤ n) :
    (movingFrequencySkeleton σ n t).frequencyTree = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [movingFrequencySkeleton, MovingSlotData.frequencyTree, ih]
    rfl

theorem MovingSlotData.skeleton_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) :
    (movingFrequencySkeleton σ n T.frequencyTree).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r hl hr =>
    simp only [MovingSlotData.frequencyTree, movingFrequencySkeleton, frequencyProduct, hl, hr]

theorem MovingSlotData.rootData_regularSlots {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.regularSlots = T.regularSlots := by
  cases T <;> rfl

theorem MovingSlotData.rootData_frequencyProduct {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.frequencyProduct = T.frequencyProduct := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, frequencyProduct, skeleton_frequencyProduct]

theorem MovingSlotData.rootData_idempotent {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.rootData.rootData = T.rootData := by
  cases T with
  | leaf => rfl
  | node s CL CR u l r =>
    simp only [rootData, movingFrequencySkeleton_frequencyTree]

theorem movingLocalSupport_rootData {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (x : MovingSlotState σ) :
    movingLocalSupport value outside ⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ ↔
      movingLocalSupport value outside x := by
  simp only [movingLocalSupport, MovingSlotData.currentSlots, movingLocalGiantUnits,
    MovingSlotData.rootData_regularSlots, MovingSlotData.rootData_frequencyProduct]

theorem movingLocalExtra_guarded {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingGuardedExtra value outside (movingLocalExtra E)) =
      movingGuardedExtra value outside (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingGuardedExtra, movingLocalSupport_rootData,
    MovingSlotData.rootData_idempotent]

/-- The sample expansion of the fully supported original coefficient. Every
sample retains its original weight, including samples whose support fails. -/
theorem movingSampledWeight_supported {σ : Type*} [Fintype σ] (value : σ → ℕ)
    (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra E)) n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n, (movingSamplesPrior μ a : ℂ) *
        movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
          (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  unfold movingSampledWeight
  rw [movingLocalExtra_guarded]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedWeight_recursive value outside childBound pivotBound F (movingLocalExtra E)
    _ t (buildMovingSlotData_follows n t small bulk a)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSampleTier_lt {n : ℕ} (i : MovingSampleIndex n) : movingSampleTier i < n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
      rcases i with i | ⟨b, i⟩
      · exact Nat.lt_succ_self n
      · exact (ih i).trans (Nat.lt_succ_self n)

theorem movingCompensationPrior_indexed {A : Type*} (μ : A → ℝ) (n : ℕ)
    (a : TreeLeafTuple (Fin 4 → A) n) :
    movingCompensationPrior μ n a =
      ∏ t : TreeLeafIndex n, ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) n a t j) := by
  induction n with
  | zero =>
      change (∏ j : Fin 4, μ (a j)) = ∏ _t : Unit, ∏ j : Fin 4, μ (a j)
      simp only [Fintype.prod_unique]
  | succ n ih =>
      change movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2 =
        ∏ t : TreeLeafIndex n ⊕ TreeLeafIndex n,
          ∏ j : Fin 4, μ (treeLeafTupleEquiv (Fin 4 → A) (n + 1) a t j)
      rw [Fintype.prod_sum_type, ih, ih]
      rfl

/-- The tree law is precisely the product of the original coordinate priors.
This identity permits the proved equality-pattern comparison to be applied
without replacing the law by a conditioned or uniform distribution. -/
theorem movingSamplesPrior_coordinates {A : Type*} (μ : ℕ → A → ℝ) (n : ℕ)
    (a : MovingSampleSlots A n) :
    movingSamplesPrior μ a =
      ∏ i : MovingSampleIndex n, μ (movingSampleTier i) (movingSampleCoordinates A n a i) := by
  induction a with
  | leaf => rfl
  | @node n u l r hl hr =>
      change movingCompensationPrior (μ n) n u * movingSamplesPrior μ l * movingSamplesPrior μ r =
        ∏ i : (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n), _
      rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_prod_type, Fintype.prod_bool,
        movingCompensationPrior_indexed, hl, hr]
      simp only [movingSampleTier, movingSampleCoordinates, Equiv.coe_fn_mk]
      ring

theorem movingSamplesPrior_reindex {A : Type*} [Fintype A] (μ : ℕ → A → ℝ)
    (n : ℕ) (F : MovingSampleSlots A n → ℂ) :
    (∑ a : MovingSampleSlots A n, (movingSamplesPrior μ a : ℂ) * F a) =
      ∑ x : MovingSampleIndex n → A,
        ((∏ i, μ (movingSampleTier i) (x i) : ℝ) : ℂ) *
          F ((movingSampleCoordinates A n).symm x) := by
  have h := (movingSampleCoordinates A n).symm.sum_comp
    (fun a => (movingSamplesPrior μ a : ℂ) * F a)
  rw [← h]
  apply Finset.sum_congr rfl
  intro x _
  rw [movingSamplesPrior_coordinates, Equiv.apply_symm_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRecursiveCompensation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting compensation from the actual supported recursion -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSlotCutoff_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E) x s v w =
      (x.compensation value : ℝ) * movingSlotCutoff value childBound pivotBound E x s v w := by
  unfold movingSlotCutoff movingCompensatedExtra
  split_ifs <;> simp only [mul_zero]

theorem MovingSlotState.compensation_rootData {σ : Type*} (value : σ → ℕ)
    (x : MovingSlotState σ) :
    (⟨x.depth, x.data.rootData, x.leftGiant, x.rightGiant⟩ : MovingSlotState σ).compensation value =
      x.compensation value := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingLocalExtra_compensated {σ : Type*} (value : σ → ℕ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    movingLocalExtra (movingCompensatedExtra value E) =
      movingCompensatedExtra value (movingLocalExtra E) := by
  funext x s v w
  simp only [movingLocalExtra, movingCompensatedExtra, MovingSlotState.compensation_rootData]

/-- Each node contributes its newly sampled compensation exactly once,
including off-support samples where both sides vanish. -/
theorem movingRecursiveWeight_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t =
        (movingSampleProduct value a : ℂ) *
          recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
            (movingSlotCutoff value childBound pivotBound E) n
            ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t := by
  let sys := movingSlotSystem value childBound pivotBound
  let cut := movingSlotCutoff value childBound pivotBound E
  let cutc := movingSlotCutoff value childBound pivotBound (movingCompensatedExtra value E)
  induction a generalizing XL XR with
  | leaf => simp only [movingSampleProduct, Nat.cast_one, one_mul, recursiveTransferWeight]
  | @node n a l r hl hr =>
    let x : MovingSlotState σ :=
      ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
    let P := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hv : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys F cutc n x t P hv,
        recursiveTransferWeight_node sys F cut n x t P hv]
      change (cutc x t.1 _ _ : ℂ) *
        recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.1 *
        star (recursiveTransferWeight sys F cutc n ⟨n, _, _, _⟩ t.2.2) = _
      simp only [ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      rw [hl, hr]
      have hc : cutc x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
          (x.compensation value : ℝ) * cut x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) :=
        movingSlotCutoff_compensated value childBound pivotBound E x _ _ _
      rw [hc]
      simp only [movingSampleProduct, Complex.ofReal_mul, Complex.ofReal_natCast,
        Nat.cast_mul, star_mul, star_natCast]
      change _ = (x.compensation value : ℂ) * _ * _ * _
      simp only [sys, movingSlotSystem, MovingSlotState.child, x, buildMovingSlotData,
        ite_true, if_true, Bool.false_eq_true, ite_false, if_false]
      ring
    · have hz₁ : recursiveTransferWeight sys F cutc (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      have hz₂ : recursiveTransferWeight sys F cut (n + 1) x t = 0 := by
        simp only [recursiveTransferWeight, P, hv, ite_false, if_false]
      rw [hz₁, hz₂, mul_zero]

theorem movingSupportedWeight_mul {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (c z : ℂ) :
    movingSupportedWeight value outside T XL XR (c * z) =
      c * movingSupportedWeight value outside T XL XR z := by
  unfold movingSupportedWeight
  split_ifs <;> simp only [mul_zero]

/-- Exact compensated prior times the supported coefficient with node
compensations removed. This is the scalar used by the pattern comparison. -/
theorem movingSampledWeight_compensated_supported {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
      (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
      n t small bulk XL XR =
      ∑ a : MovingSampleSlots σ n,
        (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) *
          movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
            (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
              (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
              ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t) := by
  rw [movingSampledWeight_supported]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingLocalExtra_compensated, movingRecursiveWeight_compensated,
    movingSupportedWeight_mul, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSamplePairExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalSampleExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient under the exact internal sampling law -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalNode_local {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingLocalExtra (movingOriginalNode value childBound pivotBound φ G) =
      movingOriginalNode value childBound pivotBound φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> rfl

theorem movingOriginalNode_compensated {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ) :
    movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G) =
      movingPhiExtra value childBound pivotBound (movingDataExtra (movingCompensationExtra value)) φ G := by
  funext x s v w
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [movingCompensatedExtra, movingOriginalNode, movingPhiExtra,
    movingDataExtra, movingCompensationExtra, MovingSlotState.compensation, Nat.cast_one, one_mul]

/-- The Fourier/window/spectator coefficient is exactly the local sampled
recursion already expanded above. -/
theorem movingOriginalSampleAverage_eq {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR =
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (movingOriginalLeaf value q F g Dq S ψ X lo hi)
      (movingOriginalNode value childBound pivotBound φ G) n t small bulk XL XR := by
  unfold movingSupportedSampledWeight
  rw [movingSampledWeight_supported, movingLocalExtra_compensated, movingOriginalNode_local,
    movingOriginalNode_compensated]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

/-- Identification with the already proved original prime-pattern expansion.
This links the finite frequency coefficient to the arithmetic comparison. -/
theorem movingFrequencyCoefficient_original {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s small bulk XL XR =
      ∑ t : MovingDescendantFrequencyIndex V n,
        movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
          n (movingRootedFrequencyTree V n s t) small bulk XL XR := by
  simp only [movingFrequencyCoefficient, movingOriginalSampleAverage_eq]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabelling repeated sampled slots by their equality-pattern classes -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.naturalProduct_map {σ τ : Type*}
    (f : σ → τ) (value : τ → ℕ) (slots : List σ) :
    naturalProduct value (slots.map f) = naturalProduct (value ∘ f) slots := by
  simp only [naturalProduct, List.map_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotStateRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the original recursion in finite pattern coordinates -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingSlotState.leftProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).leftProduct value = x.leftProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.leftProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.rightProduct_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).rightProduct value = x.rightProduct (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.rightProduct, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.compensation_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    (x.map f).compensation value = x.compensation (value ∘ f) := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.compensation, MovingSlotReversal.naturalProduct_map]

@[simp] theorem MovingSlotState.child_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (b : Bool) (x : MovingSlotState σ) (P : ℕ) :
    (x.map f).child value b P = (x.child (value ∘ f) b P).map f := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> cases b <;> simp only [MovingSlotState.map, MovingSlotData.map,
    MovingSlotState.child, MovingSlotReversal.naturalProduct_map, Bool.false_eq_true,
    ite_true, if_true, ite_false, if_false] <;> rfl

@[simp] theorem movingSlotSystem_leftState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).leftState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).leftState x P).map f :=
  MovingSlotState.child_map f value true x P

@[simp] theorem movingSlotSystem_rightState_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ) (P : ℕ) :
    (movingSlotSystem value childBound pivotBound).rightState (x.map f) P =
      ((movingSlotSystem (value ∘ f) childBound pivotBound).rightState x P).map f :=
  MovingSlotState.child_map f value false x P

@[simp] theorem movingHistoryPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) :
    historyPivot (movingSlotSystem value childBound pivotBound) (x.map f) s v w =
      historyPivot (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w := by
  simp only [historyPivot, movingSlotSystem, MovingSlotState.leftProduct_map,
    MovingSlotState.rightProduct_map]

theorem movingValidTransferNode_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ) (x : MovingSlotState σ)
    (s v w : ℤ) (P : ℕ) :
    ValidTransferNode (movingSlotSystem value childBound pivotBound) (x.map f) s v w P ↔
      ValidTransferNode (movingSlotSystem (value ∘ f) childBound pivotBound) x s v w P := by
  constructor <;> intro h
  all_goals refine ⟨h.root_ne_zero, ?_, ?_, h.pivot_pos, h.pivot_bound,
    h.left_bound, h.right_bound, ?_, h.pivot_unit⟩
  all_goals first
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map] using h.root_unit
    | simpa only [movingSlotSystem, MovingSlotState.leftProduct_map,
        MovingSlotState.rightProduct_map] using h.relation
    | simpa only [movingSlotSystem, MovingSlotState.rightProduct_map,
        MovingSlotState.map_depth] using h.range_gap

/-- A relabeling evaluates every original pivot and guard, including the
integer division by the sampled compensation product. -/
theorem movingRecursiveWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (leaf : MovingSlotState τ → ℤ → ℂ)
    (cutoff : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (x : MovingSlotState σ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) leaf cutoff n (x.map f) t =
      recursiveTransferWeight (movingSlotSystem (value ∘ f) childBound pivotBound)
        (fun x => leaf (x.map f)) (fun x => cutoff (x.map f)) n x t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [recursiveTransferWeight, movingHistoryPivot_map, movingValidTransferNode_map]
    split_ifs
    · simp only [movingSlotSystem_leftState_map, movingSlotSystem_rightState_map]
      rw [ih, ih]
    · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalWeightRelabel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant weight commutes with evaluating pattern labels -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

@[simp] theorem movingSlotModulus_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (x : MovingSlotState σ) :
    movingSlotModulus value (x.map f) = movingSlotModulus (value ∘ f) x := by
  rcases x with ⟨n, T, XL, XR⟩
  cases T <;> simp only [MovingSlotState.map, MovingSlotData.map, movingSlotModulus,
    ← List.map_append, MovingSlotReversal.naturalProduct_map]

theorem movingSlotCutoff_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingSlotCutoff value childBound pivotBound extra (x.map f) s v w =
      movingSlotCutoff (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) x s v w := by
  simp only [movingSlotCutoff, MovingSlotState.compensation_map, movingHistoryPivot_map]

theorem movingPhiExtra_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (childBound pivotBound : ℕ → ℕ)
    (extra : MovingSlotState τ → ℤ → ℤ → ℤ → ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) :
    movingPhiExtra value childBound pivotBound extra φ G (x.map f) s v w =
      movingPhiExtra (value ∘ f) childBound pivotBound
        (fun x => extra (x.map f)) φ G x s v w := by
  simp only [movingPhiExtra, MovingSlotState.map_depth, movingHistoryPivot_map,
    MovingSlotState.compensation_map]

theorem movingOriginalGiantWeight_map {σ τ I : Type*} (f : σ → τ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : τ → ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData τ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData τ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (XL XR : ℕ) :
    movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G
      (T.map f) t XL XR =
    movingOriginalGiantWeight q (value ∘ f) childBound pivotBound
      (fun T => F (T.map f)) (fun T => E (T.map f)) g Dq S ψ X lo hi φ G T t XL XR := by
  unfold movingOriginalGiantWeight
  change recursiveTransferWeight _ _ _ n
    ((⟨n, T, XL, XR⟩ : MovingSlotState σ).map f) t = _
  rw [movingRecursiveWeight_map]
  congr 1
  · funext x s
    simp only [movingWindowLeaf, movingDataLeaf, movingFourierLeaf,
      spectatorHistoryLeaf, movingSlotModulus_map, MovingSlotState.map_data]
    rfl
  · funext x s v w
    rw [movingSlotCutoff_map]
    congr 1
    funext y a b c
    rw [movingPhiExtra_map]
    rfl

theorem movingLocalGiantUnits_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℤ) :
    movingLocalGiantUnits value outside (T.map f) XL XR ↔
      movingLocalGiantUnits (value ∘ f) outside T XL XR := by
  simp only [movingLocalGiantUnits, MovingSlotData.frequencyProduct_map,
    MovingSlotData.regularSlots_map, MovingSlotReversal.naturalProduct_map]

theorem MovingSlotReversal.naturalPivot_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (s : MovingSlotReversal σ) (XL XR : ℕ) :
    (s.map f).naturalPivot value XL XR = s.naturalPivot (value ∘ f) XL XR := by
  simp only [MovingSlotReversal.naturalPivot, MovingSlotReversal.map,
    MovingSlotReversal.naturalProduct_map]

theorem movingLocalSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) (x : MovingSlotState σ) :
    movingLocalSupport value outside (x.map f) ↔
      movingLocalSupport (value ∘ f) outside x := by
  change (((x.data.map f).currentSlots value x.leftGiant x.rightGiant ++ outside).Pairwise Nat.Coprime ∧
      movingLocalGiantUnits value outside (x.data.map f) x.leftGiant x.rightGiant) ↔ _
  rw [MovingSlotData.currentSlots_map, movingLocalGiantUnits_map]
  rfl

theorem movingFullSupport_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingFullSupport value outside (T.map f) XL XR ↔
      movingFullSupport (value ∘ f) outside T XL XR := by
  induction T generalizing XL XR with
  | leaf s regular =>
    change movingLocalSupport value outside
      ((⟨0, .leaf s regular, XL, XR⟩ : MovingSlotState σ).map f) ↔ _
    exact movingLocalSupport_map f value outside _
  | node s CL CR u l r ihL ihR =>
    have hlocal := movingLocalSupport_map f value outside
      (⟨_, .node s CL CR u l r, XL, XR⟩ : MovingSlotState σ)
    change movingLocalSupport value outside
      ⟨_, .node s (CL.map f) (CR.map f) (u.map f) (l.map f) (r.map f), XL, XR⟩ ↔ _ at hlocal
    simp only [MovingSlotData.map, movingFullSupport_node, MovingSlotData.step_map,
      MovingSlotReversal.naturalPivot_map, ihL, ihR, hlocal]

theorem movingSupportedWeight_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (XL XR : ℕ) (z : ℂ) :
    movingSupportedWeight value outside (T.map f) XL XR z =
      movingSupportedWeight (value ∘ f) outside T XL XR z := by
  simp only [movingSupportedWeight, movingFullSupport_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSmallFrequencyUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-prime frequency tests follow from the actual range separation -/

namespace Ostmann

theorem MovingSlotData.Frequencies.mono {σ : Type*} {P Q : ℤ → Prop}
    {n : ℕ} {T : MovingSlotData σ n} (h : T.Frequencies P) (hPQ : ∀ s, P s → Q s) :
    T.Frequencies Q := by
  induction T with
  | leaf => exact hPQ _ h
  | node s CL CR U left right ihL ihR => exact ⟨hPQ s h.1, ihL h.2.1, ihR h.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Support inherited by the reconstructed giant-only transfer -/

namespace Ostmann
open scoped Classical

/-- All current giant tests, including descendant frequencies, follow from
pairwise support and the same large-prime separation used at the root. -/
theorem moving_local_support_of_large {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧
      ∀ q, q.Prime → q ∣ XL * XR → s.natAbs < q)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  have cast_coprime {a b : ℕ} (h : a.Coprime b) : IsCoprime (a : ℤ) (b : ℤ) := by
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa only [Int.gcd_natCast_natCast] using h)
  have giant_frequency (X : ℕ) (hX : X ∣ XL * XR) :
      IsCoprime (X : ℤ) T.frequencyProduct := by
    apply (T.frequencies_isCoprime (X : ℤ)).mp
    apply hf.mono
    intro s hs
    have hu := large_prime_factors_coprime_frequency X s hs.1
      (fun q hq hqd => hs.2 q hq (hqd.trans hX))
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using hu
  have hXL := giant_frequency XL (dvd_mul_right XL XR)
  have hXR := giant_frequency XR (dvd_mul_left XR XL)
  have hpair := hp
  change (XL :: XR :: (T.regularSlots.map value ++ outside)).Pairwise Nat.Coprime at hpair
  obtain ⟨hL, htail⟩ := List.pairwise_cons.mp hpair
  obtain ⟨hR, _⟩ := List.pairwise_cons.mp htail
  have hLreg : XL.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hL a (List.mem_cons_of_mem XR (List.mem_append_left outside ha))
  have hRreg : XR.Coprime (MovingSlotReversal.naturalProduct value T.regularSlots) := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro a ha
    exact hR a (List.mem_append_left outside ha)
  have hLout : XL.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hL a (List.mem_cons_of_mem XR (List.mem_append_right _ ha)))
  have hRout : XR.Coprime outside.prod := Nat.coprime_list_prod_right_iff.mpr
    (fun a ha => hR a (List.mem_append_right _ ha))
  exact ⟨hp, hXL, hXR, cast_coprime hLreg, cast_coprime hRreg,
    cast_coprime hLout, cast_coprime hRout⟩

/-- In the transfer application the surviving top giants are actual primes.
All the additional descendant-frequency tests are therefore automatic. -/
theorem moving_local_support_prime_giants {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR V : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime) (hVL : V < XL) (hVR : V < XR)
    (hp : (T.currentSlots value XL XR ++ outside).Pairwise Nat.Coprime)
    (hf : T.Frequencies (fun s => s ≠ 0 ∧ s.natAbs ≤ V)) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  apply moving_local_support_of_large value outside T XL XR hp
  apply hf.mono
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro q hq hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · have he : q = XL := ((Nat.dvd_prime hXL).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVL
  · have he : q = XR := ((Nat.dvd_prime hXR).mp hd).resolve_left hq.ne_one
    exact he ▸ hs.2.trans_lt hVR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_prior_reindex {V W A : Type*} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (μ : W → A → ℝ) (F : (W → A) → ℂ) :
    (∑ x : V → A, ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm)) =
      ∑ x : W → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x := by
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : W → A => ((∏ i, μ i (x i) : ℝ) : ℂ) * F x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro x _
  change ((∏ i, μ (e i) (x i) : ℝ) : ℂ) * F (x ∘ e.symm) =
    ((∏ i, μ i (x (e.symm i)) : ℝ) : ℂ) * F (x ∘ e.symm)
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => μ i (x (e.symm i)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_NodeBulkProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

theorem treeLeafProduct_indexed {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafIndex n → G) :
    treeLeafProduct n ((treeLeafTupleEquiv G n).symm x) = ∏ i, x i := by
  induction n with
  | zero =>
    change Unit → G at x
    change x () = ∏ i : Unit, x i
    exact (Fintype.prod_subsingleton x ()).symm
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → G at x
    change treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))) *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i))) = _
    rw [ih, ih]
    change _ = ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, x i
    exact (Fintype.prod_sum_type x).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplateProducts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact moduli of the regular-slot templates -/

namespace Ostmann
open scoped Classical BigOperators

theorem naturalProduct_bulkSlotLeaves {A : Type*} (value : A → ℕ) (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → A) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n (bulkSlotLeaves n m slot)) =
      ∏ i, value (slot i) := by
  rw [movingSlotValues_flatten]
  have h : movingSlotValues value n (bulkSlotLeaves n m slot) =
      (treeLeafTupleEquiv ℕ n).symm (fun j => ∏ i : Fin m, value (slot (j, i))) := by
    apply (treeLeafTupleEquiv ℕ n).injective
    funext j
    rw [movingSlotValues_indexed, Equiv.apply_symm_apply]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
      List.map_ofFn, List.prod_ofFn]
    rfl
  rw [h, treeLeafProduct_indexed, Fintype.prod_prod_type]

/-- Every regular coordinate occurs once in the small/bulk leaf lists. -/
theorem movingTemplate_product {A : Type*} (value : A → ℕ) (n r m : ℕ)
    (y : MovingRegularSlot n r m → A) :
    MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n (movingTemplateSmall n r m) ++
        flattenMovingSlots n (bulkSlotLeaves n m (movingTemplateBulk n r m))) =
      ∏ i, value (y i) := by
  rw [movingNaturalProduct_append]
  unfold movingTemplateSmall
  rw [naturalProduct_bulkSlotLeaves, naturalProduct_bulkSlotLeaves]
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Function.comp_apply, movingTemplateBulk]
  rw [Finset.prod_mul_distrib]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SupportedAlphabetSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact alphabet restriction for the original independent priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem finite_sum_embedding_support {A B M : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid M] (e : B ↪ A) (f : A → M)
    (hf : ∀ a, a ∉ Set.range e → f a = 0) :
    (∑ a, f a) = ∑ b, f (e b) := by
  rw [← Finset.sum_image e.injective.injOn]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro a _ ha
  apply hf a
  simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using ha

theorem productPrior_alphabet_sum {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    (e : B ↪ A) (μ : I → A → ℝ) (F : (I → A) → ℂ)
    (hμ : ∀ i a, μ i a ≠ 0 → a ∈ Set.range e) :
    (∑ x : I → A, ((∏ i, μ i (x i) : ℝ) : ℂ) * F x) =
      ∑ y : I → B, ((∏ i, μ i (e (y i)) : ℝ) : ℂ) * F (e ∘ y) := by
  let E : (I → B) ↪ (I → A) :=
    ⟨fun y => e ∘ y, fun x y h => funext fun i => e.injective (congrFun h i)⟩
  apply finite_sum_embedding_support E
  intro x hx
  have hp : (∏ i, μ i (x i)) = 0 := by
    by_contra hn
    have hi (i) : x i ∈ Set.range e := hμ i _ ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
    apply hx
    refine ⟨fun i => Classical.choose (hi i), ?_⟩
    funext i
    exact Classical.choose_spec (hi i)
  simp only [hp, Complex.ofReal_zero, zero_mul]

theorem movingSamplesPrior_alphabet_sum {A B : Type*} [Fintype A] [Fintype B]
    (e : B ↪ A) (μ : ℕ → A → ℝ) (n : ℕ) (F : MovingSampleSlots A n → ℂ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    (∑ x : MovingSampleSlots A n, (movingSamplesPrior μ x : ℂ) * F x) =
      ∑ y : MovingSampleSlots B n,
        (movingSamplesPrior (fun j b => μ j (e b)) y : ℂ) * F (y.map e) := by
  rw [movingSamplesPrior_reindex, movingSamplesPrior_reindex]
  rw [productPrior_alphabet_sum e (fun i => μ (movingSampleTier i))
    (fun x => F ((movingSampleCoordinates A n).symm x))
    (fun i a ha => hμ _ a (movingSampleTier_lt i) ha)]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  apply (movingSampleCoordinates A n).injective
  funext i
  simp only [Equiv.apply_symm_apply, movingSampleCoordinates_map]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAlphabetRestriction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original moving sampler on a smaller live alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingCompensationExtra_map {A B : Type*} (e : B → A) (value : A → ℕ)
    {n : ℕ} (T : MovingSlotData B n) (s v w : ℤ) :
    movingCompensationExtra value (T.map e) s v w =
      movingCompensationExtra (value ∘ e) T s v w := by
  cases T <;> simp only [MovingSlotData.map, movingCompensationExtra,
    MovingSlotReversal.naturalProduct_map]

theorem movingOriginalSampleAverage_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t (treeLeafMap (List.map e) n small) (treeLeafMap (List.map e) n bulk) XL XR =
    movingOriginalSampleAverage q (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound
      (fun T => F (T.map e)) g Dq S ψ X lo hi φ G n t small bulk XL XR := by
  unfold movingOriginalSampleAverage
  rw [movingSamplesPrior_alphabet_sum e μ n _ hμ]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← buildMovingSlotData_map, movingOriginalGiantWeight_map, movingSupportedWeight_map]
  congr 2
  funext d T s v w
  exact movingCompensationExtra_map e value T s v w

theorem movingFrequencyCoefficient_original_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List B) n)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s
      (treeLeafMap (List.map e) n small) (treeLeafMap (List.map e) n bulk) XL XR =
    movingFrequencyCoefficient (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n s small bulk XL XR := by
  simp only [movingFrequencyCoefficient_original]
  apply Finset.sum_congr rfl
  intro t _
  exact movingOriginalSampleAverage_alphabet e q value outside μ childBound pivotBound F g Dq S
    ψ X lo hi φ G n _ small bulk XL XR hμ

theorem movingTemplateCoefficient_original_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (y : MovingRegularSlot n r m → B)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m s (e ∘ y) XL XR =
    movingTemplateCoefficient (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n r m s y XL XR := by
  unfold movingTemplateCoefficient
  rw [← treeLeafMap_list_comp, ← treeLeafMap_list_comp]
  exact movingFrequencyCoefficient_original_alphabet e q value outside μ childBound pivotBound V F
    g Dq S ψ X lo hi φ G n s _ _ XL XR hμ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem normalizedResidueIndicator_sum {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    (∑ x : ZMod p, normalizedResidueIndicator S x) = 0 := by
  simp only [normalizedResidueIndicator, ← Complex.ofReal_sum, ← Finset.sum_div,
    centeredDensity_sum, zero_div, Complex.ofReal_zero]

theorem normalizedResidueTransform_zero {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    normalizedResidueTransform S 0 = 0 := by
  simp only [normalizedResidueTransform, densityFourier, additiveFourier_apply,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one, normalizedResidueIndicator_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Fourier-phase giant and its real physical inverse -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem additiveFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    additiveFourier (fun b => g (-b)) x = additiveFourier g (-x) := by
  simp only [additiveFourier_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro b
  simp only [Equiv.neg_apply, neg_neg, neg_mul, mul_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

/-- No positive integer outside this range contributes to the extension.
The endpoints are retained in the finite set. -/
theorem smoothGiant_weight_zero_outside (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hpI : p ∉ smoothGiantIntegerRange G) : φ (Real.log p - G) = 0 := by
  have hceil : ⌈Real.exp (G + 1)⌉₊ < p := by
    have hn : ¬(1 ≤ p ∧ p ≤ ⌈Real.exp (G + 1)⌉₊) := by
      simpa only [smoothGiantIntegerRange, Finset.mem_Icc] using hpI
    omega
  have hexp : Real.exp (G + 1) < (p : ℝ) :=
    (Nat.le_ceil (Real.exp (G + 1))).trans_lt (by exact_mod_cast hceil)
  have hlog : G + 1 < Real.log p := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  exact hout _ (le_trans (by linarith) (le_abs_self _))

/-- The smooth normalizer has the exact finite support stipulated in (7.3). -/
theorem smoothGiant_prime_support (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : p.Prime)
    (hφp : φ (Real.log p - G) ≠ 0) : p ∈ smoothGiantPrimeRange G := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hp⟩
  by_contra hn
  exact hφp (smoothGiant_weight_zero_outside φ G hout p hp.pos hn)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferTransform
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full Fourier transform in the actual transfer slot order -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTaggedTransform_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (giant : J → Bool)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (p ∘ e) (giant ∘ e) greg ggiant favorable D s =
      movingTaggedTransform p giant greg ggiant favorable D s := by
  unfold movingTaggedTransform
  dsimp only [Function.comp_def]
  simp_rw [tupleCofactor_equiv e p hp]
  exact e.prod_comp (fun j => (if giant j then
      (fun t => if favorable (p j) then complexUnitPhase (ggiant (p j) t) else 0)
    else greg (p j))
      ((s : ZMod (p j)) * ((D * tupleCofactor p j : ℕ) : ZMod (p j))⁻¹))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueFamily
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single family of normalized transforms for varying sampled primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem normalizedResidueFamily_eq (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] :
    normalizedResidueFamily sets q = normalizedResidueTransform (sets q) := by
  simp only [normalizedResidueFamily, dite_eq_right (NeZero.ne q)]

theorem normalizedResidueFamily_zero (sets : ∀ q : ℕ, Finset (ZMod q))
    (q : ℕ) [NeZero q] : normalizedResidueFamily sets q 0 = 0 := by
  rw [normalizedResidueFamily_eq]
  exact normalizedResidueTransform_zero _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeAlphabet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal prime amplitude is unchanged by restricting live regular primes -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_original_alphabet {A B I : Type}
    [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → A → ℝ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e)
    (hν : ∀ i a, ν i a ≠ 0 → a ∈ Set.range e)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i b => ν i (e b)) greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have he := productPrior_alphabet_sum e ν (fun y =>
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m s.val y XL XR *
    movingTaggedTransform
      (Sum.elim (fun b : Bool => if b then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val) hν
  simp only [finite_univ_canonical] at he ⊢
  rw [he]
  apply Finset.sum_congr rfl
  intro y _
  rw [movingTemplateCoefficient_original_alphabet e q value outside μ childBound pivotBound V
    F g Dq S ψ X lo hi φ G n r m s.val y XL XR hμ]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantAmbientPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full smooth giant law inside an ambient prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantMass_ambient (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) :
    smoothGiantMass P φ G = smoothGiantMass (smoothGiantPrimeRange G) φ G := by
  symm
  apply Finset.sum_subset hsub
  intro p hp hn
  have hz : φ (Real.log p - G) = 0 := by
    by_contra hne
    exact hn (smoothGiant_prime_support φ G hout p (hP p hp) hne)
  simp only [hz, zero_div]

theorem smoothGiantPrior_ambient_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
    smoothGiantPrior P φ G p = 0 := by
  have hz : φ (Real.log (p : ℕ) - G) = 0 := by
    by_contra hne
    exact hp (smoothGiant_prime_support φ G hout p (hP p p.property) hne)
  simp only [smoothGiantPrior, hz, mul_zero, zero_div]

theorem smoothGiantPrior_ambient_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) (f : P → ℝ) :
    (∑ p : P, smoothGiantPrior P φ G p * f p) =
      ∑ q : smoothGiantPrimeRange G, smoothGiantPrior (smoothGiantPrimeRange G) φ G q *
        f ⟨q, hsub q.property⟩ := by
  have hm := smoothGiantMass_ambient P hP φ G hout hsub
  let e : smoothGiantPrimeRange G → P := fun q => ⟨q, hsub q.property⟩
  have hprior (q : smoothGiantPrimeRange G) : smoothGiantPrior P φ G (e q) =
      smoothGiantPrior (smoothGiantPrimeRange G) φ G q := by
    simp only [smoothGiantPrior, smoothGiantLogNormalizer, hm, e]
  have hz (p : P) (hp : (p : ℕ) ∉ smoothGiantPrimeRange G) :
      smoothGiantPrior P φ G p * f p = 0 := by
    rw [smoothGiantPrior_ambient_zero P hP φ G hout p hp, zero_mul]
  calc
    _ = ∑ p ∈ (Finset.univ : Finset P).filter (fun p : P => (p : ℕ) ∈ smoothGiantPrimeRange G),
        smoothGiantPrior P φ G p * f p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (p : ℕ) ∈ smoothGiantPrimeRange G
      · simp only [hp, ite_true, if_true]
      · simp only [hp, ite_false, if_false, hz p hp]
    _ = ∑ q : smoothGiantPrimeRange G, smoothGiantPrior P φ G (e q) * f (e q) := by
      symm
      apply Finset.sum_bij (fun q _ => e q)
      · intro q _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.property⟩
      · intro q _ r _ hqr
        exact Subtype.ext (congrArg (fun p : P => p.val) hqr)
      · intro p hp
        refine ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, ?_⟩
        rfl
      · intro q _
        rfl
    _ = _ := by simp only [hprior, e]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantAmbientAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the giant average to its full smooth cell -/
namespace Ostmann
open scoped Classical BigOperators

theorem smoothGiantPrior_ambient_complex_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hsub : smoothGiantPrimeRange G ⊆ P) (f : P → ℂ) :
    (∑ p : P, (smoothGiantPrior P φ G p : ℂ) * f p) =
      ∑ q : smoothGiantPrimeRange G,
        (smoothGiantPrior (smoothGiantPrimeRange G) φ G q : ℂ) * f ⟨q, hsub q.property⟩ := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using smoothGiantPrior_ambient_mean P hP φ G hout hsub (fun p => (f p).re)
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using smoothGiantPrior_ambient_mean P hP φ G hout hsub (fun p => (f p).im)

theorem movingTemplatePrimeAmplitude_giant_ambient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ψ : ℝ → ℝ) (H : ℝ) (hout : ∀ x, 1 ≤ |x| → ψ x = 0)
    (hsub : smoothGiantPrimeRange H ⊆ P)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      P (smoothGiantPrior P ψ H) ν greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantPrimeRange H) (smoothGiantPrior (smoothGiantPrimeRange H) ψ H)
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  rw [smoothGiantPrior_ambient_complex_mean P hP ψ H hout hsub]
  apply Finset.sum_congr rfl
  intro XL _
  congr 1
  rw [smoothGiantPrior_ambient_complex_mean P hP ψ H hout hsub]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingInitialCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal level-zero coefficient and its original cutoff -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingFrequencyCoefficient_levelZero (σ : Type) [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ) (small bulk : List σ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G 0 s
      small bulk XL XR =
    movingGuardedLeaf value outside F ⟨0, .leaf s (small ++ bulk), XL, XR⟩ s := by
  unfold movingFrequencyCoefficient
  change (∑ t : Unit, _) = _
  rw [Finset.univ_unique, Finset.sum_singleton]
  unfold movingSupportedSampledWeight movingSampledWeight
  rw [← (movingSampleZeroEquiv σ).sum_comp]
  rw [Finset.univ_unique, Finset.sum_singleton]
  simp [movingSampleZeroEquiv, movingSamplesPrior, recursiveTransferWeight,
    buildMovingSlotData, frequencyRoot, flattenMovingSlots, movingRootedFrequencyTree]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLeafPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering the regular primes in an original terminal leaf -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLocalSupport_leaf_perm {A : Type*} (value : A → ℕ)
    (outside : List ℕ) (L R : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingLocalSupport value outside ⟨0, .leaf s L, XL, XR⟩ ↔
      movingLocalSupport value outside ⟨0, .leaf s R, XL, XR⟩ := by
  have hp : MovingSlotReversal.naturalProduct value L =
      MovingSlotReversal.naturalProduct value R := (h.map value).prod_eq
  have hpair := (((h.map value).cons XR).cons XL).append_right outside
  have he : (XL :: XR :: L.map value ++ outside).Pairwise Nat.Coprime ↔
      (XL :: XR :: R.map value ++ outside).Pairwise Nat.Coprime :=
    hpair.pairwise_iff (fun h => h.symm)
  simp only [movingLocalSupport, MovingSlotData.currentSlots, MovingSlotData.regularSlots,
    movingLocalGiantUnits, MovingSlotData.frequencyProduct, List.cons_append, hp]
  exact and_congr_left (fun _ => by simpa only [List.cons_append] using he)

theorem movingOriginalLeaf_constant_leaf_perm {A I : Type*} (value : A → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (L R : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi ⟨0, .leaf s L, XL, XR⟩ s =
    movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi ⟨0, .leaf s R, XL, XR⟩ s := by
  have hp : MovingSlotReversal.naturalProduct value L =
      MovingSlotReversal.naturalProduct value R := (h.map value).prod_eq
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, movingFourierLeaf,
    movingSlotModulus, spectatorHistoryLeaf, hp]
  rfl

theorem movingFrequencyCoefficient_zero_small_perm {A I : Type} [Fintype A]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (L R bulk : List A) (h : L.Perm R) (s : ℤ) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 s L bulk XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 s R bulk XL XR := by
  rw [movingFrequencyCoefficient_levelZero, movingFrequencyCoefficient_levelZero]
  unfold movingGuardedLeaf
  rw [movingLocalSupport_leaf_perm value outside (L ++ bulk) (R ++ bulk) (h.append_right bulk)]
  rw [movingOriginalLeaf_constant_leaf_perm value q f g Dq S ψ X lo hi
    (L ++ bulk) (R ++ bulk) (h.append_right bulk)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PhaseGiantMean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive uniform-support mean of the Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem densityFourier_reflect {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (fun b => g (-b)) x = densityFourier g (-x) := by
  simp only [densityFourier, additiveFourier_reflect]

theorem densityFourier_twice {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourier g) x = g (-x) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hs : (Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ) = p := by
    exact_mod_cast (by simpa only [pow_two] using Real.sq_sqrt (Nat.cast_nonneg p))
  unfold densityFourier
  rw [additiveFourier_const_mul, additiveFourier_twice]
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (Real.sqrt (p : ℝ) : ℂ)) * (p : ℂ)⁻¹ * g (-x) := by ring
    _ = _ := by rw [hs, mul_inv_cancel₀ hp, one_mul]

theorem densityFourier_inverse {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (x : ZMod p) :
    densityFourier (densityFourierInverse g) x = g x := by
  change densityFourier (fun b => densityFourier g (-b)) x = g x
  rw [densityFourier_reflect, densityFourier_twice, neg_neg]

/-- The giant's Fourier transform is exactly the bounded phase specified in
Section 7.1, not merely an energy majorant. -/
theorem phaseGiantPhysical_transform {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (b : ZMod p) :
    densityFourier (phaseGiantPhysical g) b = complexUnitPhase (g b) :=
  densityFourier_inverse _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimePhysicalTest
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact physical tests for the two kinds of prime position -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem primePhysicalTest_fourier {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (giant favorable : Bool) (b : ZMod p) :
    densityFourier (primePhysicalTest S giant favorable) b =
      if giant then
        if favorable then complexUnitPhase (normalizedResidueTransform S b) else 0
      else normalizedResidueTransform S b := by
  cases giant <;> cases favorable
  · rfl
  · rfl
  · simp only [primePhysicalTest, ↓reduceIte, Bool.false_eq_true, densityFourier,
      additiveFourier_apply, zero_mul, Finset.sum_const_zero, mul_zero]
  · exact phaseGiantPhysical_transform _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialLogSumScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial logarithmic cutoff centers lie below the giant scale -/

namespace Ostmann
open Filter

theorem initialLogSumWeight_support {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A)
    (h : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact h (logCellProfile_zero_outside _ (le_of_not_gt hn))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCutoffProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two cutoff weights control the full sampled product -/
namespace Ostmann
open scoped Classical BigOperators

theorem initial_half_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin ((b + (d + r)) + 1) → P)
    (hprior : productPrior (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))) x ≠ 0)
    (hw : initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail x) ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - (G + cb + cd + ∑ i, center i)| ≤ r + 3 := by
  have hpriorAt (i : Fin ((b + (d + r)) + 1)) :
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) : Fin ((b + (d + r)) + 1) → P → ℝ) i (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprior) i (Finset.mem_univ i)
  have hgiant : |Real.log (x 0 : ℝ) - G| ≤ 1 :=
    hG _ (by simpa only [Fin.cons_zero] using hpriorAt 0)
  have hcell (i : Fin r) :
      |Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ) - center i| ≤ 1 := by
    apply hc
    simpa only [Fin.cons_succ, Fin.append_right, Fin.tail] using
      hpriorAt (((i.natAdd d).natAdd b).succ)
  have hcells : |(∑ i : Fin r, Real.log (Fin.tail x ((i.natAdd d).natAdd b) : ℝ)) -
      ∑ i, center i| ≤ r := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) => hcell i)
  obtain ⟨hwb, hwd⟩ := mul_ne_zero_iff.mp hw
  have hb := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cb _ hwb).le
  have hd := (initialLogSumWeight_support (fun q : P => (q : ℕ)) cd _ hwd).le
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero)]
  rw [Fin.sum_univ_succ, Fin.sum_univ_add, Fin.sum_univ_add]
  obtain ⟨hglo, hghi⟩ := abs_le.mp hgiant
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hd
  obtain ⟨hclo, hchi⟩ := abs_le.mp hcells
  dsimp only [Fin.tail] at hblo hbhi hdlo hdhi hclo hchi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSmallCellList
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three top labels and two labels of each compensation type -/
namespace Ostmann

theorem initialSmallCellList_sum (top : ℕ) (centers : List ℕ) :
    ((initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ))).sum =
      3 * (top : ℝ) + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp; ring
  | cons j js ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at ih ⊢
    linarith only [ih]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected initial small cells on a common prime space -/
namespace Ostmann
open scoped Classical BigOperators

theorem mem_initialRegularPrimeRange (L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : (p : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) :
    p ∈ initialRegularPrimeRange L := Nat.mem_primesLE.mpr ⟨Nat.le_floor hbound, hp⟩

theorem SelectedSmallTailCell.subset_initialRegularPrimeRange
    {A B : Set ℕ} {N hi j : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L Y hi D target j) :
    selectedTailCellPrimes A B N Y hi D j ⊆ initialRegularPrimeRange L := by
  intro p hp
  obtain ⟨_, _, hindex, _, _, _, hsupport⟩ := h
  have hs := hsupport p hp
  apply mem_initialRegularPrimeRange L p hs.1
  exact hs.2.2.1.trans (Real.exp_le_exp.mpr hindex)

theorem initialSmallCellList_property (top : ℕ) (centers : List ℕ) (P : ℕ → Prop)
    (htop : P top) (hcenters : ∀ j ∈ centers, P j) :
    ∀ j ∈ initialSmallCellList top centers, P j := by
  intro j hj
  simp only [initialSmallCellList, List.mem_append, List.mem_replicate, List.mem_flatMap] at hj
  rcases hj with ⟨_, rfl⟩ | ⟨w, hw, hjw⟩
  · exact htop
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hjw
    rcases hjw with rfl | rfl <;> exact hcenters _ hw

theorem initial_selected_cells_valid
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y target : ℝ} {D : Finset ℕ}
    {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y hi D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j) centers targets) :
    ∀ j ∈ initialSmallCellList top centers,
      ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j := by
  refine initialSmallCellList_property top centers
    (fun j => ∃ t, SelectedSmallTailCell A B N a C L Y hi D t j) ⟨target, htop⟩ ?_
  induction hcenters with
  | nil => simp
  | @cons j w js ws hj hrest ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨w / 4, hj⟩
    · exact ih i hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorSplit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original spectator coordinates without changing their law -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_spectator {P : Type*} (b d r : ℕ)
    (spectator : Fin d → P) (retained : Unit ⊕ (Fin b ⊕ Fin r) → P) (i : Fin d) :
    initialHalfAssemble b d r spectator retained ((i.castAdd r).natAdd b).succ = spectator i := by
  change (Sum.elim spectator retained)
    ((initialSpectatorSlotEquiv b d r).symm (initialSpectatorSlotEquiv b d r (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSlots
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two half-lists in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialCompleteIndexEquiv_assemble {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (yl yr : InitialRetainedSlot b r → P) :
    Fin.append (initialHalfAssemble b d r sl yl) (initialHalfAssemble b d r sr yr) ∘
      initialCompleteIndexEquiv b d r =
    Sum.elim (Fin.append sl sr)
      (Sum.elim yl yr ∘ (initialRetainedIndexEquiv b r).symm) := by
  funext i
  rcases i with i | i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [initialCompleteIndexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Equiv.sumSumSumComm_apply, Equiv.sumAssoc, Equiv.sumComm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id_eq,
        finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, initialHalfAssemble, Function.comp_apply,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply,
        Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Sum.swap_inl]
  · obtain ⟨j, rfl⟩ := (initialRetainedIndexEquiv b r).surjective i
    rcases j with j | j <;>
      simp only [initialCompleteIndexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
        Equiv.sumSumSumComm_apply, Equiv.sumAssoc, Equiv.sumComm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, id_eq,
        finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, initialHalfAssemble, Function.comp_apply,
        Fin.append_left, Fin.append_right, Equiv.symm_apply_apply,
        Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Sum.swap_inr]

theorem initial_reassembled_moving_tuple {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P) :
    Fin.append
      (initialHalfAssemble b d r sl (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl))
      (initialHalfAssemble b d r sr (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr)) =
    Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm := by
  have h := initialCompleteIndexEquiv_assemble b d r sl sr
    (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl)
    (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr)
  have he : Sum.elim (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl)
      (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr) = z ∘ initialRetainedIndexEquiv b r := by
    funext i
    cases i <;> rfl
  rw [he] at h
  have hz : (z ∘ initialRetainedIndexEquiv b r) ∘ (initialRetainedIndexEquiv b r).symm = z := by
    funext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [hz] at h
  funext i
  have hh := congrFun h ((initialCompleteIndexEquiv b d r).symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hh

theorem initialMovingTuple_reindex {P : Type*} (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r =
      Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y) := by
  funext i
  simp only [initialMovingTuple, Function.comp_apply, Equiv.symm_apply_apply]

theorem initialMovingTuple_product {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (∏ i, value (initialMovingTuple b d r sl sr XL XR y i)) =
      (∏ i, value (Fin.append sl sr i)) * (value XL * value XR * ∏ i, value (y i)) := by
  rw [← (initialCompleteIndexEquiv b d r).prod_comp]
  change (∏ i, value ((initialMovingTuple b d r sl sr XL XR y ∘
    initialCompleteIndexEquiv b d r) i)) = _
  rw [initialMovingTuple_reindex, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_bool, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingAverage
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preserving the original retained prior in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initial_retained_prior {P : Type*} (b r : ℕ) (μg : P → ℝ)
    (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (i : InitialRetainedSlot b r ⊕ InitialRetainedSlot b r) :
    (Sum.elim (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc))
      (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc))) i =
    Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc)
      (initialRetainedIndexEquiv b r i) := by
  rcases i with ((u | (i | i)) | (u | (i | i))) <;>
    simp only [initialRetainedIndexEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
      initialMovingRegularPrior, Fin.append_left, Fin.append_right]

private theorem initial_sum_prior_split {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
    (μ : I → P → ℝ) (ν : J → P → ℝ) (H : (I ⊕ J → P) → ℂ) :
    (∑ x : I ⊕ J → P, ((∏ i, Sum.elim μ ν i (x i) : ℝ) : ℂ) * H x) =
      ∑ l : I → P, ((∏ i, μ i (l i) : ℝ) : ℂ) *
        ∑ r : J → P, ((∏ i, ν i (r i) : ℝ) : ℂ) * H (Sum.elim l r) := by
  rw [← (Equiv.sumArrowEquivProdArrow I J P).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr, Complex.ofReal_mul, mul_assoc]
  rfl

theorem initial_retained_average {P : Type*} [Fintype P] (b r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (H : (InitialRetainedSlot b r ⊕ InitialRetainedSlot b r → P) → ℂ) :
    let ν := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
    (∑ yl : InitialRetainedSlot b r → P, ((∏ i, ν i (yl i) : ℝ) : ℂ) *
      ∑ yr : InitialRetainedSlot b r → P, ((∏ i, ν i (yr i) : ℝ) : ℂ) * H (Sum.elim yl yr)) =
    ∑ z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) i (z i) : ℝ) : ℂ) *
        H (z ∘ initialRetainedIndexEquiv b r) := by
  intro ν
  have hs := initial_sum_prior_split ν ν H
  simp only [finite_univ_canonical] at hs ⊢
  rw [← hs]
  have he := finite_prior_reindex (initialRetainedIndexEquiv b r).symm (Sum.elim ν ν) H
  simp only [Equiv.symm_symm, finite_univ_canonical] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro z _
  congr 2
  apply Finset.prod_congr rfl
  intro i _
  have h := initial_retained_prior b r μg μb μc ((initialRetainedIndexEquiv b r).symm i)
  rw [Equiv.apply_symm_apply] at h
  exact congrFun h (z i)

private theorem initial_bool_prior_average {P : Type*} [Fintype P]
    (μ : P → ℝ) (H : (Bool → P) → ℂ) :
    (∑ x : Bool → P, ((∏ b, μ (x b) : ℝ) : ℂ) * H x) =
      ∑ L : P, (μ L : ℂ) * ∑ R : P, (μ R : ℂ) * H (fun b => if b then L else R) := by
  rw [← (initialGiantAssignment P).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro L _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  simp only [initialGiantAssignment, Equiv.coe_fn_mk, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Complex.ofReal_mul]
  ring

theorem initialFrozenAmplitude_movingOrder (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) :
    initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr =
      ∑ z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P,
        ((∏ i, Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) i (z i) : ℝ) : ℂ) *
          let x := Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm
          w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0 := by
  have h := initial_retained_average b r μg μb μc (fun z =>
    let x := Fin.append (initialHalfAssemble b d r sl (z ∘ Sum.inl))
      (initialHalfAssemble b d r sr (z ∘ Sum.inr))
    w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0)
  change initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  have hx := initial_reassembled_moving_tuple b d r sl sr z
  simp only [Function.comp_assoc] at hx ⊢
  rw [hx]

/-- Both original giants and all regular marginals keep their exact laws. -/
theorem initialFrozenAmplitude_moving (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (F : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → (p : P) → ZMod (p : ℕ) → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ)
    (w : (Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) → ℂ)
    (sl sr : Fin d → P) :
    initialFrozenAmplitude P b d r μg μb μc F ψ X V w sl sr =
      ∑ XL : P, (μg XL : ℂ) * ∑ XR : P, (μg XR : ℂ) *
        ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
          ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) *
            let x := initialMovingTuple b d r sl sr XL XR y
            w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0 := by
  rw [initialFrozenAmplitude_movingOrder]
  let K := fun z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P =>
    let x := Sum.elim (Fin.append sl sr) z ∘ (initialCompleteIndexEquiv b d r).symm
    w x * if Function.Injective x then primeTupleFourierCoefficient P F ψ X V x else 0
  have hs := initial_sum_prior_split (fun _ : Bool => μg)
    (initialMovingRegularPrior b r μb μc) K
  simp only [finite_univ_canonical] at hs ⊢
  rw [hs]
  have hb := initial_bool_prior_average μg (fun z =>
    ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) * K (Sum.elim z y))
  simp only [finite_univ_canonical] at hb
  rw [hb]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSpectatorFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact spectator cofactors in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- A regular spectator block factors from the tagged giant/regular block. -/
theorem movingTaggedTransform_spectator_split {I J : Type*} [Fintype I] [Fintype J]
    (q : I → ℕ) (p : J → ℕ) (hq : ∀ i, q i ≠ 0) (hp : ∀ j, p j ≠ 0)
    (tag : J → Bool) (g h : ∀ q : ℕ, ZMod q → ℂ) (fav : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform (Sum.elim q p) (Sum.elim (fun _ => false) tag) g h fav D s =
      (∏ i, g (q i) ((s : ZMod (q i)) * ((D * (∏ j, p j) * tupleCofactor q i : ℕ) : ZMod (q i))⁻¹)) *
        movingTaggedTransform p tag g h fav (D * ∏ i, q i) s := by
  unfold movingTaggedTransform
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [tupleCofactor_sum_left q p i (hq i)]
    simp only [Sum.elim_inl, Bool.false_eq_true, ↓reduceIte]
    have hm : D * (tupleCofactor q i * ∏ j, p j) =
        (D * ∏ j, p j) * tupleCofactor q i := by ring
    rw [hm]
    rfl
  · apply Finset.prod_congr rfl
    intro j _
    rw [tupleCofactor_sum_right q p j (hp j)]
    simp only [Sum.elim_inr]
    rw [← mul_assoc]
    rfl

theorem initialSpectatorCofactor_val {I : Type*} [Fintype I]
    (q : I → ℕ) (hc : Pairwise (fun i j => (q i).Coprime (q j))) (i : I) :
    (initialSpectatorCofactor q hc i : ZMod (q i)) = (tupleCofactor q i : ℕ) := by
  simp only [initialSpectatorCofactor, ZMod.coe_unitOfCoprime]

/-- This is precisely the spectator leaf used throughout the moving recursion. -/
theorem initial_spectator_transform {I : Type*} [Fintype I]
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (hc : Pairwise (fun i j => (q i).Coprime (q j)))
    (g : ∀ i, ZMod (q i) → ℂ) (M : ℕ) (s : ℤ) :
    movingRegularTransform q g M s =
      ∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (g i)
        (initialSpectatorCofactor q hc i) () s := by
  unfold movingRegularTransform
  apply Finset.prod_congr rfl
  intro i _
  simp only [spectatorHistoryLeaf, initialSpectatorCofactor_val,
    Nat.cast_mul, div_eq_mul_inv]
  rw [mul_comm (M : ZMod (q i))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant and regular tests under the moving-slot reindexing -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialGiantFlag_reindex (b d r : ℕ)
    (i : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b))) :
    initialGiantFlag b d r (initialCompleteIndexEquiv b d r i) =
      Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)) i := by
  let a : InitialRetainedSlot b r → Bool := Sum.elim (fun _ => true) (fun _ => false)
  have hhalf : initialHalfAssemble b d r (fun _ => false) a =
      Fin.cons true (fun _ => false) := by
    funext j
    obtain ⟨i, rfl⟩ := (initialSpectatorSlotEquiv b d r).surjective j
    rcases i with i | (u | (i | i)) <;>
      simp [initialHalfAssemble, initialSpectatorSlotEquiv, a]
  have h := initialCompleteIndexEquiv_assemble b d r (fun _ => false) (fun _ => false) a a
  rw [hhalf] at h
  have hret : Sum.elim a a ∘ (initialRetainedIndexEquiv b r).symm =
      Sum.elim (fun _ : Bool => true) (fun _ => false) := by
    funext j
    obtain ⟨i, rfl⟩ := (initialRetainedIndexEquiv b r).surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases i with ((u | (i | i)) | (u | (i | i))) <;> rfl
  rw [hret] at h
  have ha : Fin.append (fun _ : Fin d => false) (fun _ : Fin d => false) =
      (fun _ : Fin (d + d) => false) := by
    funext j
    exact Fin.addCases (fun _ => Fin.append_left _ _ _) (fun _ => Fin.append_right _ _ _) j
  rw [ha] at h
  exact congrFun h i

theorem initial_full_physical_test (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : (p : P) → Finset (ZMod (p : ℕ))) (fav : P → Bool)
    (i : Fin ((b + (d + r) + 1) + (b + (d + r) + 1))) (p : P) :
    Fin.append (primeHalfTests (n := b + (d + r)) P S fav)
      (primeHalfTests (n := b + (d + r)) P S fav) i p =
    primePhysicalTest (S p) (initialGiantFlag b d r i) (fav p) := by
  let flag : Fin (b + (d + r) + 1) → Bool := Fin.cons true (fun _ => false)
  have hh (j : Fin (b + (d + r) + 1)) :
      primeHalfTests P S fav j p =
        primePhysicalTest (S p) (flag j) (fav p) := by
    refine Fin.cases ?_ (fun k => ?_) j <;>
      simp only [flag, primeHalfTests, Fin.cons_zero, Fin.cons_succ, primePhysicalTest,
        Bool.false_eq_true, ↓reduceIte]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [initialGiantFlag, Fin.append_left] using hh j
  · simpa only [initialGiantFlag, Fin.append_right] using hh j

/-- The complete transform uses exactly the manuscript's phase at the two
original giant positions and its normalized residue transform elsewhere. -/
theorem initial_full_transform (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (x : Fin ((b + (d + r) + 1) + (b + (d + r) + 1)) → P) (s : ℤ) :
    movingRegularTransform (fun i => (x i : ℕ))
      (fun i => densityFourier (Fin.append
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)) i (x i))) 1 s =
    movingTaggedTransform (fun i => (x i : ℕ)) (initialGiantFlag b d r)
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav 1 s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [initial_full_physical_test, primePhysicalTest_fourier, normalizedResidueFamily_eq]
  split_ifs <;> rfl

/-- Exact factorization of the original transform after fixing spectators. -/
theorem initial_moving_transform (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b d r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    let x := initialMovingTuple b d r sl sr XL XR y
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let p := Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ))
    movingRegularTransform (fun i => (x i : ℕ))
      (fun i => densityFourier (Fin.append
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)) i (x i))) 1 s =
      (∏ i, normalizedResidueFamily S (q i)
        ((s : ZMod (q i)) * (((∏ j, p j) * tupleCofactor q i : ℕ) : ZMod (q i))⁻¹)) *
      movingTaggedTransform p (Sum.elim (fun _ => true) (fun _ => false))
        (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro x q p
  rw [initial_full_transform]
  have hx : (fun i => (x i : ℕ)) ∘ initialCompleteIndexEquiv b d r = Sum.elim q p := by
    funext i
    change ((initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r) i : ℕ) = _
    rw [initialMovingTuple_reindex]
    rcases i with i | (a | i)
    · rfl
    · cases a <;> rfl
    · rfl
  have ht : initialGiantFlag b d r ∘ initialCompleteIndexEquiv b d r =
      Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)) := by
    funext i
    exact initialGiantFlag_reindex b d r i
  have he := movingTaggedTransform_equiv (initialCompleteIndexEquiv b d r)
    (fun i => (x i : ℕ)) (fun i => NeZero.ne (x i : ℕ)) (initialGiantFlag b d r)
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav 1 s
  rw [hx, ht] at he
  rw [← he, movingTaggedTransform_spectator_split]
  · simp only [one_mul]
  · intro i
    exact NeZero.ne ((Fin.append sl sr i : P) : ℕ)
  · rintro (a | i)
    · cases a
      · exact NeZero.ne (XR : ℕ)
      · exact NeZero.ne (XL : ℕ)
    · exact NeZero.ne (y i : ℕ)

theorem initial_moving_tagged_zero (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (b r : ℕ) (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (D : ℕ) :
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
      (Sum.elim (fun _ => true) (fun _ => false))
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav D 0 = 0 := by
  unfold movingTaggedTransform
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl true))
  let c : ZMod (XL : ℕ) := ((D * tupleCofactor
    (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
    (Sum.inl true) : ℕ) : ZMod (XL : ℕ))⁻¹
  change (if fav (XL : ℕ) then complexUnitPhase (normalizedResidueFamily S (XL : ℕ)
    (((0 : ℤ) : ZMod (XL : ℕ)) * c)) else 0) = 0
  have hz : ((0 : ℤ) : ZMod (XL : ℕ)) * c = 0 := by simp
  rw [hz, normalizedResidueFamily_zero, complexUnitPhase_zero]
  split_ifs <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original Fourier coefficient after fixing the actual spectator list -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- Freezing spectators changes the Fourier scale by their exact product. -/
theorem initialMovingTuple_scale (P : Finset ℕ) (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (X : ℝ) :
    ((∏ i, ((initialMovingTuple b d r sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) / X =
      ((XL : ℕ) * (XR : ℕ) * (∏ i, (y i : ℕ)) : ℕ) /
        (X / ((∏ i, ((Fin.append sl sr i : P) : ℕ)) : ℕ)) := by
  rw [initialMovingTuple_product, Nat.cast_mul, div_div_eq_mul_div]
  ring

/-- Distinct original spectators give precisely the cofactor units used by
all later histories. Their transforms and the retained phase transform factor
without changing the original Fourier weight. -/
theorem initial_moving_coefficient (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr))
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ) :
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr
          (fun h => hij (hdistinct (Subtype.ext h)))
    let M := (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ)
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    primeTupleFourierCoefficient P
      (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
      ψ X V (initialMovingTuple b d r sl sr XL XR y) =
    ∑ s ∈ transferFrequencyRange V,
      normalizedFourierProfile (fun t => 𝓕 ψ t) s ((M : ℝ) / (X / (∏ i, q i : ℕ))) *
        (∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (normalizedResidueFamily S (q i))
          (initialSpectatorCofactor q hc i) () s) *
        movingTaggedTransform
          (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
          (Sum.elim (fun _ => true) (fun _ => false))
          (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro q hc M
  have : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
  unfold primeTupleFourierCoefficient
  apply Finset.sum_congr rfl
  intro s _
  rw [initialMovingTuple_scale]
  have hp : (∏ i, Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ))
      (fun i => (y i : ℕ)) i) = M := by
    simp only [Fintype.prod_sum_type, Fintype.prod_bool, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
      ite_false, if_false, ite_true, if_true]
    rfl
  have ht := initial_moving_transform P b d r S fav sl sr XL XR y s
  dsimp only at ht
  rw [hp] at ht
  change _ = movingRegularTransform q (fun i => normalizedResidueFamily S (q i)) M s * _ at ht
  rw [initial_spectator_transform q hc] at ht
  rw [ht]
  dsimp only [M, q]
  simp only [mul_assoc]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original logarithmic cutoffs depend only on retained bulk data -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_bulk {P : Type*} (b d r : ℕ)
    (sl : Fin d → P) (y : InitialRetainedSlot b r → P) (i : Fin b) :
    initialHalfAssemble b d r sl y (i.castAdd (d + r)).succ = y (.inr (.inl i)) := by
  change (Sum.elim sl y) ((initialSpectatorSlotEquiv b d r).symm
    (initialSpectatorSlotEquiv b d r (.inr (.inr (.inl i))))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem initialHalfCutoffWeight_assembled {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl : Fin d → P) (y : InitialRetainedSlot b r → P) :
    initialHalfCutoffWeight value b d r cb cd (Fin.tail (initialHalfAssemble b d r sl y)) =
      initialLogSumWeight value cb (fun i => y (.inr (.inl i))) *
        initialLogSumWeight value cd sl := by
  unfold initialHalfCutoffWeight
  simp only [Fin.tail, initialHalfAssemble_bulk, initialHalfAssemble_spectator]

theorem initialMovingTuple_cutoff {P : Type*} (value : P → ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    doubledHalfWeight (fun x : Fin (b + (d + r) + 1) → P =>
      (initialHalfCutoffWeight value b d r cb cd (Fin.tail x) : ℂ))
      (initialMovingTuple b d r sl sr XL XR y) =
    initialMovingCutoffWeight value b d r cb cd sl sr y := by
  let z : Bool ⊕ MovingRegularSlot 0 (r + r) (b + b) → P :=
    Sum.elim (fun a : Bool => if a then XL else XR) y
  have hx := initial_reassembled_moving_tuple b d r sl sr z
  change _ = initialMovingTuple b d r sl sr XL XR y at hx
  rw [← hx]
  simp only [doubledHalfWeight, Fin.append_left, Fin.append_right]
  change (initialHalfCutoffWeight value b d r cb cd
    (Fin.tail (initialHalfAssemble b d r sl (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inl))) : ℂ) *
      (initialHalfCutoffWeight value b d r cb cd
    (Fin.tail (initialHalfAssemble b d r sr (z ∘ initialRetainedIndexEquiv b r ∘ Sum.inr))) : ℂ) = _
  rw [initialHalfCutoffWeight_assembled, initialHalfCutoffWeight_assembled]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original distinct-prime test as the moving leaf's pairwise guard -/
namespace Ostmann
open scoped Classical

private theorem prime_list_pairwise_iff {I : Type*} (L : List I)
    (hnd : L.Nodup) (hcover : ∀ i, i ∈ L) (value : I → ℕ)
    (hp : ∀ i, (value i).Prime) :
    (L.map value).Pairwise Nat.Coprime ↔ Function.Injective value := by
  constructor
  · intro h i j hij
    by_contra hne
    have hs := List.pairwise_map.mp h
    have : Std.Symm (fun i j => (value i).Coprime (value j)) := ⟨fun _ _ h => h.symm⟩
    have hc := hs.forall (hcover i) (hcover j) hne
    rw [hij, Nat.coprime_self] at hc
    exact (hp j).ne_one hc
  · intro hinj
    apply List.pairwise_map.mpr
    apply hnd.imp
    intro i j hij
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

theorem initialMovingSlotList_nodup (r m d : ℕ) :
    (initialMovingSlotList r m d).Nodup := by
  unfold initialMovingSlotList
  apply List.nodup_append.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨by simp, ?_, ?_⟩
    · exact (movingTemplateSlotList_nodup 0 r m).map (by intro a b h; cases h; rfl)
    · intro a ha b hb hab
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      rcases ha with rfl | rfl <;> cases hab
  · exact (List.nodup_finRange d).map Sum.inl_injective
  · intro a ha b hb hab
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    rcases List.mem_append.mp ha with ha | ha
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> cases hab
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      cases hab

theorem mem_initialMovingSlotList (r m d : ℕ)
    (i : Fin d ⊕ (Bool ⊕ MovingRegularSlot 0 r m)) : i ∈ initialMovingSlotList r m d := by
  rcases i with i | (a | j)
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    cases a <;> simp
  · apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨j, mem_movingTemplateSlotList 0 r m j, rfl⟩

theorem initialMovingTuple_pairwise_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (((XL : ℕ) :: (XR : ℕ) ::
      (movingTemplateSlotList 0 (r + r) (b + b)).map (fun i => (y i : ℕ))) ++
      List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ))).Pairwise Nat.Coprime ↔
      Function.Injective (initialMovingTuple b d r sl sr XL XR y) := by
  let v : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b)) → P :=
    Sum.elim (Fin.append sl sr) (Sum.elim (fun a : Bool => if a then XL else XR) y)
  have h := prime_list_pairwise_iff (initialMovingSlotList (r + r) (b + b) (d + d))
    (initialMovingSlotList_nodup _ _ _) (mem_initialMovingSlotList _ _ _)
    (fun i => (v i : ℕ)) (fun i => hP (v i) (v i).property)
  have hmap : (initialMovingSlotList (r + r) (b + b) (d + d)).map (fun i => (v i : ℕ)) =
      ((XL : ℕ) :: (XR : ℕ) ::
        (movingTemplateSlotList 0 (r + r) (b + b)).map (fun i => (y i : ℕ))) ++
      List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)) := by
    simp only [initialMovingSlotList, List.map_append, List.map_cons,
      List.map_map, Function.comp_def, v, Sum.elim_inl, Sum.elim_inr,
      Bool.false_eq_true, ite_false, if_false, ite_true, if_true, List.cons_append, List.nil_append,
      List.ofFn_eq_map]
  rw [hmap] at h
  rw [h]
  have hc : Function.Injective (fun i => (v i : ℕ)) ↔ Function.Injective v := by
    constructor
    · intro hv i j hij
      exact hv (congrArg Subtype.val hij)
    · intro hv i j hij
      exact hv (Subtype.ext hij)
  rw [hc]
  have he : v = initialMovingTuple b d r sl sr XL XR y ∘ initialCompleteIndexEquiv b d r :=
    (initialMovingTuple_reindex b d r sl sr XL XR y).symm
  rw [he]
  exact (initialCompleteIndexEquiv b d r).injective_comp _

theorem initialMovingState_support_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ)
    (hs : s ≠ 0) (hXL : s.natAbs < (XL : ℕ)) (hXR : s.natAbs < (XR : ℕ)) :
    movingLocalSupport (fun p : P => (p : ℕ))
      (List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)))
      (initialMovingState P b r XL XR y s) ↔
      Function.Injective (initialMovingTuple b d r sl sr XL XR y) := by
  have hp := initialMovingTuple_pairwise_iff P hP b d r sl sr XL XR y
  constructor
  · intro h
    apply hp.mp
    simpa only [initialMovingState, movingLocalSupport, MovingSlotData.currentSlots,
      MovingSlotData.regularSlots, List.map_map, Function.comp_def] using h.1
  · intro h
    apply moving_local_support_prime_giants (V := s.natAbs) _ _ _ _ _
      (hP XL XL.property) (hP XR XR.property) hXL hXR
    · simpa only [initialMovingState, MovingSlotData.currentSlots,
        MovingSlotData.regularSlots, List.map_map, Function.comp_def] using hp.mpr h
    · exact ⟨hs, le_rfl⟩

theorem movingTemplateCoefficient_initial (P : Finset ℕ) (b r : ℕ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    movingTemplateCoefficient (fun p : P => (p : ℕ)) outside μ childBound pivotBound V
      F φ G 0 (r + r) (b + b) s y XL XR =
    movingGuardedLeaf (fun p : P => (p : ℕ)) outside F (initialMovingState P b r XL XR y s) s := by
  rw [movingTemplateCoefficient, movingFrequencyCoefficient_levelZero]
  unfold initialMovingState movingTemplateSlotList
  rw [List.map_append]
  rfl

theorem movingTemplateCoefficient_initial_supported (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (sl sr : Fin d → P)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ)
    (hs : s ≠ 0) (hXL : s.natAbs < (XL : ℕ)) (hXR : s.natAbs < (XR : ℕ)) :
    movingTemplateCoefficient (fun p : P => (p : ℕ))
      (List.ofFn (fun i : Fin (d + d) => ((Fin.append sl sr i : P) : ℕ)))
      μ childBound pivotBound V F φ G 0 (r + r) (b + b) s y XL XR =
    if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
      F (initialMovingState P b r XL XR y s) s else 0 := by
  rw [movingTemplateCoefficient_initial, movingGuardedLeaf]
  rw [initialMovingState_support_iff P hP b d r sl sr XL XR y s hs hXL hXR]
  split_ifs <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original cutoff weight as a function of the actual leaf data -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initialRegularFromList_mapped {P : Type*} (b r : ℕ) (fallback : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    initialRegularFromList b r fallback ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = y := by
  funext i
  unfold initialRegularFromList
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map] using ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i).isLt)]
  rw [List.getElem_map]
  change y ((movingTemplateSlotList 0 (r + r) (b + b)).get
    ((movingTemplateListEquiv 0 (r + r) (b + b)).symm i)) = y i
  rw [← movingTemplateListEquiv_apply, Equiv.apply_symm_apply]

theorem initialMovingDataCutoff_leaf (P : Finset ℕ) (b d r : ℕ)
    (cb cd : ℝ) (sl sr : Fin d → P) (fallback XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s v : ℤ) :
    initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback
      (initialMovingState P b r XL XR y s).data v =
      if v = 0 then 0 else initialMovingCutoffWeight (fun p : P => (p : ℕ))
        b d r cb cd sl sr y := by
  simp only [initialMovingDataCutoff, initialMovingState, MovingSlotData.regularSlots,
    initialRegularFromList_mapped]

theorem initialMovingState_modulus (P : Finset ℕ) (b r : ℕ)
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) :
    movingSlotModulus (fun p : P => (p : ℕ)) (initialMovingState P b r XL XR y s) =
      (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) := by
  have ht := movingTemplate_product (fun p : P => (p : ℕ)) 0 (r + r) (b + b) y
  have h : MovingSlotReversal.naturalProduct (fun p : P => (p : ℕ))
      ((movingTemplateSlotList 0 (r + r) (b + b)).map y) = ∏ i, (y i : ℕ) := by
    simpa only [MovingSlotReversal.naturalProduct, movingTemplateSlotList, List.map_append,
      List.map_map, Function.comp_def] using ht
  change (XL : ℕ) * (XR : ℕ) * _ = _
  rw [h]

theorem initialMovingLeaf_value {I : Type*} [Fintype I]
    (P : Finset ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (s : ℤ) (hs : s ≠ 0)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hw : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
      (((XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) : ℕ) : ℝ) / X ∈ Set.Icc lo hi) :
    movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback)
      g Dq Finset.univ (𝓕 ψ) X lo hi (initialMovingState P b r XL XR y s) s =
    initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y *
      normalizedFourierProfile (fun t => 𝓕 ψ t) s
        ((((XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ) : ℕ) : ℝ) / X) *
      ∏ i, spectatorHistoryLeaf (fun _ : Unit => (XL : ℕ) * (XR : ℕ) * ∏ j, (y j : ℕ))
        (g i) (Dq i) () s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_leaf]
  simp only [hs, ite_false, if_false]
  unfold movingFourierLeaf
  simp only [initialMovingState_modulus]
  by_cases hz : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y = 0
  · simp only [hz, ite_self, zero_mul]
  · rw [ite_eq_left (hw hz)]
    simp only [spectatorHistoryLeaf, initialMovingState_modulus]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAlphabetCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two original cutoff weights commute with the alphabet inclusion -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_map {A B : Type*} (e : B → A) (b r : ℕ)
    (fallback : B) (L : List B) :
    initialRegularFromList b r (e fallback) (L.map e) =
      e ∘ initialRegularFromList b r fallback L := by
  funext i
  simp only [initialRegularFromList, List.getD_map, Function.comp_apply]

theorem initialMovingCutoffWeight_map {A B : Type*} (e : B → A) (value : A → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → B)
    (y : MovingRegularSlot 0 (r + r) (b + b) → B) :
    initialMovingCutoffWeight value b d r cb cd (e ∘ sl) (e ∘ sr) (e ∘ y) =
      initialMovingCutoffWeight (value ∘ e) b d r cb cd sl sr y := rfl

theorem initialMovingDataCutoff_map {A B : Type*} (e : B → A) (value : A → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → B) (fallback : B)
    {n : ℕ} (T : MovingSlotData B n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd (e ∘ sl) (e ∘ sr) (e fallback) (T.map e) s =
      initialMovingDataCutoff (value ∘ e) b d r cb cd sl sr fallback T s := by
  simp only [initialMovingDataCutoff, MovingSlotData.regularSlots_map,
    initialRegularFromList_map, initialMovingCutoffWeight_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeAlphabet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws are independent of the containing prime alphabet -/
namespace Ostmann
open scoped Classical

theorem primeAlphabetEmbedding_range {P Q : Finset ℕ} (h : Q ⊆ P) (p : P) :
    p ∈ Set.range (primeAlphabetEmbedding h) ↔ (p : ℕ) ∈ Q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩

theorem primeSubsetPrior_alphabet_support {P Q S : Finset ℕ} (h : Q ⊆ P)
    (hS : S ⊆ Q) (p : P) (hp : primeSubsetPrior P S p ≠ 0) :
    p ∈ Set.range (primeAlphabetEmbedding h) :=
  (primeAlphabetEmbedding_range h p).mpr (hS (primeSubsetPrior_support P S p hp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmplitudeAlphabet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact restriction of the initial two-cutoff amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_initial_alphabet {A B I : Type}
    [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → B) (fallback : B)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot n r m → A → ℝ)
    (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e)
    (hν : ∀ i a, ν i a ≠ 0 → a ∈ Set.range e)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q
        (initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback))
        g Dq S ψ X lo hi) φ G n r m Pg ρ ν greg ggiant favorable =
    movingTemplatePrimeAmplitude (value ∘ e) outside (fun j a => μ j (e a))
      childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q
        (initialMovingDataCutoff (value ∘ e) b d rinit cb cd sl sr fallback)
        g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i a => ν i (e a)) greg ggiant favorable := by
  have hF : (fun {n} (T : MovingSlotData B n) s =>
      initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback)
        (T.map e) s) =
      (fun {n} (T : MovingSlotData B n) s =>
        initialMovingDataCutoff (value ∘ e) b d rinit cb cd sl sr fallback T s) := by
    funext n T s
    exact initialMovingDataCutoff_map e value b d rinit cb cd sl sr fallback T s
  have he := movingTemplatePrimeAmplitude_original_alphabet e q value outside μ childBound pivotBound V
      (initialMovingDataCutoff value b d rinit cb cd (e ∘ sl) (e ∘ sr) (e fallback))
      g Dq S ψ X lo hi φ G n r m Pg ρ ν hμ hν greg ggiant favorable
  rw [hF] at he
  exact he

theorem movingTemplatePrimeAmplitude_initial_prime_alphabet {I : Type}
    (P Q : Finset ℕ) (hQP : Q ⊆ P) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
    (b d rinit : ℕ) (cb cd : ℝ) (sl sr : Fin d → Q) (fallback : Q)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (Qν : MovingRegularSlot n r m → Finset ℕ)
    (hμ : ∀ j, j < n → Qμ j ⊆ Q) (hν : ∀ i, Qν i ⊆ Q)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude Subtype.val outside (fun j => primeSubsetPrior P (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd
          (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)
          (primeAlphabetEmbedding hQP fallback)) g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i => primeSubsetPrior P (Qν i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude Subtype.val outside (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d rinit cb cd sl sr fallback)
        g Dq S ψ X lo hi)
      φ G n r m Pg ρ (fun i => primeSubsetPrior Q (Qν i)) greg ggiant favorable := by
  exact movingTemplatePrimeAmplitude_initial_alphabet (primeAlphabetEmbedding hQP) q
    Subtype.val outside (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V
    b d rinit cb cd sl sr fallback g Dq S ψ X lo hi φ G n r m Pg ρ
    (fun i => primeSubsetPrior P (Qν i))
    (fun j a hj ha => primeSubsetPrior_alphabet_support hQP (hμ j hj) a ha)
    (fun i a ha => primeSubsetPrior_alphabet_support hQP (hν i) a ha)
    greg ggiant favorable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTreeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialMovingRealWeight_cast {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (initialMovingRealWeight value b d r cb cd sl sr y : ℂ) =
      initialMovingCutoffWeight value b d r cb cd sl sr y := by
  exact Complex.ofReal_mul _ _

theorem initialMovingDataCutoff_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T s =
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback T.regularSlots) : ℂ) *
        (if s = 0 then 0 else 1) := by
  rw [initialMovingRealWeight_cast]
  unfold initialMovingDataCutoff
  split_ifs <;> simp only [mul_zero, mul_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkLists
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two actual half-bulk cutoffs are independent of restored small slots -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialRegularFromList_bulk {P : Type*} (b r : ℕ) (fallback : P)
    (small : List P) (hsmall : small.length = r + r)
    (bulk : Fin (b + b) → P) (i : Fin (b + b)) :
    initialRegularFromList b r fallback (small ++ List.ofFn bulk) ((), .inr i) = bulk i := by
  let y : MovingRegularSlot 0 (r + r) (b + b) → P :=
    fun j => Sum.elim (fun z => small.get (Fin.cast hsmall.symm z)) bulk j.2
  have hlist : (movingTemplateSlotList 0 (r + r) (b + b)).map y =
      small ++ List.ofFn bulk := by
    simp only [movingTemplateSlotList, movingTemplateSmall, bulkSlotLeaves,
      treeLeafTupleEquiv, Equiv.coe_fn_symm_mk, flattenMovingSlots, List.map_append,
      List.map_ofFn, Function.comp_def, y, movingTemplateBulk, Sum.elim_inl,
      ]
    congr 1
    exact (List.ofFn_congr hsmall small.get).symm.trans (List.ofFn_get small)
  have h := congrFun (initialRegularFromList_mapped b r fallback y) ((), .inr i)
  simpa only [hlist, y, Sum.elim_inr] using h

theorem initialMovingRealWeight_list {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (small : List P) (hsmall : small.length = r + r) (bulk : Fin (b + b) → P) :
    initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback (small ++ List.ofFn bulk)) =
      initialHalfBulkWeight value b d cb cd sl sr bulk := by
  unfold initialMovingRealWeight initialHalfBulkWeight
  simp only [initialRegularFromList_bulk b r fallback small hsmall bulk]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

theorem moving_append_length_eq {P : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List P) n) (a b : ℕ)
    (hx : MovingLeafLengthEq n x a) (hy : MovingLeafLengthEq n y b) :
    MovingLeafLengthEq n (appendMovingSlotLeaves n x y) (a + b) := by
  induction n with
  | zero => exact (List.length_append).trans (congrArg₂ (· + ·) hx hy)
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length_eq {P : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → P) n) :
    MovingLeafLengthEq n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

theorem initialMovingTreeWeight_sample {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P) (a : MovingSampleSlots P n)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r) :
    initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small (bulkSlotLeaves n (b + b) slot) a) =
      initialHalfBulkProduct value b d cb cd sl sr n slot := by
  induction a generalizing s with
  | leaf =>
    change initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback ((show List P from small) ++ List.ofFn (fun i => slot ((), i)))) = _
    exact initialMovingRealWeight_list value b d r cb cd sl sr fallback small
      (hsmall.trans (by omega)) _
  | @node n samples left right ihL ihR =>
    have hl : 4 + s + 4 * n = r + r := by omega
    change initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.1
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inl j.1, j.2))) left) *
      initialMovingTreeWeight value b d r cb cd sl sr fallback
        (buildMovingSlotData n t.2.2
          (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
          (bulkSlotLeaves n (b + b) (fun j => slot (.inr j.1, j.2))) right) = _
    rw [ihL _ _ _ _ (moving_append_length_eq n _ _ 4 s
      (moving_compensation_length_eq n samples) hsmall.1) hl,
      ihR _ _ _ _ (moving_append_length_eq n _ _ 4 s
        (moving_compensation_length_eq n samples) hsmall.2) hl]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingRecursiveWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_initial_halves {σ : Type*} (value : σ → ℕ) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → σ) (fallback : σ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
          (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          F cutoff n ⟨n, T, XL, XR⟩ t := by
  induction T generalizing XL XR with
  | leaf => rfl
  | @node n s CL CR U left right ihL ihR =>
    simp only [recursiveTransferWeight]
    split_ifs
    · simp only [movingSlotSystem, MovingSlotState.child, ite_true, if_true,
        Bool.false_eq_true, ite_false, if_false] at ihL ihR ⊢
      rw [ihL, ihR]
      simp only [initialMovingTreeWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingCoefficientFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact half-bulk factorization under the unchanged compensation law -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_initial_halves {P : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List P) n)
    (XL XR : ℕ) (a : MovingSampleSlots P n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small bulk XL XR a =
    (initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small bulk a) : ℂ) *
      movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_initial_halves]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

theorem movingSupportedSampledWeight_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedSampleTerm_initial_halves,
    initialMovingTreeWeight_sample value b d r cb cd sl sr fallback n s t small slot a hsmall hlen]
  ring

theorem movingFrequencyCoefficient_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n a : ℕ) (s : ℤ) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r)
    (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_initial_halves value b d r cb cd sl sr fallback
    outside μ childBound pivotBound F _ n a _ small slot hsmall hlen XL XR, Finset.mul_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingOriginalFactor
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the genuine half-list weights in the original Fourier coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalLeaf_initial_halves {P I : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (x : MovingSlotState P) (s : ℤ) :
    movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi x s =
    (initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
  unfold movingOriginalLeaf movingWindowLeaf movingDataLeaf
  dsimp only
  rw [initialMovingDataCutoff_factor]
  split_ifs <;> ring

theorem movingFrequencyCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List P) n) (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR := by
  have he : movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      g Dq S ψ X lo hi = fun x s =>
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) *
      movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi x s := by
    funext x s
    exact movingOriginalLeaf_initial_halves value b d r cb cd sl sr fallback q g Dq S ψ X lo hi x s
  rw [he]
  exact movingFrequencyCoefficient_initial_halves value b d r cb cd sl sr fallback outside μ
    childBound pivotBound V _ φ G n a s small slot hsmall hlen XL XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingTemplateProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic product bounds from the literal two-half initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLeafLengthEq_map {P Q : Type*} (f : P → Q) (n : ℕ)
    (x : TreeLeafTuple (List P) n) (a : ℕ) (hx : MovingLeafLengthEq n x a) :
    MovingLeafLengthEq n (treeLeafMap (List.map f) n x) a := by
  induction n with
  | zero => simpa only [MovingLeafLengthEq, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length_eq {P : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → P) :
    MovingLeafLengthEq n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih =>
    change MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSmallPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Permuting small slots preserves the literal initial coefficient -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateCoefficient_original_initial_halves {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n (y ∘ movingTemplateBulk n a (b + b)) : ℂ) *
      movingTemplateCoefficient value outside μ childBound pivotBound V
        (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n a (b + b) s y XL XR := by
  unfold movingTemplateCoefficient
  rw [bulkSlotLeaves_map]
  exact movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s _ _
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR

theorem movingTemplateCoefficient_zero_small_perm {P I : Type} [Fintype P]
    (value : P → ℕ) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (f : ℤ → ℂ) (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (r m : ℕ) (s : ℤ)
    (e : Equiv.Perm (Fin r)) (y : MovingRegularSlot 0 r m → P) (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 r m s
      (y ∘ movingSmallSlotEquiv 0 m e) XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G 0 r m s y XL XR := by
  unfold movingTemplateCoefficient
  simp only [movingTemplateSmall, bulkSlotLeaves, treeLeafTupleEquiv, treeLeafMap,
    Equiv.coe_fn_symm_mk, movingTemplateBulk, movingSmallSlotEquiv, Function.comp_def,
    Equiv.prodCongr_apply, List.map_ofFn]
  apply movingFrequencyCoefficient_zero_small_perm
  change (List.ofFn ((fun i => y ((), Sum.inl i)) ∘ e)).Perm
    (List.ofFn (fun i => y ((), Sum.inl i)))
  exact e.ofFn_comp_perm _

theorem movingTemplateCoefficient_initial_zero_small_perm {P I : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (s : ℤ)
    (e : Equiv.Perm (Fin (r + r))) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (XL XR : ℕ) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) s
      (y ∘ movingSmallSlotEquiv 0 (b + b) e) XL XR =
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) s y XL XR := by
  rw [movingTemplateCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G 0 (r + r) s _ (by omega),
    movingTemplateCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G 0 (r + r) s _ (by omega)]
  rw [movingTemplateCoefficient_zero_small_perm value q _ g Dq S ψ X lo hi outside μ
    childBound pivotBound V φ G (r + r) (b + b) s e y XL XR]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialAmplitudePermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reordering actual small-cell laws preserves the initial amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem finite_prior_reindex_invariant {V A : Type*} [Fintype V] [Fintype A]
    (e : Equiv.Perm V) (ν : V → A → ℝ) (F : (V → A) → ℂ)
    (hF : ∀ x, F (x ∘ e.symm) = F x) :
    (∑ x : V → A, ((∏ i, ν (e i) (x i) : ℝ) : ℂ) * F x) =
      ∑ x : V → A, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x := by
  have he := finite_prior_reindex e ν F
  simpa only [hF] using he

theorem movingTaggedTransform_small_perm {A : Type} (value : A → ℕ)
    (hvalue : ∀ a, value a ≠ 0) (r m : ℕ) (e : Equiv.Perm (Fin r))
    (y : MovingRegularSlot 0 r m → A) (XL XR : ℕ) (hXL : XL ≠ 0) (hXR : XR ≠ 0)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then XL else XR)
        (value ∘ (y ∘ movingSmallSlotEquiv 0 m e)))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s =
    movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then XL else XR) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  let E := Equiv.sumCongr (Equiv.refl Bool) (movingSmallSlotEquiv 0 m e)
  let p : Bool ⊕ MovingRegularSlot 0 r m → ℕ :=
    Sum.elim (fun a : Bool => if a then XL else XR) (value ∘ y)
  have hp : ∀ i, p i ≠ 0 := by
    intro i
    rcases i with a | i
    · cases a <;> assumption
    · exact hvalue _
  have hpull : p ∘ E = Sum.elim (fun a : Bool => if a then XL else XR)
      (value ∘ (y ∘ movingSmallSlotEquiv 0 m e)) := by
    funext i
    cases i <;> rfl
  have hflag : (Sum.elim (fun _ : Bool => true)
      (fun _ : MovingRegularSlot 0 r m => false)) ∘ E =
      Sum.elim (fun _ => true) (fun _ => false) := by
    funext i
    cases i <;> rfl
  have he := movingTaggedTransform_equiv E p hp
    (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s
  rw [hpull, hflag] at he
  exact he

theorem movingTemplatePrimeAmplitude_small_perm {A : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState A → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ) (r m : ℕ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 r m → A → ℝ) (e : Equiv.Perm (Fin r))
    (hC : ∀ s y XL XR,
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s
        (y ∘ movingSmallSlotEquiv 0 m e.symm) XL XR =
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s
        y XL XR)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G 0 r m Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 m e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G 0 r m Pg ρ
      ν greg ggiant favorable := by
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  apply congrArg (fun z : ℂ => (ρ XL : ℂ) * z)
  apply Finset.sum_congr rfl
  intro XR _
  apply congrArg (fun z : ℂ => (ρ XR : ℂ) * z)
  apply Finset.sum_congr rfl
  intro s _
  let term := fun y : MovingRegularSlot 0 r m → A =>
    movingTemplateCoefficient value outside μ childBound pivotBound V F φ G 0 r m s.val
      y XL XR * movingTaggedTransform
      (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (value ∘ y))
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable outside.prod s.val
  have hterm : ∀ y, term (y ∘ (movingSmallSlotEquiv 0 m e).symm) = term y := by
    intro y
    change term (y ∘ movingSmallSlotEquiv 0 m e.symm) = term y
    dsimp only [term]
    rw [hC]
    rw [movingTaggedTransform_small_perm value hvalue r m e.symm y XL XR
      (hPg _ XL.property) (hPg _ XR.property)]
  have he := finite_prior_reindex_invariant (movingSmallSlotEquiv 0 m e) ν term hterm
  simpa only [term, finite_univ_canonical] using he

theorem movingTemplatePrimeAmplitude_initial_small_permutation {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (ν : MovingRegularSlot 0 (r + r) (b + b) → A → ℝ)
    (e : Equiv.Perm (Fin (r + r)))
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 (b + b) e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ ν greg ggiant favorable := by
  exact movingTemplatePrimeAmplitude_small_perm value hvalue outside μ childBound pivotBound V
    _ φ G (r + r) (b + b) Pg hPg ρ ν e
    (fun s y XL XR => movingTemplateCoefficient_initial_zero_small_perm value b d r cb cd
      sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G s
      e.symm y XL XR) greg ggiant favorable

theorem movingTemplatePrimeAmplitude_initial_small_equiv {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (rnew : ℕ) (ν : MovingRegularSlot 0 rnew (b + b) → A → ℝ)
    (e : Fin (r + r) ≃ Fin rnew)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 (r + r) (b + b) Pg ρ
      (fun i => ν (movingSmallSlotEquiv 0 (b + b) e i)) greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G 0 rnew (b + b) Pg ρ ν greg ggiant favorable := by
  have hr : r + r = rnew := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst rnew
  exact movingTemplatePrimeAmplitude_initial_small_permutation value hvalue b d r cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G Pg hPg ρ ν e
    greg ggiant favorable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellSchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual four-at-a-time compensation cell schedule -/
namespace Ostmann
open scoped Classical

theorem initialSmallCellList_schedule_perm (top : ℕ) (cs : List ℕ) :
    (initialSmallCellList top cs ++ initialSmallCellList top cs).Perm
      (scheduledSmallCellList top cs) := by
  let T := List.replicate 3 top
  let U := cs.flatMap (fun c => [c, c])
  have hswap : ((T ++ U) ++ (T ++ U)).Perm ((T ++ T) ++ (U ++ U)) := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := U) (l₂ := T)).append_right U).append_left T
  have hflat : (U ++ U).Perm (cs.flatMap (fun c => List.replicate 4 c)) := by
    simpa only [U, List.replicate_succ, List.replicate_zero, List.cons_append,
      List.nil_append] using List.flatMap_append_perm cs (fun c => [c, c]) (fun c => [c, c])
  have htop : T ++ T = List.replicate 6 top := by
    dsimp only [T]
    rfl
  exact (hswap.trans ((List.Perm.refl _).append hflat)).trans
    (by simpa only [htop, scheduledSmallCellList] using
      (List.perm_append_comm (l₁ := List.replicate 6 top)
        (l₂ := cs.flatMap (fun c => List.replicate 4 c))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialCellScheduleEquiv
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exact index bijection for the two original cell lists -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallCell_ofFn (top : ℕ) (cs : List ℕ) :
    List.ofFn (scheduledSmallCell top cs) = scheduledSmallCellList top cs := by
  induction cs with
  | nil => exact List.ofFn_const 6 top
  | cons c cs ih =>
    change List.ofFn (Fin.append (fun _ : Fin 4 => c) (scheduledSmallCell top cs)) = _
    rw [List.ofFn_fin_append, List.ofFn_const, ih]
    rfl

theorem ofFn_perm_index_equiv {n m : ℕ} (f : Fin n → ℕ) (g : Fin m → ℕ)
    (h : (List.ofFn f).Perm (List.ofFn g)) :
    ∃ e : Fin n ≃ Fin m, ∀ i, g (e i) = f i := by
  let E : Fin (List.ofFn f).length ≃ Fin (List.ofFn g).length :=
    ⟨h.idxBij, h.symm.idxBij, fun _ => h.idxBij_symm_idxBij,
      fun _ => h.idxBij_idxBij_symm⟩
  let e := ((finCongr (List.length_ofFn (f := f)).symm).trans E).trans
    (finCongr (List.length_ofFn (f := g)))
  refine ⟨e, ?_⟩
  intro i
  have hi := h.getElem_idxBij_eq_getElem ((finCongr (List.length_ofFn (f := f)).symm) i)
  simp only [List.getElem_ofFn] at hi
  convert hi using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)

theorem initialCellSchedule_index_equiv (top : ℕ) (cs : List ℕ) :
    let cells := initialSmallCellList top cs
    ∃ e : Fin (cells.length + cells.length) ≃ Fin (scheduledSmallLength cs),
      ∀ i, scheduledSmallCell top cs (e i) = Fin.append cells.get cells.get i := by
  intro cells
  apply ofFn_perm_index_equiv
  rw [List.ofFn_fin_append]
  simp only [List.ofFn_get, scheduledSmallCell_ofFn]
  exact initialSmallCellList_schedule_perm top cs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialScheduledPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected original priors in compensation order -/
namespace Ostmann
open scoped Classical

theorem initialMovingRegularPrior_cell_reindex {A : Type}
    (cell : ℕ → A → ℝ) (bulk : A → ℝ) (top : ℕ) (cs : List ℕ) (b : ℕ) :
    let cells := initialSmallCellList top cs
    ∃ e : Fin (cells.length + cells.length) ≃ Fin (scheduledSmallLength cs),
      initialMovingRegularPrior b cells.length (fun _ => bulk) (fun i => cell (cells.get i)) =
        fun i => scheduledRegularPrior cell bulk top cs 0 (b + b)
          (movingSmallSlotEquiv 0 (b + b) e i) := by
  intro cells
  obtain ⟨e, he⟩ := initialCellSchedule_index_equiv top cs
  refine ⟨e, ?_⟩
  funext i
  rcases i with ⟨j, i | i⟩
  · change Fin.append (fun i => cell (cells.get i)) (fun i => cell (cells.get i)) i =
      cell (scheduledSmallCell top cs (e i))
    rw [he]
    change Fin.append (fun i => cell (cells.get i)) (fun i => cell (cells.get i)) i =
      cell (Fin.append cells.get cells.get i)
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  · change Fin.append (fun _ : Fin b => bulk) (fun _ : Fin b => bulk) i = bulk
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]

theorem scheduledRegularPrior_prime (cell : ℕ → Finset ℕ) (bulk P : Finset ℕ)
    (top : ℕ) (cs : List ℕ) (n m : ℕ) :
    scheduledRegularPrior (fun j => primeSubsetPrior P (cell j))
      (primeSubsetPrior P bulk) top cs n m =
      fun i => primeSubsetPrior P (scheduledRegularPrimeSets cell bulk top cs n m i) := by
  funext i
  rcases i with ⟨j, i | i⟩ <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialScheduledAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal initial amplitude starts the compensation schedule -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplatePrimeAmplitude_initial_schedule {A J : Type} [Fintype A]
    (value : A → ℕ) (hvalue : ∀ a, value a ≠ 0)
    (b d top : ℕ) (cs : List ℕ) (cb cd : ℝ) (sl sr : Fin d → A) (fallback : A)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → A → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Pg : Finset ℕ) (hPg : ∀ p ∈ Pg, p ≠ 0) (ρ : Pg → ℝ)
    (cell : ℕ → A → ℝ) (bulk : A → ℝ)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    let cells := initialSmallCellList top cs
    let F := movingOriginalLeaf value q
      (initialMovingDataCutoff value b d cells.length cb cd sl sr fallback) g Dq S ψ X lo hi
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
      0 (cells.length + cells.length) (b + b) Pg ρ
      (initialMovingRegularPrior b cells.length (fun _ => bulk) (fun i => cell (cells.get i)))
      greg ggiant favorable =
    movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G
      0 (scheduledSmallLength cs) (b + b) Pg ρ
      (scheduledRegularPrior cell bulk top cs 0 (b + b)) greg ggiant favorable := by
  intro cells F
  obtain ⟨e, he⟩ := initialMovingRegularPrior_cell_reindex cell bulk top cs b
  rw [he]
  exact movingTemplatePrimeAmplitude_initial_small_equiv value hvalue b d cells.length cb cd
    sl sr fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G Pg hPg ρ
    (scheduledSmallLength cs) (scheduledRegularPrior cell bulk top cs 0 (b + b)) e
    greg ggiant favorable

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothGiantActiveSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size and separation on the support of the smooth giant law -/

namespace Ostmann

theorem smoothGiantPrior_active_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (G : ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (p : P) (hp : smoothGiantPrior P φ G p ≠ 0) :
    Real.exp (G - 1) < (p : ℝ) ∧ (p : ℝ) < Real.exp (G + 1) := by
  have hφ : φ (Real.log (p : ℕ) - G) ≠ 0 := by
    intro h
    apply hp
    simp only [smoothGiantPrior, h, mul_zero, zero_div]
  have habs : |Real.log (p : ℕ) - G| < 1 := lt_of_not_ge (fun h => hφ (hout _ h))
  have hpos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (hP _ p.property).pos
  constructor
  · apply (Real.exp_lt_exp.mpr (show G - 1 < Real.log (p : ℕ) by linarith [(abs_lt.mp habs).1])).trans_eq
    exact Real.exp_log hpos
  · rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr (by linarith [(abs_lt.mp habs).2])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPrimeRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Live prime ranges of the selected finite schedule -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallCell_property (P : ℕ → Prop) (top : ℕ) (cs : List ℕ)
    (htop : P top) (hcs : ∀ c ∈ cs, P c) :
    ∀ i, P (scheduledSmallCell top cs i) := by
  induction cs with
  | nil => exact fun _ => htop
  | cons c cs ih =>
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [scheduledSmallCell, Fin.append_left] using hcs c (by simp)
    · simpa only [scheduledSmallCell, Fin.append_right] using
        ih (fun d hd => hcs d (by simp [hd])) j

theorem mem_initialSmallCellList_of_eq_or_mem (top : ℕ) (cs : List ℕ) (j : ℕ)
    (h : j = top ∨ j ∈ cs) : j ∈ initialSmallCellList top cs := by
  rcases h with rfl | hj
  · simp [initialSmallCellList]
  · simp only [initialSmallCellList, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨j, hj, by simp⟩

theorem scheduledSmallCell_mem_initial (top : ℕ) (cs : List ℕ) (j : ℕ)
    (i : Fin (scheduledSmallLength (cs.drop j))) :
    scheduledSmallCell top (cs.drop j) i ∈ initialSmallCellList top cs := by
  apply scheduledSmallCell_property
  · exact mem_initialSmallCellList_of_eq_or_mem top cs top (Or.inl rfl)
  · intro c hc
    exact mem_initialSmallCellList_of_eq_or_mem top cs c
      (Or.inr (List.mem_of_mem_drop hc))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAmplitudeAlphabet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scheduled initial weight restricts to its actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem scheduledCellAmplitude_initial_prime_alphabet {J : Type}
    (P Q : Finset ℕ) (hQP : Q ⊆ P) (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (Qμ cell : ℕ → Finset ℕ) (bulk : Finset ℕ)
    (childBound pivotBound V : ℕ → ℕ)
    (b d top : ℕ) (cs : List ℕ) (cb cd : ℝ) (sl sr : Fin d → Q) (fallback : Q)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (Pg : Finset ℕ) (ρ : Pg → ℝ)
    (hμ : ∀ j, j < n → Qμ j ⊆ Q)
    (hcell : ∀ c ∈ initialSmallCellList top cs, cell c ⊆ Q) (hbulk : bulk ⊆ Q)
    (greg ggiant : ∀ p : ℕ, ZMod p → ℂ) (favorable : ℕ → Bool) :
    scheduledCellAmplitude Subtype.val outside (fun j => primeSubsetPrior P (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd
          (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)
          (primeAlphabetEmbedding hQP fallback)) g Dq S ψ X lo hi)
      φ G Pg ρ (fun c => primeSubsetPrior P (cell c)) (primeSubsetPrior P bulk)
      top cs n (b + b) greg ggiant favorable =
    scheduledCellAmplitude Subtype.val outside (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V
      (movingOriginalLeaf Subtype.val q
        (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd
          sl sr fallback) g Dq S ψ X lo hi)
      φ G Pg ρ (fun c => primeSubsetPrior Q (cell c)) (primeSubsetPrior Q bulk)
      top cs n (b + b) greg ggiant favorable := by
  unfold scheduledCellAmplitude
  rw [scheduledRegularPrior_prime, scheduledRegularPrior_prime]
  apply movingTemplatePrimeAmplitude_initial_prime_alphabet P Q hQP q outside Qμ
    childBound pivotBound V b d (initialSmallCellList top cs).length cb cd sl sr fallback
    g Dq S ψ X lo hi φ G n (scheduledSmallLength (cs.drop n)) (b + b) Pg ρ
    (scheduledRegularPrimeSets cell bulk top (cs.drop n) n (b + b)) hμ
  intro i
  rcases i with ⟨u, j | j⟩
  · exact hcell _ (scheduledSmallCell_mem_initial top cs n j)
  · exact hbulk

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original kernel at level zero of the moving iteration -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initial_moving_kernel (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr))
    (fallback XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (hXL : V 0 < (XL : ℕ)) (hXR : V 0 < (XR : ℕ))
    (hwindow : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
      ((∏ i, ((initialMovingTuple b d r sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) / X ∈
        Set.Icc lo hi) :
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (X / (∏ i, q i : ℕ)) lo hi
    initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y *
      (if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
        primeTupleFourierCoefficient P
          (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
            (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
          ψ X (V 0) (initialMovingTuple b d r sl sr XL XR y) else 0) =
    ∑ s ∈ transferFrequencyRange (V 0),
      movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
        F φ G 0 (r + r) (b + b) s y XL XR *
      movingTaggedTransform
        (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
        (Sum.elim (fun _ => true) (fun _ => false))
        (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro q hc inst F
  have : ∀ i, Fact (q i).Prime := inst
  let W := initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y
  let M := (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ)
  let T := fun s : ℤ => movingTaggedTransform
    (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
    (Sum.elim (fun _ => true) (fun _ => false))
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s
  have hwin : W ≠ 0 → (M : ℝ) / (X / (∏ i, q i : ℕ)) ∈ Set.Icc lo hi := by
    intro hw
    have hh := hwindow hw
    rw [initialMovingTuple_scale] at hh
    exact hh
  have hpoint (s : ℤ) (hs : s ∈ transferFrequencyRange (V 0)) :
      movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
        F φ G 0 (r + r) (b + b) s y XL XR * T s =
      W * (if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
        normalizedFourierProfile (fun t => 𝓕 ψ t) s ((M : ℝ) / (X / (∏ i, q i : ℕ))) *
          (∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (normalizedResidueFamily S (q i))
            (initialSpectatorCofactor q hc i) () s) * T s else 0) := by
    by_cases hs0 : s = 0
    · subst s
      have ht : T 0 = 0 := initial_moving_tagged_zero P b r S fav XL XR y _
      rw [ht]
      split_ifs <;> simp only [mul_zero]
    · have hsV := (mem_transferFrequencyRange (V 0) s).mp hs
      rw [movingTemplateCoefficient_initial_supported P hP b d r sl sr μ childBound pivotBound V
        F φ G XL XR y s hs0 (hsV.trans_lt hXL) (hsV.trans_lt hXR)]
      have hv := initialMovingLeaf_value P b d r cb cd sl sr fallback XL XR y s hs0
        q (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) ψ
        (X / (∏ i, q i : ℕ)) lo hi hwin
      change F (initialMovingState P b r XL XR y s) s = _ at hv
      rw [hv]
      split_ifs <;> ring
  by_cases hx : Function.Injective (initialMovingTuple b d r sl sr XL XR y)
  · simp only [hx, ite_true, if_true]
    rw [initial_moving_coefficient P hP b d r S fav sl sr hdistinct XL XR y ψ X (V 0)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simpa only [hx, ite_true, if_true] using (hpoint s hs).symm
  · simp only [hx, ite_false, if_false, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    simpa only [hx, ite_false, if_false, mul_zero] using hpoint s hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initial_frozen_moving_amplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr)) (fallback : P)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hlarge : ∀ p : P, μg p ≠ 0 → V 0 < (p : ℕ))
    (hwindow : ∀ (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P),
      μg XL ≠ 0 → μg XR ≠ 0 →
      (∏ i, initialMovingRegularPrior b r μb μc i (y i)) ≠ 0 →
      initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
      ((∏ i, ((initialMovingTuple b d r sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) / X ∈
        Set.Icc lo hi) :
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (X / (∏ i, q i : ℕ)) lo hi
    initialFrozenAmplitude P b d r μg μb μc
      (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
      ψ X (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + r) + 1) → P =>
        (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd (Fin.tail x) : ℂ))) sl sr =
    movingTemplatePrimeAmplitude (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
      F φ G 0 (r + r) (b + b) P μg (initialMovingRegularPrior b r μb μc)
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav := by
  intro q hc inst F
  have : ∀ i, Fact (q i).Prime := inst
  rw [initialFrozenAmplitude_moving]
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  by_cases hXL : μg XL = 0
  · simp only [hXL, Complex.ofReal_zero, zero_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  by_cases hXR : μg XR = 0
  · simp only [hXR, Complex.ofReal_zero, zero_mul]
  congr 1
  have hsum := Finset.sum_coe_sort (transferFrequencyRange (V 0)) (fun s : ℤ =>
    ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q)
          μ childBound pivotBound V F φ G 0 (r + r) (b + b) s y XL XR *
          movingTaggedTransform
            (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
            (Sum.elim (fun _ => true) (fun _ => false))
            (normalizedResidueFamily S) (normalizedResidueFamily S) fav (List.ofFn q).prod s))
  simp only [finite_univ_canonical, Function.comp_def] at hsum ⊢
  rw [hsum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : (∏ i, initialMovingRegularPrior b r μb μc i (y i)) = 0
  · simp only [finite_univ_canonical] at hy
    simp only [hy, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
  rw [← Finset.mul_sum]
  congr 1
  rw [initialMovingTuple_cutoff]
  simpa only [List.prod_ofFn, Function.comp_def] using
    initial_moving_kernel P hP b d r cb cd sl sr hdistinct fallback XL XR y S fav ψ X lo hi
      μ childBound pivotBound V φ G (hlarge XL hXL) (hlarge XR hXR) (hwindow XL XR y hXL hXR hy)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Live original tuples after the spectator coordinates are fixed -/
namespace Ostmann
open scoped Classical BigOperators

theorem initialHalfAssemble_prior {P : Type*} (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) :
    initialHalfAssemble b d r μd (Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)) =
      Fin.cons μg (Fin.append μb (Fin.append μd μc)) := by
  funext j
  obtain ⟨i, rfl⟩ := (initialSpectatorSlotEquiv b d r).surjective j
  rcases i with i | (u | (i | i)) <;>
    simp [initialHalfAssemble, initialSpectatorSlotEquiv]

theorem initial_full_prior_reindex {P : Type*} (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (i : Fin (d + d) ⊕ (Bool ⊕ MovingRegularSlot 0 (r + r) (b + b))) :
    let ν : Fin (b + (d + r) + 1) → P → ℝ := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    Fin.append ν ν (initialCompleteIndexEquiv b d r i) =
      Sum.elim (Fin.append μd μd)
        (Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc)) i := by
  intro ν
  let ρ := Sum.elim (fun _ : Unit => μg) (Sum.elim μb μc)
  have h := initialCompleteIndexEquiv_assemble b d r μd μd ρ ρ
  rw [initialHalfAssemble_prior] at h
  have hr : Sum.elim ρ ρ ∘ (initialRetainedIndexEquiv b r).symm =
      Sum.elim (fun _ : Bool => μg) (initialMovingRegularPrior b r μb μc) := by
    funext j
    have hh := initial_retained_prior b r μg μb μc ((initialRetainedIndexEquiv b r).symm j)
    rw [Equiv.apply_symm_apply] at hh
    exact hh
  rw [hr] at h
  exact congrFun h i

theorem initialMovingTuple_prior_nonzero {P : Type*} [Fintype P] (b d r : ℕ)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (sl sr : Fin d → P) (hs : ∀ i, μd i (sl i) ≠ 0) (ht : ∀ i, μd i (sr i) ≠ 0)
    (XL XR : P) (hXL : μg XL ≠ 0) (hXR : μg XR ≠ 0)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : (∏ i, initialMovingRegularPrior b r μb μc i (y i)) ≠ 0) :
    let ν : Fin (b + (d + r) + 1) → P → ℝ := Fin.cons μg (Fin.append μb (Fin.append μd μc))
    productPrior (Fin.append ν ν) (initialMovingTuple b d r sl sr XL XR y) ≠ 0 := by
  intro ν
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  obtain ⟨j, rfl⟩ := (initialCompleteIndexEquiv b d r).surjective i
  rw [initial_full_prior_reindex]
  have hx := congrFun (initialMovingTuple_reindex b d r sl sr XL XR y) j
  change initialMovingTuple b d r sl sr XL XR y (initialCompleteIndexEquiv b d r j) = _ at hx
  rw [hx]
  rcases j with j | (a | j)
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa only [Sum.elim_inl, Fin.append_left] using hs k
    · simpa only [Sum.elim_inl, Fin.append_right] using ht k
  · cases a <;> assumption
  · exact (Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialDoubledCutoffProduct
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product windows on both actual copies of the weighted initial list -/
namespace Ostmann
open scoped Classical BigOperators

theorem initial_doubled_cutoff_log_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    |Real.log (∏ i, (x i : ℝ)) - 2 * (G + cb + cd + ∑ i, center i)| ≤ 2 * (r + 3) := by
  let n := (b + (d + r)) + 1
  let xl : Fin n → P := fun i => x (i.castAdd n)
  let xr : Fin n → P := fun i => x (i.natAdd n)
  let ν : Fin n → P → ℝ := Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))
  have hp : productPrior ν xl ≠ 0 ∧ productPrior ν xr ≠ 0 := by
    unfold productPrior at hprior ⊢
    rw [Fin.prod_univ_add] at hprior
    simpa only [Fin.append_left, Fin.append_right, ne_eq, mul_eq_zero, not_or] using hprior
  have hw' : (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xl) : ℂ) ≠ 0 ∧
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail xr) : ℂ) ≠ 0 :=
    mul_ne_zero_iff.mp hw
  have hl := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xl hp.1 (by exact_mod_cast hw'.1)
  have hr := initial_half_cutoff_log_product P hP b d r μ₀ μb μd μc G cb cd center hG hc
    xr hp.2 (by exact_mod_cast hw'.2)
  have hlog (y : Fin n → P) : Real.log (∏ i, (y i : ℝ)) = ∑ i, Real.log (y i : ℝ) :=
    Real.log_prod (fun i _ => by exact_mod_cast (hP _ (y i).property).ne_zero)
  rw [hlog xl] at hl
  rw [hlog xr] at hr
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hP _ (x i).property).ne_zero), Fin.sum_univ_add]
  obtain ⟨hllo, hlhi⟩ := abs_le.mp hl
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hr
  dsimp only [xl, xr] at hllo hlhi hrlo hrhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialSampledProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained logarithmic window gives both Poisson cutoffs -/
namespace Ostmann
open scoped BigOperators

theorem sampled_product_window_of_log_error {I : Type*} [Fintype I]
    (v : I → ℕ) (hv : ∀ i, v i ≠ 0) (X Δ E : ℝ) (hX : 0 < X)
    (hlog : |Real.log (∏ i, (v i : ℝ)) - (Real.log X + Δ)| ≤ E) :
    X * Real.exp (Δ - E) ≤ ∏ i, (v i : ℝ) ∧
      (∏ i, (v i : ℝ)) ≤ X * Real.exp (Δ + E) := by
  have hp : 0 < ∏ i, (v i : ℝ) := Finset.prod_pos (fun i _ => by
    exact_mod_cast Nat.pos_of_ne_zero (hv i))
  obtain ⟨hl, hu⟩ := abs_le.mp hlog
  constructor
  · calc
      _ = Real.exp (Real.log X + (Δ - E)) := by rw [Real.exp_add, Real.exp_log hX]
      _ ≤ Real.exp (Real.log (∏ i, (v i : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hp
  · calc
      _ = Real.exp (Real.log (∏ i, (v i : ℝ))) := (Real.exp_log hp).symm
      _ ≤ Real.exp (Real.log X + (Δ + E)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hX]

/-- The cutoff weights restrict the sampled product without changing any
marginal prior. The only extra loss is the already bounded cell rounding. -/
theorem initial_doubled_product_window (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b d r : ℕ) (μ₀ : P → ℝ) (μb : Fin b → P → ℝ)
    (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ) (G cb cd : ℝ) (center : Fin r → ℝ)
    (hG : ∀ q : P, μ₀ q ≠ 0 → |Real.log (q : ℝ) - G| ≤ 1)
    (hc : ∀ i (q : P), μc i q ≠ 0 → |Real.log (q : ℝ) - center i| ≤ 1)
    (X Δ E : ℝ) (hX : 0 < X)
    (htarget : |2 * (G + cb + cd + ∑ i, center i) - (Real.log X + Δ)| ≤ E)
    (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P)
    (hprior : productPrior (Fin.append
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0)
    (hw : doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
      (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0) :
    X * Real.exp (Δ - (E + 2 * (r + 3))) ≤ ∏ i, (x i : ℝ) ∧
      (∏ i, (x i : ℝ)) ≤ X * Real.exp (Δ + (E + 2 * (r + 3))) := by
  have hlog := initial_doubled_cutoff_log_product P hP b d r μ₀ μb μd μc
    G cb cd center hG hc x hprior hw
  apply sampled_product_window_of_log_error (fun i => (x i : ℕ))
    (fun i => (hP _ (x i).property).ne_zero) X Δ (E + 2 * (r + 3)) hX
  exact (abs_sub_le _ _ _).trans (by linarith only [add_le_add hlog htarget])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialProductWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.nonzeroScheduledHistoryFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact product center of the original selected mixed prior -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedInitialCellCenter_sum (top : ℕ) (centers : List ℕ) :
    (∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) =
        3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  rw [← List.sum_ofFn]
  have he : (List.ofFn (fun i : Fin (initialSmallCellList top centers).length =>
      ((initialSmallCellList top centers).get i : ℝ))) =
      (initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ)) := by
    change List.ofFn ((fun j : ℕ => (j : ℝ)) ∘ (initialSmallCellList top centers).get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [he]
  exact initialSmallCellList_sum top centers

/-- The narrow window is centered at the actual selected total. Its width
depends only on the number of fixed cell roles, including the giant. -/
theorem selected_initial_product_window
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let ν := Fin.cons (smoothGiantPrior P logCellProfile G)
      (Fin.append μb (Fin.append μd μc))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    ∀ x : Fin (((b + (d + cells.length)) + 1) + ((b + (d + cells.length)) + 1)) → P,
      productPrior (Fin.append ν ν) x ≠ 0 →
      doubledHalfWeight (fun y : Fin ((b + (d + cells.length)) + 1) → P =>
        (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d cells.length cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
      Real.exp Y * Real.exp (Δ - 2 * (cells.length + 3)) ≤ ∏ i, (x i : ℝ) ∧
        (∏ i, (x i : ℝ)) ≤ Real.exp Y * Real.exp (Δ + 2 * (cells.length + 3)) := by
  intro cells μc ν Δ x hprior hw
  have hgiant (p : P) (hp : smoothGiantPrior P logCellProfile G p ≠ 0) :
      |Real.log (p : ℝ) - G| ≤ 1 := by
    have hh := smoothGiantPrior_active_bounds P hP logCellProfile G logCellProfile_zero_outside p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p p.property).pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hh.1
    have hhi := (Real.log_lt_iff_lt_exp hp0).mpr hh.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcell (i : Fin cells.length) (p : P) (hp : μc i p ≠ 0) :
      |Real.log (p : ℝ) - (cells.get i : ℝ)| ≤ 1 := by
    have hmem := primeSubsetPrior_support P _ p hp
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
    obtain ⟨_, _, _, _, _, _, hsupport⟩ := ht
    have hs := hsupport p hmem
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hs.1.pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hs.2.1
    have hhi := (Real.log_le_iff_le_exp hp0).mpr hs.2.2.1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htarget : |2 * (G + cb + cd + ∑ i : Fin cells.length, (cells.get i : ℝ)) -
      (Real.log (Real.exp Y) + Δ)| ≤ 0 := by
    rw [Real.log_exp]
    change |2 * (G + cb + cd + ∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) -
        (Y + selectedInitialLogCenter G Y cb cd top centers)| ≤ 0
    rw [selectedInitialCellCenter_sum]
    simp only [selectedInitialLogCenter]
    ring_nf
    simp
  simpa only [zero_add] using initial_doubled_product_window P hP b d cells.length
    (smoothGiantPrior P logCellProfile G) μb μd μc G cb cd (fun i => (cells.get i : ℝ))
    hgiant hcell (Real.exp Y) Δ 0 (Real.exp_pos _) htarget x hprior hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected full-prior window after fixing the spectators -/
namespace Ostmann
open scoped Classical BigOperators

private theorem primeSubsetPrior_ne_zero (P Q : Finset ℕ) (p : P)
    (hp : (p : ℕ).Prime) (hmem : (p : ℕ) ∈ Q) : primeSubsetPrior P Q p ≠ 0 := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
  have hm : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹ :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨p, hmem, hpos⟩
  simp only [primeSubsetPrior, ite_eq_left hmem]
  exact ne_of_gt (div_pos hpos hm)

theorem selected_initial_moving_window
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (μb : Fin b → P → ℝ) (sl sr : Fin d → P)
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd) :
    let cells := initialSmallCellList top centers
    let μg := smoothGiantPrior P logCellProfile G
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    ∀ (XL XR : P) (y : MovingRegularSlot 0 (cells.length + cells.length) (b + b) → P),
      μg XL ≠ 0 → μg XR ≠ 0 →
      (∏ i, initialMovingRegularPrior b cells.length μb μc i (y i)) ≠ 0 →
      initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd sl sr y ≠ 0 →
      ((∏ i, ((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) /
        Real.exp Y ∈ Set.Icc (Real.exp (Δ - 2 * (cells.length + 3)))
          (Real.exp (Δ + 2 * (cells.length + 3))) := by
  intro cells μg μc Δ XL XR y hXL hXR hy hw
  have hs (i : Fin d) : primeSubsetPrior P Qd (sl i) ≠ 0 := by
    exact primeSubsetPrior_ne_zero P Qd (sl i) (hP _ (sl i).property) (hsl i)
  have ht (i : Fin d) : primeSubsetPrior P Qd (sr i) ≠ 0 := by
    exact primeSubsetPrior_ne_zero P Qd (sr i) (hP _ (sr i).property) (hsr i)
  have hp := initialMovingTuple_prior_nonzero b d cells.length μg μb
    (fun _ => primeSubsetPrior P Qd) μc sl sr hs ht XL XR hXL hXR y hy
  have hc : doubledHalfWeight (fun z : Fin (b + (d + cells.length) + 1) → P =>
      (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd (Fin.tail z) : ℂ))
      (initialMovingTuple b d cells.length sl sr XL XR y) ≠ 0 := by
    rwa [initialMovingTuple_cutoff]
  have h := selected_initial_product_window htop hcenters P hP b d μb
    (fun _ => primeSubsetPrior P Qd) (initialMovingTuple b d cells.length sl sr XL XR y) hp hc
  have he : ((∏ i, ((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) =
      ∏ i, (((initialMovingTuple b d cells.length sl sr XL XR y i : P) : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [he]
  exact ⟨(le_div_iff₀ (Real.exp_pos Y)).mpr (by simpa only [mul_comm] using h.1),
    (div_le_iff₀ (Real.exp_pos Y)).mpr (by simpa only [mul_comm] using h.2)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialMovingAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected endpoint statistic gives the original moving amplitude -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem selected_initial_frozen_moving_amplitude
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (b d : ℕ) (μb : Fin b → P → ℝ) (sl sr : Fin d → P)
    (hdistinct : Function.Injective (Fin.append sl sr))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd) (fallback : P)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (Gseq : ℕ → ℝ)
    (hlarge : ∀ p : P, smoothGiantPrior P logCellProfile G p ≠ 0 → V 0 < (p : ℕ)) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G) μb μc
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd (Fin.tail x) : ℂ))) sl sr =
    movingTemplatePrimeAmplitude (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
      F φ Gseq 0 (cells.length + cells.length) (b + b) P (smoothGiantPrior P logCellProfile G)
      (initialMovingRegularPrior b cells.length μb μc)
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav := by
  exact initial_frozen_moving_amplitude P hP b d (initialSmallCellList top centers).length
    cb cd sl sr hdistinct fallback (smoothGiantPrior P logCellProfile G) μb _ S fav ψ
    (Real.exp Y) _ _ μ childBound pivotBound V φ Gseq hlarge
    (selected_initial_moving_window htop hcenters P hP b d μb sl sr hsl hsr)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedInitialScheduledAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem selected_initial_frozen_scheduled_amplitude
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (b d : ℕ) (μb : P → ℝ) (sl sr : Fin d → P)
    (hdistinct : Function.Injective (Fin.append sl sr))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd) (fallback : P)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (Gseq : ℕ → ℝ)
    (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G) (fun _ => μb) μc
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => S p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d cells.length cb cd (Fin.tail x) : ℂ))) sl sr =
    scheduledCellAmplitude (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
      F φ Gseq P (smoothGiantPrior P logCellProfile G)
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D c)) μb
      top centers 0 (b + b) (normalizedResidueFamily S) (normalizedResidueFamily S) fav := by
  intro cells μc Δ q hc inst F
  have hlarge (p : P) (hp : smoothGiantPrior P logCellProfile G p ≠ 0) : V 0 < (p : ℕ) := by
    have hp' := (smoothGiantPrior_active_bounds P hP logCellProfile G
      logCellProfile_zero_outside p hp).1
    exact_mod_cast hV0.trans hp'
  have he := selected_initial_frozen_moving_amplitude (cb := cb) (cd := cd) htop hcenters P hP b d (fun _ => μb)
    sl sr hdistinct hsl hsr fallback S fav ψ μ childBound pivotBound V φ Gseq hlarge
  refine he.trans ?_
  exact movingTemplatePrimeAmplitude_initial_schedule Subtype.val
    (fun p => (hP p p.property).ne_zero) b d top centers cb cd sl sr fallback
    q (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
    (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ)) (Real.exp (Δ - 2 * (cells.length + 3)))
    (Real.exp (Δ + 2 * (cells.length + 3))) (List.ofFn q) μ childBound pivotBound V φ Gseq
    P (fun p hp => (hP p hp).ne_zero) (smoothGiantPrior P logCellProfile G)
    (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D c)) μb
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSmallAmplitude
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed positive statistic on the actual regular-prime alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem frozen_initial_small_amplitude_oai
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D Qd : Finset ℕ} {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) cs targets)
    (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)] (hP : ∀ p ∈ P, p.Prime)
    (hQP : initialRegularPrimeRange L ⊆ P)
    (hgiant : smoothGiantPrimeRange G ⊆ P)
    (bulk : Finset ℕ) (hbulk : bulk ⊆ initialRegularPrimeRange L)
    (b d : ℕ) (sl sr : Fin d → initialRegularPrimeRange L)
    (hinj : Function.Injective (Fin.append
      (primeAlphabetEmbedding hQP ∘ sl) (primeAlphabetEmbedding hQP ∘ sr)))
    (hsl : ∀ i, (sl i : ℕ) ∈ Qd) (hsr : ∀ i, (sr i : ℕ) ∈ Qd)
    (fallback : initialRegularPrimeRange L)
    (sets : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool) (ψ : 𝓢(ℝ, ℂ))
    (Qμ : ℕ → Finset ℕ) (childBound pivotBound V : ℕ → ℕ)
    (hV0 : (V 0 : ℝ) < Real.exp (G - 1)) :
    let Q := initialRegularPrimeRange L
    let e := primeAlphabetEmbedding hQP
    let cells := initialSmallCellList top cs
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append (e ∘ sl) (e ∘ sr) i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property)
        (hP _ (Fin.append (e ∘ sl) (e ∘ sr) j).property)).mpr
          (fun h => hij (hinj (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i =>
      ⟨hP _ (Fin.append (e ∘ sl) (e ∘ sr) i).property⟩
    let Δ := selectedInitialLogCenter G Y cb cd top cs
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d cells.length cb cd sl sr fallback)
      (fun i => normalizedResidueFamily sets (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
      (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    initialFrozenAmplitude P b d cells.length (smoothGiantPrior P logCellProfile G)
      (fun _ => primeSubsetPrior P bulk)
      (fun i => primeSubsetPrior P (selectedTailCellPrimes A B N Y endpoint D (cells.get i)))
      (Fin.append (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p))
        (primeHalfTests (n := b + (d + cells.length)) P (fun p => sets p) (fun p => fav p)))
      ψ (Real.exp Y) (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + cells.length) + 1) → P =>
        (initialHalfCutoffWeight Subtype.val b d cells.length cb cd (Fin.tail x) : ℂ)))
      (e ∘ sl) (e ∘ sr) =
    scheduledCellAmplitude Subtype.val (List.ofFn q) (fun j => primeSubsetPrior Q (Qμ j))
      childBound pivotBound V F logCellProfile (fun _ => G)
      (smoothGiantPrimeRange G) (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
      (fun c => primeSubsetPrior Q (selectedTailCellPrimes A B N Y endpoint D c))
      (primeSubsetPrior Q bulk) top cs 0 (b + b)
      (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav := by
  intro Q e cells q hc inst Δ F
  have hstart := selected_initial_frozen_scheduled_amplitude (cb := cb) (cd := cd) htop hcs P hP b d
    (primeSubsetPrior P bulk) (e ∘ sl) (e ∘ sr) hinj hsl hsr (e fallback) sets fav ψ
    (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V logCellProfile (fun _ => G) hV0
  dsimp only at hstart
  unfold scheduledCellAmplitude at hstart
  rw [movingTemplatePrimeAmplitude_giant_ambient Subtype.val (List.ofFn q)
    (fun j => primeSubsetPrior P (Qμ j)) childBound pivotBound V _ logCellProfile
    (fun _ => G) 0 _ (b + b) P hP logCellProfile G logCellProfile_zero_outside hgiant] at hstart
  have halphabet := scheduledCellAmplitude_initial_prime_alphabet P Q hQP q (List.ofFn q)
    Qμ (selectedTailCellPrimes A B N Y endpoint D) bulk childBound pivotBound V b d top cs
    cb cd sl sr fallback (fun i => normalizedResidueFamily sets (q i))
    (initialSpectatorCofactor q hc) Finset.univ (𝓕 ψ) (Real.exp Y / (∏ i, q i : ℕ))
    (Real.exp (Δ - 2 * (cells.length + 3))) (Real.exp (Δ + 2 * (cells.length + 3)))
    logCellProfile (fun _ => G) 0 (smoothGiantPrimeRange G)
    (smoothGiantPrior (smoothGiantPrimeRange G) logCellProfile G)
    (fun j hj => by omega)
    (fun c hc => (Classical.choose_spec (initial_selected_cells_valid htop hcs c hc)).subset_initialRegularPrimeRange)
    hbulk (normalizedResidueFamily sets) (normalizedResidueFamily sets) fav
  exact hstart.trans halphabet

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.frozen_initial_small_amplitude_oai := @OAI.Ostmann.frozen_initial_small_amplitude_oai
