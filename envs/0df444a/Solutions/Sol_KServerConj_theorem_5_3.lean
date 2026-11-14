-- Prove2me | solution 1 for KServerConj.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T03:49:29.49664+00:00
-- url     : https://prove2.me/submissions/1b2229e2-6359-4d17-b18a-ffa70cb558a2

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Definitions.Def_KServerConj_cl
import Definitions.Def_KServerConj_IsWFATraj
import Definitions.Def_KServerConj_extCost
import Theorems.Thm_KServerConj_theorem_2_4
import Theorems.Thm_KServerConj_lemma_5_1
import Theorems.Thm_KServerConj_lemma_5_2
import Theorems.Thm_KServerConj_corollary_4_4
import Theorems.Thm_KServerConj_lemma_1_1
set_option autoImplicit false

section PaperFile000
open scoped BigOperators

namespace KServerConj

theorem paper53_payment_telescope (e : ℕ → ℝ) (Φ : ℕ → WithTop ℝ) (T : ℕ)
    (hstep : ∀ t, 1 ≤ t → t ≤ T → (e t : WithTop ℝ) + Φ (t - 1) ≤ Φ t) :
    ((∑ t ∈ Finset.Icc 1 T, e t : ℝ) : WithTop ℝ) + Φ 0 ≤ Φ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hp := ih (fun t ht htT => hstep t ht (htT.trans (Nat.le_succ T)))
    have hs := hstep (T + 1) (Nat.succ_le_succ (Nat.zero_le T)) le_rfl
    calc
      _ = (e (T + 1) : WithTop ℝ) +
          (((∑ t ∈ Finset.Icc 1 T, e t : ℝ) : WithTop ℝ) + Φ 0) := by
        rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le T)), WithTop.coe_add]
        ac_rfl
      _ ≤ (e (T + 1) : WithTop ℝ) + Φ T := add_le_add le_rfl hp
      _ ≤ Φ (T + 1) := by simpa only [Nat.add_sub_cancel] using hs

end KServerConj
end PaperFile000

section PaperFile076
namespace KServerConj

theorem paper53_exists_injective_enumeration {M : Type*} [DecidableEq M] {k : ℕ}
    (X : Finset M) (hX : X.card = k) :
    ∃ x : Fin k → M, Function.Injective x ∧ Finset.univ.image x = X := by
  classical
  let e : X ≃ Fin k := X.equivFinOfCardEq hX
  let x : Fin k → M := fun i => (e.symm i).val
  have hx : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  refine ⟨x, hx, ?_⟩
  apply Finset.ext
  intro a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e.symm i).property
  · intro ha
    refine ⟨e ⟨a, ha⟩, ?_⟩
    exact congrArg Subtype.val (e.symm_apply_apply ⟨a, ha⟩)

end KServerConj
end PaperFile076

section PaperFile089
open scoped BigOperators

namespace KServerConj

theorem paper53_extended_cost_bound_of_run {M : Type*} [PseudoMetricSpace M]
    [Fintype M] [DecidableEq M] {m : ℕ}
    (hm : 1 ≤ m) (s : Fin (m + 1) → M) (hs : Function.Injective s) (r : ℕ → M) (T : ℕ)
    (q qn : ℕ → M → Fin (m + 1) → K (m + 1) M) (hrun : IsRun s r T q qn)
    (XT : Finset M) (hXT : XT.card = m + 1) :
    (∑ t ∈ Finset.Icc 1 T, extCost (m + 1) (Finset.univ.image s) r t) ≤
      (((m + 1 : ℕ) : ℝ) + 1) * workFn (m + 1) (Finset.univ.image s) r T XT +
        cl (Finset.univ.image s) - cl XT := by
  have hpaid := paper53_payment_telescope
    (fun t => extCost (m + 1) (Finset.univ.image s) r t) (fun t => Psi (q t)) T
    (corollary_4_4 hm s hs r T q qn hrun)
  rw [hrun.1, lemma_5_2 hm s hs] at hpaid
  have hend := lemma_5_1 hm s hs r T q qn hrun T le_rfl XT hXT
  have hbound := hpaid.trans hend
  rw [← WithTop.coe_add] at hbound
  have hreal := WithTop.coe_le_coe.mp hbound
  have hcoeff : ((m + 2 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) + 1 := by
    norm_num [Nat.cast_add, add_assoc]
  rw [hcoeff] at hreal
  linarith only [hreal]

end KServerConj
end PaperFile089

open KServerConj

open scoped BigOperators

theorem solution {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 2 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (T : ℕ) (XT : Finset M) (hXT : XT.card = k)
    (hmin : ∀ X : Finset M, X.card = k → workFn k C₀ r T XT ≤ workFn k C₀ r T X) :
    (∑ t ∈ Finset.Icc 1 T, extCost k C₀ r t ≤
        ((k : ℝ) + 1) * workFn k C₀ r T XT + cl C₀ - cl XT) ∧
    ∀ C : ℕ → Finset M, IsWFATraj k C₀ r T C →
      wfaCost C T ≤ (k : ℝ) * workFn k C₀ r T XT + cl C₀ - cl XT := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, (Nat.sub_add_cancel hk).symm⟩
  obtain ⟨s, hs, hsimage⟩ := paper53_exists_injective_enumeration C₀ hC₀
  have hm : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨q, qn, hrun⟩ := (theorem_2_4 hm s hs r T).1
  have hExt := paper53_extended_cost_bound_of_run hm s hs r T q qn hrun XT hXT
  rw [hsimage] at hExt
  refine ⟨hExt, ?_⟩
  intro C hC
  have hk1 : 1 ≤ n + 2 := Nat.succ_le_succ (Nat.zero_le (n + 1))
  have haccount := lemma_1_1 (n + 2) hk1 C₀ hC₀ r T C hC
  have hCT : (C T).card = n + 2 := by
    by_cases hT : T = 0
    · simpa only [hT, hC.1] using hC₀
    · exact (hC.2 T (Nat.one_le_iff_ne_zero.mpr hT) le_rfl).1
  have hminCT := hmin (C T) hCT
  linarith only [hExt, haccount, hminCT]

#print axioms solution
