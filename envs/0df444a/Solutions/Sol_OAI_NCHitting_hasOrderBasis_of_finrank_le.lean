-- Prove2me | solution 1 for OAI.NCHitting.hasOrderBasis_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:20:46.024422+00:00
-- url     : https://prove2.me/submissions/e95cca9c-3096-4dc5-a1b3-474e8102c985

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/OrderBasis.lean:L31-L122
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.hasOrderBasis_of_finrank_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis

-- ---- from OAI.Algebra.FormulaHitting.OrderBasis ----
namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Submodule

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem hasOrderBasis_bot : HasOrderBasis (⊥ : Submodule F (PowerSeries F)) := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearIndependent_empty_type
  · simp
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

omit [CharZero F] in
theorem hasOrderBasis_of_finrank_le (N : ℕ) :
    ∀ (V : Submodule F (PowerSeries F)) [FiniteDimensional F V],
      Module.finrank F V ≤ N → HasOrderBasis V := by
  classical
  induction N with
  | zero =>
    intro V _ hV
    have he : V = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hV)
    rw [he]
    exact hasOrderBasis_bot
  | succ N ih =>
    intro V _ hV
    by_cases he : V = ⊥
    · rw [he]; exact hasOrderBasis_bot
    have hex : ∃ a : ℕ, ∃ v : PowerSeries F, v ∈ V ∧ PowerSeries.coeff a v ≠ 0 := by
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot he
      have hc : ∃ a, PowerSeries.coeff a v ≠ 0 := by
        by_contra h
        push Not at h
        apply hv0
        ext a
        simpa using h a
      obtain ⟨a, ha⟩ := hc
      exact ⟨a, v, hv, ha⟩
    let a := Nat.find hex
    obtain ⟨v, hv, hva⟩ := Nat.find_spec hex
    have hlow : ∀ x ∈ V, ∀ r < a, PowerSeries.coeff r x = 0 := by
      intro x hx r hr
      by_contra hc
      have hh := Nat.find_min' hex ⟨x, hx, hc⟩
      omega
    let W : Submodule F (PowerSeries F) := V ⊓ LinearMap.ker (PowerSeries.coeff a)
    have hWlt : W < V := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      have hvW : v ∈ W := h.symm ▸ hv
      exact hva ((LinearMap.mem_ker.mp hvW.2))
    have hdim : Module.finrank F W ≤ N := by
      have hlt := Submodule.finrank_lt_finrank_of_lt hWlt
      omega
    obtain ⟨k, b, aa, hli, hspan, hinj, hlead, hzero⟩ := ih W hdim
    have hbW : ∀ i, b i ∈ W := by
      intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hvnot : v ∉ Submodule.span F (Set.range b) := by
      rw [hspan]
      intro h
      exact hva (LinearMap.mem_ker.mp h.2)
    have hneq : ∀ i, a ≠ aa i := by
      intro i hi
      exact hlead i (hi ▸ LinearMap.mem_ker.mp (hbW i).2)
    refine ⟨k+1, Fin.cons v b, Fin.cons a aa, hli.finCons hvnot, ?_, ?_, ?_, ?_⟩
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hv
        · simpa using (hbW j).1
      · intro x hx
        let c : F := PowerSeries.coeff a x / PowerSeries.coeff a v
        have hy : x - c • v ∈ W := by
          constructor
          · exact V.sub_mem hx (V.smul_mem c hv)
          · apply LinearMap.mem_ker.mpr
            simp only [map_sub, map_smul, smul_eq_mul, c]
            rw [div_mul_cancel₀ _ hva, sub_self]
        have hvm : v ∈ Submodule.span F (Set.range (Fin.cons v b)) :=
          Submodule.subset_span ⟨0, rfl⟩
        have hym : x - c • v ∈ Submodule.span F (Set.range (Fin.cons v b)) := by
          apply (Submodule.span_mono (s := Set.range b) ?_)
          · rwa [hspan]
          · rintro y ⟨j, rfl⟩
            exact ⟨j.succ, rfl⟩
        have := Submodule.add_mem (Submodule.span F (Set.range (Fin.cons v b)))
          hym (Submodule.smul_mem _ c hvm)
        simpa using this
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro _; rfl
        · intro hij; exact (hneq j' (by simpa using hij)).elim
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro hij; exact (hneq i' (by simpa using hij.symm)).elim
        · intro hij
          have hij' : aa i' = aa j' := by simpa using hij
          exact congrArg Fin.succ (hinj hij')
    · intro i
      exact Fin.cases hva hlead i
    · intro i
      exact Fin.cases (hlow v hv) hzero i

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open PowerSeries Submodule


theorem solution : type_of% @_root_.OAI.NCHitting.hasOrderBasis_of_finrank_le := @_root_.OAI.NCHitting.hasOrderBasis_of_finrank_le
