-- Prove2me | solution 2 for OAI.MetricEntropyDuality.FieldGraphSeparation.no_short_walk
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:02:01.012721+00:00
-- url     : https://prove2.me/submissions/f2df11a4-b0f3-495a-a27e-dd5c8141f211

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FieldGraphSeparation.lean:L93-L121
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.FieldGraphSeparation.no_short_walk. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Theorems.Thm_OAI_MetricEntropyDuality_SymmetricForm_eval_eq_of_contract_eq

-- ---- from OAI.Analysis.MetricEntropy.FieldGraphSeparation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uK uι uα uV uA

/-!
# Actual contraction labels obstruct short walks

One label is chosen for each edge of a hypothetical short walk. These labels
are padded to the full degree using one fixed member of the same set of
directions. Symmetry moves each edge's direction to the contracted slot, so
evaluation on this single tuple is constant along the walk. This contradicts
robust nonvanishing of the difference of its endpoints.
-/

noncomputable section

namespace MetricEntropyDuality

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

end SymmetricForm

namespace FieldGraphSeparation

variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}

private theorem padTuple_mem {α : Type uα} {k h : ℕ} (T : Finset α)
    (a : Fin k → α) (filler : α) (ha : ∀ i, a i ∈ T) (hf : filler ∈ T)
    (i : Fin h) : padTuple a filler i ∈ T := by
  unfold padTuple
  split_ifs with hi
  · exact ha ⟨i.val, hi⟩
  · exact hf

private theorem padTuple_cast {α : Type uα} {k h : ℕ} (a : Fin k → α)
    (filler : α) (hkh : k ≤ h) (i : Fin k) :
    padTuple a filler (⟨i.val, lt_of_lt_of_le i.isLt hkh⟩ : Fin h) = a i := by
  simp only [padTuple, dite_eq_left i.isLt]

/-- A finite walk along which a function agrees at each consecutive pair has
equal values at its endpoints. This includes the empty walk. -/
private theorem eval_eq_of_walk_steps {V : Type uV} {A : Type uA} {G : SimpleGraph V} {x y : V}
    (w : G.Walk x y) (f : V → A)
    (hf : ∀ n, n < w.length → f (w.getVert n) = f (w.getVert (n + 1))) :
    f x = f y := by
  have hconst : ∀ n, n ≤ w.length → f (w.getVert n) = f x := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        exact (hf n (Nat.lt_of_succ_le hn)).symm.trans
          (ih (Nat.le_of_succ_le hn))
  simpa only [SimpleGraph.Walk.getVert_length] using (hconst w.length le_rfl).symm

/-- A robustly nonzero form difference rules out every short walk in the
actual contraction partition graph. No separation certificate is assumed. -/
theorem no_short_walk (t : ι → (Fin r → K)) (T : Finset ι) (hT : T.Nonempty)
    (x y : SymmetricForm K r (j + 1))
    (hrobust : ∀ a : Fin (j + 1) → ι, (∀ l, a l ∈ T) →
      (y - x).eval (fun l => t (a l)) ≠ 0)
    (w : (PartitionGraph.graph (labels t) T).Walk x y) : j + 1 < w.length := by
  classical
  by_contra hlong
  have hlength : w.length ≤ j + 1 := Nat.le_of_not_gt hlong
  obtain ⟨filler, hfiller⟩ := hT
  have hedge : ∀ l : Fin w.length, ∃ i ∈ T,
      labels t i (w.getVert l.val) = labels t i (w.getVert (l.val + 1)) := by
    intro l
    have hadj := w.adj_getVert_succ l.isLt
    change _ ≠ _ ∧ ∃ i ∈ T, labels t i _ = labels t i _ at hadj
    exact hadj.2
  choose edge hedge_mem hedge_eq using hedge
  let a : Fin (j + 1) → ι := padTuple edge filler
  have ha : ∀ l, a l ∈ T := padTuple_mem T edge filler hedge_mem hfiller
  have heval : x.eval (fun l => t (a l)) = y.eval (fun l => t (a l)) := by
    apply eval_eq_of_walk_steps w (fun F => F.eval (fun l => t (a l)))
    intro n hn
    let l : Fin w.length := ⟨n, hn⟩
    apply SymmetricForm.eval_eq_of_contract_eq (t (edge l)) _ _ (hedge_eq l)
      (fun l => t (a l)) (⟨n, lt_of_lt_of_le hn hlength⟩ : Fin (j + 1))
    exact congrArg t (padTuple_cast edge filler hlength l)
  apply hrobust a ha
  rw [SymmetricForm.eval_sub, heval, sub_self]

end FieldGraphSeparation
end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FieldGraphSeparation


theorem solution.{uK,uι} : type_of% @_root_.OAI.MetricEntropyDuality.FieldGraphSeparation.no_short_walk.{uK,uι} := @_root_.OAI.MetricEntropyDuality.FieldGraphSeparation.no_short_walk.{uK,uι}
