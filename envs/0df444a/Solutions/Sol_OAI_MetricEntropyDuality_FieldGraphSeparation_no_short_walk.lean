-- Prove2me | solution 1 for OAI.MetricEntropyDuality.FieldGraphSeparation.no_short_walk
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:55:03.137782+00:00
-- url     : https://prove2.me/submissions/aa116856-14ef-49df-bc7b-640350aa0bdf

import Mathlib
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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FieldGraphSeparation
universe uK uι uα uV uA
variable {K : Type uK} {ι : Type uι} [CommRing K] {r j : ℕ}
section h51nsw
variable {K' : Type*} [CommRing K'] {r' : ℕ}

lemma h51m_eval_perm {n : ℕ} (F : SymmetricForm K' r' n) (args : Fin n → (Fin r' → K'))
    (σ : Equiv.Perm (Fin n)) : SymmetricForm.eval F (args ∘ σ) = SymmetricForm.eval F args := by
  unfold SymmetricForm.eval
  let e : (Fin n → Fin r') ≃ (Fin n → Fin r') :=
    ⟨fun b => b ∘ σ, fun b => b ∘ σ.symm, fun b => by funext i; simp, fun b => by funext i; simp⟩
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  show F (tupleSym (b ∘ σ)) * ∏ i, args (σ i) (b (σ i)) = _
  rw [tupleSym_comp_perm]
  congr 1
  exact Equiv.prod_comp σ (fun i => args i (b i))

lemma h51m_eval_contract {j' : ℕ} (v : Fin r' → K') (F : SymmetricForm K' r' (j' + 1))
    (args : Fin j' → (Fin r' → K')) :
    SymmetricForm.eval (SymmetricForm.contract v F) args = SymmetricForm.eval F (Fin.cons v args) := by
  unfold SymmetricForm.eval
  rw [← (Fin.consEquiv (fun _ : Fin (j'+1) => Fin r')).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, tupleSym_cons, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, SymmetricForm.contract_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

lemma h51m_eval_eq {j' : ℕ} (v : Fin r' → K') (F G : SymmetricForm K' r' (j' + 1))
    (hFG : SymmetricForm.contract v F = SymmetricForm.contract v G)
    (args : Fin (j' + 1) → (Fin r' → K')) (a : Fin (j' + 1)) (ha : args a = v) :
    SymmetricForm.eval F args = SymmetricForm.eval G args := by
  set σ := Equiv.swap 0 a
  have h1 : ∀ H : SymmetricForm K' r' (j' + 1), SymmetricForm.eval H args =
      SymmetricForm.eval (SymmetricForm.contract v H) (Fin.tail (args ∘ σ)) := by
    intro H
    rw [h51m_eval_contract, ← h51m_eval_perm H args σ]
    congr 1
    rw [← Fin.cons_self_tail (args ∘ σ)]
    congr 1
  rw [h1 F, h1 G, hFG]
end h51nsw

theorem solution (t : ι → (Fin r → K)) (T : Finset ι) (hT : T.Nonempty)
    (x y : SymmetricForm K r (j + 1))
    (hrobust : ∀ a : Fin (j + 1) → ι, (∀ l, a l ∈ T) →
      (y - x).eval (fun l => t (a l)) ≠ 0)
    (w : (PartitionGraph.graph (labels t) T).Walk x y) : j + 1 < w.length := by
  classical
  by_contra hlen
  push_neg at hlen
  obtain ⟨i0, hi0⟩ := hT
  let G := PartitionGraph.graph (labels (j := j) t) T
  have hidx : ∀ d : G.Dart, ∃ i ∈ T, labels t i d.fst = labels t i d.snd := fun d =>
    ((PartitionGraph.adj_iff (labels (j := j) t) T).mp d.adj).2
  let idx : G.Dart → ι := fun d => Classical.choose (hidx d)
  have idx_mem : ∀ d, idx d ∈ T := fun d => (Classical.choose_spec (hidx d)).1
  have idx_eq : ∀ d, labels t (idx d) d.fst = labels t (idx d) d.snd :=
    fun d => (Classical.choose_spec (hidx d)).2
  let a : Fin (j + 1) → ι := fun l =>
    if hl : l.val < w.darts.length then idx (w.darts.get ⟨l.val, hl⟩) else i0
  have ha_mem : ∀ l, a l ∈ T := by
    intro l; simp only [a]; split_ifs
    · exact idx_mem _
    · exact hi0
  have hcover : ∀ d ∈ w.darts, ∃ l, a l = idx d := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hk' : k < j + 1 := by
      rw [SimpleGraph.Walk.length_darts] at hk; omega
    refine ⟨⟨k, hk'⟩, ?_⟩
    simp only [a, dif_pos hk]
    rfl
  -- evaluation is constant along the walk
  have key : ∀ (u v : SymmetricForm K r (j + 1)) (p : G.Walk u v),
      (∀ d ∈ p.darts, ∃ l, a l = idx d) →
      SymmetricForm.eval u (fun l => t (a l)) = SymmetricForm.eval v (fun l => t (a l)) := by
    intro u v p
    induction p with
    | nil => intro _; rfl
    | cons hadj q ih =>
      intro hp
      rename_i u' m v'
      have hd := hp ⟨(u', m), hadj⟩ (by simp)
      obtain ⟨l, hl⟩ := hd
      rw [← ih (fun d hd => hp d (by simp [hd]))]
      apply h51m_eval_eq (t (a l)) _ _ _ _ l rfl
      have := idx_eq ⟨(u', m), hadj⟩
      rw [← hl] at this
      exact this
  have := key x y w hcover
  apply hrobust a ha_mem
  rw [SymmetricForm.eval_sub, this, sub_self]

