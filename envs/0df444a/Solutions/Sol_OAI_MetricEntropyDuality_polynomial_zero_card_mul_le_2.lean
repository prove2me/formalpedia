-- Prove2me | solution 2 for OAI.MetricEntropyDuality.polynomial_zero_card_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:56:53.942346+00:00
-- url     : https://prove2.me/submissions/5eaeb9b0-de5d-4165-afe5-ce4b6681e7df

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/PolynomialZeroBound.lean:L61-L93
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.polynomial_zero_card_mul_le. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.PolynomialZeroBound ----
namespace OAI

universe uV

/-!
# Polynomial zero counts over a finite prime field

The sample space contains every assignment of the finite variable set. In
particular, using a product variable type imposes no restriction on repeated
vector indices. The exact counting bound is obtained from the
Schwartz–Zippel theorem by renaming variables and clearing positive denominators.
-/

noncomputable section

namespace MetricEntropyDuality

variable {p : ℕ} [Fact p.Prime]

private theorem polynomial_zero_card_mul_le_fin {n : ℕ}
    (P : MvPolynomial (Fin n) (ZMod p)) (hP : P ≠ 0) :
    p * (polynomialZeros P).card ≤ P.totalDegree * p ^ n := by
  have hSZ := MvPolynomial.schwartz_zippel_totalDegree hP
    (Finset.univ : Finset (ZMod p))
  have hzeros :
      (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (ZMod p)))).filter
        (fun x => MvPolynomial.eval x P = 0) = polynomialZeros P := by
    classical
    ext x
    simp [polynomialZeros]
  have hratio : ((polynomialZeros P).card : ℚ≥0) / (p : ℚ≥0) ^ n ≤
      (P.totalDegree : ℚ≥0) / (p : ℚ≥0) := by
    rw [hzeros] at hSZ
    simpa only [Finset.card_univ, ZMod.card] using hSZ
  have hp : (0 : ℚ≥0) < p := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hcross := (div_le_div_iff₀ (pow_pos hp n) hp).mp hratio
  have hnat : (polynomialZeros P).card * p ≤ P.totalDegree * p ^ n := by
    exact_mod_cast hcross
  simpa only [Nat.mul_comm] using hnat

/-- Schwartz–Zippel as a natural-number inequality, for any finite variable
type, including the empty variable type. -/
theorem polynomial_zero_card_mul_le {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) :
    p * (polynomialZeros P).card ≤ P.totalDegree * p ^ Fintype.card V := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let Q : MvPolynomial (Fin (Fintype.card V)) (ZMod p) :=
    MvPolynomial.renameEquiv (ZMod p) e P
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    apply (MvPolynomial.renameEquiv (ZMod p) e).injective
    simpa only [map_zero] using h
  have hcard : (polynomialZeros P).card = (polynomialZeros Q).card := by
    apply Finset.card_bij (fun x _ i => x (e.symm i))
    · intro x hx
      rw [mem_polynomialZeros] at hx ⊢
      simpa only [Q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hx
    · intro x hx y hy h
      funext v
      simpa only [Equiv.symm_apply_apply] using congrFun h (e v)
    · intro y hy
      refine ⟨fun v => y (e v), ?_, ?_⟩
      · rw [mem_polynomialZeros] at hy ⊢
        simpa only [Q, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
          Function.comp_def] using hy
      · funext i
        simp only [Equiv.apply_symm_apply]
  rw [hcard]
  have h := polynomial_zero_card_mul_le_fin Q hQ
  simpa only [Q, MvPolynomial.totalDegree_renameEquiv] using h

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution.{uV} : type_of% @_root_.OAI.MetricEntropyDuality.polynomial_zero_card_mul_le.{uV} := @_root_.OAI.MetricEntropyDuality.polynomial_zero_card_mul_le.{uV}
