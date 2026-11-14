-- Prove2me | solution 1 for OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:37:30.792422+00:00
-- url     : https://prove2.me/submissions/fcbc1928-16ca-4f1a-8540-7c52094fa5b8

import Mathlib
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.TransferInstance
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_CoarseAssembly
import Definitions.Def_OAIQ229C045
import Theorems.Thm_OAI_CoarseAssembly_publishedKazhdanInput_of_elementaryReduction_ca

section
-- module Solutions.Q229_CA.CoarseAssembly_AnalyticKHomology
attribute [-instance] _root_.OAI.CoarseAssembly.Analytic.Coarsening.instDirectedSystemNatLocallyFiniteK1SpaceCoeAddMonoidHomMap _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The odd Fredholm-module group

The group is formed from actual analytic cycles, modulo degeneracy, unitary
equivalence, orthogonal direct sum and norm homotopy. Pullback of star
representations descends to this quotient. This gives the analytic domain
needed for the subsequent geometric construction; no assembly or nonzero
class is postulated here.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A}

theorem relation_zero {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) :
    (QuotientAddGroup.mk z : OddK A) = 0 :=
  (QuotientAddGroup.eq_zero_iff z).2 (AddSubgroup.subset_closure hz)

theorem degenerate_zero (c : OddCycle A) (hc : c.Degenerate) : cycleClass A c = 0 :=
  relation_zero (.degenerate c hc)

theorem directSum_eq (c d e : OddCycle A) (h : c.IsDirectSum d e) :
    cycleClass A e = cycleClass A c + cycleClass A d := by
  have hz := relation_zero (.directSum c d e h)
  exact sub_eq_zero.mp (by simpa only [cycleClass, OddK, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] using hz)

theorem homotopy_eq (h : OddHomotopy A) :
    cycleClass A (h.eval start) = cycleClass A (h.eval finish) := by
  have hz := relation_zero (.homotopy h)
  exact sub_eq_zero.mp (by simpa only [cycleClass, OddK, QuotientAddGroup.mk_sub] using hz)

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Assembly
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible analytic indices and their coarsening limit

The scale-index homomorphisms and their compatibility are the precise
published input from Willett--Yu, *Higher Index Theory*, §§5.1, 6.7, 7.1--7.2
(with errata 30--31). Their source is the Fredholm-module group of the actual
C₀ algebra; their target is the topological K₁ of the actual nonunital algebra.
The induced coarse map is constructed here by the universal property of the
direct limit. No geometric detection, filling or transfer conclusion is part
of this input.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u v

namespace CompatibleIndexFamily

variable {C D : Coarsening.{u}} {A B : Type v}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Scale-level analytic naturality passes to the actual coarsening limit. -/
theorem assembly_natural (I : CompatibleIndexFamily C A) (J : CompatibleIndexFamily D B)
    (f : CoarseningMorphism C D) (φ : A →⋆ₙₐ[ℂ] B)
    (hnat : ∀ r, (J.atScale r).comp (pushforward (f.atScale r)) =
      (OperatorKTheory.map φ).comp (I.atScale r)) :
    J.assembly.comp f.homologyMap = (OperatorKTheory.map φ).comp I.assembly := by
  apply AddCommGroup.DirectLimit.hom_ext
  intro r
  apply AddMonoidHom.ext
  intro a
  change J.assembly (f.homologyMap (C.of r a)) =
    OperatorKTheory.map φ (I.assembly (C.of r a))
  simp only [CoarseningMorphism.homologyMap_of, assembly_of]
  exact DFunLike.congr_fun (hnat r) a

end CompatibleIndexFamily

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceQuotients
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.holonomyCharge_reduceSteps _root_.OAI.CoarseAssembly.Congruence.holonomyWord_reduceSteps _root_.OAI.CoarseAssembly.Congruence.quotientMap_comp _root_.OAI.CoarseAssembly.Congruence.quotientMap_holonomy _root_.OAI.CoarseAssembly.Congruence.quotientMap_reduce _root_.OAI.CoarseAssembly.Congruence.quotientMap_self _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual congruence quotients and diagonal holonomies

The congruence quotient is `SL₃(ℤ/2^kℤ)`, including the singleton quotient
for `k = 0`.
Its diagonal matrices have entries `t,t⁻¹,1`, and the finite-level matrices
are obtained by the genuine 2-adic reduction maps.
-/

namespace CoarseAssembly.Congruence

/-- Powers of the diagonal holonomy have the expected Laurent trace. -/
theorem trace_diagonal_pow {R : Type*} [CommRing R] (t : Rˣ) (m : ℕ) :
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (t ^ m : Rˣ) + ((t ^ m)⁻¹ : Rˣ) + 1 := by
  change Matrix.trace ((diagonalHom t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R) = _
  rw [← map_pow]
  simp [diagonalHom, diagonal, Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

theorem trace_diagonal_zpow {R : Type*} [CommRing R] (t : Rˣ) (m : ℤ) :
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
      (t ^ m : Rˣ) + ((t ^ m)⁻¹ : Rˣ) + 1 := by
  change Matrix.trace ((diagonalHom t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R) = _
  rw [← map_zpow]
  simp [diagonalHom, diagonal, Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

/-- Reversing the signed charge leaves the diagonal trace unchanged. -/
theorem trace_diagonal_neg {R : Type*} [CommRing R] (t : Rˣ) (m : ℤ) :
    Matrix.trace ((diagonal t ^ (-m) : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
    Matrix.trace ((diagonal t ^ m : Matrix.SpecialLinearGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) := by
  rw [trace_diagonal_zpow t (-m), trace_diagonal_zpow t m]
  simp only [zpow_neg, inv_inv]
  rw [add_comm (((t ^ m)⁻¹ : Rˣ) : R)]

theorem trace_conjugate {R : Type*} [CommRing R]
    (q z : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.trace ((z⁻¹ * q * z : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Matrix.trace (q : Matrix (Fin 3) (Fin 3) R) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mul]

/-- Integral word traces reduce to their ordinary residue classes. -/
theorem trace_reduce (k : ℕ) (w : ArithmeticGroup) :
    Matrix.trace (reduce k w : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
      ((Matrix.trace (w : Matrix (Fin 3) (Fin 3) ℤ) : ℤ) : ZMod (2 ^ k)) := by
  simp [reduce, Matrix.trace, Matrix.SpecialLinearGroup.map_apply_coe]

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberEmbedding
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.quotientCopy_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constant-fiber spatial isometry

This is the actual map from the base Roe module to the fibered Roe module.
On singleton boundary fibers it is exactly the coordinate inclusion.
-/

noncomputable section

namespace CoarseAssembly

variable {I : Type*} (Q : I → Type*) [∀ i, Fintype (Q i)] [∀ i, Nonempty (Q i)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem fiberEmbedding_singleton [DecidableEq I] [DecidableEq (Sigma Q)]
    (i : I) [Subsingleton (Q i)] (q : Q i) (h : H) :
    fiberEmbedding Q (lp.single 2 i h) = lp.single 2 ⟨i, q⟩ h := by
  let : Unique (Q i) := ⟨⟨q⟩, fun x => Subsingleton.elim x q⟩
  apply lp.ext
  funext z
  rcases z with ⟨j, r⟩
  by_cases hji : j = i
  · subst j
    have hqr : r = q := Subsingleton.elim _ _
    subst r
    simp [fiberEmbedding_apply]
  · have hz : (⟨j, r⟩ : Sigma Q) ≠ ⟨i, q⟩ := fun h => hji (congrArg Sigma.fst h)
    simp [fiberEmbedding_apply, hji, hz]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Holonomy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.holonomyCharge_reduceSteps _root_.OAI.CoarseAssembly.Congruence.holonomyWord_reduceSteps _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The group calculation for a charged closed walk

In §3, left Cayley moves commute with the right holonomy. Recording a step
as `(s,m)` means `z ↦ s * z * g^m`; a pure Cayley step has `m=0`, and a
pure base step has `s=1`. The accumulated endpoint formula and conjugacy
obstruction are expressed using an actual finite list of steps.
-/

namespace CoarseAssembly

variable {Q : Type*} [Group Q]

/-- Left multiplication and right holonomy accumulate independently. -/
theorem holonomyEndpoint_eq (g z : Q) (steps : List (Q × ℤ)) :
    holonomyEndpoint g steps z = holonomyWord steps * z * g ^ holonomyCharge steps := by
  induction steps generalizing z with
  | nil => simp [holonomyEndpoint, holonomyWord, holonomyCharge]
  | cons s steps ih =>
    simp only [holonomyEndpoint, holonomyWord, holonomyCharge, ih, zpow_add]
    group

/-- A closed walk forces its right holonomy to be conjugate to the inverse
of its left word. No commutativity of the finite quotient is assumed. -/
theorem holonomy_conjugacy (g z : Q) (steps : List (Q × ℤ))
    (hclosed : holonomyEndpoint g steps z = z) :
    g ^ holonomyCharge steps = z⁻¹ * (holonomyWord steps)⁻¹ * z := by
  rw [holonomyEndpoint_eq] at hclosed
  calc
    g ^ holonomyCharge steps =
        (z⁻¹ * (holonomyWord steps)⁻¹) *
          (holonomyWord steps * z * g ^ holonomyCharge steps) := by group
    _ = z⁻¹ * (holonomyWord steps)⁻¹ * z := by rw [hclosed]

/-- Any conjugacy invariant, in particular matrix trace, detects the
obstruction supplied by a closed charged walk. -/
theorem holonomy_invariant_eq {T : Type*} (tr : Q → T)
    (htr : ∀ q z, tr (z⁻¹ * q * z) = tr q)
    (g z : Q) (steps : List (Q × ℤ))
    (hclosed : holonomyEndpoint g steps z = z) :
    tr (g ^ holonomyCharge steps) = tr (holonomyWord steps)⁻¹ := by
  rw [holonomy_conjugacy g z steps hclosed, htr]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TraceSeparation
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Trace separation for the congruence-fiber construction

These are elementary ingredients of Lemma 3.1 of *A counterexample to the
coarse Novikov conjecture* (September 23, 2026). No analytic index theorem or
property (T) is assumed here. The actual reduction maps are the existing
`PadicInt.toZModPow` maps.
-/

namespace CoarseAssembly

section LaurentTrace

variable {R : Type*} [CommRing R]

/-- An integral trace would make the positive power of the unit a root of
`X² + (1-c)X + 1`. Thus a transcendental unit has no such trace. -/
theorem diagonalTrace_ne_int (t : Rˣ) (ht : Transcendental ℤ (t : R))
    {n : ℕ} (hn : 0 < n) (c : ℤ) : diagonalTrace t n ≠ (c : R) := by
  intro h
  let y : R := (t ^ n : Rˣ)
  let z : R := ((t ^ n)⁻¹ : Rˣ)
  have hyz : y * z = 1 := Units.mul_inv (t ^ n)
  have heq : y + z + 1 = (c : R) := h
  have hmul := congrArg (fun a : R => a * y) heq
  have hroot : y ^ 2 + (1 - (c : R)) * y + 1 = 0 := by
    linear_combination hmul - hyz
  let f : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (1 - c) * Polynomial.X + 1
  have htrans : Transcendental ℤ y := by
    simpa [y] using ht.pow hn
  have hf : Polynomial.aeval y f = 0 := by
    simpa [f] using hroot
  have hfzero : f = 0 := (transcendental_iff.mp htrans) f hf
  have hcoeff := congrArg (fun q : Polynomial ℤ => q.coeff 0) hfzero
  simp [f] at hcoeff

end LaurentTrace

section FiniteReduction

variable {p : ℕ} [Fact p.Prime]

/-- Once two p-adic integers differ modulo `p^m`, they differ at every
deeper level. This is the compatibility needed by the short-loop argument. -/
theorem reduction_ne_of_le {x y : ℤ_[p]} {m n : ℕ} (hmn : m ≤ n)
    (hxy : PadicInt.toZModPow m x ≠ PadicInt.toZModPow m y) :
    PadicInt.toZModPow n x ≠ PadicInt.toZModPow n y := by
  intro h
  apply hxy
  rw [← PadicInt.cast_toZModPow m n hmn x, ← PadicInt.cast_toZModPow m n hmn y, h]

/-- Distinct p-adic integers are separated by some finite quotient. -/
theorem exists_reduction_ne {x y : ℤ_[p]} (hxy : x ≠ y) :
    ∃ n : ℕ, PadicInt.toZModPow n x ≠ PadicInt.toZModPow n y := by
  by_contra h
  apply hxy
  exact PadicInt.ext_of_toZModPow.mp (by simpa only [not_exists, not_not] using h)

/-- A finite collection of unequal p-adic pairs has one common positive
level above which every pair remains separated. -/
theorem finite_uniform_reduction_separation {ι : Type*} (s : Finset ι)
    (x y : ι → ℤ_[p]) (hxy : ∀ i ∈ s, x i ≠ y i) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ i ∈ s,
      PadicInt.toZModPow n (x i) ≠ PadicInt.toZModPow n (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, by simp⟩
  | @insert i s his ih =>
    obtain ⟨N, hN, hs⟩ := ih (fun j hj => hxy j (Finset.mem_insert_of_mem hj))
    obtain ⟨m, hm⟩ := exists_reduction_ne (hxy i (Finset.mem_insert_self _ _))
    refine ⟨max N m, hN.trans (le_max_left _ _), ?_⟩
    intro n hn j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact reduction_ne_of_le ((le_max_right _ _).trans hn) hm
    · exact hs n ((le_max_left _ _).trans hn) j hj

/-- The specialization used in the paper: for finitely many integral word
traces and a bounded positive exponent, every sufficiently deep congruence
quotient separates the diagonal holonomy trace from all the word traces.

For a nonzero signed charge, use its positive absolute value; the diagonal
trace is unchanged by reversing the sign. -/
theorem finite_trace_separation (t : ℤ_[p]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[p])) (A : ℕ) (traces : Finset ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n, N ≤ n → ∀ m ∈ Finset.Icc 1 A, ∀ c ∈ traces,
      PadicInt.toZModPow n (diagonalTrace t m) ≠ (c : ZMod (p ^ n)) := by
  obtain ⟨N, hN, hsep⟩ := finite_uniform_reduction_separation
    ((Finset.Icc 1 A).product traces)
    (fun q => diagonalTrace t q.1) (fun q => (q.2 : ℤ_[p])) (by
      intro q hq
      have hqm := (Finset.mem_product.mp hq).1
      exact diagonalTrace_ne_int t ht (Finset.mem_Icc.mp hqm).1 q.2)
  refine ⟨N, hN, ?_⟩
  intro n hn m hm c hc
  simpa only [map_intCast] using hsep n hn (m, c) (Finset.mem_product.mpr ⟨hm, hc⟩)

end FiniteReduction

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TraceObstruction
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.holonomyCharge_reduceSteps _root_.OAI.CoarseAssembly.Congruence.holonomyWord_reduceSteps _root_.OAI.CoarseAssembly.Congruence.quotientMap_comp _root_.OAI.CoarseAssembly.Congruence.quotientMap_holonomy _root_.OAI.CoarseAssembly.Congruence.quotientMap_reduce _root_.OAI.CoarseAssembly.Congruence.quotientMap_self _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix trace separation in the congruence quotients

The elementary p-adic separation result is connected here to the actual
`SL₃` matrices and to the closed-walk holonomy identity.
-/

namespace CoarseAssembly.Congruence

/-- The finite matrix trace is the reduction of the p-adic Laurent trace. -/
theorem trace_holonomy_pow (t : ℤ_[2]ˣ) (k m : ℕ) :
    Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
      PadicInt.toZModPow k (diagonalTrace t m) := by
  rw [holonomy, trace_diagonal_pow]
  simp [diagonalTrace]

/-- The two nontrivial diagonal entries are exchanged when the charge is
negated, so the trace only depends on its absolute value. -/
theorem trace_holonomy_natAbs (t : ℤ_[2]ˣ) (k : ℕ) (m : ℤ) :
    Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
    Matrix.trace ((holonomy t k ^ m.natAbs : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  cases m with
  | ofNat n =>
    exact congrArg
      (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
      (zpow_natCast (holonomy t k) n)
  | negSucc n =>
    change Matrix.trace ((holonomy t k ^ (-((n + 1 : ℕ) : ℤ)) : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) = _
    calc
      _ = Matrix.trace ((holonomy t k ^ (((n + 1 : ℕ) : ℤ)) : Quotient k) :
          Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :=
        trace_diagonal_neg _ _
      _ = _ := congrArg
        (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
        (zpow_natCast (holonomy t k) (n + 1))

/-- Simultaneous trace separation from a finite set of integral word traces,
now stated for the actual finite special linear groups. -/
theorem matrix_trace_separation (t : ℤ_[2]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[2])) (A : ℕ) (traces : Finset ℤ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ m ∈ Finset.Icc 1 A,
      ∀ w : ArithmeticGroup, Matrix.trace (w : Matrix (Fin 3) (Fin 3) ℤ) ∈ traces →
        Matrix.trace ((holonomy t k ^ m : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) ≠
          Matrix.trace (reduce k w : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) := by
  obtain ⟨N, hN, hsep⟩ := finite_trace_separation t ht A traces
  refine ⟨N, hN, ?_⟩
  intro k hk m hm w hw
  rw [trace_holonomy_pow, trace_reduce]
  exact hsep k hk m hm _ hw

/-- A closed word in a finite quotient forces equality of the concrete
matrix traces. This is the contradiction paired with separation above. -/
theorem closed_walk_trace (t : ℤ_[2]ˣ) (k : ℕ) (z : Quotient k)
    (steps : List (Quotient k × ℤ))
    (hclosed : holonomyEndpoint (holonomy t k) steps z = z) :
    Matrix.trace ((holonomy t k ^ holonomyCharge steps : Quotient k) :
      Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) =
    Matrix.trace (((holonomyWord steps)⁻¹ : Quotient k) : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))) :=
  holonomy_invariant_eq
    (fun q : Quotient k => Matrix.trace (q : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ k))))
    (fun q z => trace_conjugate q z) (holonomy t k) z steps hclosed

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteWords
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Congruence.quotientMap_reduce _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform exclusion of short charged closed words

This is the algebraic part of the small-loop lemma in §3, specialized to
`SL₃(ℤ)` and its actual congruence quotients. The finite family of possible
word traces is constructed, rather than postulated as an extra input.
-/

namespace CoarseAssembly.Congruence

theorem wordBall_mono (S : Finset ArithmeticGroup) {n m : ℕ} (h : n ≤ m) :
    wordBall S n ⊆ wordBall S m := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact ih.trans Finset.subset_union_left

theorem holonomyWord_mem (S : Finset ArithmeticGroup) (steps : List (ArithmeticGroup × ℤ))
    (hS : ∀ s ∈ steps, s.1 ∈ S) : holonomyWord steps ∈ wordBall S steps.length := by
  induction steps with
  | nil => simp [holonomyWord, wordBall]
  | cons s steps ih =>
    have hs : s.1 ∈ S := hS s (by simp)
    have ht : ∀ q ∈ steps, q.1 ∈ S := fun q hq => hS q (by simp [hq])
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨holonomyWord steps, ih ht,
      Finset.mem_image.mpr ⟨s.1, hs, rfl⟩⟩

theorem holonomyCharge_natAbs_le (steps : List (ArithmeticGroup × ℤ))
    (hs : ∀ s ∈ steps, s.2.natAbs ≤ 1) : (holonomyCharge steps).natAbs ≤ steps.length := by
  induction steps with
  | nil => simp [holonomyCharge]
  | cons s steps ih =>
    have hhead : s.2.natAbs ≤ 1 := hs s (by simp)
    have htail : (holonomyCharge steps).natAbs ≤ steps.length :=
      ih (fun q hq => hs q (by simp [hq]))
    exact (Int.natAbs_add_le _ _).trans (by simpa [Nat.add_comm] using Nat.add_le_add hhead htail)

/-- At a sufficiently deep quotient, no bounded list of allowed Cayley/base
moves can close with nonzero charge. This conclusion does not assume a
spectral gap, a property-(T) theorem, or an analytic K-homology fact. -/
theorem bounded_closed_lifts_have_zero_charge (t : ℤ_[2]ˣ)
    (ht : Transcendental ℤ (t : ℤ_[2])) (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ z : Quotient k,
      ∀ steps : List (ArithmeticGroup × ℤ), steps.length ≤ A →
        (∀ s ∈ steps, s.1 ∈ S ∧ s.2.natAbs ≤ 1) →
        holonomyEndpoint (holonomy t k) (reduceSteps k steps) z = z →
        holonomyCharge steps = 0 := by
  let traces := (wordBall S A).image
    (fun w => Matrix.trace ((w⁻¹ : ArithmeticGroup) : Matrix (Fin 3) (Fin 3) ℤ))
  obtain ⟨N, hN, hsep⟩ := matrix_trace_separation t ht A traces
  refine ⟨N, hN, ?_⟩
  intro k hk z steps hlen hsteps hclosed
  by_contra hcharge
  have hpos : 1 ≤ (holonomyCharge steps).natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcharge)
  have hbound : (holonomyCharge steps).natAbs ≤ A :=
    (holonomyCharge_natAbs_le steps (fun s hs => (hsteps s hs).2)).trans hlen
  have hword : holonomyWord steps ∈ wordBall S A :=
    wordBall_mono S hlen (holonomyWord_mem S steps (fun s hs => (hsteps s hs).1))
  have htrace : Matrix.trace (((holonomyWord steps)⁻¹ : ArithmeticGroup) :
      Matrix (Fin 3) (Fin 3) ℤ) ∈ traces :=
    Finset.mem_image.mpr ⟨holonomyWord steps, hword, rfl⟩
  have hne := hsep k hk (holonomyCharge steps).natAbs
    (Finset.mem_Icc.mpr ⟨hpos, hbound⟩) (holonomyWord steps)⁻¹ htrace
  apply hne
  rw [← trace_holonomy_natAbs]
  simpa only [holonomyCharge_reduceSteps, holonomyWord_reduceSteps, map_inv] using
    closed_walk_trace t k z (reduceSteps k steps) hclosed

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_TranscendentalUnit
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionMetric _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A transcendental principal p-adic unit

The holonomy construction chooses a transcendental element of `1 + 2ℤ₂`.
The existence proof below works for every prime: algebraic elements form a
countable set, and the Baire theorem makes its complement dense in the
complete, perfect p-adic field.
-/

namespace CoarseAssembly

open Set

variable {p : ℕ} [Fact p.Prime]

/-- Transcendental elements over the integers are dense in the p-adic field. -/
theorem dense_padic_transcendental : Dense {x : ℚ_[p] | Transcendental ℤ x} := by
  have hcount : Set.Countable {x : ℚ_[p] | IsAlgebraic ℤ x} :=
    Algebraic.countable ℤ ℚ_[p]
  have hd : Dense (⋂ x ∈ {x : ℚ_[p] | IsAlgebraic ℤ x}, ({x}ᶜ : Set ℚ_[p])) :=
    dense_biInter_of_isOpen (fun _ _ => isOpen_compl_singleton) hcount
      (fun x _ => dense_compl_singleton x)
  apply hd.mono
  intro x hx hxalg
  have hxnot := Set.mem_iInter₂.mp hx x hxalg
  exact hxnot (Set.mem_singleton x)

/-- The exact principal-unit choice needed for diagonal holonomy exists.
The specialization `p = 2` lies in `1 + 2ℤ₂`. -/
theorem exists_transcendental_principal_unit :
    ∃ t : ℤ_[p]ˣ, Transcendental ℤ (t : ℤ_[p]) ∧
      ∃ a : ℤ_[p], (t : ℤ_[p]) = 1 + (p : ℤ_[p]) * a := by
  obtain ⟨x, hx, hclose⟩ :=
    (dense_padic_transcendental (p := p)).exists_dist_lt (1 : ℚ_[p]) zero_lt_one
  have hnear : ‖x - 1‖ < 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hclose
  have hxnorm : ‖x‖ = 1 := by
    simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right
      (show ‖x - 1‖ < ‖(1 : ℚ_[p])‖ by simpa using hnear)
  let z : ℤ_[p] := ⟨x, hxnorm.le⟩
  have hznorm : ‖z‖ = 1 := hxnorm
  obtain ⟨t, ht⟩ := PadicInt.isUnit_iff.mpr hznorm
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    intro hzalg
    let f : ℤ_[p] →ₐ[ℤ] ℚ_[p] :=
      { PadicInt.Coe.ringHom with commutes' := fun n => by simp }
    exact hx (hzalg.algHom f)
  · have hzclose : ‖z - 1‖ < 1 := hnear
    obtain ⟨a, ha⟩ := (PadicInt.norm_lt_one_iff_dvd (z - 1)).mp hzclose
    refine ⟨a, ?_⟩
    rw [ht]
    linear_combination ha

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ChosenHolonomy
attribute [-instance] _root_.OAI.CoarseAssembly.Congruence.quotientZeroSubsingleton _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single principal holonomy for all finite scales

The choice in §3 is made once. The separation level can then depend on the
length bound, without changing the chosen 2-adic unit.
-/

namespace CoarseAssembly.Congruence

theorem chosenHolonomyUnit_transcendental :
    Transcendental ℤ (chosenHolonomyUnit : ℤ_[2]) :=
  (exists_transcendental_principal_unit (p := 2)).choose_spec.1

/-- The fixed principal holonomy excludes short charged closed lifts at every
finite length bound. This is an arithmetic statement, not a coarse assembly
or K-homology theorem. -/
theorem chosenHolonomy_short_lifts (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k, N ≤ k → ∀ z : Quotient k,
      ∀ steps : List (ArithmeticGroup × ℤ), steps.length ≤ A →
        (∀ s ∈ steps, s.1 ∈ S ∧ s.2.natAbs ≤ 1) →
        holonomyEndpoint (holonomy chosenHolonomyUnit k) (reduceSteps k steps) z = z →
        holonomyCharge steps = 0 :=
  bounded_closed_lifts_have_zero_charge chosenHolonomyUnit
    chosenHolonomyUnit_transcendental S A

end CoarseAssembly.Congruence

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ShortLoops
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Short loops and the Rips edge cocycle

The combinatorial step in §4 of the coarse Novikov manuscript. The only
hypothesis on the charge is vanishing on short closed graph walks, exactly
the output required from the manuscript's small-loop lemma. This is a
conditional combinatorial result, not an assumption about analytic K-homology.
-/

namespace CoarseAssembly

variable {V : Type*} {G : SimpleGraph V}

/-- Unit graph edges retain their original charges in the Rips cocycle. -/
theorem ripsCharge_on_edge (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (h : G.Adj u v) : ripsCharge hG a u v = a u v := by
  rw [ripsCharge_eq_walkCharge hG a ha r hloop h.toWalk (by simpa using hr)]
  simp [SimpleGraph.Adj.toWalk]

/-- In particular, the same boundary walk has the same winding charge after
passing to a Rips scale. -/
theorem ripsCharge_on_walk (hG : G.Connected) (a : V → V → ℤ)
    (ha : ∀ u v, G.Adj u v → a v u = -a u v) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ u (p : G.Walk u u), p.length ≤ 2 * r → walkCharge a p = 0)
    {u v : V} (p : G.Walk u v) :
    walkCharge (ripsCharge hG a) p = walkCharge a p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [walkCharge_cons, ripsCharge_on_edge hG a ha r hr hloop h, ih]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LatticeCharge
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.discHatWeights_apply _root_.OAI.CoarseAssembly.latticeHatWeights_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A combinatorial ray charge and the half-plane argument

We use a half-open cut along the positive horizontal ray: an edge entering
height zero from below has charge one exactly when its endpoint has positive
first coordinate. This is a combinatorial convention at ray vertices; edges
incident to the origin have charge zero. Its restriction to any of the six
open lattice half-planes is an exact difference of vertex potentials.
-/

namespace CoarseAssembly

theorem latticeCharge_reverse (u v : LatticeVertex) : latticeCharge v u = -latticeCharge u v := by
  simp only [latticeCharge]
  split_ifs <;> omega

theorem HexDirection.adj_bound (d : HexDirection) {u v : LatticeVertex}
    (h : triangularGraph.Adj u v) : |d.eval u - d.eval v| ≤ 1 := by
  rcases h with ⟨ha, hb, hab, _⟩
  rw [abs_le] at ha hb hab ⊢
  cases d <;> simp only [HexDirection.eval] <;> omega

theorem HexDirection.radius_witness (u : LatticeVertex) :
    ∃ d : HexDirection, d.eval u = latticeRadius u := by
  simp only [latticeRadius]
  rcases le_total |u.1| |u.2| with h | h
  · rw [max_eq_right h]
    rcases le_total |u.2| |u.1 + u.2| with h' | h'
    · rw [max_eq_right h']
      by_cases hs : 0 ≤ u.1 + u.2
      · exact ⟨.sum, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negSum, (abs_of_neg (by omega)).symm⟩
    · rw [max_eq_left h']
      by_cases hs : 0 ≤ u.2
      · exact ⟨.b, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negB, (abs_of_neg (by omega)).symm⟩
  · rw [max_eq_left h]
    rcases le_total |u.1| |u.1 + u.2| with h' | h'
    · rw [max_eq_right h']
      by_cases hs : 0 ≤ u.1 + u.2
      · exact ⟨.sum, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negSum, (abs_of_neg (by omega)).symm⟩
    · rw [max_eq_left h']
      by_cases hs : 0 ≤ u.1
      · exact ⟨.a, (abs_of_nonneg hs).symm⟩
      · exact ⟨.negA, (abs_of_neg (by omega)).symm⟩

/-- Exactness on all six open half-planes is the winding-zero argument,
including repeated edges and stationary projections. -/
theorem latticeCharge_halfPlane (d : HexDirection) {u v : LatticeVertex}
    (h : u = v ∨ triangularGraph.Adj u v) (hu : 0 < d.eval u) (hv : 0 < d.eval v) :
    latticeCharge u v = d.potential v - d.potential u := by
  rcases h with rfl | h
  · simp
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, e⟩
  simp only [triangularGraph, abs_le] at h
  cases d <;> simp only [HexDirection.eval, HexDirection.potential, latticeCharge] at * <;>
    split_ifs <;> omega

section ProjectedWalks

variable {V : Type*} {G : SimpleGraph V} (π : V → LatticeVertex)
variable (hπ : ∀ u v, G.Adj u v → π u = π v ∨ triangularGraph.Adj (π u) (π v))

include hπ

theorem projected_functional_bound (d : HexDirection) {u v : V} (p : G.Walk u v) :
    |d.eval (π u) - d.eval (π v)| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have he : |d.eval (π u) - d.eval (π v)| ≤ 1 := by
      rcases hπ u v h with he | he
      · simp [he]
      · exact d.adj_bound he
    calc
      _ ≤ |d.eval (π u) - d.eval (π v)| + |d.eval (π v) - d.eval (π w)| :=
        abs_sub_le _ _ _
      _ ≤ 1 + (p.length : ℤ) := add_le_add he ih
      _ = ((SimpleGraph.Walk.cons h p).length : ℤ) := by simp; omega

theorem projected_charge_exact (d : HexDirection) {u v : V} (p : G.Walk u v)
    (hp : ∀ w ∈ p.support, 0 < d.eval (π w)) :
    walkCharge (fun u v => latticeCharge (π u) (π v)) p =
      d.potential (π v) - d.potential (π u) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have hu := hp u (by simp)
    have htail : ∀ z ∈ p.support, 0 < d.eval (π z) := by
      intro z hz
      exact hp z (by simp [hz])
    rw [walkCharge_cons, latticeCharge_halfPlane d (hπ u v h) hu
      (htail v p.start_mem_support), ih htail]
    omega

/-- A charged closed path must meet the nonpositive side of every one of
the six linear functionals. -/
theorem charged_walk_meets_halfPlane (d : HexDirection) {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0) :
    ∃ w ∈ p.support, d.eval (π w) ≤ 0 := by
  by_contra h
  push Not at h
  have hz := projected_charge_exact π hπ d p h
  exact hc (by simpa using hz)

/-- The geometric estimate in the small-loop lemma. -/
theorem charged_walk_radius_bound {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0) :
    2 * latticeRadius (π u) ≤ (p.length : ℤ) := by
  obtain ⟨d, hd⟩ := HexDirection.radius_witness (π u)
  obtain ⟨w, hw, hf⟩ := charged_walk_meets_halfPlane π hπ d p hc
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hw
  have hq := projected_functional_bound π hπ d q
  have hr := projected_functional_bound π hπ d r
  rw [abs_le] at hq hr
  simp only [SimpleGraph.Walk.length_append, Nat.cast_add]
  omega

/-- The same estimate holds at every occurrence of a vertex, by rotating
the closed walk. No simplicity hypothesis is needed. -/
theorem charged_walk_all_radius_bound {u : V} (p : G.Walk u u)
    (hc : walkCharge (fun u v => latticeCharge (π u) (π v)) p ≠ 0)
    {w : V} (hw : w ∈ p.support) :
    2 * latticeRadius (π w) ≤ (p.length : ℤ) := by
  obtain ⟨q, r, rfl⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hw
  have hrot : walkCharge (fun u v => latticeCharge (π u) (π v)) (r.append q) ≠ 0 := by
    simpa only [walkCharge_append, add_comm] using hc
  have hb := charged_walk_radius_bound π hπ (r.append q) hrot
  simpa only [SimpleGraph.Walk.length_append, Nat.add_comm] using hb

end ProjectedWalks

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberedGraph
attribute [-instance] _root_.OAI.CoarseAssembly.discGraphMetric _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.CoarseAssembly.discBoundaryBase_depth _root_.OAI.CoarseAssembly.discHatWeights_apply _root_.OAI.CoarseAssembly.latticeHatWeights_apply _root_.OAI.CoarseAssembly.mem_baseNeighbors _root_.OAI.CoarseAssembly.mem_fiberedNeighbors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite graph with congruence fibers

The inter-fiber edge relation is written at the common shallower level.
This uniformly describes the equal-depth, parent and child cases. The
generating set is symmetrized and contains the identity to record pure
base moves in a common list of left/right operations.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem fiberedGraph_projects {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x y : FiberVertex j) (h : (fiberedGraph S t j).Adj x y) :
    x.1.val = y.1.val ∨ triangularGraph.Adj x.1.val y.1.val := by
  obtain ⟨s, hs, hp, he⟩ := h.2
  exact hp.elim (fun e => Or.inl (congrArg Subtype.val e)) (fun e => Or.inr e.1)

/-- An edge has the same left/right description at every lower common level. -/
theorem liftStep_reduce {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j l : ℕ}
    {x y : FiberVertex j} (h : LiftStep S t x y)
    (hx : l ≤ discDepth j x.1) (hy : l ≤ discDepth j y.1) :
    ∃ s ∈ symmetricMoves S,
      fiberCoordinate y hy = reduce l s * fiberCoordinate x hx *
        holonomy t l ^ fiberCharge x y := by
  obtain ⟨s, hs, hp, he⟩ := h
  exact ⟨s, hs, he l hx hy⟩

/-- Record every edge of a walk as an integral left move and a ray charge,
after reducing all its coordinates to one common level. -/
theorem walk_reduced_lift {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    {u v : FiberVertex j} (p : (fiberedGraph S t j).Walk u v) (l : ℕ)
    (hp : ∀ w ∈ p.support, l ≤ discDepth j w.1) :
    ∃ steps : List (ArithmeticGroup × ℤ),
      steps.length = p.length ∧
      holonomyCharge steps = walkCharge fiberCharge p ∧
      (∀ s ∈ steps, s.1 ∈ symmetricMoves S ∧ s.2.natAbs ≤ 1) ∧
      holonomyEndpoint (holonomy t l) (reduceSteps l steps)
          (fiberCoordinate u (hp u p.start_mem_support)) =
        fiberCoordinate v (hp v p.end_mem_support) := by
  induction p with
  | nil => exact ⟨[], rfl, rfl, by simp, rfl⟩
  | @cons u v w h p ih =>
    have ht : ∀ z ∈ p.support, l ≤ discDepth j z.1 :=
      fun z hz => hp z (by simp [hz])
    obtain ⟨s, hs, he⟩ := liftStep_reduce h.2 (hp u (by simp))
      (hp v (by simp))
    obtain ⟨steps, hlen, hcharge, hsteps, hend⟩ := ih ht
    refine ⟨(s, fiberCharge u v) :: steps, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_cons, SimpleGraph.Walk.length_cons] using congrArg (· + 1) hlen
    · simp only [holonomyCharge, walkCharge_cons, hcharge]
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · refine ⟨hs, ?_⟩
        simp only [fiberCharge, latticeCharge]
        split_ifs <;> norm_num
      · exact hsteps a ha
    · simpa only [reduceSteps, List.map_cons, holonomyEndpoint, ← he] using hend

/-- The manuscript's small-loop assertion for the actual finite fibered
graphs. The radius estimate supplies a common deep quotient; arithmetic
trace separation then forces the ray charge to vanish. -/
theorem fiberedGraph_short_loops (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ u : FiberVertex j,
      ∀ p : (fiberedGraph S chosenHolonomyUnit j).Walk u u,
        p.length ≤ A → walkCharge fiberCharge p = 0 := by
  obtain ⟨N, hN, hsep⟩ := chosenHolonomy_short_lifts (symmetricMoves S) A
  refine ⟨N + A / 2, ?_⟩
  intro j hj u p hlen
  by_contra hc
  have hdepth : ∀ w ∈ p.support, N ≤ discDepth j w.1 := by
    intro w hw
    have hr := charged_walk_all_radius_bound (fun v : FiberVertex j => v.1.val)
      (fiberedGraph_projects) p hc hw
    have hd := discDepth_int j w.1
    omega
  obtain ⟨steps, hstepslen, hcharge, hsteps, hend⟩ := walk_reduced_lift p N hdepth
  have hz := hsep N le_rfl (fiberCoordinate u (hdepth u p.start_mem_support))
    steps (hstepslen.trans_le hlen) hsteps hend
  exact hc (hcharge ▸ hz)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_GraphMetric
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The metric of a connected graph

The metric on a connected graph is exactly the real-valued shortest-path
length. A proof-independent extension uses the discrete metric otherwise.
-/

noncomputable section

namespace CoarseAssembly

variable {V : Type*} (G : SimpleGraph V)

theorem graphMetric_separated (hG : G.Connected) {x y : V} (hxy : x ≠ y) :
    (1 : ℝ) ≤ @dist V (graphMetric G hG).toDist x y := by
  rw [graphMetric_eq]
  change (1 : ℝ) ≤ (G.dist x y : ℝ)
  exact_mod_cast hG.pos_dist_of_ne hxy

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SeparatedGeometry
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded geometry of the separated union

Uniform component ball bounds pass to the union. All cross-component pairs
in a fixed distance range lie in a finite prefix, which also supplies the
finite exceptional set in the transfer argument.
-/

noncomputable section

namespace CoarseAssembly

variable {V : ℕ → Type*} [∀ i, MetricSpace (V i)] [∀ i, Fintype (V i)]

omit [∀ i, Fintype (V i)] in
/-- Unit separation in each component gives unit separation in the union. -/
theorem separated_uniform_discrete (o : ∀ i, V i)
    (hcomp : ∀ i (x y : V i), x ≠ y → 1 ≤ dist x y)
    (x y : Sigma V) (hxy : x ≠ y) : 1 ≤ separatedDist o x y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases hij : i = j
  · subst j
    rw [separatedDist_same]
    exact hcomp i x y (fun h => hxy (congrArg (Sigma.mk i) h))
  · rw [separatedDist_different o hij]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith [dist_nonneg (x := x) (y := o i), dist_nonneg (x := o j) (y := y)]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConcreteSpaces
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual base and fibered coarse unions

Both metrics restrict to shortest-path metrics on the components. The
fibered union is indexed by base vertices so its Hilbert module has exactly
the form used by the finite-fiber transfer theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem vertexUnion_separated (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    (x y : VertexUnion) (h : x ≠ y) :
    1 ≤ @dist VertexUnion (vertexUnionMetric S t).toDist x y := by
  let := componentMetric S t
  let e := Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u))
  exact separated_uniform_discrete fiberBoundaryBase
    (fun j _x _y h => by
      change 1 ≤ @dist _ (componentMetric S t j).toDist _x _y
      rw [componentMetric_eq, ← graphMetric_eq]
      exact graphMetric_separated (fiberedGraph S t j)
        (fiberedGraph_connected S t j) h) (e x) (e y) (fun he => h (e.injective he))

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryEmbedding
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.discHatWeights_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact spatial boundary factorization

Boundary fibers have depth zero and are singletons. The normalized fiber
embedding therefore agrees exactly with the coordinate inclusion there,
which proves the operator factorization needed by assembly naturality.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem fiberEmbedding_boundary :
    (fiberEmbedding (H := H) BaseFiber).comp boundaryBaseIsometry = boundaryVertexIsometry := by
  classical
  have he : (fiberEmbedding (H := H) BaseFiber).toContinuousLinearMap.comp
      (boundaryBaseIsometry.toContinuousLinearMap) =
      boundaryVertexIsometry.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro b
    apply ContinuousLinearMap.ext
    intro h
    change fiberEmbedding BaseFiber (inclusionIsometry boundaryToBase (lp.single 2 b h)) =
      inclusionIsometry boundaryToVertex (lp.single 2 b h)
    rw [inclusionIsometry_single, inclusionIsometry_single]
    have : Subsingleton (BaseFiber b.val) := by
      change Subsingleton (Quotient (discDepth b.val.1 b.val.2))
      rw [b.property]
      infer_instance
    exact fiberEmbedding_singleton BaseFiber b.val 1 h
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun he x

theorem boundary_operator_factorization
    (T : lp (fun _ : BoundaryVertex => H) 2 →L[ℂ] lp (fun _ : BoundaryVertex => H) 2) :
    operatorConjugation (fiberEmbedding BaseFiber) (operatorConjugation boundaryBaseIsometry T) =
      operatorConjugation boundaryVertexIsometry T := by
  rw [operatorConjugation_comp, fiberEmbedding_boundary]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_LoopCircle
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parametrizing a closed path by the circle

The interval endpoints are identified using Mathlib's quotient-circle
construction. The resulting continuous map agrees with the path on the
entire closed interval, including its identified endpoint.
-/

noncomputable section

namespace CoarseAssembly

open unitInterval

variable {Y : Type*} [TopologicalSpace Y] {y : Y}

theorem loopCircle_integerLift {f : Y → WindingCircle} (γ : Path y y) {n : ℤ}
    (L : IntegerPathLift f γ n) (t : unitInterval) :
    f (loopCircle γ (t : ℝ)) = (L.path t : WindingCircle) := by
  rw [loopCircle_apply]
  exact L.commutes t

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CirclePairing
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise published circle-index input

Only the scalar-unitary index pairing, its naturality for a parametrized
loop, and the classical winding formula are assumed. The domain groups
are the Fredholm-module groups.

References: Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998),
Proposition 18.7.1 and Corollary 18.10.3; Khalkhali, *Basic Noncommutative
Geometry* (2009), Example 4.2.4, with the sign convention of manuscript §2.3.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The constructed real lift is sufficient for the published index formula. -/
theorem PublishedCircleInput.loop_pairing (input : PublishedCircleInput)
    [CompactSpace Y] [T2Space Y] {y : Y}
    (f : C(Y, WindingCircle)) (γ : Path y y) (n : ℤ)
    (L : IntegerPathLift f γ n) :
    input.pairing f (pushforward (compactMap (loopCircle γ)) input.fundamental) = n := by
  rw [input.loop_naturality]
  apply input.winding _ n L.path
  intro t
  exact loopCircle_integerLift γ L t

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledEdges
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.mapPoint_weight_self _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear edges in the filled polygon

The polygon's straight paths map to the actual barycentric Rips edges.
These identities supply the filling factorization of the boundary walk.
-/

noncomputable section

namespace CoarseAssembly

open Rips

theorem latticeHat_vertex (u v : LatticeVertex) :
    latticeHat (realVertex u) v = if v = u then 1 else 0 := by
  classical
  by_cases h : v = u
  · subst v
    simp [latticeHat, realVertex, hatKernel, realLatticeRadius]
  · rw [ite_eq_right h]
    apply le_antisymm _ (latticeHat_nonneg _ _)
    by_contra hn
    have hp := (latticeHat_pos_iff (realVertex u) v).mp (lt_of_not_ge hn)
    dsimp only [realVertex] at hp
    have hx : |u.1 - v.1| < 1 := by exact_mod_cast hp.1
    have hy : |u.2 - v.2| < 1 := by exact_mod_cast hp.2.1
    rw [abs_lt] at hx hy
    apply h
    exact (Prod.ext (by omega) (by omega) : u = v).symm

@[simp] theorem filledToRips_vertex {j : ℕ} (v : Disc j) :
    filledToRipsPoint j (filledVertex v) = vertex v (by norm_num) := by
  classical
  apply Point.ext
  apply Finsupp.ext
  intro w
  change latticeHat (realVertex v.val) w.val = (Finsupp.single v (1 : ℝ)) w
  rw [latticeHat_vertex]
  by_cases h : w = v
  · subst w
    simp
  · have hv : v ≠ w := Ne.symm h
    have hc : w.val ≠ v.val := fun hc => h (Subtype.ext hc)
    simp [hv, hc]

theorem realLatticeRadius_adj_difference {j : ℕ} {u v : Disc j}
    (h : (discGraph j).Adj u v) : realLatticeRadius (realVertex v.val - realVertex u.val) = 1 := by
  have hx := h.1
  have hy := h.2.1
  have hn := h.2.2.2
  have hsum := h.2.2.1
  have hr : latticeRadius (v.val - u.val) = 1 := by
    change max (max |v.val.1 - u.val.1| |v.val.2 - u.val.2|)
      |(v.val.1 - u.val.1) + (v.val.2 - u.val.2)| = 1
    rw [abs_sub_comm] at hx hy hsum
    have hz : v.val.1 - u.val.1 + (v.val.2 - u.val.2) =
        (v.val.1 + v.val.2) - (u.val.1 + u.val.2) := by ring
    rw [hz]
    have hne : u.val.1 ≠ v.val.1 ∨ u.val.2 ≠ v.val.2 := by
      by_contra! hneg
      exact hn (Prod.ext hneg.1 hneg.2)
    apply le_antisymm (max_le (max_le hx hy) hsum)
    rcases hne with hx' | hy'
    · have hpos : 0 < |v.val.1 - u.val.1| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx'))
      exact (show 1 ≤ |v.val.1 - u.val.1| by omega).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · have hpos : 0 < |v.val.2 - u.val.2| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hy'))
      exact (show 1 ≤ |v.val.2 - u.val.2| by omega).trans
        ((le_max_right _ _).trans (le_max_left _ _))
  have he : realVertex v.val - realVertex u.val = realVertex (v.val - u.val) := by
    ext <;> simp [realVertex]
  rw [he, realLatticeRadius_vertex, hr]
  norm_num

theorem latticeHat_eq_radius (p : ℝ × ℝ) (v : LatticeVertex) :
    latticeHat p v = max 0 (1 - realLatticeRadius (p - realVertex v)) := rfl

theorem filledSegment_hat_left {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    latticeHat (filledSegment (filledVertex u) (filledVertex v) t).val u.val = 1 - (t : ℝ) := by
  rw [latticeHat_eq_radius]
  have he : (filledSegment (filledVertex u) (filledVertex v) t).val - realVertex u.val =
      (t : ℝ) • (realVertex v.val - realVertex u.val) := by
    rw [filledSegment_val]
    ext <;> simp [filledVertex] <;> ring
  rw [he, realLatticeRadius_smul _ t.2.1, realLatticeRadius_adj_difference h, mul_one,
    max_eq_right (sub_nonneg.mpr t.2.2)]

theorem filledSegment_hat_right {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    latticeHat (filledSegment (filledVertex u) (filledVertex v) t).val v.val = (t : ℝ) := by
  rw [latticeHat_eq_radius]
  have he : (filledSegment (filledVertex u) (filledVertex v) t).val - realVertex v.val =
      (1 - (t : ℝ)) • (realVertex u.val - realVertex v.val) := by
    rw [filledSegment_val]
    ext <;> simp [filledVertex] <;> ring
  rw [he, realLatticeRadius_smul _ (sub_nonneg.mpr t.2.2),
    realLatticeRadius_adj_difference h.symm, mul_one,
    max_eq_right (by linarith [t.2.1] : 0 ≤ 1 - (1 - (t : ℝ)))]
  ring

theorem Rips.Point.weight_zero_of_two {X : Type*} [PseudoMetricSpace X] [Fintype X]
    {r : ℝ} (p : Point X r) {x y z : X} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hs : p.weight x + p.weight y = 1) : p.weight z = 0 := by
  classical
  have hle : (∑ w ∈ ({x, y, z} : Finset X), p.weight w) ≤ ∑ w : X, p.weight w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => p.nonneg w)
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  simp only [Finset.sum_insert (by simp [hxy, hxz] : x ∉ ({y, z} : Finset X)),
    Finset.sum_insert (by simp [hyz] : y ∉ ({z} : Finset X)), Finset.sum_singleton,
    p.sum_weight] at hle
  exact le_antisymm (by linarith) (p.nonneg z)

/-- The actual hat-function filling agrees exactly with the Rips edge. -/
theorem filledToRips_edge {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    filledToRipsPoint j (filledSegment (filledVertex u) (filledVertex v) t) =
      edgePath (show dist u v ≤ (1 : ℝ) by
        rw [discGraphMetric_eq]
        change ((discGraph j).dist u v : ℝ) ≤ 1
        exact_mod_cast (show (discGraph j).dist u v ≤ 1 by
          simpa using (discGraph j).dist_le h.toWalk)) t := by
  classical
  let p := filledToRipsPoint j (filledSegment (filledVertex u) (filledVertex v) t)
  have hleft : p.weight u = 1 - (t : ℝ) := filledSegment_hat_left h t
  have hright : p.weight v = (t : ℝ) := filledSegment_hat_right h t
  have huv : u ≠ v := fun he => h.2.2.2 (congrArg Subtype.val he)
  apply Point.ext
  apply Finsupp.ext
  intro w
  change p.weight w = (1 - (t : ℝ)) * (Finsupp.single u (1 : ℝ) w) +
    (t : ℝ) * (Finsupp.single v (1 : ℝ) w)
  by_cases hwu : w = u
  · subst w
    simpa [Ne.symm huv] using hleft
  by_cases hwv : w = v
  · subst w
    simpa [huv] using hright
  · rw [p.weight_zero_of_two huv hwu hwv (by rw [hleft, hright]; ring)]
    simp [Ne.symm hwu, Ne.symm hwv]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FilledWalks
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.mapPoint_weight_self _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint _root_.OAI.CoarseAssembly.separatedRipsMap_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filling the actual parametrized lattice walks

Straight segments in the compact polygon follow the same concatenation as
the barycentric graph path. Thus every closed base walk, with its original
parametrization, factors through the filled polygon.
-/

noncomputable section

namespace CoarseAssembly

open Rips

theorem filledToRips_walk {j : ℕ} {u v : Disc j} (p : (discGraph j).Walk u v)
    (t : unitInterval) :
    filledToRipsPoint j (filledWalk p t) =
      walkPath (by norm_num : (0 : ℝ) ≤ 1) discEdgeBound p t := by
  induction p generalizing t with
  | nil => exact filledToRips_vertex _
  | cons h p ih =>
    simp only [filledWalk, walkPath, Path.trans_apply]
    split_ifs
    · exact filledToRips_edge h _
    · exact ih _

/-- Exact factorization through the filled compact polygon, not a homotopy
or a change of parametrization. -/
theorem filledToRips_loop {j : ℕ} {u : Disc j} (p : (discGraph j).Walk u u) :
    (filledToRips j).comp (loopCircle (filledWalk p)) =
      loopCircle (walkPath (by norm_num : (0 : ℝ) ≤ 1) discEdgeBound p) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [ContinuousMap.comp_apply, loopCircle_apply]
  exact filledToRips_walk p t

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryIndex
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The boundary index diagram

The algebraic final calculation in §6 of the coarse Novikov manuscript.
This is a diagram lemma, not a definition or construction of coarse assembly.
The two naturality equations are the precise consequences of Willett--Yu,
*Higher Index Theory*, §§5.1, 6.7, 7.1--7.2 used in that calculation.
The geometric filling and operator factorization remain separate obligations.
-/

namespace CoarseAssembly

variable {HB HD HX KB KD KX : Type*}
variable [AddCommGroup HB] [AddCommGroup HD] [AddCommGroup HX]
variable [AddCommGroup KB] [AddCommGroup KD] [AddCommGroup KX]

/-- Naturality and an actual factorization through a filling annihilate the
index of the included boundary. `filled` is the conclusion of the geometric
filling argument, and `factor` is induced by the proved operator identity
`V E = I`. Neither is being declared to be a published input. -/
theorem boundary_index_zero
    (e : HB →+ HD) (i : HB →+ HX)
    (μB : HB →+ KB) (μD : HD →+ KD) (μX : HX →+ KX)
    (eRoe : KB →+ KD) (iRoe : KB →+ KX) (transfer : KD →+ KX)
    (natural_e : μD.comp e = eRoe.comp μB)
    (natural_i : μX.comp i = iRoe.comp μB)
    (factor : transfer.comp eRoe = iRoe)
    (β : HB) (filled : e β = 0) : μX (i β) = 0 := by
  calc
    μX (i β) = iRoe (μB β) := DFunLike.congr_fun natural_i β
    _ = transfer (eRoe (μB β)) := (DFunLike.congr_fun factor (μB β)).symm
    _ = transfer (μD (e β)) := congrArg transfer (DFunLike.congr_fun natural_e β).symm
    _ = 0 := by rw [filled, map_zero, map_zero]

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryAssemblyMaps
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual boundary assembly diagram

All three Roe maps below are constructed spatial homomorphisms on the
ordinary reduced locally compact Roe algebras. The transfer factorization
is proved before the two published assembly naturality equations are used.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Analytic DiscreteRoe

attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric1

local instance boundaryAssemblyMetric2_rf41b27_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric3
theorem transferRoeHom_boundary (hgap : PublishedKazhdanInput) :
    (transferRoeHom hgap).comp boundaryBaseRoeHom = boundaryTotalRoeHom := by
  apply DFunLike.ext
  intro T
  apply Subtype.ext
  change operatorConjugation (fiberEmbedding (H := AmpleSpace) BaseFiber)
      (operatorConjugation (boundaryBaseIsometry (H := AmpleSpace)) T.1) =
    operatorConjugation (boundaryVertexIsometry (H := AmpleSpace)) T.1
  exact boundary_operator_factorization (H := AmpleSpace) T.1

theorem transferK1_boundary (hgap : PublishedKazhdanInput) :
    (OperatorKTheory.map (transferRoeHom hgap)).comp (OperatorKTheory.map boundaryBaseRoeHom) =
      OperatorKTheory.map boundaryTotalRoeHom := by
  exact (OperatorKTheory.map_comp boundaryBaseRoeHom (transferRoeHom hgap)).symm.trans
    (congrArg OperatorKTheory.map (transferRoeHom_boundary hgap))

/-- Vanishing in the base annihilates the included boundary index by the
proved spatial transfer. Filling is a geometric premise, not a published input. -/
theorem boundary_assembly_zero (input : PublishedBoundaryAssemblyInput)
    (hgap : PublishedKazhdanInput) (β : Rips.KX1 BoundaryVertex)
    (hfilled : boundaryBaseCoarsening.homologyMap β = 0) :
    input.total.assembly (boundaryTotalCoarsening.homologyMap β) = 0 := by
  exact boundary_index_zero boundaryBaseCoarsening.homologyMap
    boundaryTotalCoarsening.homologyMap input.boundary.assembly input.base.assembly
    input.total.assembly (OperatorKTheory.map boundaryBaseRoeHom)
    (OperatorKTheory.map boundaryTotalRoeHom) (OperatorKTheory.map (transferRoeHom hgap))
    (input.boundary.assembly_natural input.base boundaryBaseCoarsening
      boundaryBaseRoeHom input.natural_base)
    (input.boundary.assembly_natural input.total boundaryTotalCoarsening
      boundaryTotalRoeHom input.natural_total)
    (transferK1_boundary hgap) β hfilled

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryWalks
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boundary walks and their canonical lifts

Depth-zero fibers are singletons, so every edge of the actual boundary
subgraph has its unique lift. The walk construction and charge comparison
here leave only the explicit hexagonal boundary walk to be supplied.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem boundary_walk_charge (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    {u v : BoundaryComponent j} (p : (boundaryGraph j).Walk u v) :
    walkCharge fiberCharge (p.map (boundaryFiberHom S t j)) =
      walkCharge (fun x y : Disc j => latticeCharge x.val y.val) (p.map (boundaryBaseHom j)) := by
  rw [walkCharge_map, walkCharge_map]
  rfl

theorem HexagonalBoundaryWalks.fiber_charge_one (w : HexagonalBoundaryWalks)
    (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) (hj : 2 ≤ j) :
    walkCharge fiberCharge (w.fiberWalk S t j) = 1 := by
  exact (boundary_walk_charge S t (w.walk j)).trans (w.charge_one j hj)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyMap
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proper maps from componentwise compact families into Rips realizations

The boundary family will be a countable family of parametrized circles.
Compact subsets of the target use finitely many vertices, hence meet only
finitely many members of this family. This proves properness directly.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

variable [∀ j, Fintype (V j)]

theorem ripsFamilyMap_coarsen (o : ∀ j, V j) {r s : ℝ} (hrs : r ≤ s)
    (γ : ∀ j, C(Z j, Point (V j) r)) (δ : ∀ j, C(Z j, Point (V j) s))
    (hγ : ∀ j z, coarsen hrs (γ j z) = δ j z) :
    letI := separatedMetric o
    (inclusion hrs).comp (ripsFamilyMap o r γ) = ripsFamilyMap o s δ := by
  let := separatedMetric o
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change coarsen hrs (separatedRipsMap o r j (γ j z)) = separatedRipsMap o s j (δ j z)
  dsimp only [separatedRipsMap]
  rw [coarsen_mapPoint, hγ]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsWindingTest
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Winding tests from the short-loop theorem

This connects the proved graph-theoretic small-loop argument to the actual
continuous circle map and its real path lift. It assumes no analytic pairing
or nonvanishing conclusion.
-/

noncomputable section

namespace CoarseAssembly

open Rips

variable {X : Type*} {G : SimpleGraph X}

theorem graphRipsCocycle_on_walk (hG : G.Connected) (a : X → X → ℤ)
    (ha : ∀ x y, G.Adj x y → a y x = -a x y) (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x y : X} (p : G.Walk x y) :
    letI := graphMetric G hG
    walkCharge (graphRipsCocycle hG a ha r hloop).charge p = walkCharge a p := by
  let := graphMetric G hG
  exact ripsCharge_on_walk hG a ha r hr (fun x p hp => hloop x p (by omega)) p

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiniteWindingIndex
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic winding test on a finite Rips component

This derives the finite-component index evaluation from the explicit
published scalar-circle pairing. The cocycle, continuous map, parametrized
loop and its degree are explicit.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable {X : Type} [Fintype X] {G : SimpleGraph X}

/-- The finite-component analytic index is the original graph winding. -/
theorem graph_loop_index (input : PublishedCircleInput) (hG : G.Connected)
    (a : X → X → ℤ) (ha : ∀ x y, G.Adj x y → a y x = -a x y)
    (r : ℕ) (hr : 1 ≤ r)
    (hloop : ∀ x (p : G.Walk x x), p.length ≤ 3 * r → walkCharge a p = 0)
    {x : X} (p : G.Walk x x) :
    letI := graphMetric G hG
    input.pairing (graphRipsCocycle hG a ha r hloop).toContinuousMap
      (graphLoopClass input hG r hr p) = walkCharge a p := by
  let := graphMetric G hG
  let c := graphRipsCocycle hG a ha r hloop
  change input.pairing c.toContinuousMap
    (pushforward (compactMap (loopCircle (walkPath (by positivity)
      (graphEdgeBound hG r hr) p))) input.fundamental) = _
  rw [input.loop_pairing c.toContinuousMap _ _
    (c.walkLift (by positivity) (graphEdgeBound hG r hr) p)]
  exact graphRipsCocycle_on_walk hG a ha r hr hloop p

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_Persistence
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebraic persistence in the coarse Novikov construction

The direct-limit and rationalization arguments apply to arbitrary abelian
groups. No compatibility between the tests at different scales is assumed
or needed.
-/

namespace CoarseAssembly

section DirectLimit

variable {G : ℕ → Type*} [∀ r, AddCommGroup (G r)]
variable (f : ∀ r s, r ≤ s → G r →+ G s)
variable [DirectedSystem G (fun r s h => f r s h)]

/-- A class detected with value one at every later scale has no nonzero integer
multiple that vanishes in the actual algebraic direct limit. This is the last
argument of the manuscript's Proposition 4.1, with the geometric tests supplied
as explicit parameters. The tests need not form a compatible family. -/
theorem persistent_multiples_ne_zero (r₀ : ℕ) (a : G r₀)
    (test : ∀ r, r₀ ≤ r → G r →+ ℤ)
    (detects : ∀ r (hr : r₀ ≤ r), test r hr (f r₀ r hr a) = 1)
    (n : ℤ) (hn : n ≠ 0) :
    n • AddCommGroup.DirectLimit.of G f r₀ a ≠ 0 := by
  intro h
  have h' : AddCommGroup.DirectLimit.of G f r₀ (n • a) = 0 := by
    simpa only [map_zsmul] using h
  obtain ⟨r, hr, hz⟩ := AddCommGroup.DirectLimit.of.zero_exact r₀ (n • a) h'
  have ht := congrArg (test r hr) hz
  simp only [map_zsmul, map_zero, detects, zsmul_eq_mul, mul_one] at ht
  exact hn ht

end DirectLimit

section Rationalization

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An element with no nonzero integer annihilator remains nonzero after
rationalization. This is the torsion-kernel fact used after Proposition 4.1. -/
theorem rationalization_ne_zero (a : A)
    (ha : ∀ n : ℤ, n ≠ 0 → n • a ≠ 0) :
    (1 : ℚ) ⊗ₜ[ℤ] a ≠ 0 := by
  intro h
  have heq : TensorProduct.mk ℤ ℚ A 1 a = TensorProduct.mk ℤ ℚ A 1 0 := by
    simpa using h
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ)
    (f := TensorProduct.mk ℤ ℚ A 1) heq
  exact ha s (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
    (by simpa only [Submonoid.smul_def, smul_zero] using hs)

/-- A non-torsion kernel element prevents both integral and rational
injectivity. The scalar extension is the actual tensor product of groups. -/
theorem kernel_obstructs_injectivity (μ : A →+ B) (a : A)
    (ha : ∀ n : ℤ, n ≠ 0 → n • a ≠ 0) (hμ : μ a = 0) :
    ¬ Function.Injective μ ∧
      ¬ Function.Injective (μ.toIntLinearMap.lTensor ℚ) := by
  constructor
  · intro hinj
    have hz : a = 0 := hinj (hμ.trans μ.map_zero.symm)
    exact ha 1 one_ne_zero (by simpa using hz)
  · intro hinj
    apply rationalization_ne_zero a ha
    apply hinj
    simp [hμ]

end Rationalization

end CoarseAssembly

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ClopenNaturality
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction across a proper map

If the preimage of a compact open component is exactly the specified
compact open component of the source, the corresponding KK restrictions
commute with pushforward. The identity is proved on functions first.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {A B X Y : Type} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace A] [CompactSpace B] [T2Space X] [T2Space Y]

/-- This is the coordinate restriction identity used by the changing
finite-component index test. It is derived from the geometric preimage
identity, without invoking or assuming a global detection theorem. -/
theorem restrictComponent_natural (e : A ↪ X) (he : IsOpenEmbedding e)
    (d : B ↪ Y) (hd : IsOpenEmbedding d) (f : CocompactMap X Y) (g : CocompactMap A B)
    (commutes : ∀ a, f (e a) = d (g a))
    (preimage : ∀ x, f x ∈ Set.range d ↔ x ∈ Set.range e) :
    (restrictComponent d hd).comp (pushforward f) =
      (pushforward g).comp (restrictComponent e he) := by
  change (precomp (zeroExtensionHom d hd)).comp (precomp (pullback f)) =
    (precomp (pullback g)).comp (precomp (zeroExtensionHom e he))
  rw [← precomp_comp, ← precomp_comp, pullback_zeroExtension e he d hd f g commutes preimage]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsFamilyRestriction
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact coordinates of the pushed-forward family

Restriction to a late Rips component recovers precisely the corresponding
member of the source family, irrespective of links among other components.
-/

noncomputable section

namespace CoarseAssembly

open Topology Rips Analytic

variable {V : ℕ → Type} [∀ j, MetricSpace (V j)] [∀ j, Fintype (V j)]
  {Z : ℕ → Type} [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)]

theorem ripsFamily_component_preimage (o : ∀ j, V j) (r : ℝ)
    (γ : ∀ j, C(Z j, Point (V j) r)) (j : ℕ) :
    letI := separatedMetric o
    ∀ z, ripsFamilyMap o r γ z ∈ Set.range (separatedRipsEmbedding o r j) ↔
      z ∈ Set.range (sigmaComponent Z j) := by
  let := separatedMetric o
  rintro ⟨k, z⟩
  constructor
  · intro h
    have hs : ↑(ripsFamilyMap o r γ ⟨k, z⟩).weight.support ⊆
        Set.range (separatedComponent (V := V) j) := by
      exact (Set.ext_iff.mp (mapPoint_range (separatedComponent j)
        (separatedComponent_isometry o j)) _).mp h
    obtain ⟨x, hx⟩ := (γ k z).exists_positive
    have hmem : (⟨k, x⟩ : Sigma V) ∈ (ripsFamilyMap o r γ ⟨k, z⟩).weight.support := by
      apply Finsupp.mem_support_iff.mpr
      change (separatedRipsMap o r k (γ k z)).weight ⟨k, x⟩ ≠ 0
      rw [separatedRipsMap_weight]
      exact ne_of_gt hx
    obtain ⟨y, hy⟩ := hs hmem
    have hjk : j = k := congrArg Sigma.fst hy
    subst k
    exact ⟨z, rfl⟩
  · rintro ⟨z', hz'⟩
    change Sigma.mk j z' = Sigma.mk k z at hz'
    cases hz'
    exact ⟨γ j z', rfl⟩

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsPathCoarsening
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarsening preserves the parametrized graph loop

The paths at different Rips scales are the same barycentric paths. This
gives equality of their pushed-forward analytic classes, not merely a
choice of unrelated loops at successive scales.
-/

noncomputable section

namespace CoarseAssembly.Rips

variable {X : Type*} [PseudoMetricSpace X] {r s : ℝ}

theorem coarsen_edgePath (hrs : r ≤ s) {x y : X} (hxy : dist x y ≤ r) (t : unitInterval) :
    coarsen hrs (edgePath hxy t) = edgePath (hxy.trans hrs) t := by
  apply Point.ext
  rfl

theorem coarsen_walkPath {G : SimpleGraph X} (hrs : r ≤ s) (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) {x y : X} (p : G.Walk x y)
    (t : unitInterval) :
    coarsen hrs (walkPath hr hE p t) =
      walkPath (hr.trans hrs) (fun x y h => (hE x y h).trans hrs) p t := by
  induction p generalizing t with
  | nil =>
    apply Point.ext
    rfl
  | cons h p ih =>
    simp only [walkPath, Path.trans_apply]
    split_ifs
    · exact coarsen_edgePath hrs _ _
    · exact ih _

theorem coarsen_loopCircle {G : SimpleGraph X} (hrs : r ≤ s) (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) {x : X} (p : G.Walk x x) :
    (inclusion hrs).toContinuousMap.comp (loopCircle (walkPath hr hE p)) =
      loopCircle (walkPath (hr.trans hrs) (fun x y h => (hE x y h).trans hrs) p) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [ContinuousMap.comp_apply, loopCircle_apply]
  exact coarsen_walkPath hrs hr hE p t

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FiberedPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence in the actual congruence-fiber graph family

The arithmetic small-loop theorem, finite-component circle index and exact
family restriction are combined here. Boundary walks remain explicit
geometric arguments; they are not labeled as published inputs. The only
published inputs in the resulting detector are the stated circle pairing
and countable first-variable additivity.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

variable (S : Finset ArithmeticGroup)
  (boundary : ∀ j, (fiberedGraph S chosenHolonomyUnit j).Walk
    (fiberBoundaryBase j) (fiberBoundaryBase j))

theorem fiberedBoundaryLoops_coarsen {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≤ s) :
    letI := componentMetric S chosenHolonomyUnit
    ∀ j z, coarsen (by exact_mod_cast hrs) (fiberedBoundaryLoops S boundary r hr j z) =
      fiberedBoundaryLoops S boundary s hs j z := by
  let := componentMetric S chosenHolonomyUnit
  intro j z
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have h := coarsen_loopCircle hrs' (by positivity : (0 : ℝ) ≤ r)
    (graphEdgeBound (fiberedGraph_connected S chosenHolonomyUnit j) r hr) (boundary j)
  exact DFunLike.congr_fun h z

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_FamilyFilling
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entire family of base loops vanishes through its actual filling

Both arrows through the disjoint union of compact polygons are constructed
proper maps. The vanishing follows only from the specified published compact
homotopy and countable-additivity inputs.
-/

noncomputable section

namespace CoarseAssembly

open Rips Analytic

variable (o : ∀ j, Disc j) (p : ∀ j, (discGraph j).Walk (o j) (o j))

theorem boundaryFamily_factors :
    letI := separatedMetric o
    ripsFamilyMap o 1 (baseBoundaryLoops o p) =
      (ripsFamilyMap o 1 filledToRips).comp (compactFamilyMap (filledBoundaryLoops o p)) := by
  let := separatedMetric o
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change separatedRipsMap o 1 j (baseBoundaryLoops o p j z) =
    separatedRipsMap o 1 j (filledToRips j (filledBoundaryLoops o p j z))
  exact congrArg (separatedRipsMap o 1 j) (DFunLike.congr_fun (filledToRips_loop (p j)) z).symm

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsMapCalculus
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact naturality of the parametrized Rips paths

Injective nonexpanding vertex maps commute with barycentric interpolation,
edge paths and concatenated graph walks, including their parametrizations.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Topology

variable {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  {r : ℝ}

theorem mapPoint_weight (e : X ↪ Y) (he) (p : Point X r) :
    (mapPoint e he p).weight = p.weight.embDomain e := rfl

theorem mapPoint_interpolate (e : X ↪ Y) (he) (p q : Point X r) (hpq) (t : unitInterval) :
    mapPoint e he (interpolate p q hpq t) =
      interpolate (mapPoint e he p) (mapPoint e he q)
        (by
          intro x hx y hy
          change x ∈ (p.weight.embDomain e).support at hx
          change y ∈ (q.weight.embDomain e).support at hy
          rw [Finsupp.support_embDomain, Finset.mem_map] at hx hy
          obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, rfl⟩ := hy
          exact (he a b).trans (hpq a ha b hb)) t := by
  classical
  apply Point.ext
  apply Finsupp.ext
  intro y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    simp only [mapPoint, interpolate, Finsupp.embDomain_apply_self, Finsupp.coe_add,
      Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply]
  · simp only [mapPoint, interpolate, Finsupp.embDomain_of_notMem_range _ _ _ hy,
      Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_zero, add_zero]

theorem mapPoint_edgePath (e : X ↪ Y) (he) {x y : X} (hxy : dist x y ≤ r)
    (t : unitInterval) :
    mapPoint e he (edgePath hxy t) = edgePath ((he x y).trans hxy) t := by
  simp only [edgePath, simplexPath, Path.coe_mk_mk]
  rw [mapPoint_interpolate]
  apply Point.ext
  change (1 - (t : ℝ)) • (mapPoint e he (vertex x _)).weight +
    (t : ℝ) • (mapPoint e he (vertex y _)).weight = _
  rw [congrArg Point.weight (mapPoint_vertex e he x _),
    congrArg Point.weight (mapPoint_vertex e he y _)]
  rfl

theorem mapPoint_walkPath {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : X ↪ Y) (he) (hgraph : ∀ x y, G.Adj x y → H.Adj (e x) (e y))
    (hr : 0 ≤ r) (hG : ∀ x y, G.Adj x y → dist x y ≤ r)
    (hH : ∀ x y, H.Adj x y → dist x y ≤ r)
    {x y : X} (p : G.Walk x y) (t : unitInterval) :
    mapPoint e he (walkPath hr hG p t) =
      walkPath hr hH (p.map ⟨e, fun h => hgraph _ _ h⟩) t := by
  induction p generalizing t with
  | nil =>
    change mapPoint e he (vertex _ hr) = vertex _ hr
    exact mapPoint_vertex e he _ hr
  | cons h p ih =>
    simp only [walkPath, SimpleGraph.Walk.map_cons, Path.trans_apply]
    split_ifs
    · exact mapPoint_edgePath e he (hG _ _ h) _
    · exact ih _

theorem mapPoint_loopCircle {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : X ↪ Y) (he) (hgraph : ∀ x y, G.Adj x y → H.Adj (e x) (e y))
    (hr : 0 ≤ r) (hG : ∀ x y, G.Adj x y → dist x y ≤ r)
    (hH : ∀ x y, H.Adj x y → dist x y ≤ r)
    {x : X} (p : G.Walk x x) (z : WindingCircle) :
    mapPoint e he (loopCircle (walkPath hr hG p) z) =
      loopCircle (walkPath hr hH (p.map ⟨e, fun h => hgraph _ _ h⟩)) z := by
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [loopCircle_apply]
  exact mapPoint_walkPath e he hgraph hr hG hH p t

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_RipsRealClass
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real-radius classes at integer coarsening stages -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem classAt_zero (n : ℕ) (r : ℝ) (h : r = (n : ℝ)) :
    classAt (X := X) n r h 0 = 0 := by
  subst r
  exact (coarsening X).of n |>.map_zero

theorem embedding_classAt (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (n : ℕ) (r : ℝ) (h : r = (n : ℝ))
    (a : LocallyFiniteK1 (Point X r)) :
    (embeddingCoarsening e he).homologyMap (classAt (X := X) n r h a) =
      classAt (X := Y) n r h (pushforward (embeddingMap e he r) a) := by
  subst r
  dsimp only [classAt]
  exact CoarseningMorphism.homologyMap_of (embeddingCoarsening e he) n a

end CoarseAssembly.Rips

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_BoundaryLoopMaps
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same boundary family maps to the filled base and detected total space

The source class is defined on the actual boundary Rips complex. Its base
image is identified with the previously constructed filled loop family.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric7

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric8

attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric1
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric2
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric3
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric5
theorem boundaryLoop_base (j : ℕ) (z : WindingCircle) :
    mapPoint (boundaryComponentToBase j) (boundaryComponentToBase_nonexpanding j)
      (boundaryLoops j z) = baseBoundaryLoops discBoundaryBase concreteBaseWalk j z := by
  exact mapPoint_loopCircle (boundaryComponentToBase j) (boundaryComponentToBase_nonexpanding j)
    (fun _ _ h => h) (by norm_num) (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    discEdgeBound (hexagonalWalk j) z

local instance boundaryLoopMetric4_rf41b27_1 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.boundaryLoopMetric6
theorem boundaryFamily_toBase :
    (embeddingMap boundaryToBase
      (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit) 1).comp
        (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops) =
      ripsFamilyMap discBoundaryBase 1 (baseBoundaryLoops discBoundaryBase concreteBaseWalk) := by
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change mapPoint boundaryToBase (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)
    (mapPoint boundaryReindex.toEmbedding
      (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
      (mapPoint (separatedComponent j)
        (fun x y => ((separatedComponent_isometry boundaryRoot j).dist_eq x y).le)
        (boundaryLoops j z))) =
    mapPoint (separatedComponent j)
      (fun x y => ((separatedComponent_isometry discBoundaryBase j).dist_eq x y).le)
      (baseBoundaryLoops discBoundaryBase concreteBaseWalk j z)
  rw [← boundaryLoop_base j z]
  apply Point.ext
  simp only [mapPoint_weight]
  simp only [← Finsupp.embDomain_trans_apply]
  have he : ((separatedComponent j).trans boundaryReindex.toEmbedding).trans boundaryToBase =
      (boundaryComponentToBase j).trans (separatedComponent j) := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [he]

theorem boundaryLoop_fiber (j : ℕ) (z : WindingCircle) :
    mapPoint (boundaryFiberEmbedding j) (fun _ _ => le_rfl) (boundaryLoops j z) =
      fiberLoopsOne j z := by
  have h := mapPoint_loopCircle (boundaryFiberEmbedding j) (fun _ _ => le_rfl)
    (fun _ _ h => boundaryFiber_adj elementaryMoves chosenHolonomyUnit h) (by norm_num)
    (boundaryEdgeBound elementaryMoves chosenHolonomyUnit)
    (fun x y h => by
      have he := graphEdgeBound (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
        1 le_rfl x y h
      simpa only [Nat.cast_one] using he)
    (hexagonalWalk j) z
  exact h

theorem boundaryFamily_toFiber :
    (embeddingMap totalToFiber.toEmbedding (fun x y => (totalToFiber_dist x y).le) 1).comp
      ((embeddingMap boundaryToVertex
        (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit) 1).comp
        (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops)) =
      ripsFamilyMap fiberBoundaryBase 1 fiberLoopsOne := by
  apply CocompactMap.ext
  rintro ⟨j, z⟩
  change mapPoint totalToFiber.toEmbedding (fun x y => (totalToFiber_dist x y).le)
    (mapPoint boundaryToVertex (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)
      (mapPoint boundaryReindex.toEmbedding
        (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
        (mapPoint (separatedComponent j)
          (fun x y => ((separatedComponent_isometry boundaryRoot j).dist_eq x y).le)
          (boundaryLoops j z)))) =
    mapPoint (separatedComponent j)
      (fun x y => ((separatedComponent_isometry fiberBoundaryBase j).dist_eq x y).le)
      (fiberLoopsOne j z)
  rw [← boundaryLoop_fiber j z]
  apply Point.ext
  simp only [mapPoint_weight]
  simp only [← Finsupp.embDomain_trans_apply]
  have he : (((separatedComponent j).trans boundaryReindex.toEmbedding).trans boundaryToVertex).trans
      totalToFiber.toEmbedding = (boundaryFiberEmbedding j).trans (separatedComponent j) := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [he]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CompactFamilyHomotopy
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Norm continuity of pullback along component-preserving family homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

open Filter
open scoped ZeroAtInfty Topology CStarAlgebra

variable {X Y : ℕ → Type} [∀ j, TopologicalSpace (X j)]
  [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (X j)]
  [∀ j, CompactSpace (Y j)] [∀ j, T2Space (Y j)]

/-- Componentwise compact homotopies give a proper family homotopy on analytic classes. -/
theorem compactFamily_homotopy_invariance (f g : ∀ j, C(X j, Y j))
    (H : ∀ j, (f j).Homotopy (g j)) :
    pushforward (compactFamilyMap f) = pushforward (compactFamilyMap g) := by
  have hstart : compactFamilySlice (fun j => (H j).toContinuousMap) start =
      compactFamilyMap f := by
    apply CocompactMap.ext
    rintro ⟨j, x⟩
    apply congrArg (Sigma.mk j)
    exact (H j).map_zero_left x
  have hfinish : compactFamilySlice (fun j => (H j).toContinuousMap) finish =
      compactFamilyMap g := by
    apply CocompactMap.ext
    rintro ⟨j, x⟩
    apply congrArg (Sigma.mk j)
    exact (H j).map_one_left x
  apply hom_ext
  intro c
  change precomp _ (cycleClass C₀(Sigma X, ℂ) c) =
    precomp _ (cycleClass C₀(Sigma X, ℂ) c)
  rw [precomp_cycleClass, precomp_cycleClass]
  have hh := homotopy_eq (compactFamilyCycleHomotopy (fun j => (H j).toContinuousMap) c)
  change cycleClass C₀(Sigma Y, ℂ) (c.precomp (pullback
    (compactFamilySlice (fun j => (H j).toContinuousMap) start))) =
      cycleClass C₀(Sigma Y, ℂ) (c.precomp (pullback
        (compactFamilySlice (fun j => (H j).toContinuousMap) finish))) at hh
  rwa [hstart, hfinish] at hh

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_CongruenceElementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary generators in the finite congruence quotients -/

noncomputable section

namespace CoarseAssembly

open Congruence
open NuclearUltrapower

lemma reduce_transvection (k : ℕ) {i j : Fin 3} (h : i ≠ j) (a : ℤ) :
    reduce k (Matrix.SpecialLinearGroup.transvection h a) =
      Matrix.SpecialLinearGroup.transvection h (a : ZMod (2 ^ k)) := by
  apply Subtype.ext
  ext r s
  simp [reduce, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, Matrix.one_apply]

lemma transvection_mem_elementaryReduction (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) :
    Matrix.SpecialLinearGroup.transvection h a ∈ (elementaryReduction k).range := by
  refine ⟨Elementary.elementaryTransvection h (a.val : ℤ), ?_⟩
  change reduce k (Matrix.SpecialLinearGroup.transvection h (a.val : ℤ)) = _
  rw [reduce_transvection]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma elementaryReduction_zero_surjective : Function.Surjective (elementaryReduction 0) := by
  intro q
  exact ⟨1, Subsingleton.elim _ _⟩

lemma elementaryReduction_one_surjective : Function.Surjective (elementaryReduction 1) := by
  let : Fact (Nat.Prime (2 ^ 1)) := ⟨by norm_num⟩
  intro q
  have hmem : q ∈ (elementaryReduction 1).range := by
    apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun M => M ∈ (elementaryReduction 1).range) q
    · intro i j hij c hc
      have hc1 : c = 1 := by
        change ZMod 2 at c
        change c ≠ (0 : ZMod 2) at hc
        fin_cases c
        · exact (hc rfl).elim
        · rfl
      subst c
      have hdiag : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod (2 ^ 1)) (by simp) = 1 := by
        apply Subtype.ext
        ext r s
        simp [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.one_apply]
      rw [hdiag]
      exact one_mem _
    · intro i j hij a
      exact transvection_mem_elementaryReduction 1 hij a
    · intro A B hA hB
      exact mul_mem hA hB
  exact hmem

lemma elementary_row_same (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) (q : Congruence.Quotient k) (c : Fin 3) :
    (Matrix.SpecialLinearGroup.transvection h a * q).val i c = q.val i c + a * q.val j c := by
  change (Matrix.transvection i j a * q.val) i c = _
  simp only [Matrix.transvection_mul_apply_same]

lemma elementary_row_other (k : ℕ) {i j : Fin 3} (h : i ≠ j)
    (a : ZMod (2 ^ k)) (q : Congruence.Quotient k) (r c : Fin 3) (hr : r ≠ i) :
    (Matrix.SpecialLinearGroup.transvection h a * q).val r c = q.val r c := by
  change (Matrix.transvection i j a * q.val) r c = _
  exact Matrix.transvection_mul_apply_of_ne i j r c hr a q.val

lemma upperUnitriangular_mem_elementaryReduction (k : ℕ) (q : Congruence.Quotient k)
    (h00 : q.val 0 0 = 1) (h11 : q.val 1 1 = 1) (h22 : q.val 2 2 = 1)
    (h10 : q.val 1 0 = 0) (h20 : q.val 2 0 = 0) (h21 : q.val 2 1 = 0) :
    q ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have he : q = T 0 1 (by decide) (q.val 0 1) *
      T 0 2 (by decide) (q.val 0 2 - q.val 0 1 * q.val 1 2) *
      T 1 2 (by decide) (q.val 1 2) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply,
        h00, h11, h22, h10, h20, h21]
  rw [he]
  exact mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
    (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _)

lemma diagonal_mem_elementaryReduction (k : ℕ) (u : (ZMod (2 ^ k))ˣ) :
    diagonal u ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have hw (v : (ZMod (2 ^ k))ˣ) :
      (T 0 1 (by decide) v *
        T 1 0 (by decide) (-((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) v).val = !![0, (v : ZMod (2 ^ k)), 0; -((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), 0, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, mul_add, add_mul]
  have hneg : (T 0 1 (by decide) (-1) * T 1 0 (by decide) 1 *
      T 0 1 (by decide) (-1)).val = !![0, (-1 : ZMod (2 ^ k)), 0; 1, 0, 0; 0, 0, 1] := by
    simpa using hw (-1)
  have he : diagonal u =
      (T 0 1 (by decide) u *
        T 1 0 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) u) *
      (T 0 1 (by decide) (-1) * T 1 0 (by decide) 1 *
        T 0 1 (by decide) (-1)) := by
    apply Subtype.ext
    change _ = (T 0 1 (by decide) u *
        T 1 0 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 0 1 (by decide) u).val * _
    rw [hw, hneg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
  rw [he]
  exact mul_mem
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))

lemma secondDiagonal_mem_elementaryReduction (k : ℕ) (u : (ZMod (2 ^ k))ˣ) :
    secondDiagonal k u ∈ (elementaryReduction k).range := by
  let T (i j : Fin 3) (h : i ≠ j) (a : ZMod (2 ^ k)) :=
    Matrix.SpecialLinearGroup.transvection h a
  have hw (v : (ZMod (2 ^ k))ˣ) :
      (T 1 2 (by decide) v *
        T 2 1 (by decide) (-((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) v).val = !![1, 0, 0; 0, 0, (v : ZMod (2 ^ k)); 0, -((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.single, Matrix.one_apply, mul_add, add_mul]
  have hneg : (T 1 2 (by decide) (-1) * T 2 1 (by decide) 1 *
      T 1 2 (by decide) (-1)).val = !![1, 0, 0; 0, 0, (-1 : ZMod (2 ^ k)); 0, 1, 0] := by
    simpa using hw (-1)
  have he : secondDiagonal k u =
      (T 1 2 (by decide) u *
        T 2 1 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) u) *
      (T 1 2 (by decide) (-1) * T 2 1 (by decide) 1 *
        T 1 2 (by decide) (-1)) := by
    apply Subtype.ext
    change _ = (T 1 2 (by decide) u *
        T 2 1 (by decide) (-((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))) *
        T 1 2 (by decide) u).val * _
    rw [hw, hneg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [secondDiagonal, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]
  rw [he]
  exact mul_mem
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))
    (mul_mem (mul_mem (transvection_mem_elementaryReduction k _ _)
      (transvection_mem_elementaryReduction k _ _)) (transvection_mem_elementaryReduction k _ _))

lemma upperTriangular_mem_elementaryReduction (k : ℕ) (q : Congruence.Quotient k)
    (h10 : q.val 1 0 = 0) (h20 : q.val 2 0 = 0) (h21 : q.val 2 1 = 0)
    (h00 : IsUnit (q.val 0 0)) (h11 : IsUnit (q.val 1 1)) :
    q ∈ (elementaryReduction k).range := by
  obtain ⟨u, hu⟩ := h00
  obtain ⟨v, hv⟩ := h11
  let a := diagonal u⁻¹
  let b := secondDiagonal k (u * v)⁻¹
  let n := b * (a * q)
  have hn (i j : Fin 3) : n.val i j =
      (![1, (((u * v)⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), ((u * v : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k))] i) *
      ((![((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)), (u : ZMod (2 ^ k)), 1] i) * q.val i j) := by
    change (b.val * (a.val * q.val)) i j = _
    simp [b, a, secondDiagonal, diagonal, Matrix.diagonal_mul]
  have hdet : ((u * v : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) * q.val 2 2 = 1 := by
    have h := q.property
    rw [Matrix.det_fin_three] at h
    simpa only [h10, h20, h21, mul_zero, zero_mul, add_zero, sub_zero,
      ← hu, ← hv, Units.val_mul, mul_assoc] using h
  have hn00 : n.val 0 0 = 1 := by rw [hn, ← hu]; simp
  have hn11 : n.val 1 1 = 1 := by
    rw [hn, ← hv]
    change (((u * v)⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) *
      ((u : ZMod (2 ^ k)) * (v : ZMod (2 ^ k))) = 1
    change (((u * v)⁻¹ * (u * v) : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = 1
    simp
  have hn22 : n.val 2 2 = 1 := by simpa [hn] using hdet
  have hn10 : n.val 1 0 = 0 := by rw [hn, h10]; simp
  have hn20 : n.val 2 0 = 0 := by rw [hn, h20]; simp
  have hn21 : n.val 2 1 = 0 := by rw [hn, h21]; simp
  have hnmem := upperUnitriangular_mem_elementaryReduction k n hn00 hn11 hn22 hn10 hn20 hn21
  have ha : a ∈ (elementaryReduction k).range := diagonal_mem_elementaryReduction k u⁻¹
  have hb : b ∈ (elementaryReduction k).range := secondDiagonal_mem_elementaryReduction k (u * v)⁻¹
  exact ((elementaryReduction k).range.mul_mem_cancel_left ha).mp
    (((elementaryReduction k).range.mul_mem_cancel_left hb).mp hnmem)

lemma isUnit_of_mod_two_one {k : ℕ} (hk : 1 ≤ k) (a : ZMod (2 ^ k))
    (ha : residueMap hk a = 1) : IsUnit a := by
  have hval : (a.val : ZMod 2) = 1 := by
    simpa only [residueMap, ZMod.castHom_apply, ZMod.cast_eq_val, pow_one] using ha
  rw [← ZMod.natCast_zmod_val a]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (lt_of_lt_of_le Nat.zero_lt_one hk)).2
  intro hd
  have hz := (ZMod.natCast_eq_zero_iff a.val 2).2 hd
  exact zero_ne_one (hz.symm.trans hval)

lemma mod_two_identity_entry {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) (i j : Fin 3) :
    residueMap hk (q.val i j) = if i = j then 1 else 0 := by
  have h := congrArg (fun z : Congruence.Quotient 1 => z.val i j) hq
  simpa only [quotientMap, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply] using h

lemma mod_two_identity_first_pivot {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) : IsUnit (q.val 0 0) := by
  apply isUnit_of_mod_two_one hk
  simpa using mod_two_identity_entry hk q hq 0 0

lemma mod_two_identity_schur_pivot {k : ℕ} (hk : 1 ≤ k) (q : Congruence.Quotient k)
    (hq : quotientMap hk q = 1) (a : ZMod (2 ^ k)) :
    IsUnit (q.val 1 1 - q.val 1 0 * a * q.val 0 1) := by
  apply isUnit_of_mod_two_one hk
  rw [map_sub, map_mul, map_mul]
  have h11 : residueMap hk (q.val 1 1) = 1 := by
    simpa using mod_two_identity_entry hk q hq 1 1
  have h10 : residueMap hk (q.val 1 0) = 0 := by
    simpa using mod_two_identity_entry hk q hq 1 0
  rw [h11, h10, zero_mul, zero_mul, sub_zero]

lemma mod_two_kernel_mem_elementaryReduction {k : ℕ} (hk : 1 ≤ k)
    (q : Congruence.Quotient k) (hq : quotientMap hk q = 1) :
    q ∈ (elementaryReduction k).range := by
  obtain ⟨u, hu⟩ := mod_two_identity_first_pivot hk q hq
  let t1 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0)
    (-q.val 1 0 * ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m1 := t1 * q
  have hm1row0 (c : Fin 3) : m1.val 0 c = q.val 0 c :=
    elementary_row_other k _ _ q 0 c (by decide)
  have hm1row2 (c : Fin 3) : m1.val 2 c = q.val 2 c :=
    elementary_row_other k _ _ q 2 c (by decide)
  have hm110 : m1.val 1 0 = 0 := by
    change (t1 * q).val 1 0 = 0
    rw [elementary_row_same, ← hu]
    simp [mul_assoc]
  let t2 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0)
    (-q.val 2 0 * ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m2 := t2 * m1
  have hm2row0 (c : Fin 3) : m2.val 0 c = q.val 0 c :=
    (elementary_row_other k _ _ m1 0 c (by decide)).trans (hm1row0 c)
  have hm210 : m2.val 1 0 = 0 :=
    (elementary_row_other k _ _ m1 1 0 (by decide)).trans hm110
  have hm220 : m2.val 2 0 = 0 := by
    change (t2 * m1).val 2 0 = 0
    rw [elementary_row_same, hm1row2, hm1row0, ← hu]
    simp [mul_assoc]
  have hm211 : m2.val 1 1 = q.val 1 1 - q.val 1 0 *
      ((u⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) * q.val 0 1 := by
    change (t2 * m1).val 1 1 = _
    rw [elementary_row_other k _ _ m1 1 1 (by decide)]
    change (t1 * q).val 1 1 = _
    rw [elementary_row_same]
    ring
  have hunit2 : IsUnit (m2.val 1 1) := by
    rw [hm211]
    exact mod_two_identity_schur_pivot hk q hq _
  obtain ⟨v, hv⟩ := hunit2
  let t3 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1)
    (-m2.val 2 1 * ((v⁻¹ : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)))
  let m3 := t3 * m2
  have hm310 : m3.val 1 0 = 0 :=
    (elementary_row_other k _ _ m2 1 0 (by decide)).trans hm210
  have hm320 : m3.val 2 0 = 0 := by
    change (t3 * m2).val 2 0 = 0
    rw [elementary_row_same, hm220, hm210, mul_zero, add_zero]
  have hm321 : m3.val 2 1 = 0 := by
    change (t3 * m2).val 2 1 = 0
    rw [elementary_row_same, ← hv]
    simp [mul_assoc]
  have hm300 : IsUnit (m3.val 0 0) := by
    have he : m3.val 0 0 = q.val 0 0 :=
      (elementary_row_other k _ _ m2 0 0 (by decide)).trans (hm2row0 0)
    rw [he, ← hu]
    exact u.isUnit
  have hm311 : IsUnit (m3.val 1 1) := by
    have he : m3.val 1 1 = m2.val 1 1 := elementary_row_other k _ _ m2 1 1 (by decide)
    rw [he, ← hv]
    exact v.isUnit
  have hm3 := upperTriangular_mem_elementaryReduction k m3 hm310 hm320 hm321 hm300 hm311
  have ht1 : t1 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  have ht2 : t2 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  have ht3 : t3 ∈ (elementaryReduction k).range := transvection_mem_elementaryReduction k _ _
  exact ((elementaryReduction k).range.mul_mem_cancel_left ht1).mp
    (((elementaryReduction k).range.mul_mem_cancel_left ht2).mp
      (((elementaryReduction k).range.mul_mem_cancel_left ht3).mp hm3))

/-- Surjectivity is proved by reduction to level one followed by elimination
inside the kernel of reduction modulo two. -/
theorem elementaryReduction_surjective (k : ℕ) : Function.Surjective (elementaryReduction k) := by
  by_cases hk : k = 0
  · subst k
    exact elementaryReduction_zero_surjective
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  intro q
  obtain ⟨e, he⟩ := elementaryReduction_one_surjective (quotientMap hk1 q)
  let r := (elementaryReduction k e)⁻¹ * q
  have hr : quotientMap hk1 r = 1 := by
    change quotientMap hk1 ((elementaryReduction k e)⁻¹ * q) = 1
    rw [map_mul, map_inv]
    have heq : quotientMap hk1 (elementaryReduction k e) = quotientMap hk1 q := by
      change quotientMap hk1 (reduce k e.val) = _
      rw [quotientMap_reduce]
      exact he
    rw [heq, inv_mul_cancel]
  obtain ⟨f, hf⟩ := mod_two_kernel_mem_elementaryReduction hk1 r hr
  refine ⟨e * f, ?_⟩
  rw [map_mul, hf]
  change elementaryReduction k e * ((elementaryReduction k e)⁻¹ * q) = q
  group

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ProperGeometry
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Properness of the concrete coarse spaces

The proved finite-ball estimates imply compact closed balls in the actual
shortest-path metrics. No completion or change of metric is involved.
-/

noncomputable section

namespace CoarseAssembly

theorem UniformFiniteBalls.properSpace {X : Type*} [PseudoMetricSpace X]
    (hX : UniformFiniteBalls X) : ProperSpace X :=
  ⟨fun x r => (hX.finite_closedBall x r).isCompact⟩

theorem vertexUnion_proper (S : Finset Congruence.ArithmeticGroup) (t : ℤ_[2]ˣ) :
    @ProperSpace VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace :=
  @UniformFiniteBalls.properSpace VertexUnion (vertexUnionMetric S t).toPseudoMetricSpace
    (vertexUnion_uniform_balls S t)

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_SigmaCycleRestriction
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedIndexFamily_atScale _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coordinates of an actual countable Fredholm cycle -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {A : Type} [NonUnitalCStarAlgebra A]

theorem zeroRepresentationCycle_degenerate (H : HilbertSpace) (F : End H) :
    (zeroRepresentationCycle (A := A) H F).Degenerate := by
  constructor
  · intro a
    change F * (0 : End H) - 0 * F = 0
    simp
  constructor
  · intro a
    change (F * F - 1) * (0 : End H) = 0
    simp
  · intro a
    change (star F - F) * (0 : End H) = 0
    simp

variable (Y : ℕ → Type) [∀ j, TopologicalSpace (Y j)] [∀ j, CompactSpace (Y j)]
  [∀ j, T2Space (Y j)]

variable (c : ∀ j, OddCycle C(Y j, ℂ))
variable (M : ℝ) (hM : 0 ≤ M) (hF : ∀ j, ‖(c j).operator‖ ≤ M)

theorem sigmaCycle_coordinate (hself : ∀ j, IsSelfAdjoint (c j).operator)
    (hsq : ∀ j, (c j).operator * (c j).operator = 1) (j : ℕ) :
    restrictComponent (sigmaComponent Y j) (sigmaComponent_open Y j)
      (cycleClass C₀(Sigma Y, ℂ) (sigmaCycle Y c M hM hF hself hsq)) =
      cycleClass C₀(Y j, ℂ) ((c j).precomp compactFunctionForget) := by
  rw [restrictComponent, precomp_cycleClass]
  rw [directSum_eq _ _ _ (sigmaCycle_directSum Y c M hM hF hself hsq j)]
  have hz : cycleClass C₀(Y j, ℂ) (sigmaComplementCycle Y c M hM hF j) = 0 :=
    degenerate_zero _ (zeroRepresentationCycle_degenerate _ _)
  rw [hz, add_zero]

end CoarseAssembly.Analytic

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitCircleFamily
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedIndexFamily_atScale _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The circle-family class without a countable-additivity assumption -/

noncomputable section

namespace CoarseAssembly

open Analytic
open scoped ZeroAtInfty

theorem windingCircleCycle_class :
    cycleClass C₀(WindingCircle, ℂ) (windingCircleCycle.precomp compactFunctionForget) =
      circleFundamental := by
  unfold circleFundamental negativeCircleClass pushforward windingCircleCycle
  rw [precomp_cycleClass, OddCycle.precomp_comp, OddCycle.precomp_comp]
  congr 2

theorem explicitCircleFamily_coordinate (j : ℕ) :
    restrictComponent (sigmaComponent CircleFamily j) (sigmaComponent_open CircleFamily j)
      explicitCircleFamily = circleFundamental := by
  exact (sigmaCycle_coordinate CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
    (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    (fun _ => negativeCircleOperator_sq) j).trans windingCircleCycle_class

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitFamilyFilling
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.binaryBlock_apply _root_.OAI.CoarseAssembly.Analytic.binaryBlock_one _root_.OAI.CoarseAssembly.Analytic.binaryBlock_zero _root_.OAI.CoarseAssembly.Analytic.binaryFlip_apply _root_.OAI.CoarseAssembly.Analytic.binaryLeft_adjoint _root_.OAI.CoarseAssembly.Analytic.binaryRight_adjoint _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Analytic.projectionSwapUnitary_clm _root_.OAI.CoarseAssembly.Analytic.projectionSwap_apply _root_.OAI.CoarseAssembly.Analytic.tailInsert_succ _root_.OAI.CoarseAssembly.Analytic.tailInsert_zero _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedIndexFamily_atScale _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Filling the explicit circle family without countable-additivity inputs -/

noncomputable section

namespace CoarseAssembly

open Rips Analytic
open scoped ZeroAtInfty

theorem windingCircleCycle_representation_const (z : ℂ) :
    windingCircleCycle.representation (ContinuousMap.const WindingCircle z) =
      z • (1 : End circleSequenceSpace) := by
  change circleRepresentation (ContinuousMap.const Circle z) = _
  have he : (ContinuousMap.const Circle z : C(Circle, ℂ)) = z • 1 := by
    ext x
    simp
  rw [he, map_smul, map_one]

variable {Y : ℕ → Type} [∀ j, TopologicalSpace (Y j)] [∀ j, T2Space (Y j)]

theorem circleFamily_constant_degenerate (y : ∀ j, Y j) :
    (circleSigmaCycle.precomp (pullback
      (compactFamilyMap (fun j => ContinuousMap.const WindingCircle (y j))))).Degenerate := by
  dsimp only [OddCycle.Degenerate, OddCycle.precomp, circleSigmaCycle, sigmaCycle]
  constructor
  · intro f
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    have he : sigmaFunctionRestriction CircleFamily j
        (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f) =
        ContinuousMap.const WindingCircle (f ⟨j, y j⟩) := by
      ext z
      rfl
    change windingCircleCycle.operator
        (windingCircleCycle.representation (sigmaFunctionRestriction CircleFamily j
          (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f)) (x j)) -
        windingCircleCycle.representation (sigmaFunctionRestriction CircleFamily j
          (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f))
          (windingCircleCycle.operator (x j)) = 0
    rw [he, windingCircleCycle_representation_const]
    change windingCircleCycle.operator ((f ⟨j, y j⟩) • (x j)) -
      (f ⟨j, y j⟩) • windingCircleCycle.operator (x j) = 0
    rw [map_smul, sub_self]
  constructor
  · intro f
    have hs := sigmaCycleOperator_sq CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
      (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_sq)
    rw [hs, sub_self, zero_mul]
  · intro f
    have hs := sigmaCycleOperator_selfAdjoint CircleFamily (fun _ => windingCircleCycle) 1
      (by norm_num) (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    rw [hs.star_eq, sub_self, zero_mul]

theorem explicitCircleFamily_constant_zero (y : ∀ j, Y j) :
    pushforward (compactFamilyMap (fun j => ContinuousMap.const WindingCircle (y j)))
      explicitCircleFamily = 0 := by
  change precomp _ (cycleClass C₀(Sigma CircleFamily, ℂ) circleSigmaCycle) = 0
  rw [precomp_cycleClass]
  exact degenerate_zero _ (circleFamily_constant_degenerate y)

theorem explicitCircleFamily_filled_zero (o : ∀ j, Disc j)
    (p : ∀ j, (discGraph j).Walk (o j) (o j)) :
    pushforward (compactFamilyMap (filledBoundaryLoops o p)) explicitCircleFamily = 0 := by
  have h (j : ℕ) : (filledBoundaryLoops o p j).Homotopy
      (ContinuousMap.const WindingCircle (filledDiscCenter j)) := by
    have hc : (filledDiscContraction j).center = filledDiscCenter j := rfl
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp, hc] using
      (filledDiscContraction j).homotopy.compContinuousMap (filledBoundaryLoops o p j)
  rw [compactFamily_homotopy_invariance _ _ h]
  exact explicitCircleFamily_constant_zero _

theorem explicitBaseBoundaryFamily_zero (o : ∀ j, Disc j)
    (p : ∀ j, (discGraph j).Walk (o j) (o j)) :
    letI := separatedMetric o
    pushforward (ripsFamilyMap o 1 (baseBoundaryLoops o p)) explicitCircleFamily = 0 := by
  let := separatedMetric o
  rw [boundaryFamily_factors o p, pushforward_comp, AddMonoidHom.comp_apply,
    explicitCircleFamily_filled_zero o p, map_zero]

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitPersistence
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedIndexFamily_atScale _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Persistence of the explicit circle cycle in the actual graph union -/

noncomputable section

namespace CoarseAssembly

open Topology Congruence Rips Analytic

theorem ripsFamily_restriction_class {V Z : ℕ → Type}
    [∀ j, MetricSpace (V j)] [∀ j, Fintype (V j)]
    [∀ j, TopologicalSpace (Z j)] [∀ j, CompactSpace (Z j)] [∀ j, T2Space (Z j)]
    (o : ∀ j, V j) (r : ℝ) (γ : ∀ j, C(Z j, Point (V j) r))
    (j : ℕ) (hj : r < j) (a : LocallyFiniteK1 (Sigma Z)) :
    letI := separatedMetric o
    restrictComponent (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
      (pushforward (ripsFamilyMap o r γ) a) =
        pushforward (compactMap (γ j))
          (restrictComponent (sigmaComponent Z j) (sigmaComponent_open Z j) a) := by
  let := separatedMetric o
  exact DFunLike.congr_fun (restrictComponent_natural
    (sigmaComponent Z j) (sigmaComponent_open Z j)
    (separatedRipsEmbedding o r j) (separatedRipsEmbedding_open o r j hj)
    (ripsFamilyMap o r γ) (compactMap (γ j)) (fun _ => rfl)
    (ripsFamily_component_preimage o r γ j)) a

attribute [local instance] OAI.CoarseAssembly.explicitPersistenceComponent
attribute [local instance] OAI.CoarseAssembly.explicitPersistenceMetric
theorem explicitFiberStage_coarsen {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : r ≤ s) :
    pushforward (inclusion (by exact_mod_cast hrs)) (explicitFiberStage r hr) =
      explicitFiberStage s hs := by
  change pushforward _ (pushforward _ explicitCircleFamily) = _
  dsimp only [explicitFiberLoops]
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp,
    ripsFamilyMap_coarsen fiberBoundaryBase _ _ _
      (fiberedBoundaryLoops_coarsen elementaryMoves
        (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit) hr hs hrs)]
  rfl

theorem explicitFiberStage_detected (r : ℕ) (hr : 1 ≤ r) :
    ∃ test : LocallyFiniteK1 (Point FiberedUnion (r : ℝ)) →+ ℤ,
      test (explicitFiberStage r hr) = 1 := by
  obtain ⟨J, hJ⟩ := fiberedGraph_short_loops elementaryMoves (3 * r)
  let j := max J (r + 2)
  have hj : (r : ℝ) < j := by
    have h : r < j := by dsimp [j]; omega
    exact_mod_cast h
  have hj₂ : 2 ≤ j := by dsimp [j]; omega
  have hloop := hJ j (by dsimp [j]; omega)
  let c := graphRipsCocycle (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j)
    fiberCharge (fun x y _ => latticeCharge_reverse _ _) r hloop
  let d := separatedRipsEmbedding fiberBoundaryBase (r : ℝ) j
  have hd := separatedRipsEmbedding_open fiberBoundaryBase (r : ℝ) j hj
  refine ⟨(provedCircleInput.pairing c.toContinuousMap).comp (restrictComponent d hd), ?_⟩
  change provedCircleInput.pairing c.toContinuousMap
    (restrictComponent d hd (explicitFiberStage r hr)) = 1
  rw [explicitFiberStage, ripsFamily_restriction_class fiberBoundaryBase (r : ℝ)
    (explicitFiberLoops r hr) j hj, explicitCircleFamily_coordinate]
  change provedCircleInput.pairing c.toContinuousMap
    (graphLoopClass provedCircleInput
      (fiberedGraph_connected elementaryMoves chosenHolonomyUnit j) r hr
      (hexagonalBoundaryWalks.fiberWalk elementaryMoves chosenHolonomyUnit j)) = 1
  rw [graph_loop_index provedCircleInput _ fiberCharge
    (fun x y _ => latticeCharge_reverse _ _) r hr hloop,
    hexagonalBoundaryWalks.fiber_charge_one elementaryMoves chosenHolonomyUnit j hj₂]

theorem explicitFiberClass_infinite_order (n : ℤ) (hn : n ≠ 0) :
    n • explicitFiberClass ≠ 0 := by
  let C := coarsening FiberedUnion
  let test := fun r hr => (explicitFiberStage_detected r hr).choose
  have hdetect : ∀ r (hr : 1 ≤ r),
      test r hr (C.map 1 r hr (explicitFiberStage 1 le_rfl)) = 1 := by
    intro r hr
    change test r hr (pushforward (inclusion (by exact_mod_cast hr))
      (explicitFiberStage 1 le_rfl)) = 1
    rw [explicitFiberStage_coarsen le_rfl hr hr]
    exact (explicitFiberStage_detected r hr).choose_spec
  exact persistent_multiples_ne_zero C.map 1 (explicitFiberStage 1 le_rfl) test hdetect n hn

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ExplicitBoundaryConclusion
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.bounded_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.regularize_eval _root_.OAI.CoarseAssembly.Analytic.OddHomotopy.unitalSelfAdjoint_eval _root_.OAI.CoarseAssembly.Analytic.completedRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.familyRepresentation_apply _root_.OAI.CoarseAssembly.Analytic.localizedCycle_operator _root_.OAI.CoarseAssembly.Rips.analyticFamilyIndex_class _root_.OAI.CoarseAssembly.Rips.separatedIndexFamily_atScale _root_.OAI.CoarseAssembly.Rips.separatedRipsIndex_class _root_.OAI.CoarseAssembly.Rips.sqrtCoordinate_selfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterexample with circle, filling and additivity inputs discharged -/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric6
theorem explicitRealFiberStage_cast (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (h : r = (n : ℝ)) :
    (h ▸ explicitRealFiberStage r hr) = explicitFiberStage n hn := by
  subst r
  rfl

local instance explicitBoundaryMetric1_rf41b27_1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitBoundaryMetric2_rf41b27_1 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance explicitBoundaryMetric3_rf41b27_1 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric4
theorem explicitBoundaryStage_base_zero :
    pushforward (embeddingMap boundaryToBase
      (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
      explicitBoundaryStage = 0 := by
  change pushforward _ (pushforward _ explicitCircleFamily) = 0
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp, boundaryFamily_toBase]
  exact explicitBaseBoundaryFamily_zero discBoundaryBase concreteBaseWalk

theorem explicitBoundaryClass_base_zero :
    boundaryBaseCoarsening.homologyMap explicitBoundaryClass = 0 := by
  change (embeddingCoarsening boundaryToBase
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
    (classAt 1 1 (by norm_num) explicitBoundaryStage) = 0
  rw [embedding_classAt, explicitBoundaryStage_base_zero, classAt_zero]

attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric5
attribute [local instance] OAI.CoarseAssembly.explicitBoundaryMetric7
theorem explicitCounterexampleClass_image :
    totalToFiberCoarsening.homologyMap explicitCounterexampleClass = explicitFiberClass := by
  change (embeddingCoarsening totalToFiber.toEmbedding
    (fun x y => (totalToFiber_dist x y).le)).homologyMap
    ((embeddingCoarsening boundaryToVertex
      (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
      (classAt 1 1 (by norm_num) explicitBoundaryStage)) = _
  rw [embedding_classAt, embedding_classAt]
  have hs : pushforward (embeddingMap totalToFiber.toEmbedding
      (fun x y => (totalToFiber_dist x y).le) 1)
      (pushforward (embeddingMap boundaryToVertex
        (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
        explicitBoundaryStage) = explicitRealFiberStage 1 le_rfl := by
    have hp := congrArg pushforward boundaryFamily_toFiber
    have hv := DFunLike.congr_fun hp explicitCircleFamily
    simpa only [pushforward_comp, AddMonoidHom.comp_apply, explicitBoundaryStage,
      explicitRealFiberStage, fiberLoopsOne] using hv
  rw [hs]
  apply congrArg ((coarsening FiberedUnion).of 1)
  exact explicitRealFiberStage_cast 1 le_rfl 1 le_rfl (by norm_num)

theorem explicitCounterexampleClass_infinite_order (n : ℤ) (hn : n ≠ 0) :
    n • explicitCounterexampleClass ≠ 0 := by
  intro hz
  have h := congrArg totalToFiberCoarsening.homologyMap hz
  rw [map_zsmul, map_zero, explicitCounterexampleClass_image] at h
  exact explicitFiberClass_infinite_order n hn h

theorem explicitCounterexampleClass_index_zero (index : PublishedBoundaryAssemblyInput)
    (hgap : PublishedKazhdanInput) : index.total.assembly explicitCounterexampleClass = 0 :=
  boundary_assembly_zero index hgap explicitBoundaryClass explicitBoundaryClass_base_zero

/-- The full geometric conclusion, with only canonical assembly and the fixed-generator
published Kazhdan gap remaining. The particular countable class and its filling are proved. -/
theorem bounded_geometry_counterexample_from_index_gap
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) := by
  refine ⟨vertexUnion_proper elementaryMoves chosenHolonomyUnit,
    vertexUnion_uniform_balls elementaryMoves chosenHolonomyUnit,
    vertexUnion_separated elementaryMoves chosenHolonomyUnit,
    explicitCounterexampleClass, explicitCounterexampleClass_infinite_order,
    explicitCounterexampleClass_index_zero index hgap, ?_, ?_, ?_⟩
  · exact rationalization_ne_zero _ explicitCounterexampleClass_infinite_order
  · exact (kernel_obstructs_injectivity index.total.assembly _
      explicitCounterexampleClass_infinite_order
      (explicitCounterexampleClass_index_zero index hgap)).1
  · exact (kernel_obstructs_injectivity index.total.assembly _
      explicitCounterexampleClass_infinite_order
      (explicitCounterexampleClass_index_zero index hgap)).2

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_ConstructedConclusion
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counterexample for the constructed analytic coarse assembly map

Only the fixed-generator spectral-gap input remains in this theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.constructedConclusionMetric

theorem bounded_geometry_counterexample_from_gap (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_index_gap constructedBoundaryAssembly hgap

end CoarseAssembly

end

end OAI
end

section
-- module Solutions.Q229_CA.CoarseAssembly_UnconditionalConclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unconditional bounded-geometry counterexample

The geometric construction, analytic assembly, integral spectral certificate
and finite congruence generation are combined here.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.unconditionalConclusionMetric

theorem provedKazhdanInput : PublishedKazhdanInput :=
  publishedKazhdanInput_of_elementaryReduction_ca elementaryReduction_surjective

/-- The constructed ordinary coarse assembly map has an infinite-order
kernel class and fails injectivity both integrally and rationally. -/
theorem bounded_geometry_counterexample_unconditional :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_gap provedKazhdanInput

/-- The graph-family clauses of the main theorem, together with the full
coarse-assembly conclusion for its concrete separated union. -/
theorem bounded_geometry_graph_counterexample_unconditional_oai :
    (∀ j, Finite (FiberVertex j) ∧
      (fiberedGraph elementaryMoves chosenHolonomyUnit j).Connected) ∧
    (∃ D : ℕ, ∀ j (x : FiberVertex j),
      Nat.card {y // (fiberedGraph elementaryMoves chosenHolonomyUnit j).Adj x y} ≤ D) ∧
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) := by
  refine ⟨?_, ?_, bounded_geometry_counterexample_unconditional⟩
  · intro j
    exact ⟨inferInstance, fiberedGraph_connected elementaryMoves chosenHolonomyUnit j⟩
  · exact ⟨7 * (symmetricMoves elementaryMoves).card * 2 ^ 9,
      fun _ x => card_fibered_neighbors_le elementaryMoves chosenHolonomyUnit x⟩

end CoarseAssembly

end

end OAI
end

theorem solution : type_of% @OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional_oai := @OAI.CoarseAssembly.bounded_geometry_graph_counterexample_unconditional_oai
