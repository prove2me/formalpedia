-- Prove2me | solution 1 for OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:54:56.092622+00:00
-- url     : https://prove2.me/submissions/a2ae85d1-6401-4278-be86-ae0a32311e7c

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAIQ092A009

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ApproximateBisection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Approximate rational bisection for a Lipschitz residual.  A numerically
ambiguous sign terminates with a certified residual bound; otherwise the
true endpoint signs are preserved.  No monotonicity or derivative lower
bound is required. -/

namespace ContinuumCoulomb.ApproximateBisection

theorem midpoint_mem (s : Interval) (h : s.lo ≤ s.hi) :
    s.lo ≤ midpoint s ∧ midpoint s ≤ s.hi := by
  dsimp [midpoint]
  constructor <;> linarith

theorem initial_invariant {a b δ : ℚ} {f : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) :
    Invariant a b f δ (initial a b) := by
  refine ⟨le_rfl, le_rfl, hab, ?_, ?_⟩
  · simp [initial]
  · intro _
    exact ⟨ha, hb⟩

theorem step_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (_hδ : 0 ≤ δ)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    {s : Interval} (hs : Invariant a b f δ s) :
    Invariant a b f δ (step δ evaluate s) := by
  have hm := midpoint_mem s hs.ordered
  have he := abs_le.mp (heval (midpoint s) ⟨hs.lower.trans hm.1, hm.2.trans hs.upper⟩)
  unfold step
  split_ifs with hd hp hn
  · exact hs
  · have hp' : (δ : ℝ) < evaluate (midpoint s) := by exact_mod_cast hp
    refine ⟨hs.lower.trans hm.1, hs.upper, hm.2, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨by linarith [he.2], (hs.signs (by simpa using hd)).2⟩
  · have hn' : (evaluate (midpoint s) : ℝ) < -(δ : ℝ) := by exact_mod_cast hn
    refine ⟨hs.lower, hm.2.trans hs.upper, hm.1, ?_, ?_⟩
    · simp
    · intro _
      exact ⟨(hs.signs (by simpa using hd)).1, by linarith [he.1]⟩
  · have hp' : (evaluate (midpoint s) : ℝ) ≤ δ := by exact_mod_cast le_of_not_gt hp
    have hn' : -(δ : ℝ) ≤ evaluate (midpoint s) := by exact_mod_cast le_of_not_gt hn
    refine ⟨hs.lower.trans hm.1, hm.2.trans hs.upper, le_rfl, ?_, ?_⟩
    · intro _
      refine ⟨rfl, abs_le.mpr ?_⟩
      constructor <;> linarith [he.1, he.2]
    · simp

theorem step_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    {s : Interval} (hs : Invariant a b f δ s) :
    width (step δ evaluate s) ≤ width s / 2 := by
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  unfold step
  split_ifs with hd hp hn
  · have heq := (hs.certified hd).1
    simp only [width, heq, sub_self, zero_div, le_refl]
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, midpoint_cast]
    linarith
  · simp only [width, sub_self]
    linarith

theorem run_invariant {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    Invariant a b f δ (run δ evaluate a b n) := by
  induction n with
  | zero => exact initial_invariant hab ha hb
  | succ n ih =>
    change Invariant a b f δ ((step δ evaluate)^[n + 1] (initial a b))
    rw [Function.iterate_succ_apply']
    exact step_invariant hδ heval ih

theorem run_width {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ)) (n : ℕ) :
    width (run δ evaluate a b n) ≤ ((b : ℝ) - a) / 2 ^ n := by
  induction n with
  | zero => simp [run, initial, width]
  | succ n ih =>
    have hw := step_width (evaluate := evaluate) (run_invariant hδ hab ha hb heval n)
    have hrun : run δ evaluate a b (n + 1) = step δ evaluate (run δ evaluate a b n) :=
      Function.iterate_succ_apply' _ _ _
    rw [hrun]
    calc
      width (step δ evaluate (run δ evaluate a b n)) ≤
          width (run δ evaluate a b n) / 2 := hw
      _ ≤ (((b : ℝ) - a) / 2 ^ n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = ((b : ℝ) - a) / 2 ^ (n + 1) := by rw [pow_succ, div_div]

theorem invariant_residual {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|)
    {s : Interval} (hs : Invariant a b f δ s) :
    |f (midpoint s)| ≤ 2 * (δ : ℝ) + L * width s := by
  have hl : (a : ℝ) ≤ s.lo := by exact_mod_cast hs.lower
  have hu : (s.hi : ℝ) ≤ b := by exact_mod_cast hs.upper
  have ho : (s.lo : ℝ) ≤ s.hi := by exact_mod_cast hs.ordered
  have hm := midpoint_mem s hs.ordered
  have hmlo : (s.lo : ℝ) ≤ midpoint s := by exact_mod_cast hm.1
  have hmhi : (midpoint s : ℝ) ≤ s.hi := by exact_mod_cast hm.2
  have hw : 0 ≤ width s := sub_nonneg.mpr ho
  by_cases hd : s.settled = true
  · obtain ⟨heq, herr⟩ := hs.certified hd
    have he : midpoint s = s.lo := by simp [midpoint, heq]
    rw [he]
    exact herr.trans (le_add_of_nonneg_right (mul_nonneg hL hw))
  · have hsign := hs.signs (by simpa using hd)
    have hmemb : (midpoint s : ℝ) ∈ Set.Icc (a : ℝ) b := ⟨hl.trans hmlo, hmhi.trans hu⟩
    have hleft := hLip (midpoint s) hmemb s.lo ⟨hl, ho.trans hu⟩
    have hright := hLip (midpoint s) hmemb s.hi ⟨hl.trans ho, hu⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hmlo)] at hleft
    rw [abs_of_nonpos (sub_nonpos.mpr hmhi)] at hright
    have hlw : L * ((midpoint s : ℝ) - s.lo) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hrw : L * -((midpoint s : ℝ) - s.hi) ≤ L * width s :=
      mul_le_mul_of_nonneg_left (by dsimp [width]; linarith) hL
    have hδ' : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ
    apply abs_le.mpr
    constructor
    · have h := (neg_le_abs (f (midpoint s) - f s.lo)).trans hleft
      linarith [hsign.1]
    · have h := (le_abs_self (f (midpoint s) - f s.hi)).trans hright
      linarith [hsign.2]

/-- After `n` steps the returned rational has residual at most numerical
ambiguity plus the Lipschitz constant times the halved interval width. -/
theorem run_residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (midpoint (run δ evaluate a b n))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  exact (invariant_residual hδ hL hLip (run_invariant hδ hab ha hb heval n)).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left (run_width hδ hab ha hb heval n) hL) _)

end ContinuumCoulomb.ApproximateBisection

end OAI
end

section
-- module Solutions.OAIQ092_CC.QuantumFactoring_BinaryRoots
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

lemma rootSearch_spec {m e : ℕ} (_he : 0 < e) (k guess : ℕ)
    (hlo : guess^e ≤ m) (hhi : m < (guess+2^k)^e) :
    (rootSearch m e k guess)^e ≤ m ∧ m < (rootSearch m e k guess+1)^e := by
  induction k generalizing guess with
  | zero => simpa only [rootSearch,pow_zero] using And.intro hlo hhi
  | succ k ih =>
    simp only [rootSearch]
    by_cases hnext : (guess+2^k)^e ≤ m
    · rw [ite_eq_left hnext]
      apply ih _ hnext
      have hh : guess+2^k+2^k=guess+2^(k+1) := by rw [pow_succ]; omega
      rw [hh]
      exact hhi
    · rw [ite_eq_right hnext]
      exact ih _ hlo (by omega)

lemma boundedRoot_spec {m e n : ℕ} (he : 0 < e) (hm : m < 2^n) :
    (boundedRoot m e n)^e ≤ m ∧ m < (boundedRoot m e n+1)^e := by
  apply rootSearch_spec he n 0
  · simp [Nat.ne_of_gt he]
  · simp only [zero_add]
    exact hm.trans_le (Nat.le_self_pow he.ne' (2^n))

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_SquareRootProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bitwise integer square-root search and its actual polynomial-time
Boolean-stack implementation. This supplies arithmetic for finite-precision
geometric constants and mediator amplitudes without a real square-root oracle. -/

namespace ContinuumCoulomb.SquareRootProgram
open ExactQuantumFactoring.BitStackProgram

/-- The returned integer brackets the true square root by adjacent integers. -/
theorem root_spec (m : ℕ) : root m ^ 2 ≤ m ∧ m < (root m + 1) ^ 2 := by
  apply ExactQuantumFactoring.Primality.boundedRoot_spec (by decide)
  simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self m

end ContinuumCoulomb.SquareRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_DyadicRootProgram
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A computed dyadic square root of a nonnegative rational, with strict
error below one unit in the requested binary precision. Precision is unary;
numerator, denominator, and result are binary. -/

namespace ContinuumCoulomb.DyadicRootProgram
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b N F : ℕ) (hF : 0 < F) :
    0 ≤ Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) ∧
      Real.sqrt ((N : ℝ) / F) - (value b N F : ℝ) < 1 / (2 : ℝ) ^ b := by
  let p : ℕ := 2 ^ b
  let m : ℕ := N * p ^ 2 / F
  let r : ℕ := SquareRootProgram.root m
  have hp : (0 : ℝ) < p := by dsimp [p]; positivity
  have hFr : (0 : ℝ) < F := by exact_mod_cast hF
  have hlo : r ^ 2 * F ≤ N * p ^ 2 :=
    (Nat.mul_le_mul_right F (SquareRootProgram.root_spec m).1).trans (Nat.div_mul_le_self _ _)
  have hhi : N * p ^ 2 < (r + 1) ^ 2 * F :=
    (Nat.div_lt_iff_lt_mul hF).mp (SquareRootProgram.root_spec m).2
  have hlo' : (r : ℝ) ^ 2 * F ≤ (N : ℝ) * (p : ℝ) ^ 2 := by exact_mod_cast hlo
  have hhi' : (N : ℝ) * (p : ℝ) ^ 2 < ((r : ℝ) + 1) ^ 2 * F := by exact_mod_cast hhi
  have hrad : 0 ≤ (N : ℝ) / F := by positivity
  have hsquare : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 * F = (N : ℝ) * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrad]
    field_simp [hFr.ne']
  have hs : 0 ≤ Real.sqrt ((N : ℝ) / F) * p := by positivity
  have hslo : (r : ℝ) ^ 2 ≤ (Real.sqrt ((N : ℝ) / F) * p) ^ 2 := by
    apply (mul_le_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hlo'
  have hshi : (Real.sqrt ((N : ℝ) / F) * p) ^ 2 < ((r : ℝ) + 1) ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hFr).mp
    rw [hsquare]
    exact hhi'
  have hl : (r : ℝ) ≤ Real.sqrt ((N : ℝ) / F) * p := by
    nlinarith only [hslo, hs, show 0 ≤ (r : ℝ) by positivity]
  have hu : Real.sqrt ((N : ℝ) / F) * p < (r : ℝ) + 1 := by
    nlinarith only [hshi, hs, show 0 ≤ (r : ℝ) by positivity]
  have hvalue : (value b N F : ℝ) = (r : ℝ) / p := by
    simp only [value, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, p, r, m,
      Nat.cast_pow, Nat.cast_ofNat]
  have hpcast : (p : ℝ) = (2 : ℝ) ^ b := by simp only [p, Nat.cast_pow, Nat.cast_ofNat]
  rw [hvalue, ← hpcast]
  constructor
  · exact sub_nonneg.mpr ((div_le_iff₀ hp).mpr hl)
  · apply (lt_div_iff₀ hp).mpr
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
    linarith

end ContinuumCoulomb.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_RationalSquareRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certified evaluation of square roots of nonnegative rational samples.
The same finite dyadic procedure serves the fixed Gaussian constants and
softened Coulomb distances. -/

namespace ContinuumCoulomb.RationalSquareRoot
open ExactQuantumFactoring.BitStackProgram

theorem value_error (b : ℕ) {q : ℚ} (hq : 0 ≤ q) :
    |(value (b, q) : ℝ) - Real.sqrt (q : ℝ)| ≤ (2 : ℝ)⁻¹ ^ b := by
  have hnum : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnumq : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum
  have hrepr : (q.num.toNat : ℚ) / q.den = q := by rw [hnumq, Rat.num_div_den]
  have hre : (q.num.toNat : ℝ) / q.den = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using congrArg (fun x : ℚ => (x : ℝ)) hrepr
  have h := DyadicRootProgram.value_error b q.num.toNat q.den q.pos
  rw [hre] at h
  change |(DyadicRootProgram.value b q.num.toNat q.den : ℝ) - Real.sqrt (q : ℝ)| ≤ _
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2.le.trans_eq (by simp only [one_div, inv_pow])

end ContinuumCoulomb.RationalSquareRoot

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionRegisters
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common-denominator registers for approximate bisection.  Each update
doubles the denominator and uses only addition and doubling of numerators;
therefore every register gains at most one bit per iteration. -/

namespace ContinuumCoulomb.BisectionRegisters
open ExactQuantumFactoring.BitStackProgram

theorem initial_den_pos (a b : ℚ) : 0 < (initial a b).2.2.1 :=
  Nat.mul_pos a.pos b.pos

theorem middle_eq (r : Registers) (hr : 0 < r.2.2.1) :
    middle r = ApproximateBisection.midpoint (interval r) := by
  have hd : (r.2.2.1 : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [middle, ApproximateBisection.midpoint, interval, left, right,
    Rat.mkRat_eq_div, Int.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem initial_interval (a b : ℚ) :
    interval (initial a b) = ApproximateBisection.initial a b := by
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have hl : left (initial a b) = a := by
    change mkRat (a.num * b.den) (a.den * b.den) = a
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den a]
    field_simp
  have hh : right (initial a b) = b := by
    change mkRat (b.num * a.den) (a.den * b.den) = b
    rw [Rat.mkRat_eq_div]
    push_cast
    conv_rhs => rw [← Rat.num_div_den b]
    field_simp
  change (⟨left (initial a b), right (initial a b), false⟩ :
    ApproximateBisection.Interval) = ⟨a, b, false⟩
  rw [hl, hh]

theorem step_den_pos (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : 0 < (step δ evaluate r).2.2.1 := by
  unfold step
  split_ifs <;> first | exact hr | exact Nat.mul_pos (by decide) hr

private theorem double_quotient (z : ℤ) (d : ℕ) (hd : 0 < d) :
    mkRat (2 * z) (2 * d) = mkRat z d := by
  have h : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Rat.mkRat_eq_div, Int.cast_mul, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem step_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) : interval (step δ evaluate r) =
      ApproximateBisection.step δ evaluate (interval r) := by
  have hm : middle r = (left r + right r) / 2 := middle_eq r hr
  unfold step ApproximateBisection.step
  simp only [interval, ApproximateBisection.midpoint, ← hm]
  split_ifs <;> simp [left, right, middle, double_quotient, hr]

theorem iterate_interval (δ : ℚ) (evaluate : ℚ → ℚ) (r : Registers)
    (hr : 0 < r.2.2.1) (n : ℕ) :
    0 < ((step δ evaluate)^[n] r).2.2.1 ∧
      interval ((step δ evaluate)^[n] r) =
        (ApproximateBisection.step δ evaluate)^[n] (interval r) := by
  induction n with
  | zero => exact ⟨hr, rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ⟨step_den_pos δ evaluate _ ih.1, (step_interval δ evaluate _ ih.1).trans
      (congrArg (ApproximateBisection.step δ evaluate) ih.2)⟩

/-- The actual unreduced register execution satisfies the analytic residual
bound; all evaluation calls remain inside the initial rational interval. -/
theorem residual {a b δ : ℚ} {f : ℝ → ℝ} {evaluate : ℚ → ℚ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (middle ((step δ evaluate)^[n] (initial a b)))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) := by
  obtain ⟨hp, hi⟩ := iterate_interval δ evaluate (initial a b) (initial_den_pos a b) n
  rw [middle_eq _ hp, hi, initial_interval]
  exact ApproximateBisection.run_residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionRegisters

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_Programs_BisectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal polynomial-time bisection with a supplied polynomial-time
rational evaluator.  The evaluator environment and tolerance remain in
the input registers; they are not fixed nonuniform advice. -/

namespace ContinuumCoulomb.BisectionProgram
open ExactQuantumFactoring.BitStackProgram
open BisectionRegisters

theorem residual {E : Type} (evaluate : E → ℚ → ℚ) (e : E)
    {a b δ : ℚ} {f : ℝ → ℝ} {L : ℝ}
    (hδ : 0 ≤ δ) (hab : a ≤ b) (ha : 0 ≤ f a) (hb : f b ≤ 0) (hL : 0 ≤ L)
    (heval : ∀ q ∈ Set.Icc a b, |(evaluate e q : ℝ) - f q| ≤ (δ : ℝ))
    (hLip : ∀ x ∈ Set.Icc (a : ℝ) b, ∀ y ∈ Set.Icc (a : ℝ) b,
      |f x - f y| ≤ L * |x - y|) (n : ℕ) :
    |f (approximate evaluate (n, (e, (δ, (a, b)))))| ≤
      2 * (δ : ℝ) + L * (((b : ℝ) - a) / 2 ^ n) :=
  BisectionRegisters.residual hδ hab ha hb hL heval hLip n

end ContinuumCoulomb.BisectionProgram

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombQuadratureBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial mesh and precision budgets for the six-coordinate
Coulomb quadrature. All varying parameters below are unary naturals. -/

noncomputable section
namespace ContinuumCoulomb.CoulombQuadratureSchedule

theorem dyadic_le_inverse (b : ℕ) : (2 : ℝ)⁻¹ ^ b ≤ ((b : ℝ) + 1)⁻¹ := by
  have hb : (b : ℝ) + 1 ≤ (2 : ℝ) ^ b := by
    exact_mod_cast Nat.succ_le_of_lt b.lt_two_pow_self
  rw [inv_pow]
  exact inv_anti₀ (by positivity) hb

end ContinuumCoulomb.CoulombQuadratureSchedule

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedEvaluationBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial accuracy schedule for the calibrated hopping
residual. The square-root input uses quadratic precision in the requested
inverse error, rather than assuming a spectral gap for numerical samples. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

theorem root_budget (P : ℕ) :
    (2 : ℝ)⁻¹ ^ rootPrecision P ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  apply (CoulombQuadratureSchedule.dyadic_le_inverse _).trans
  apply inv_anti₀ (by positivity)
  simp only [rootPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CalibratedBisectionLocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every returned rational remains in its original search interval. This
geometric invariant does not need an accuracy or residual-sign hypothesis. -/

namespace ContinuumCoulomb

private theorem bisection_step_nested (δ : ℚ) (evaluate : ℚ → ℚ)
    {a b : ℚ} (s : ApproximateBisection.Interval)
    (hs : a ≤ s.lo ∧ s.lo ≤ s.hi ∧ s.hi ≤ b) :
    a ≤ (ApproximateBisection.step δ evaluate s).lo ∧
      (ApproximateBisection.step δ evaluate s).lo ≤ (ApproximateBisection.step δ evaluate s).hi ∧
      (ApproximateBisection.step δ evaluate s).hi ≤ b := by
  have hm := ApproximateBisection.midpoint_mem s hs.2.1
  unfold ApproximateBisection.step
  split_ifs
  · exact hs
  · exact ⟨hs.1.trans hm.1, hm.2, hs.2.2⟩
  · exact ⟨hs.1, hm.1, hm.2.trans hs.2.2⟩
  · exact ⟨hs.1.trans hm.1, le_rfl, hm.2.trans hs.2.2⟩

theorem bisection_run_nested (δ : ℚ) (evaluate : ℚ → ℚ) (a b : ℚ)
    (hab : a ≤ b) (n : ℕ) :
    a ≤ (ApproximateBisection.run δ evaluate a b n).lo ∧
      (ApproximateBisection.run δ evaluate a b n).lo ≤
        (ApproximateBisection.run δ evaluate a b n).hi ∧
      (ApproximateBisection.run δ evaluate a b n).hi ≤ b := by
  induction n with
  | zero => exact ⟨le_rfl, hab, le_rfl⟩
  | succ n ih =>
    simpa only [ApproximateBisection.run, Function.iterate_succ_apply'] using
      bisection_step_nested δ evaluate (ApproximateBisection.run δ evaluate a b n) ih

theorem bisection_value_mem {E : Type} (evaluate : E → ℚ → ℚ) (e : E)
    (δ a b : ℚ) (hab : a ≤ b) (n : ℕ) :
    BisectionProgram.approximate evaluate (n, (e, (δ, (a, b)))) ∈ Set.Icc a b := by
  obtain ⟨hp, hi⟩ := BisectionRegisters.iterate_interval δ (evaluate e)
    (BisectionRegisters.initial a b) (BisectionRegisters.initial_den_pos a b) n
  unfold BisectionProgram.approximate
  rw [BisectionRegisters.middle_eq _ hp, hi, BisectionRegisters.initial_interval]
  have hs := bisection_run_nested δ (evaluate e) a b hab n
  have hm := ApproximateBisection.midpoint_mem (ApproximateBisection.run δ (evaluate e) a b n) hs.2.1
  exact ⟨hs.1.trans hm.1, hm.2.trans hs.2.2⟩

end ContinuumCoulomb

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactTemplates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fixed nine-link contact templates used after spin subdivision.
Coordinates use the Euclidean plane. The link lengths and separation
bounds are stable under small movements of the sites. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem contactPoint_dist_sq (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ^ 2 =
      (x - x') ^ 2 + (y - y') ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, contactPoint_zero, contactPoint_one, Real.dist_eq, sq_abs]

theorem contactStepX_lower {c : ℝ} (hc : c ≤ 1) (k : ℕ) : c ≤ contactStepX c k := by
  unfold contactStepX
  split_ifs <;> linarith

/-- Horizontal projection accumulates a uniform positive amount per step. -/
theorem contactPath_horizontal_lower {c : ℝ} (hc : c ≤ 1) {i j : ℕ} (hij : i ≤ j) :
    c * (j - i : ℕ) ≤ contactPathVertex c j 0 - contactPathVertex c i 0 := by
  change c * (j - i : ℕ) ≤ (∑ k ∈ Finset.range j, contactStepX c k) -
    ∑ k ∈ Finset.range i, contactStepX c k
  rw [← Finset.sum_Ico_eq_sub _ hij]
  calc
    c * (j - i : ℕ) = ∑ _k ∈ Finset.Ico i j, c := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun k _ => contactStepX_lower hc k)

/-- Nonconsecutive vertices on a backbone are separated by at least 1.5. -/
theorem contactPath_nonlink_separation {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 1)
    {i j : ℕ} (hij : i + 2 ≤ j) :
    3 / 2 ≤ dist (contactPathVertex c j) (contactPathVertex c i) := by
  have h := contactPath_horizontal_lower hc' (show i ≤ j by omega)
  have hcount : (2 : ℝ) ≤ (j - i : ℕ) := by exact_mod_cast (show 2 ≤ j - i by omega)
  have hx : 3 / 2 ≤ contactPathVertex c j 0 - contactPathVertex c i 0 := by
    nlinarith
  have hdist := contactPoint_dist_sq
    (∑ k ∈ Finset.range j, contactStepX c k) (∑ k ∈ Finset.range j, contactStepY c k)
    (∑ k ∈ Finset.range i, contactStepX c k) (∑ k ∈ Finset.range i, contactStepY c k)
  change dist (contactPathVertex c j) (contactPathVertex c i) ^ 2 =
    (contactPathVertex c j 0 - contactPathVertex c i 0) ^ 2 +
    (contactPathVertex c j 1 - contactPathVertex c i 1) ^ 2 at hdist
  nlinarith [sq_nonneg (contactPathVertex c j 1 - contactPathVertex c i 1),
    show 0 ≤ dist (contactPathVertex c j) (contactPathVertex c i) from dist_nonneg]

/-- The paper's nonlink margin survives independent small movements. -/
theorem contact_separation_stable (x y x' y' : ContactPoint)
    (hsep : 7 / 5 ≤ dist x y) (hx : dist x x' ≤ 1 / 20) (hy : dist y y' ≤ 1 / 20) :
    6 / 5 < dist x' y' := by
  have h := dist_triangle x x' y
  have h' := dist_triangle x' y' y
  rw [dist_comm y' y] at h'
  linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactAdjustment
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit one-variable continuation for independent contact lengths.
Four sloping links share a transverse height; the other five remain axial.
Thus each nine-link path is adjusted by one scalar intermediate-value solve,
with fixed endpoints and no solve whose dimension grows with the lattice. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

/-- A quantitative square-root estimate, with fixed rational margins. -/
theorem adjustedContactForward_bound {length c h : ℝ}
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance)
    (hc : 7 / 10 ≤ c) (hc' : c ≤ 9 / 10) (hh : h ^ 2 = 1 - c ^ 2) :
    c - 1 / 10000 ≤ adjustedContactForward length h ∧
      adjustedContactForward length h ≤ c + 1 / 10000 := by
  have hlnonneg : 0 ≤ length := by unfold contactLengthTolerance at hl; linarith
  have hlo : (1 - contactLengthTolerance) ^ 2 ≤ length ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ length + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hhi : length ^ 2 ≤ (1 + contactLengthTolerance) ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hl')
      (show 0 ≤ (1 + contactLengthTolerance) + length by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ c ^ 2 := by nlinarith
  have hrad : 0 ≤ length ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hlo
    nlinarith
  have hs : adjustedContactForward length h ^ 2 = length ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsnonneg : 0 ≤ adjustedContactForward length h := Real.sqrt_nonneg _
  unfold contactLengthTolerance at hlo hhi
  constructor <;> nlinarith

theorem contactHeightLow_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ^ 2 = 1 - (c + 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeightHigh_sq {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightHigh c ^ 2 = 1 - (c - 1 / 1000) ^ 2 := by
  apply Real.sq_sqrt
  nlinarith

theorem contactHeight_order {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8) :
    contactHeightLow c ≤ contactHeightHigh c := by
  have hlow := contactHeightLow_sq hc hc'
  have hhigh := contactHeightHigh_sq hc hc'
  have hl : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  nlinarith

theorem adjustedContactSpan_continuous (lengths : ℕ → ℝ) :
    Continuous (adjustedContactSpan lengths) := by
  unfold adjustedContactSpan adjustedContactStepX adjustedContactForward
  apply continuous_finsetSum
  intro k _
  split_ifs <;> fun_prop

/-- The low-height endpoint overshoots the desired unperturbed span. -/
theorem adjustedContactSpan_low {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    5 + 4 * c + contactLengthTolerance ≤ adjustedContactSpan lengths (contactHeightLow c) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have h2 := (hf 2 (by norm_num)).1
  have h3 := (hf 3 (by norm_num)).1
  have h5 := (hf 5 (by norm_num)).1
  have h6 := (hf 6 (by norm_num)).1
  have h0 := hl 0 (by norm_num)
  have h1 := hl 1 (by norm_num)
  have h4 := hl 4 (by norm_num)
  have h7 := hl 7 (by norm_num)
  have h8 := hl 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- The high-height endpoint undershoots the desired unperturbed span. -/
theorem adjustedContactSpan_high {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    adjustedContactSpan lengths (contactHeightHigh c) ≤ 5 + 4 * c - contactLengthTolerance := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_bound (hl k hk) (hl' k hk)
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have h2 := (hf 2 (by norm_num)).2
  have h3 := (hf 3 (by norm_num)).2
  have h5 := (hf 5 (by norm_num)).2
  have h6 := (hf 6 (by norm_num)).2
  have h0 := hl' 0 (by norm_num)
  have h1 := hl' 1 (by norm_num)
  have h4 := hl' 4 (by norm_num)
  have h7 := hl' 7 (by norm_num)
  have h8 := hl' 8 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  unfold contactLengthTolerance at *
  linarith

/-- All nine link lengths can be prescribed independently while both
endpoints remain fixed at any allowed span. -/
theorem adjustedContactSpan_exists {c span : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hspan : 5 + 4 * c - contactLengthTolerance ≤ span)
    (hspan' : span ≤ 5 + 4 * c + contactLengthTolerance) :
    ∃ h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c), adjustedContactSpan lengths h = span := by
  have hiv := intermediate_value_Icc' (contactHeight_order hc hc')
    (adjustedContactSpan_continuous lengths).continuousOn
  exact hiv ⟨(adjustedContactSpan_high hc hc' lengths hl hl').trans hspan,
    hspan'.trans (adjustedContactSpan_low hc hc' lengths hl hl')⟩

theorem adjustedContactVertex_end (lengths : ℕ → ℝ) (h : ℝ) :
    adjustedContactVertex lengths h 9 = contactPoint (adjustedContactSpan lengths h) 0 := by
  ext i
  fin_cases i
  · rfl
  · norm_num [adjustedContactVertex, contactPoint, Finset.sum_range_succ, adjustedContactStepY]

/-- The continued path has the prescribed actual Euclidean link lengths. -/
theorem adjustedContact_link_length {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k) {k : ℕ} (hk : k < 9) :
    dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) = lengths k := by
  have hlength : 0 ≤ lengths k := by
    have := hl k hk
    unfold contactLengthTolerance at this
    linarith
  have hlow : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh := contactHeightHigh_sq hc hc'
  have hh0 : 0 ≤ h := hlow.trans hh.1
  have hh2 : h ^ 2 ≤ contactHeightHigh c ^ 2 := by nlinarith [hh.2]
  have hmin := hl k hk
  have hmin2 : (1 - contactLengthTolerance) ^ 2 ≤ lengths k ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hmin)
      (show 0 ≤ lengths k + (1 - contactLengthTolerance) by
        unfold contactLengthTolerance; linarith)
    nlinarith
  have hc2 : (7 / 10 : ℝ) ^ 2 ≤ (c - 1 / 1000) ^ 2 := by nlinarith
  have hrad : 0 ≤ lengths k ^ 2 - h ^ 2 := by
    unfold contactLengthTolerance at hmin2
    nlinarith
  have hroot : adjustedContactForward (lengths k) h ^ 2 = lengths k ^ 2 - h ^ 2 := Real.sq_sqrt hrad
  have hsq : dist (adjustedContactVertex lengths h (k + 1)) (adjustedContactVertex lengths h k) ^ 2 =
      lengths k ^ 2 := by
    unfold adjustedContactVertex
    rw [contactPoint_dist_sq]
    simp only [Finset.sum_range_succ, add_sub_cancel_left]
    unfold adjustedContactStepX adjustedContactStepY
    split_ifs <;> (try omega) <;> nlinarith
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h (k + 1))
    (adjustedContactVertex lengths h k) from dist_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactDisplacement
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform displacement bounds for the explicit independent-length paths. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

theorem adjustedContactForward_antitone {length h h' : ℝ} (hh : 0 ≤ h) (hle : h ≤ h') :
    adjustedContactForward length h' ≤ adjustedContactForward length h := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem adjustedContactForward_near {c h length : ℝ}
    (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (hl : 1 - contactLengthTolerance ≤ length) (hl' : length ≤ 1 + contactLengthTolerance) :
    |adjustedContactForward length h - c| ≤ 11 / 10000 := by
  have hlow := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c + 1 / 1000 by linarith)
    (show c + 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightLow_sq hc hc')
  have hhigh := adjustedContactForward_bound hl hl'
    (show 7 / 10 ≤ c - 1 / 1000 by linarith)
    (show c - 1 / 1000 ≤ 9 / 10 by linarith) (contactHeightHigh_sq hc hc')
  have hlo : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hh0 : 0 ≤ h := hlo.trans hh.1
  have ha := adjustedContactForward_antitone (length := length) hlo hh.1
  have hb := adjustedContactForward_antitone (length := length) hh0 hh.2
  apply abs_le.mpr
  constructor <;> linarith

theorem contactHeight_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    |h - contactSlopeHeight c| ≤ 1 / 250 := by
  have hbase := contactSlopeHeight_sq (by linarith : -1 ≤ c) (by linarith : c ≤ 1)
  have hlowsq := contactHeightLow_sq hc hc'
  have hhighsq := contactHeightHigh_sq hc hc'
  have hbase0 : 0 ≤ contactSlopeHeight c := Real.sqrt_nonneg _
  have hlow0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hhigh0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hbaseMin : 2 / 5 ≤ contactSlopeHeight c := by nlinarith
  have hlowMin : 2 / 5 ≤ contactHeightLow c := by nlinarith
  have hhighMin : 2 / 5 ≤ contactHeightHigh c := by nlinarith
  have hlowNear : contactSlopeHeight c - 1 / 250 ≤ contactHeightLow c := by nlinarith
  have hhighNear : contactHeightHigh c ≤ contactSlopeHeight c + 1 / 250 := by nlinarith
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem adjustedContactStepX_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k < 9) :
    |adjustedContactStepX lengths h k - contactStepX c k| ≤ 11 / 10000 := by
  unfold adjustedContactStepX contactStepX
  split_ifs
  · exact adjustedContactForward_near hc hc' hh (hl k hk) (hl' k hk)
  · apply abs_le.mpr
    have h1 := hl k hk
    have h2 := hl' k hk
    unfold contactLengthTolerance at h1 h2
    constructor <;> linarith

theorem adjustedContactStepY_near {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) (k : ℕ) :
    |adjustedContactStepY h k - contactStepY c k| ≤ 1 / 250 := by
  have hnear := contactHeight_near hc hc' hh
  unfold adjustedContactStepY contactStepY
  split_ifs
  · exact hnear
  · simpa only [neg_sub_neg, abs_sub_comm] using hnear
  · norm_num

theorem contact_sum_error {f g : ℕ → ℝ} {k : ℕ} {eta : ℝ}
    (h : ∀ j < k, |f j - g j| ≤ eta) :
    |(∑ j ∈ Finset.range k, f j) - ∑ j ∈ Finset.range k, g j| ≤ k * eta := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range k, |f j - g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, eta := Finset.sum_le_sum (fun j hj => h j (Finset.mem_range.mp hj))
    _ = _ := by simp

/-- A uniform displacement bound with room for moving the path origin. -/
theorem adjustedContactVertex_displacement {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c))
    (lengths : ℕ → ℝ)
    (hl : ∀ j < 9, 1 - contactLengthTolerance ≤ lengths j)
    (hl' : ∀ j < 9, lengths j ≤ 1 + contactLengthTolerance) {k : ℕ} (hk : k ≤ 9) :
    dist (adjustedContactVertex lengths h k) (contactPathVertex c k) < 1 / 25 := by
  have hx := contact_sum_error (k := k)
    (fun j hj => adjustedContactStepX_near hc hc' hh lengths hl hl' (by omega : j < 9))
  have hy := contact_sum_error (k := k)
    (fun j _ => adjustedContactStepY_near hc hc' hh j)
  have hkreal : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hx' : |adjustedContactVertex lengths h k 0 - contactPathVertex c k 0| ≤ 99 / 10000 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepX lengths h j) -
      ∑ j ∈ Finset.range k, contactStepX c j| ≤ 99 / 10000
    linarith
  have hy' : |adjustedContactVertex lengths h k 1 - contactPathVertex c k 1| ≤ 9 / 250 := by
    change |(∑ j ∈ Finset.range k, adjustedContactStepY h j) -
      ∑ j ∈ Finset.range k, contactStepY c j| ≤ 9 / 250
    linarith
  have hdist := contactPoint_dist_sq
    (∑ j ∈ Finset.range k, adjustedContactStepX lengths h j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h j)
    (∑ j ∈ Finset.range k, contactStepX c j)
    (∑ j ∈ Finset.range k, contactStepY c j)
  change dist (adjustedContactVertex lengths h k) (contactPathVertex c k) ^ 2 =
    (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 +
    (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 at hdist
  have hxSq : (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0) ^ 2 ≤ (99 / 10000 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 0 - contactPathVertex c k 0))
      (by norm_num : (0 : ℝ) ≤ 99 / 10000)).mpr hx'
  have hySq : (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1) ^ 2 ≤ (9 / 250 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg
      (adjustedContactVertex lengths h k 1 - contactPathVertex c k 1))
      (by norm_num : (0 : ℝ) ≤ 9 / 250)).mpr hy'
  nlinarith [show 0 ≤ dist (adjustedContactVertex lengths h k) (contactPathVertex c k) from dist_nonneg]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGadgets
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two signed-edge contact gadgets. Each has twenty sites, nineteen
links, fixed original endpoints, and independently prescribed link lengths.
A negative input sign places the central partner off the backbone. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactGadgetSlope_bounds (negative : Bool) :
    3 / 4 ≤ contactGadgetSlope negative ∧ contactGadgetSlope negative ≤ 7 / 8 := by
  cases negative <;> norm_num [contactGadgetSlope]

theorem contactGadgetSpan_bounds (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    5 + 4 * contactGadgetSlope negative - contactLengthTolerance ≤ contactGadgetSpan negative central ∧
      contactGadgetSpan negative central ≤ 5 + 4 * contactGadgetSlope negative + contactLengthTolerance := by
  cases negative
  · simp only [contactGadgetSlope, contactGadgetSpan, Bool.false_eq_true, ite_false, if_false]
    constructor <;> linarith
  · norm_num [contactGadgetSlope, contactGadgetSpan, contactLengthTolerance]

theorem contactGadgetRightNode_position (negative : Bool) (central : ℝ)
    (leftLengths rightLengths : ℕ → ℝ) (leftHeight rightHeight : ℝ)
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central)
    (k : Fin 10) :
    contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (contactGadgetRightNode negative k) =
      contactPoint (contactGadgetRightOrigin negative central) 0 +
        adjustedContactVertex rightLengths rightHeight k.val := by
  by_cases hk : k = 0
  · subst k
    rw [contactGadgetRightNode, dite_eq_left rfl]
    cases negative
    · simp [contactGadgetPosition, contactGadgetSide, adjustedContactVertex, contactPoint]
    · change adjustedContactVertex leftLengths leftHeight 9 = contactPoint (17 / 2) 0 +
        adjustedContactVertex rightLengths rightHeight 0
      rw [adjustedContactVertex_end, hleft]
      simp [contactGadgetSpan, adjustedContactVertex, contactPoint]
  · rw [contactGadgetRightNode, dite_eq_right hk]
    change contactPoint (contactGadgetRightOrigin negative central) 0 +
      adjustedContactVertex rightLengths rightHeight (k.val - 1 + 1) = _
    congr 2
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    omega

/-- Every physical link has its independently prescribed length. -/
theorem contactGadget_link_lengths (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central)
    (leftLengths rightLengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths k)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths k)
    {leftHeight rightHeight : ℝ}
    (hleftHeight : leftHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hrightHeight : rightHeight ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hleft : adjustedContactSpan leftLengths leftHeight = contactGadgetSpan negative central) :
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (Sum.inl k.castSucc)) = leftLengths k.val) ∧
    dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide)
      (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9)) = central ∧
    (∀ k : Fin 9,
      dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.succ))
        (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
          (contactGadgetRightNode negative k.castSucc)) = rightLengths k.val) := by
  have hs := contactGadgetSlope_bounds negative
  have hcentral : 0 ≤ central := by unfold contactLengthTolerance at hc; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact adjustedContact_link_length hs.1 hs.2 hleftHeight leftLengths hl k.isLt
  · have hA : contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        (Sum.inl 9) = contactPoint (contactGadgetSpan negative central) 0 := by
      change adjustedContactVertex leftLengths leftHeight 9 = _
      rw [adjustedContactVertex_end, hleft]
    rw [hA]
    have hsq : dist (contactGadgetPosition negative central leftLengths rightLengths leftHeight rightHeight
        contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0) ^ 2 = central ^ 2 := by
      cases negative <;> simp only [contactGadgetSide, contactGadgetPosition, Sum.elim_inr,
        contactGadgetRightOrigin, contactGadgetSpan, Bool.false_eq_true, ite_false, if_false,
        ite_true, if_true, contactPoint_dist_sq] <;> ring
    nlinarith [show 0 ≤ dist (contactGadgetPosition negative central leftLengths rightLengths
      leftHeight rightHeight contactGadgetSide) (contactPoint (contactGadgetSpan negative central) 0)
      from dist_nonneg]
  · intro k
    rw [contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      contactGadgetRightNode_position negative central leftLengths rightLengths leftHeight rightHeight hleft,
      dist_add_left]
    exact adjustedContact_link_length hs.1 hs.2 hrightHeight rightLengths hr k.isLt

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform separation of contacts from different lattice edges. The estimates
use only fixed strip bounds, so the lattice size never enters their constants. -/

noncomputable section
namespace ContinuumCoulomb

theorem contact_interval_lattice_distance {x margin : ℝ}
    (hx : margin ≤ x) (hx' : x ≤ 17 - margin) (k : ℤ) :
    margin ≤ |x - 17 * k| := by
  by_cases hk : k ≤ 0
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    exact (le_abs_self _).trans' (by linarith)
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    exact (neg_le_abs _).trans' (by linarith)

theorem contactPoint_coordinate_le_dist (p q : ContactPoint) (i : Fin 2) :
    |p i - q i| ≤ dist p q := by
  have hdist := EuclideanSpace.dist_sq_eq p q
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hdist
  fin_cases i
  · change |p 0 - q 0| ≤ dist p q
    nlinarith [sq_nonneg (p 1 - q 1), abs_nonneg (p 0 - q 0),
      sq_abs (p 0 - q 0), show 0 ≤ dist p q from dist_nonneg]
  · change |p 1 - q 1| ≤ dist p q
    nlinarith [sq_nonneg (p 0 - q 0), abs_nonneg (p 1 - q 1),
      sq_abs (p 1 - q 1), show 0 ≤ dist p q from dist_nonneg]

/-- Perpendicular gadgets retain the paper's 1.4 nonlink margin. -/
theorem perpendicularContact_separation (a b c d : ℤ) (p q : ContactStripSite) :
    7 / 5 < dist (horizontalContact a b p) (verticalContact c d q) := by
  by_cases hp : p.transverse = 0
  · by_cases hq : q.transverse = 0
    · have hx := contact_interval_lattice_distance p.axial_lower
        (show p.axial ≤ 17 - (1 : ℝ) by linarith [p.axial_upper]) (c - a)
      have hy := contact_interval_lattice_distance q.axial_lower
        (show q.axial ≤ 17 - (1 : ℝ) by linarith [q.axial_upper]) (b - d)
      have hdist := contactPoint_dist_sq
        (17 * a + p.axial) (17 * b + p.transverse)
        (17 * c - q.transverse) (17 * d + q.axial)
      have hx' : 1 ≤ |17 * (a : ℝ) + p.axial - (17 * c - q.transverse)| := by
        push_cast at hx
        rw [hq, sub_zero]
        convert hx using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        ring
      have hy' : 1 ≤ |17 * (b : ℝ) + p.transverse - (17 * d + q.axial)| := by
        push_cast at hy
        rw [hp]
        have hneg : 17 * (b : ℝ) + 0 - (17 * d + q.axial) =
            -(q.axial - 17 * ((b : ℝ) - d)) := by ring
        rw [hneg, abs_neg]
        exact hy
      have hx2 : 1 ≤ (17 * (a : ℝ) + p.axial - (17 * c - q.transverse)) ^ 2 := by
        nlinarith [sq_abs (17 * (a : ℝ) + p.axial - (17 * c - q.transverse))]
      have hy2 : 1 ≤ (17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) ^ 2 := by
        nlinarith [sq_abs (17 * (b : ℝ) + p.transverse - (17 * d + q.axial))]
      change dist (horizontalContact a b p) (verticalContact c d q) ^ 2 = _ at hdist
      nlinarith [show 0 ≤ dist (horizontalContact a b p) (verticalContact c d q) from dist_nonneg]
    · have hy := contact_interval_lattice_distance (q.off_axis_lower hq)
        (show q.axial ≤ 17 - (11 / 4 : ℝ) by linarith [q.off_axis_upper hq]) (b - d)
      push_cast at hy
      have htriangle := abs_add_le (q.axial - 17 * ((b : ℝ) - d) - p.transverse) p.transverse
      have htrans : |p.transverse| ≤ 4 / 3 := by
        rw [abs_of_nonneg p.transverse_lower]
        exact p.transverse_upper
      have hcoordinate := contactPoint_coordinate_le_dist
        (horizontalContact a b p) (verticalContact c d q) 1
      change |17 * (b : ℝ) + p.transverse - (17 * d + q.axial)| ≤ _ at hcoordinate
      have hneg : q.axial - 17 * ((b : ℝ) - d) - p.transverse =
          -(17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) := by ring
      rw [hneg, abs_neg] at htriangle
      have hsum : -(17 * (b : ℝ) + p.transverse - (17 * d + q.axial)) + p.transverse =
          q.axial - 17 * ((b : ℝ) - d) := by ring
      rw [hsum] at htriangle
      linarith
  · have hx := contact_interval_lattice_distance (p.off_axis_lower hp)
      (show p.axial ≤ 17 - (11 / 4 : ℝ) by linarith [p.off_axis_upper hp]) (c - a)
    push_cast at hx
    have htriangle := abs_sub_le (p.axial - 17 * ((c : ℝ) - a) + q.transverse) (0 : ℝ) q.transverse
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    have htrans : |q.transverse| ≤ 4 / 3 := by
      rw [abs_of_nonneg q.transverse_lower]
      exact q.transverse_upper
    have hcoordinate := contactPoint_coordinate_le_dist
      (horizontalContact a b p) (verticalContact c d q) 0
    change |17 * (a : ℝ) + p.axial - (17 * c - q.transverse)| ≤ _ at hcoordinate
    have hdiff : p.axial - 17 * ((c : ℝ) - a) + q.transverse - q.transverse =
        p.axial - 17 * ((c : ℝ) - a) := by ring
    rw [hdiff] at htriangle
    have hsum : p.axial - 17 * ((c : ℝ) - a) + q.transverse =
        17 * (a : ℝ) + p.axial - (17 * c - q.transverse) := by ring
    rw [hsum] at htriangle
    linarith

/-- Internal points from distinct collinear length-17 intervals are at least
2 apart in their axial projection. -/
theorem contact_interval_separation (a c : ℤ) (hne : a ≠ c) {x y : ℝ}
    (hx : 1 ≤ x) (hx' : x ≤ 16) (hy : 1 ≤ y) (hy' : y ≤ 16) :
    2 ≤ |17 * (a : ℝ) + x - (17 * c + y)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (a : ℝ) + 1 ≤ c := by exact_mod_cast (show a + 1 ≤ c by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (c : ℝ) + 1 ≤ a := by exact_mod_cast (show c + 1 ≤ a by omega)
    exact (le_abs_self _).trans' (by linarith)

theorem contact_parallel_line_separation (b d : ℤ) (hne : b ≠ d) {x y : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 4 / 3) (hy : 0 ≤ y) (hy' : y ≤ 4 / 3) :
    47 / 3 ≤ |17 * (b : ℝ) + x - (17 * d + y)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (b : ℝ) + 1 ≤ d := by exact_mod_cast (show b + 1 ≤ d by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (d : ℝ) + 1 ≤ b := by exact_mod_cast (show d + 1 ≤ b by omega)
    exact (le_abs_self _).trans' (by linarith)

/-- Parallel gadgets from distinct oriented lattice edges do not interfere. -/
theorem horizontalContact_separation (a b c d : ℤ)
    (hne : (a, b) ≠ (c, d)) (p q : ContactStripSite) :
    7 / 5 < dist (horizontalContact a b p) (horizontalContact c d q) := by
  by_cases hb : b = d
  · have ha : a ≠ c := by intro ha; exact hne (Prod.ext ha hb)
    have h := contact_interval_separation a c ha p.axial_lower p.axial_upper q.axial_lower q.axial_upper
    have hdist := contactPoint_coordinate_le_dist (horizontalContact a b p) (horizontalContact c d q) 0
    change |17 * (a : ℝ) + p.axial - (17 * c + q.axial)| ≤ _ at hdist
    linarith
  · have h := contact_parallel_line_separation b d hb p.transverse_lower p.transverse_upper
      q.transverse_lower q.transverse_upper
    have hdist := contactPoint_coordinate_le_dist (horizontalContact a b p) (horizontalContact c d q) 1
    change |17 * (b : ℝ) + p.transverse - (17 * d + q.transverse)| ≤ _ at hdist
    linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactBaseSeparation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact nineteen-link base gadget and all of its nonlink separations. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPath_second_axial_lower {c : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    {k : ℕ} (hk : 2 ≤ k) : 2 ≤ contactPathVertex c k 0 := by
  have h := contactPath_horizontal_lower (by linarith : c ≤ 1) hk
  have h2 : contactPathVertex c 2 0 = 2 := by
    norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ, contactStepX]
  rw [h2] at h
  have hn : 0 ≤ c * (k - 2 : ℕ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  linarith

theorem contact_axial_separation (p q : ContactPoint) {margin : ℝ}
    (h : margin ≤ p 0 - q 0) : margin ≤ dist p q :=
  h.trans ((le_abs_self _).trans (contactPoint_coordinate_le_dist p q 0))

theorem contactBase_left_left_separation (negative : Bool) (i j : Fin 10)
    (hne : i ≠ j) (hlink : Nat.dist i.val j.val ≠ 1) :
    7 / 5 ≤ dist (contactPathVertex (contactGadgetSlope negative) i.val)
      (contactPathVertex (contactGadgetSlope negative) j.val) := by
  have hs := contactGadgetSlope_bounds negative
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt h)] at hlink
    rw [dist_comm]
    exact (by norm_num : (7 / 5 : ℝ) ≤ 3 / 2).trans
      (contactPath_nonlink_separation hs.1 (by linarith [hs.2]) (by omega))
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.le_of_lt h)] at hlink
    exact (by norm_num : (7 / 5 : ℝ) ≤ 3 / 2).trans
      (contactPath_nonlink_separation hs.1 (by linarith [hs.2]) (by omega))

theorem contactBase_left_right_separation (negative : Bool) (i : Fin 10) (j : Fin 9)
    (hlink : ¬(negative = true ∧ i = 9 ∧ j = 0)) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative (Sum.inl i))
      (contactBaseGadgetPosition negative (Sum.inr (Sum.inl j))) := by
  have hs := contactGadgetSlope_bounds negative
  have hr := (leftContactStripSite (contactGadgetSlope negative) hs.1 hs.2
    (j.val + 1) (by omega) (by have := j.isLt; omega)).axial_lower
  change 1 ≤ contactPathVertex (contactGadgetSlope negative) (j.val + 1) 0 at hr
  have hl := (contactPath_axial_bounds hs.1 hs.2 (show i.val ≤ 9 by have := i.isLt; omega)).2
  rw [dist_comm]
  apply contact_axial_separation
  change 7 / 5 ≤ contactGadgetRightOrigin negative 1 +
    contactPathVertex (contactGadgetSlope negative) (j.val + 1) 0 -
      contactPathVertex (contactGadgetSlope negative) i.val 0
  cases negative
  · norm_num [contactGadgetRightOrigin, contactGadgetSlope] at *
    linarith
  · by_cases hi : i = 9
    · have hj : j ≠ 0 := fun hj => hlink ⟨rfl, hi, hj⟩
      have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
      subst i
      change 7 / 5 ≤ 17 / 2 + contactPathVertex (7 / 8) (j.val + 1) 0 - contactPathVertex (7 / 8) 9 0
      rw [contactPathVertex_end, contactPoint_zero]
      norm_num [contactGadgetSlope] at hsecond ⊢
      linarith
    · have hi8 : i.val ≤ 8 := by
        have hv : i.val ≠ 9 := fun h => hi (Fin.ext h)
        have := i.isLt
        omega
      by_cases hi0 : i.val = 0
      · have hx : contactPathVertex (7 / 8) i.val 0 = 0 := by rw [hi0]; simp [contactPathVertex]
        norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hr ⊢
        rw [hx]
        linarith
      · have hlast := (contactPath_internal_axial_bounds hs.1 hs.2 (show 1 ≤ i.val by omega) hi8).2
        norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hr hlast ⊢
        linarith

theorem contactBase_side_left_separation (negative : Bool) (i : Fin 10) (hi : i ≠ 9) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative contactGadgetSide)
      (contactBaseGadgetPosition negative (Sum.inl i)) := by
  have hs := contactGadgetSlope_bounds negative
  have hi8 : i.val ≤ 8 := by
    have hv : i.val ≠ 9 := fun h => hi (Fin.ext h)
    have := i.isLt
    omega
  cases negative
  · apply contact_axial_separation
    change 7 / 5 ≤ 9 - contactPathVertex (3 / 4) i.val 0
    by_cases hi0 : i.val = 0
    · rw [hi0]
      norm_num [contactPathVertex]
    · have hlast := (contactPath_internal_axial_bounds hs.1 hs.2 (show 1 ≤ i.val by omega) hi8).2
      norm_num [contactGadgetSlope] at hlast
      linarith
  · by_cases hi' : i.val = 8
    · have hx : contactPathVertex (7 / 8) i.val = contactPoint (15 / 2) 0 := by
        rw [hi']
        ext k
        fin_cases k <;> norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ,
          contactStepX, contactStepY]
      change 7 / 5 ≤ dist (contactPoint (17 / 2) 1) (contactPathVertex (7 / 8) i.val)
      rw [hx]
      have hd := contactPoint_dist_sq (17 / 2) 1 (15 / 2) 0
      norm_num at hd
      nlinarith [show 0 ≤ dist (contactPoint (17 / 2) 1) (contactPoint (15 / 2) 0) from dist_nonneg]
    · have hproj := contactPath_horizontal_lower (c := (7 / 8 : ℝ)) (by norm_num)
        (show i.val ≤ 9 by omega)
      rw [contactPathVertex_end, contactPoint_zero] at hproj
      have hcount : (2 : ℝ) ≤ (9 - i.val : ℕ) := by exact_mod_cast (show 2 ≤ 9 - i.val by omega)
      apply contact_axial_separation
      change 7 / 5 ≤ 17 / 2 - contactPathVertex (7 / 8) i.val 0
      norm_num at hproj
      nlinarith

theorem contactBase_side_right_separation (negative : Bool) (j : Fin 9)
    (hlink : ¬(negative = false ∧ j = 0)) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative contactGadgetSide)
      (contactBaseGadgetPosition negative (Sum.inr (Sum.inl j))) := by
  have hs := contactGadgetSlope_bounds negative
  cases negative
  · have hj : j ≠ 0 := fun h => hlink ⟨rfl, h⟩
    have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
    rw [dist_comm]
    apply contact_axial_separation
    change 7 / 5 ≤ (contactGadgetRightOrigin false 1 + contactPathVertex (3 / 4) (j.val + 1) 0) - 9
    norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hsecond ⊢
    linarith
  · by_cases hj : j = 0
    · subst j
      have hx : contactPoint (17 / 2) 0 + contactPathVertex (7 / 8) 1 = contactPoint (19 / 2) 0 := by
        ext k
        fin_cases k <;> norm_num [contactPathVertex, contactPoint, Finset.sum_range_succ,
          contactStepX, contactStepY, PiLp.add_apply]
      change 7 / 5 ≤ dist (contactPoint (17 / 2) 1)
        (contactPoint (17 / 2) 0 + contactPathVertex (7 / 8) 1)
      rw [hx]
      have hd := contactPoint_dist_sq (17 / 2) 1 (19 / 2) 0
      norm_num at hd
      nlinarith [show 0 ≤ dist (contactPoint (17 / 2) 1) (contactPoint (19 / 2) 0) from dist_nonneg]
    · have hv : j.val ≠ 0 := fun h => hj (Fin.ext h)
      have hsecond := contactPath_second_axial_lower hs.1 hs.2 (show 2 ≤ j.val + 1 by omega)
      rw [dist_comm]
      apply contact_axial_separation
      change 7 / 5 ≤ (contactGadgetRightOrigin true 1 + contactPathVertex (7 / 8) (j.val + 1) 0) - 17 / 2
      norm_num [contactGadgetRightOrigin, contactGadgetSlope] at hsecond ⊢
      linarith

/-- Every distinct nonlinked pair in either actual base gadget is at
least1.4 apart, including the negative-sign side site. -/
theorem contactBaseGadget_nonlink_separation (negative : Bool) (x y : ContactGadgetSite)
    (hne : x ≠ y) (hlink : ¬ contactGadgetLinked negative x y) :
    7 / 5 ≤ dist (contactBaseGadgetPosition negative x) (contactBaseGadgetPosition negative y) := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩)
  · exact contactBase_left_left_separation negative i j (fun h => hne (congrArg Sum.inl h)) hlink
  · exact contactBase_left_right_separation negative i j hlink
  · rw [dist_comm]
    exact contactBase_side_left_separation negative i hlink
  · rw [dist_comm]
    exact contactBase_left_right_separation negative j i hlink
  · change 7 / 5 ≤ dist (contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (j.val + 1))
    rw [dist_add_left]
    have hi10 : i.val + 1 < 10 := by have := i.isLt; omega
    have hj10 : j.val + 1 < 10 := by have := j.isLt; omega
    apply contactBase_left_left_separation negative ⟨i.val + 1, hi10⟩ ⟨j.val + 1, hj10⟩
    · intro h
      have hv := congrArg Fin.val h
      have hij : i = j := Fin.ext (by simpa using hv)
      exact hne (congrArg (fun k : Fin 9 => (Sum.inr (Sum.inl k) : ContactGadgetSite)) hij)
    · change Nat.dist (i.val + 1) (j.val + 1) ≠ 1
      simpa only [Nat.dist_add_add_right, contactGadgetLinked] using hlink
  · rw [dist_comm]
    exact contactBase_side_right_separation negative i hlink
  · exact contactBase_side_left_separation negative j hlink
  · exact contactBase_side_right_separation negative j hlink
  · exact False.elim (hne rfl)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGadgetStability
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed nineteen-link gadgets retain the nonlink separation of the
base shapes. All estimates concern the actual coordinate constructions. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_axis_dist (x x' : ℝ) :
    dist (contactPoint x 0) (contactPoint x' 0) = |x - x'| := by
  have h := contactPoint_dist_sq x 0 x' 0
  nlinarith [sq_abs (x - x'), abs_nonneg (x - x'),
    show 0 ≤ dist (contactPoint x 0) (contactPoint x' 0) from dist_nonneg]

theorem contactPoint_vertical_dist (x y y' : ℝ) :
    dist (contactPoint x y) (contactPoint x y') = |y - y'| := by
  have h := contactPoint_dist_sq x y x y'
  nlinarith [sq_abs (y - y'), abs_nonneg (y - y'),
    show 0 ≤ dist (contactPoint x y) (contactPoint x y') from dist_nonneg]

theorem contactGadgetOrigin_near (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance) :
    dist (contactPoint (contactGadgetRightOrigin negative central) 0)
      (contactPoint (contactGadgetRightOrigin negative 1) 0) ≤ contactLengthTolerance := by
  rw [contactPoint_axis_dist]
  cases negative
  · apply abs_le.mpr
    simp only [contactGadgetRightOrigin, Bool.false_eq_true, ite_false, if_false]
    constructor <;> linarith
  · norm_num [contactGadgetRightOrigin, contactLengthTolerance]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediator
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAEvenRouteData.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPathEmbedding.nextPosition_old _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_fresh _root_.OAI.ContinuumCoulomb.QMAPortRouteData.crossingPosition_old _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_fresh _root_.OAI.ContinuumCoulomb.QuantumEvenRouteLabels.vertex_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_fresh _root_.OAI.ContinuumCoulomb.qmaSubdivisionCell_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit labels for the eighteen fresh sites of each three-stage
mediator gadget. These identify the actual iterated graph with the
nineteen-link contact geometry, rather than only matching their counts. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorGraph MediatorIteration

theorem localEdge_contactLinked (negative : Bool) (e : LocalEdge) :
    contactGadgetLinked negative
      (localToContact (localLeft (if negative then 0 else 1) e))
      (localToContact (localRight e)) := by
  rcases e with ⟨⟩ | (p | ⟨p, t⟩)
  · cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
  · cases p with
    | inl s => fin_cases s <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
  · cases p with
    | inl s => fin_cases s <;> fin_cases t <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]

theorem spoke_nonneg (r W G : ℕ) (J : ℚ) : 0 ≤ MediatorParameters.spoke r W G J := by
  unfold MediatorParameters.spoke DyadicRootProgram.value
  positivity

theorem member_spoke (r W G : ℕ) (J : ℚ) :
    member (MediatorParameters.spoke r W G J) = 1 := by
  simp only [member, not_lt.mpr (spoke_nonneg r W G J), ite_false, if_false]

theorem member_nat (N : ℕ) : member (N : ℚ) = 1 := by
  simp [member]

theorem member_secondPath {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (p : LocalPath) :
    member ((secondPaths F W G).weight (pathIndex r e p)) = 1 := by
  cases p with
  | inl s =>
    simp [secondPaths, join, secondCentral, central, pathIndex, member_nat]
  | inr st =>
    rcases st with ⟨s, t⟩
    simp [secondPaths, join, secondSpokes, spokes, pathIndex, spokeIndex, member_spoke]

/-- Every left endpoint of the actual three-stage graph has the explicit
local gadget label. This identity retains the original edge index. -/
theorem finalGraph_left {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (a : LocalEdge) :
    (finalGraph F W G).left (encodeEdge r e a) =
      localVertex (F.left e) (F.right e) e (localLeft (member (F.weight e)) a) := by
  rcases a with ⟨⟩ | (p | ⟨p, t⟩)
  · simp [finalGraph, encodeEdge, join, lift, retainedCentral, firstCentral, central,
      localVertex, localLeft, localFirst, siteEquiv, encodeSite]
  · simp [finalGraph, encodeEdge, join, thirdCentral, central,
      localVertex, localLeft, localThird, siteEquiv, encodeSite]
  · cases p with
    | inl s =>
      fin_cases s <;> fin_cases t <;>
        simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, secondPaths, secondCentral,
          central, pathIndex, spokeIndex, localVertex, localLeft, secondEndpoint,
          localSecond, siteEquiv, encodeSite]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;>
        simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, secondPaths, secondSpokes,
          firstSpokes, pathIndex, spokeIndex, member_spoke, localVertex, localLeft,
          secondEndpoint, firstAttachment, localOld, localFirst, localSecond, siteEquiv,
          encodeSite]

/-- The matching right-endpoint identity uses the proved nonnegativity of
the actual rounded spokes, so later subdivisions always use member one. -/
theorem finalGraph_right {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (a : LocalEdge) :
    (finalGraph F W G).right (encodeEdge r e a) =
      localVertex (F.left e) (F.right e) e (localRight a) := by
  rcases a with ⟨⟩ | (p | ⟨p, t⟩)
  · simp [finalGraph, encodeEdge, join, lift, retainedCentral, firstCentral, central,
      localVertex, localRight, localFirst, siteEquiv, encodeSite]
  · simp [finalGraph, encodeEdge, join, thirdCentral, central,
      localVertex, localRight, localThird, siteEquiv, encodeSite]
  · have hm := member_secondPath F W G e p
    fin_cases t <;>
      simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, spokeIndex, hm,
        localVertex, localRight, localThird, siteEquiv, encodeSite]

theorem member_edgeNegative {n r : ℕ} (F : Bonds n r) (e : Fin r) :
    member (F.weight e) = if edgeNegative F e then 0 else 1 := by
  simp [member, edgeNegative]

end ContinuumCoulomb.ContactMediator

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediatorGeometry
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Independent prescribed lengths for the exact nineteen local edges
identified with the actual iterated mediator graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

theorem leftEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
      (G (localToContact (localRight (leftEdge k)))) =
        dist (G (Sum.inl k.succ)) (G (Sum.inl k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [leftEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, dist_comm] <;> first | rfl | exact dist_comm _ _

theorem rightEdge_distance (negative : Bool) (G : ContactGadgetSite → ContactPoint) (k : Fin 9) :
    dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
      (G (localToContact (localRight (rightEdge k)))) =
        dist (G (contactGadgetRightNode negative k.succ))
          (G (contactGadgetRightNode negative k.castSucc)) := by
  fin_cases k <;> cases negative <;>
    simp [rightEdge, localToContact, localLeft, localRight, secondEndpoint, firstAttachment,
      localOld, localFirst, localSecond, localThird, contactGadgetRightNode, contactGadgetSide,
      dist_comm] <;> first | rfl | exact dist_comm _ _

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightBounds
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform direct and inverse moduli for the nine-link height solve. The
four sloping links keep this one-dimensional solve quantitatively regular. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactHeight_interval_bounds {c h : ℝ} (hc : 3 / 4 ≤ c) (hc' : c ≤ 7 / 8)
    (hh : h ∈ Set.Icc (contactHeightLow c) (contactHeightHigh c)) :
    2 / 5 ≤ h ∧ h ≤ 3 / 4 := by
  have hl0 : 0 ≤ contactHeightLow c := Real.sqrt_nonneg _
  have hu0 : 0 ≤ contactHeightHigh c := Real.sqrt_nonneg _
  have hl := contactHeightLow_sq hc hc'
  have hu := contactHeightHigh_sq hc hc'
  constructor
  · nlinarith [hh.1]
  · nlinarith [hh.2]

theorem adjustedContactForward_slope {length h₁ h₂ : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4) :
    (h₂ - h₁) / 5 ≤ adjustedContactForward length h₁ - adjustedContactForward length h₂ ∧
      adjustedContactForward length h₁ - adjustedContactForward length h₂ ≤ 2 * (h₂ - h₁) := by
  have h₁0 : 0 ≤ h₁ := by linarith
  have h₂0 : 0 ≤ h₂ := by linarith
  have h₁U : h₁ ≤ 3 / 4 := hh.trans hh₂
  have h₂L : 2 / 5 ≤ h₂ := hh₁.trans hh
  have hl0 : 0 ≤ length := by linarith
  have hl2lo : (99 / 100 : ℝ) ^ 2 ≤ length ^ 2 := by nlinarith
  have hl2hi : length ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by nlinarith
  have hr₁ : 0 ≤ length ^ 2 - h₁ ^ 2 := by nlinarith
  have hr₂ : 0 ≤ length ^ 2 - h₂ ^ 2 := by nlinarith
  let x₁ := adjustedContactForward length h₁
  let x₂ := adjustedContactForward length h₂
  have hx₁ : 0 ≤ x₁ := Real.sqrt_nonneg _
  have hx₂ : 0 ≤ x₂ := Real.sqrt_nonneg _
  have hx₁sq : x₁ ^ 2 = length ^ 2 - h₁ ^ 2 := Real.sq_sqrt hr₁
  have hx₂sq : x₂ ^ 2 = length ^ 2 - h₂ ^ 2 := Real.sq_sqrt hr₂
  have hx₁lo : 1 / 2 ≤ x₁ := by nlinarith
  have hx₂lo : 1 / 2 ≤ x₂ := by nlinarith
  have hx₁hi : x₁ ≤ 2 := by nlinarith
  have hx₂hi : x₂ ≤ 2 := by nlinarith
  have hxx : x₂ ≤ x₁ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg h₁0 h₂0)]
  have hid : (x₁ - x₂) * (x₁ + x₂) = (h₂ - h₁) * (h₁ + h₂) := by nlinarith
  change (h₂ - h₁) / 5 ≤ x₁ - x₂ ∧ x₁ - x₂ ≤ 2 * (h₂ - h₁)
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ 4 - (x₁ + x₂) by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ h₁ + h₂ - 4 / 5 by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hxx)
      (show 0 ≤ x₁ + x₂ - 1 by linarith),
      mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 2 - (h₁ + h₂) by linarith)]

theorem adjustedContactSpan_broad_slope {h₁ h₂ : ℝ}
    (hh₁ : 2 / 5 ≤ h₁) (hh : h₁ ≤ h₂) (hh₂ : h₂ ≤ 3 / 4)
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    (h₂ - h₁) / 2 ≤ adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ∧
      adjustedContactSpan lengths h₁ - adjustedContactSpan lengths h₂ ≤ 8 * (h₂ - h₁) := by
  have hf (k : ℕ) (hk : k < 9) := adjustedContactForward_slope
    (show 99 / 100 ≤ lengths k by have := hl k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    (show lengths k ≤ 101 / 100 by have := hl' k hk; norm_num [contactLengthTolerance] at this ⊢; linarith)
    hh₁ hh hh₂
  have hf₂ := hf 2 (by norm_num)
  have hf₃ := hf 3 (by norm_num)
  have hf₅ := hf 5 (by norm_num)
  have hf₆ := hf 6 (by norm_num)
  norm_num [adjustedContactSpan, Finset.sum_range_succ, adjustedContactStepX]
  constructor <;> linarith [hf₂.1, hf₂.2, hf₃.1, hf₃.2, hf₅.1, hf₅.2, hf₆.1, hf₆.2]

theorem adjustedContactSpan_broad_inverse_error {h h₀ span : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4))
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance)
    (hroot : adjustedContactSpan lengths h₀ = span) :
    |h - h₀| ≤ 2 * |adjustedContactSpan lengths h - span| := by
  rcases le_total h h₀ with hle | hle
  · have hs := (adjustedContactSpan_broad_slope hh.1 hle hh₀.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : 0 ≤ adjustedContactSpan lengths h - span := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hle), abs_of_nonneg hx]
    linarith
  · have hs := (adjustedContactSpan_broad_slope hh₀.1 hle hh.2 lengths hl hl').1
    rw [hroot] at hs
    have hx : adjustedContactSpan lengths h - span ≤ 0 := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hle), abs_of_nonpos hx]
    linarith

theorem adjustedContactSpan_broad_lipschitz {h h' : ℝ}
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4))
    (lengths : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ lengths k)
    (hl' : ∀ k < 9, lengths k ≤ 1 + contactLengthTolerance) :
    |adjustedContactSpan lengths h - adjustedContactSpan lengths h'| ≤ 8 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh.1 hle hh'.2 lengths hl hl'
    have hs : 0 ≤ adjustedContactSpan lengths h - adjustedContactSpan lengths h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlower, hupper⟩ := adjustedContactSpan_broad_slope hh'.1 hle hh.2 lengths hl hl'
    have hs : adjustedContactSpan lengths h - adjustedContactSpan lengths h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightEvaluation
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational evaluator for the one-dimensional height residual.
There are exactly four dyadic square-root calls; all other terms are exact. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem rootSample_error (e : Environment) (h : ℚ) (k : ℕ)
    (hl : 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(rootSample e h k : ℝ) - adjustedContactForward (lengthAt e k) h| ≤
      (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 := by
  have hlow : (99 / 100 : ℝ) ≤ lengthAt e k := by
    norm_num [contactLengthTolerance] at hl
    linarith
  have hrad : (0 : ℝ) ≤ (lengthAt e k : ℝ) ^ 2 - (h : ℝ) ^ 2 := by
    have hh0 : (0 : ℝ) ≤ h := by linarith [hh.1]
    nlinarith [hh.2]
  have hradQ : (0 : ℚ) ≤ (lengthAt e k) ^ 2 - h ^ 2 := by exact_mod_cast hrad
  have he := RationalSquareRoot.value_error (CalibratedEvaluation.rootPrecision e.1) hradQ
  simpa only [rootSample, adjustedContactForward, Rat.cast_sub, Rat.cast_pow] using he

private theorem four_errors {a b c d E : ℝ}
    (ha : |a| ≤ E) (hb : |b| ≤ E) (hc : |c| ≤ E) (hd : |d| ≤ E) :
    |a + b + c + d| ≤ 4 * E := by
  have h₁ := (abs_add_le a b).trans (add_le_add ha hb)
  have h₂ := (abs_add_le c d).trans (add_le_add hc hd)
  have h := (abs_add_le (a + b) (c + d)).trans (add_le_add h₁ h₂)
  rw [add_assoc (a + b) c d]
  exact h.trans_eq (by ring)

theorem approximation_error (e : Environment) (h : ℚ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hh : (h : ℝ) ∈ Set.Icc (2 / 5) (3 / 4)) :
    |(value e h : ℝ) - residual e h| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have h₂ := rootSample_error e h 2 (hl 2 (by norm_num)) hh
  have h₃ := rootSample_error e h 3 (hl 3 (by norm_num)) hh
  have h₅ := rootSample_error e h 5 (hl 5 (by norm_num)) hh
  have h₆ := rootSample_error e h 6 (hl 6 (by norm_num)) hh
  have heq : (value e h : ℝ) - residual e h =
      ((rootSample e h 2 : ℝ) - adjustedContactForward (lengthAt e 2) h) +
      ((rootSample e h 3 : ℝ) - adjustedContactForward (lengthAt e 3) h) +
      ((rootSample e h 5 : ℝ) - adjustedContactForward (lengthAt e 5) h) +
      ((rootSample e h 6 : ℝ) - adjustedContactForward (lengthAt e 6) h) := by
    norm_num [value, residual, adjustedContactSpan, adjustedContactStepX,
      Finset.sum_range_succ, Rat.cast_add, Rat.cast_sub]
    ring
  rw [heq]
  apply (four_errors h₂ h₃ h₅ h₆).trans
  have hb := mul_le_mul_of_nonneg_left (CalibratedEvaluation.root_budget e.1)
    (show (0 : ℝ) ≤ 4 by norm_num)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [show (e.1 : ℝ) + 1 ≠ 0 by positivity]

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactHeightBisection
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The height search uses fixed rational endpoints, its concrete evaluator,
and a linear unary precision schedule. The reference height is supplied by
the already proved contact intermediate-value theorem. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem bisect_mem (e : Environment) (n : ℕ) :
    (bisect e n : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
  have hm := bisection_value_mem value e (tolerance e) (2 / 5) (3 / 4)
    (by norm_num) n
  have hm' : bisect e n ∈ Set.Icc (2 / 5 : ℚ) (3 / 4) := hm
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.1
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hm'.2

theorem endpoint_signs (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    0 ≤ residual e (2 / 5) ∧ residual e (3 / 4) ≤ 0 := by
  have ha := (adjustedContactSpan_broad_slope (by norm_num) hh₀.1 hh₀.2
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  have hb := (adjustedContactSpan_broad_slope hh₀.1 hh₀.2 (by norm_num)
    (fun k => (lengthAt e k : ℝ)) hl hl').1
  rw [hroot] at ha hb
  constructor <;> unfold residual <;> linarith [hh₀.1, hh₀.2]

theorem bisect_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) (n : ℕ) :
    |residual e (bisect e n)| ≤ 2 * ((e.1 : ℝ) + 1)⁻¹ +
      8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ n) := by
  have heval (q : ℚ) (hq : q ∈ Set.Icc (2 / 5 : ℚ) (3 / 4)) :
      |(value e q : ℝ) - residual e q| ≤ (tolerance e : ℝ) := by
    have hq' : (q : ℝ) ∈ Set.Icc (2 / 5) (3 / 4) := by
      constructor
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.1
      · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hq.2
    simpa only [tolerance, Rat.cast_div, Rat.cast_one, Rat.cast_add,
      Rat.cast_natCast, one_div, Rat.cast_inv] using approximation_error e q hl hq'
  have hLip (r : ℝ) (hr : r ∈ Set.Icc (2 / 5) (3 / 4))
      (s : ℝ) (hs : s ∈ Set.Icc (2 / 5) (3 / 4)) :
      |residual e r - residual e s| ≤ 8 * |r - s| := by
    simpa only [residual, sub_sub_sub_cancel_right] using
      adjustedContactSpan_broad_lipschitz hr hs (fun k => (lengthAt e k : ℝ)) hl hl'
  have ha' : 0 ≤ residual e ((2 / 5 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  have hb' : residual e ((3 / 4 : ℚ) : ℝ) ≤ 0 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hb
  have hLip' (r : ℝ) (hr : r ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ))
      (s : ℝ) (hs : s ∈ Set.Icc ((2 / 5 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ)) :
      |residual e r - residual e s| ≤ 8 * |r - s| :=
    hLip r (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hr)
      s (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hs)
  have he := BisectionProgram.residual value e
    (show 0 ≤ tolerance e by unfold tolerance; positivity)
    (show (2 / 5 : ℚ) ≤ 3 / 4 by norm_num) ha' hb'
    (show (0 : ℝ) ≤ 8 by norm_num) heval hLip' n
  simpa only [bisect, argument, tolerance, Rat.cast_div, Rat.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat, one_div, Rat.cast_inv] using he

theorem scheduled_residual (e : Environment)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (ha : 0 ≤ residual e (2 / 5)) (hb : residual e (3 / 4) ≤ 0) :
    |residual e (scheduledValue e)| ≤ (2 * ((e.1 : ℝ) + 1))⁻¹ := by
  have he := bisect_residual (refinedEnvironment e) hl hl' ha hb (iterations e)
  have he' : |residual e (scheduledValue e)| ≤
      2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ +
        8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) := by
    simpa only [scheduledValue, refinedEnvironment, residual, lengthAt, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using he
  have hS : (0 : ℝ) < (e.1 : ℝ) + 1 := by positivity
  have hn : (iterations e : ℝ) = 64 * ((e.1 : ℝ) + 1) := by
    simp only [iterations, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have hn0 : (0 : ℝ) < iterations e := by rw [hn]; positivity
  have hfirst : 2 * (16 * ((e.1 : ℝ) + 1) + 1)⁻¹ ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 8 * ((e.1 : ℝ) + 1))).mpr
    linarith
  have hsecond : 8 * (((3 / 4 : ℝ) - 2 / 5) / 2 ^ iterations e) ≤
      (8 * ((e.1 : ℝ) + 1))⁻¹ := by
    calc
      _ ≤ 8 * (2 : ℝ)⁻¹ ^ iterations e := by
        rw [div_eq_mul_inv, inv_pow]
        gcongr
        norm_num
      _ ≤ 8 * ((iterations e : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left (CoulombQuadratureSchedule.dyadic_le_inverse _) (by norm_num)
      _ ≤ 8 * (iterations e : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hn0 (by linarith)) (by norm_num)
      _ = (8 * ((e.1 : ℝ) + 1))⁻¹ := by
        rw [hn]
        field_simp [ne_of_gt hS]
        ring
  apply he'.trans ((add_le_add hfirst hsecond).trans _)
  simp only [mul_inv_rev]
  norm_num
  nlinarith [inv_pos.mpr hS]

theorem scheduled_height_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ)) :
    |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹ := by
  have hs := endpoint_signs e h₀ hl hl' hh₀ hroot
  have he := scheduled_residual e hl hl' hs.1 hs.2
  have hi := adjustedContactSpan_broad_inverse_error
    (bisect_mem (refinedEnvironment e) (iterations e)) hh₀
    (fun k => (lengthAt e k : ℝ)) hl hl' hroot
  have h := hi.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * (2 * ((e.1 : ℝ) + 1))⁻¹ := h
    _ = _ := by field_simp

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact vertices approximate the same exact height witness as
the deterministic height solve. This estimate preserves separation margins
when the requested precision is increased. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ContactHeightEvaluation

theorem forward_lipschitz {length h h' : ℝ}
    (hl : 99 / 100 ≤ length) (hl' : length ≤ 101 / 100)
    (hh : h ∈ Set.Icc (2 / 5) (3 / 4)) (hh' : h' ∈ Set.Icc (2 / 5) (3 / 4)) :
    |adjustedContactForward length h - adjustedContactForward length h'| ≤ 2 * |h - h'| := by
  rcases le_total h h' with hle | hle
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh.1 hle hh'.2
    have hs : 0 ≤ adjustedContactForward length h - adjustedContactForward length h' := by linarith
    rw [abs_of_nonneg hs, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · obtain ⟨hlo, hhi⟩ := adjustedContactForward_slope hl hl' hh'.1 hle hh.2
    have hs : adjustedContactForward length h - adjustedContactForward length h' ≤ 0 := by linarith
    rw [abs_of_nonpos hs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith

theorem stepX_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹)
    {k : ℕ} (hk : k < 9) :
    |(stepX e (scheduledValue e) k : ℝ) -
      adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ k| ≤
        3 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hs : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6
  · have hh := bisect_mem (refinedEnvironment e) (iterations e)
    have hlower : (99 / 100 : ℝ) ≤ lengthAt e k := by
      have := hl k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hupper : (lengthAt e k : ℝ) ≤ 101 / 100 := by
      have := hl' k hk
      norm_num [contactLengthTolerance] at this ⊢
      linarith
    have hsample := rootSample_error e (scheduledValue e) k (hl k hk) hh
    have hforward := forward_lipschitz hlower hupper hh hh₀
    have hdyadic : (2 : ℝ)⁻¹ ^ CalibratedEvaluation.rootPrecision e.1 ≤
        ((e.1 : ℝ) + 1)⁻¹ := (CalibratedEvaluation.root_budget e.1).trans (by
      apply inv_anti₀ (by positivity)
      nlinarith [show (0 : ℝ) ≤ e.1 from Nat.cast_nonneg e.1])
    have h := (abs_sub_le (rootSample e (scheduledValue e) k : ℝ)
      (adjustedContactForward (lengthAt e k) (scheduledValue e))
      (adjustedContactForward (lengthAt e k) h₀)).trans
        (add_le_add (hsample.trans hdyadic) (hforward.trans (mul_le_mul_of_nonneg_left he (by norm_num))))
    have h' : |(rootSample e (scheduledValue e) k : ℝ) -
        adjustedContactForward (lengthAt e k) h₀| ≤ 3 * ((e.1 : ℝ) + 1)⁻¹ := by
      calc
        _ ≤ ((e.1 : ℝ) + 1)⁻¹ + 2 * ((e.1 : ℝ) + 1)⁻¹ := h
        _ = _ := by ring
    simpa only [stepX, adjustedContactStepX, ite_eq_left hs] using h'
  · simp only [stepX, adjustedContactStepX, ite_eq_right hs, sub_self, abs_zero]
    positivity

theorem stepY_error (e : Environment) (h₀ : ℝ)
    (he : |(scheduledValue e : ℝ) - h₀| ≤ ((e.1 : ℝ) + 1)⁻¹) (k : ℕ) :
    |(stepY (scheduledValue e) k : ℝ) - adjustedContactStepY h₀ k| ≤
      ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases h₁ : k = 2 ∨ k = 3
  · simpa only [stepY, adjustedContactStepY, ite_eq_left h₁] using he
  · by_cases h₂ : k = 5 ∨ k = 6
    · simpa only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_left h₂,
        Rat.cast_neg, neg_sub_neg, abs_sub_comm] using he
    · simp only [stepY, adjustedContactStepY, ite_eq_right h₁, ite_eq_right h₂, Rat.cast_zero,
        sub_zero, abs_zero]
      positivity

private theorem contactPoint_dist_le_abs (x y x' y' : ℝ) :
    dist (contactPoint x y) (contactPoint x' y') ≤ |x - x'| + |y - y'| := by
  have hsq := contactPoint_dist_sq x y x' y'
  nlinarith [sq_abs (x - x'), sq_abs (y - y'),
    mul_nonneg (abs_nonneg (x - x')) (abs_nonneg (y - y')),
    show 0 ≤ dist (contactPoint x y) (contactPoint x' y') from dist_nonneg,
    abs_nonneg (x - x'), abs_nonneg (y - y')]

theorem vertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (vertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  have he := scheduled_height_error e h₀ hl hl' hh₀ hroot
  have hx : |(∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j| ≤
        (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, 3 * ((e.1 : ℝ) + 1)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact stepX_error e h₀ hl hl' hh₀ he (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
      _ = _ := by simp
  have hy : |(∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ)) -
      ∑ j ∈ Finset.range k, adjustedContactStepY h₀ j| ≤
        (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.range k, ((e.1 : ℝ) + 1)⁻¹ := by
        exact Finset.sum_le_sum (fun j _ => stepY_error e h₀ he j)
      _ = _ := by simp
  have hd := contactPoint_dist_le_abs
    (∑ j ∈ Finset.range k, (stepX e (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, (stepY (scheduledValue e) j : ℝ))
    (∑ j ∈ Finset.range k, adjustedContactStepX (fun j => (lengthAt e j : ℝ)) h₀ j)
    (∑ j ∈ Finset.range k, adjustedContactStepY h₀ j)
  have hk' : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hb : (k : ℝ) * (3 * ((e.1 : ℝ) + 1)⁻¹) + (k : ℝ) * ((e.1 : ℝ) + 1)⁻¹ ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right hk' (inv_nonneg.mpr
      (show (0 : ℝ) ≤ e.1 + 1 by positivity))]
  simpa only [vertexPoint, vertex, adjustedContactVertex, Rat.cast_sum] using
    hd.trans ((add_le_add hx hy).trans hb)

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactClosedCoordinates
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational path keeps both original endpoints exact. Replacing its
last approximate prefix sum by the prescribed span improves its distance
to the exact reference path and does not change the polynomial program. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

theorem closedVertex_start (e : Environment) : closedVertex e 0 = (0, 0) := by
  simp [closedVertex, vertex]

theorem closedVertex_end (e : Environment) : closedVertex e 9 = (e.2.2, 0) := by
  simp [closedVertex]

theorem closedVertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (closedVertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hk9 : k = 9
  · subst k
    rw [adjustedContactVertex_end, hroot]
    simp only [closedVertexPoint, closedVertex_end, Rat.cast_zero, dist_self]
    positivity
  · simpa only [closedVertexPoint, closedVertex, ite_eq_right hk9, vertexPoint] using
      vertex_error e h₀ hl hl' hh₀ hroot hk

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGadget
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete rational twenty-site gadget. The two paths share the same
rational prescribed span; their outer endpoints are exact and their
internal vertices approximate the original independent-length gadget. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGadget
open ContactHeightEvaluation

theorem span_cast (b : Bool) (c : ℚ) :
    (span b c : ℝ) = contactGadgetSpan b c := by
  cases b <;> simp [span, contactGadgetSpan, Rat.cast_div, Rat.cast_sub]

theorem origin_cast (b : Bool) (c : ℚ) :
    (origin b c : ℝ) = contactGadgetRightOrigin b c := by
  cases b <;> simp [origin, contactGadgetRightOrigin, Rat.cast_div, Rat.cast_add]

theorem point_left (x : Input) (k : Fin 10) :
    point x (Sum.inl k) = closedVertexPoint (leftEnvironment x) k.val := rfl

theorem point_right (x : Input) (k : Fin 9) :
    point x (Sum.inr (Sum.inl k)) =
      contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
        closedVertexPoint (rightEnvironment x) (k.val + 1) := by
  ext i
  fin_cases i <;>
    simp [point, position, closedVertexPoint, contactPoint, Rat.cast_add,
      origin_cast, PiLp.add_apply]

theorem point_side (x : Input) :
    point x contactGadgetSide =
      if x.2.1 then contactPoint (17 / 2) x.2.2.1
      else contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 := by
  cases hb : x.2.1 <;>
    simp [point, position, contactGadgetSide, hb, origin_cast, Rat.cast_div]

theorem point_start (x : Input) : point x (Sum.inl 0) = contactPoint 0 0 := by
  rw [point_left]
  simp [closedVertexPoint, closedVertex_start]

theorem point_end (x : Input) :
    point x (contactGadgetRightNode x.2.1 9) = contactPoint 17 0 := by
  have hnode : contactGadgetRightNode x.2.1 9 = Sum.inr (Sum.inl 8) := by
    simp [contactGadgetRightNode]
  rw [hnode, point_right]
  change contactPoint (contactGadgetRightOrigin x.2.1 x.2.2.1) 0 +
    closedVertexPoint (rightEnvironment x) 9 = _
  simp only [closedVertexPoint, closedVertex_end, rightEnvironment, span_cast, Rat.cast_zero]
  cases hb : x.2.1 <;> ext i <;> fin_cases i
  all_goals simp [contactGadgetRightOrigin, contactGadgetSpan, contactPoint, PiLp.add_apply]
  all_goals ring

theorem point_near_reference (x : Input) (hL hR : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance)
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
      (contactHeightHigh (contactGadgetSlope x.2.1)))
    (hLroot : adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1)
    (hRroot : adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1)
    (s : ContactGadgetSite) :
    dist (point x s)
      (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
        36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hL' := contactHeight_interval_bounds hs.1 hs.2 hLmem
  have hR' := contactHeight_interval_bounds hs.1 hs.2 hRmem
  have hLroot' : adjustedContactSpan (leftLengths x) hL =
      ((leftEnvironment x).2.2 : ℝ) := by simpa only [leftEnvironment, span_cast] using hLroot
  have hRroot' : adjustedContactSpan (rightLengths x) hR =
      ((rightEnvironment x).2.2 : ℝ) := by simpa only [rightEnvironment, span_cast] using hRroot
  rcases s with k | (k | u)
  · rw [point_left]
    exact closedVertex_error (leftEnvironment x) hL hl hl' hL' hLroot'
      (by have := k.isLt; omega)
  · rw [point_right]
    change dist (_ + _) (_ + _) ≤ _
    rw [dist_add_left]
    exact closedVertex_error (rightEnvironment x) hR hr hr' hR' hRroot'
      (by have := k.isLt; omega)
  · cases u
    change dist (point x contactGadgetSide) _ ≤ _
    rw [point_side]
    change dist _ (if x.2.1 then _ else _) ≤ _
    rw [dist_self]
    positivity

theorem exists_reference (x : Input)
    (hc : 1 - contactLengthTolerance ≤ (x.2.2.1 : ℝ))
    (hc' : (x.2.2.1 : ℝ) ≤ 1 + contactLengthTolerance)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ leftLengths x k)
    (hl' : ∀ k < 9, leftLengths x k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rightLengths x k)
    (hr' : ∀ k < 9, rightLengths x k ≤ 1 + contactLengthTolerance) :
    ∃ hL hR,
      hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope x.2.1))
        (contactHeightHigh (contactGadgetSlope x.2.1)) ∧
      adjustedContactSpan (leftLengths x) hL = contactGadgetSpan x.2.1 x.2.2.1 ∧
      adjustedContactSpan (rightLengths x) hR = contactGadgetSpan x.2.1 x.2.2.1 ∧
      ∀ s, dist (point x s)
        (contactGadgetPosition x.2.1 x.2.2.1 (leftLengths x) (rightLengths x) hL hR s) ≤
          36 * ((x.1 : ℝ) + 1)⁻¹ := by
  have hs := contactGadgetSlope_bounds x.2.1
  have hspan := contactGadgetSpan_bounds x.2.1 hc hc'
  obtain ⟨hL, hLmem, hLroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (leftLengths x) hl hl' hspan.1 hspan.2
  obtain ⟨hR, hRmem, hRroot⟩ := adjustedContactSpan_exists hs.1 hs.2
    (rightLengths x) hr hr' hspan.1 hspan.2
  exact ⟨hL, hR, hLmem, hRmem, hLroot, hRroot,
    point_near_reference x hL hR hl hl' hr hr' hLmem hRmem hLroot hRroot⟩

theorem reference_near_base (negative : Bool) {central : ℝ}
    (hc : 1 - contactLengthTolerance ≤ central) (hc' : central ≤ 1 + contactLengthTolerance)
    (ll rr : ℕ → ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ ll k)
    (hl' : ∀ k < 9, ll k ≤ 1 + contactLengthTolerance)
    (hr : ∀ k < 9, 1 - contactLengthTolerance ≤ rr k)
    (hr' : ∀ k < 9, rr k ≤ 1 + contactLengthTolerance)
    {hL hR : ℝ}
    (hLmem : hL ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative)))
    (hRmem : hR ∈ Set.Icc (contactHeightLow (contactGadgetSlope negative))
      (contactHeightHigh (contactGadgetSlope negative))) (s : ContactGadgetSite) :
    dist (contactGadgetPosition negative central ll rr hL hR s)
      (contactBaseGadgetPosition negative s) < 9 / 200 := by
  have hs := contactGadgetSlope_bounds negative
  rcases s with k | (k | ⟨⟩)
  · exact (adjustedContactVertex_displacement hs.1 hs.2 hLmem ll hl hl'
      (by have := k.isLt; omega)).trans (by norm_num)
  · have hp := adjustedContactVertex_displacement hs.1 hs.2 hRmem rr hr hr'
      (show k.val + 1 ≤ 9 by have := k.isLt; omega)
    have ho := contactGadgetOrigin_near negative hc hc'
    have hd := dist_add_add_le (contactPoint (contactGadgetRightOrigin negative central) 0)
      (adjustedContactVertex rr hR (k.val + 1))
      (contactPoint (contactGadgetRightOrigin negative 1) 0)
      (contactPathVertex (contactGadgetSlope negative) (k.val + 1))
    change dist (_ + _) (_ + _) < _
    unfold contactLengthTolerance at ho
    linarith
  · cases negative
    · have ho := contactGadgetOrigin_near false hc hc'
      norm_num [contactGadgetRightOrigin, contactLengthTolerance] at ho
      change dist (contactPoint ((17 + central) / 2) 0) (contactPoint 9 0) < _
      linarith
    · change dist (contactPoint (17 / 2) central) (contactPoint (17 / 2) 1) < _
      rw [contactPoint_vertical_dist]
      have habs : |central - 1| ≤ contactLengthTolerance := abs_le.mpr ⟨by linarith, by linarith⟩
      exact habs.trans_lt (by norm_num [contactLengthTolerance])

end ContinuumCoulomb.ContactRationalGadget

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalLocal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational contact coordinates indexed by the actual nineteen local
mediator edges. Every link has a quantitative error and the nonedge margin
survives with a fixed minimum requested precision. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalLocal
open ContactMediator ContactRationalGadget

private theorem length_ofFn (f : Fin 9 → ℚ) (k : ℕ) (hk : k < 9) :
    ((List.ofFn f).drop k).headD 1 = f ⟨k, hk⟩ := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using hk)]
  simp only [List.headD_cons, List.getElem_ofFn]

theorem left_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    leftLengths (input P negative ℓ) k = (ℓ (leftEdge ⟨k, hk⟩) : ℝ) := by
  simp only [leftLengths, ContactHeightEvaluation.lengthAt, leftEnvironment, input]
  rw [length_ofFn _ k hk]

theorem right_length (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (k : ℕ) (hk : k < 9) :
    rightLengths (input P negative ℓ) k = (ℓ (rightEdge ⟨k, hk⟩) : ℝ) := by
  simp only [rightLengths, ContactHeightEvaluation.lengthAt, rightEnvironment, input]
  rw [length_ofFn _ k hk]

private theorem distance_error {x y x' y' : ContactPoint} {E : ℝ}
    (hx : dist x x' ≤ E) (hy : dist y y' ≤ E) :
    |dist x y - dist x' y'| ≤ 2 * E := by
  have h := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at h
  exact h.trans (by linarith)

theorem exists_link_approximation (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance)) :
    point P negative ℓ (localOld 0) = contactPoint 0 0 ∧
      point P negative ℓ (localOld 1) = contactPoint 17 0 ∧
      (∀ a, |dist (point P negative ℓ (localLeft (if negative then 0 else 1) a))
        (point P negative ℓ (localRight a)) - (ℓ a : ℝ)| ≤ 72 * ((P : ℝ) + 1)⁻¹) ∧
      (∀ s, dist (point P negative ℓ s)
        (contactBaseGadgetPosition negative (localToContact s)) <
          36 * ((P : ℝ) + 1)⁻¹ + 9 / 200) := by
  let x := input P negative ℓ
  have hl (k : ℕ) (hk : k < 9) : leftLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show leftLengths x k = _ from left_length P negative ℓ k hk]
    exact hℓ _
  have hr (k : ℕ) (hk : k < 9) : rightLengths x k ∈
      Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance) := by
    rw [show rightLengths x k = _ from right_length P negative ℓ k hk]
    exact hℓ _
  obtain ⟨hL, hR, hLmem, hRmem, hLroot, hRroot, hnear⟩ := ContactRationalGadget.exists_reference x
    (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
    (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
    (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2)
  let G := contactGadgetPosition negative (ℓ (Sum.inl ())) (leftLengths x) (rightLengths x) hL hR
  have hlinks := contactGadget_link_lengths negative (hℓ (Sum.inl ())).1
    (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hr k hk).1)
    hLmem hRmem hLroot
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ContactRationalGadget.point_start x
  · simpa [point, localToContact, localOld, x, input, contactGadgetRightNode] using
      ContactRationalGadget.point_end x
  · intro a
    have he := distance_error (hnear (localToContact (localLeft (if negative then 0 else 1) a)))
      (hnear (localToContact (localRight a)))
    have hexact : dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a))) = (ℓ a : ℝ) := by
      obtain ⟨b, rfl⟩ := contactEdgeEquiv.surjective a
      rcases b with k | (⟨⟩ | k)
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (leftEdge k))))
          (G (localToContact (localRight (leftEdge k)))) = (ℓ (leftEdge k) : ℝ)
        rw [leftEdge_distance]
        exact (hlinks.1 k).trans (left_length P negative ℓ k.val k.isLt)
      · change dist (G (Sum.inl 9)) (G contactGadgetSide) = _
        rw [dist_comm]
        exact hlinks.2.1
      · change dist (G (localToContact (localLeft (if negative then 0 else 1) (rightEdge k))))
          (G (localToContact (localRight (rightEdge k)))) = (ℓ (rightEdge k) : ℝ)
        rw [rightEdge_distance]
        exact (hlinks.2.2 k).trans (right_length P negative ℓ k.val k.isLt)
    change |dist (ContactRationalGadget.point x _)
        (ContactRationalGadget.point x _) -
      dist (G (localToContact (localLeft (if negative then 0 else 1) a)))
        (G (localToContact (localRight a)))| ≤ 2 * (36 * ((P : ℝ) + 1)⁻¹) at he
    change |dist (ContactRationalGadget.point x _) (ContactRationalGadget.point x _) - _| ≤ _
    rw [hexact] at he
    exact he.trans_eq (by ring)
  · intro s
    have hb := ContactRationalGadget.reference_near_base negative (hℓ (Sum.inl ())).1 (hℓ (Sum.inl ())).2
      (leftLengths x) (rightLengths x) (fun k hk => (hl k hk).1) (fun k hk => (hl k hk).2)
      (fun k hk => (hr k hk).1) (fun k hk => (hr k hk).2) hLmem hRmem (localToContact s)
    exact (dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt (hnear _) hb)

theorem nonedge_separation (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hP : 1440 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (s t : LocalSite) (hne : s ≠ t)
    (hnon : ¬contactGadgetLinked negative (localToContact s) (localToContact t)) :
    6 / 5 < dist (point P negative ℓ s) (point P negative ℓ t) := by
  have hnear := (exists_link_approximation P negative ℓ hℓ).2.2.2
  have hsmall : 36 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 40 := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have hPR : (1440 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hs := hnear s
  have ht := hnear t
  have hbase := contactBaseGadget_nonlink_separation negative (localToContact s) (localToContact t)
    (fun h => hne (localContactEquiv.injective h)) hnon
  have h₁ := dist_triangle (contactBaseGadgetPosition negative (localToContact s))
    (point P negative ℓ s) (contactBaseGadgetPosition negative (localToContact t))
  have h₂ := dist_triangle (point P negative ℓ s) (point P negative ℓ t)
    (contactBaseGadgetPosition negative (localToContact t))
  rw [dist_comm] at hs
  linarith

theorem near_base (P : ℕ) (negative : Bool) (ℓ : LocalEdge → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (s : LocalSite) :
    dist (point P negative ℓ s) (contactBaseGadgetPosition negative (localToContact s)) < 1 / 20 := by
  have h := (exists_link_approximation P negative ℓ hℓ).2.2.2 s
  have hsmall : 36 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 200 := by
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have hPR : (7200 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  linarith

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactMediatorLinks
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contact adjacency is exactly the edge relation of the actual
nineteen-link gadget, including the signed central attachment. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

theorem samePair_swap_target {α : Type*} {a b c d : α} (h : samePair a b c d) :
    samePair a b d c := h.symm

theorem samePair_map {α β : Type*} (f : α → β) {a b c d : α}
    (h : samePair a b c d) : samePair (f a) (f b) (f c) (f d) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [samePair]

theorem leftEdge_pair (negative : Bool) (k : Fin 9) :
    contactPair negative (leftEdge k) (Sum.inl k.castSucc) (Sum.inl k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]

theorem rightEdge_pair (negative : Bool) (k : Fin 9) :
    contactPair negative (rightEdge k) (contactGadgetRightNode negative k.castSucc)
      (contactGadgetRightNode negative k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]

private theorem adjacent_indices {n : ℕ} (i j : Fin (n + 1)) (h : Nat.dist i.val j.val = 1) :
    ∃ k : Fin n, (i = k.castSucc ∧ j = k.succ) ∨ (i = k.succ ∧ j = k.castSucc) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Nat.dist at h
  by_cases hij : i.val ≤ j.val
  · refine ⟨⟨i.val, by omega⟩, Or.inl ⟨Fin.ext rfl, Fin.ext (by dsimp; omega)⟩⟩
  · refine ⟨⟨j.val, by omega⟩, Or.inr ⟨Fin.ext (by dsimp; omega), Fin.ext rfl⟩⟩

private theorem left_adjacent_exists (negative : Bool) (i j : Fin 10)
    (h : Nat.dist i.val j.val = 1) :
    ∃ a, contactPair negative a (Sum.inl i) (Sum.inl j) := by
  obtain ⟨k, h | h⟩ := adjacent_indices i j h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨leftEdge k, leftEdge_pair negative k⟩
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨leftEdge k, samePair_swap_target (leftEdge_pair negative k)⟩

private theorem right_nodes (negative : Bool) (k : Fin 8) :
    contactGadgetRightNode negative k.succ.castSucc = Sum.inr (Sum.inl k.castSucc) ∧
    contactGadgetRightNode negative k.succ.succ = Sum.inr (Sum.inl k.succ) := by
  fin_cases k <;> cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]

private theorem right_adjacent_exists (negative : Bool) (i j : Fin 9)
    (h : Nat.dist i.val j.val = 1) :
    ∃ a, contactPair negative a (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) := by
  obtain ⟨k, h | h⟩ := adjacent_indices i j h
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rightEdge k.succ, ?_⟩
    simpa only [contactPair, (right_nodes negative k).1, (right_nodes negative k).2] using
      rightEdge_pair negative k.succ
  · rcases h with ⟨rfl, rfl⟩
    refine ⟨rightEdge k.succ, ?_⟩
    apply samePair_swap_target
    simpa only [contactPair, (right_nodes negative k).1, (right_nodes negative k).2] using
      rightEdge_pair negative k.succ

theorem contactLinked_exists (negative : Bool) (x y : ContactGadgetSite)
    (h : contactGadgetLinked negative x y) : ∃ a, contactPair negative a x y := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩)
  · exact left_adjacent_exists negative i j h
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]⟩
  · change i = 9 at h
    subst i
    refine ⟨Sum.inl (), ?_⟩
    cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]
  · rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]⟩
  · exact right_adjacent_exists negative i j h
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]⟩
  · change j = 9 at h
    subst j
    refine ⟨Sum.inl (), ?_⟩
    cases negative <;> norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨rightEdge 0, by norm_num [contactPair, samePair, localToContact, localLeft, localRight,
      leftEdge, rightEdge, secondEndpoint, firstAttachment, localOld, localFirst,
      localSecond, localThird, contactGadgetRightNode, contactGadgetSide, Fin.ext_iff]⟩
  · exact False.elim h

theorem contactLinked_symm (negative : Bool) {x y : ContactGadgetSite}
    (h : contactGadgetLinked negative x y) : contactGadgetLinked negative y x := by
  rcases x with i | (i | ⟨⟩) <;> rcases y with j | (j | ⟨⟩) <;>
    first | exact h | simpa only [contactGadgetLinked, Nat.dist_comm] using h

theorem contactLinked_iff (negative : Bool) (x y : LocalSite) :
    contactGadgetLinked negative (localToContact x) (localToContact y) ↔
      ∃ a, samePair (localLeft (if negative then 0 else 1) a) (localRight a) x y := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := contactLinked_exists negative (localToContact x) (localToContact y) h
    refine ⟨a, ?_⟩
    rcases ha with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨localContactEquiv.injective hx, localContactEquiv.injective hy⟩
    · exact Or.inr ⟨localContactEquiv.injective hx, localContactEquiv.injective hy⟩
  · rintro ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact localEdge_contactLinked negative a
    · exact contactLinked_symm negative (localEdge_contactLinked negative a)

/-- A contact link is an edge of the actual full graph. Consequently a
nonedge of that graph cannot be an unaccounted local contact. -/
theorem finalGraph_nonedge_contactNonlink {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (x y : LocalSite)
    (h : ¬∃ a, samePair ((finalGraph F W G).left a) ((finalGraph F W G).right a)
      (localVertex (F.left e) (F.right e) e x) (localVertex (F.left e) (F.right e) e y)) :
    ¬contactGadgetLinked (edgeNegative F e) (localToContact x) (localToContact y) := by
  intro hc
  obtain ⟨a, ha⟩ := (contactLinked_iff (edgeNegative F e) x y).mp hc
  rw [← member_edgeNegative F e] at ha
  apply h
  refine ⟨encodeEdge r e a, ?_⟩
  rw [finalGraph_left, finalGraph_right]
  exact samePair_map (localVertex (F.left e) (F.right e) e) ha

end ContinuumCoulomb.ContactMediator

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactLattice
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_end _root_.OAI.ContinuumCoulomb.ContactGridEdge.place_zero _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.contactReflect_strip _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual gadget sites fit the common lattice strips. Together with
ContactStrips, this separates distinct edges without a size-dependent loss. -/

noncomputable section
namespace ContinuumCoulomb

theorem contactPoint_eta (p : ContactPoint) : contactPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl

/-- Every base-gadget site other than the two original vertices belongs to
the uniform internal strip. -/
theorem contactBaseGadget_internal_strip (negative : Bool) (x : ContactGadgetSite)
    (hleft : x ≠ Sum.inl 0) (hright : x ≠ contactGadgetRightNode negative 9) :
    ∃ p : ContactStripSite,
      contactBaseGadgetPosition negative x = contactPoint p.axial p.transverse := by
  have hs := contactGadgetSlope_bounds negative
  rcases x with i | (i | ⟨⟩)
  · have hi : 1 ≤ i.val := by
      have hv : i.val ≠ 0 := fun h => hleft (congrArg Sum.inl (Fin.ext h))
      omega
    let p := leftContactStripSite (contactGadgetSlope negative) hs.1 hs.2 i.val hi
      (show i.val ≤ 9 by have := i.isLt; omega)
    exact ⟨p, (contactPoint_eta (contactPathVertex (contactGadgetSlope negative) i.val)).symm⟩
  · have hi8 : i.val ≠ 8 := by
      intro h
      have hi : i = 8 := Fin.ext h
      subst i
      apply hright
      norm_num [contactGadgetRightNode] <;> (simp; try rfl)
    have hi : i.val + 1 ≤ 8 := by have := i.isLt; omega
    have horigin : contactGadgetRightOrigin negative 1 + (5 + 4 * contactGadgetSlope negative) = 17 := by
      cases negative <;> norm_num [contactGadgetRightOrigin, contactGadgetSlope]
    let p := rightContactStripSite (contactGadgetSlope negative) (contactGadgetRightOrigin negative 1)
      hs.1 hs.2 horigin (i.val + 1) (by omega) hi
    refine ⟨p, ?_⟩
    change contactPoint (contactGadgetRightOrigin negative 1) 0 +
      contactPathVertex (contactGadgetSlope negative) (i.val + 1) =
      contactPoint (contactGadgetRightOrigin negative 1 +
        contactPathVertex (contactGadgetSlope negative) (i.val + 1) 0)
        (contactPathVertex (contactGadgetSlope negative) (i.val + 1) 1)
    ext j
    fin_cases j <;> simp [contactPoint, PiLp.add_apply]
  · cases negative
    · let p : ContactStripSite := {
        axial := 9
        transverse := 0
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro h; exact False.elim (h rfl)
        off_axis_upper := by intro h; exact False.elim (h rfl) }
      exact ⟨p, rfl⟩
    · let p : ContactStripSite := {
        axial := 17 / 2
        transverse := 1
        axial_lower := by norm_num
        axial_upper := by norm_num
        transverse_lower := by norm_num
        transverse_upper := by norm_num
        off_axis_lower := by intro _; norm_num
        off_axis_upper := by intro _; norm_num }
      exact ⟨p, rfl⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_left _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.contactEdge_right _root_.OAI.ContinuumCoulomb.contactGridPoint_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rigid placements of the fixed contact strip on the square lattice.
Reversing an original edge reflects its axial coordinate; this keeps its
internal points in the same canonical strip. -/

noncomputable section
namespace ContinuumCoulomb

private theorem contact_dist_eq_of_sq_eq {p q x y : ContactPoint}
    (h : dist p q ^ 2 = dist x y ^ 2) : dist p q = dist x y := by
  nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := x) (y := y)]

theorem contactReflect_dist (p q : ContactPoint) :
    dist (contactReflect p) (contactReflect q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactReflect, contactReflect, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactHorizontal_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactHorizontal a p) (contactHorizontal a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactHorizontal, contactHorizontal, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem contactVertical_dist (a : ℤ × ℤ) (p q : ContactPoint) :
    dist (contactVertical a p) (contactVertical a q) = dist p q := by
  apply contact_dist_eq_of_sq_eq
  rw [contactVertical, contactVertical, contactPoint_dist_sq, ← contactPoint_eta p,
    ← contactPoint_eta q, contactPoint_dist_sq]
  simp only [contactPoint_zero, contactPoint_one]
  ring

theorem ContactGridEdge.place_dist (e : ContactGridEdge) (p q : ContactPoint) :
    dist (e.place p) (e.place q) = dist p q := by
  cases e with
  | mk vertical anchor reversed =>
    cases vertical <;> cases reversed <;>
      simp [ContactGridEdge.place, contactHorizontal_dist, contactVertical_dist, contactReflect_dist]

/-- The orientation flag does not alter the strip containing an internal site. -/
theorem ContactGridEdge.place_strip (e : ContactGridEdge) (p : ContactStripSite) :
    ∃ q : ContactStripSite, e.place (contactPoint p.axial p.transverse) =
      if e.vertical then verticalContact e.anchor.1 e.anchor.2 q
      else horizontalContact e.anchor.1 e.anchor.2 q := by
  refine ⟨if e.reversed then p.reflect else p, ?_⟩
  cases h : e.reversed <;> cases v : e.vertical <;>
    simp [ContactGridEdge.place, h, v, contactReflect, contactHorizontal, contactVertical,
      horizontalContact, verticalContact, ContactStripSite.reflect]

/-- Vertical parallel strips have the same separation as horizontal ones. -/
theorem verticalContact_separation (a b c d : ℤ)
    (hne : (a, b) ≠ (c, d)) (p q : ContactStripSite) :
    7 / 5 < dist (verticalContact a b p) (verticalContact c d q) := by
  have hk : (b, -a) ≠ (d, -c) := by
    intro h
    apply hne
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by omega) h₁
  have hs := horizontalContact_separation b (-a) d (-c) hk p q
  have hd : dist (verticalContact a b p) (verticalContact c d q) =
      dist (horizontalContact b (-a) p) (horizontalContact d (-c) q) := by
    apply contact_dist_eq_of_sq_eq
    simp only [verticalContact, horizontalContact, contactPoint_dist_sq, Int.cast_neg]
    ring
  rw [hd]
  exact hs

theorem ContactGridEdge.distinct_strip_separation (e f : ContactGridEdge)
    (hne : e.key ≠ f.key) (p q : ContactStripSite) :
    7 / 5 < dist (e.place (contactPoint p.axial p.transverse))
      (f.place (contactPoint q.axial q.transverse)) := by
  obtain ⟨p', hp⟩ := e.place_strip p
  obtain ⟨q', hq⟩ := f.place_strip q
  rw [hp, hq]
  cases he : e.vertical <;> cases hf : f.vertical <;> simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
  · apply horizontalContact_separation _ _ _ _ _ p' q'
    intro h
    exact hne (by simp [ContactGridEdge.key, he, hf, Prod.ext_iff] at h ⊢; exact h)
  · exact perpendicularContact_separation _ _ _ _ p' q'
  · rw [dist_comm]
    exact perpendicularContact_separation _ _ _ _ q' p'
  · apply verticalContact_separation _ _ _ _ _ p' q'
    intro h
    exact hne (by simp [ContactGridEdge.key, he, hf, Prod.ext_iff] at h ⊢; exact h)

/-- Perturbed internal nodes of distinct original edges remain noncontacts. -/
theorem ContactGridEdge.distinct_perturbed_separation (e f : ContactGridEdge)
    (hne : e.key ≠ f.key) (p q : ContactStripSite) (x y : ContactPoint)
    (hx : dist (e.place (contactPoint p.axial p.transverse)) x ≤ 1 / 20)
    (hy : dist (f.place (contactPoint q.axial q.transverse)) y ≤ 1 / 20) :
    6 / 5 < dist x y :=
  contact_separation_stable _ _ _ _ (e.distinct_strip_separation f hne p q).le hx hy

private theorem int_abs_difference_one {a b : ℤ} (h : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne h with h | h
  · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    exact (neg_le_abs _).trans' (by linarith)
  · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    exact (le_abs_self _).trans' (by linarith)

theorem contactGridPoint_separation {a b : ℤ × ℤ} (hne : a ≠ b) :
    17 ≤ dist (contactGridPoint a) (contactGridPoint b) := by
  by_cases h₀ : a.1 = b.1
  · have h₁ : a.2 ≠ b.2 := fun h => hne (Prod.ext h₀ h)
    have ha := int_abs_difference_one h₁
    have hd := contactPoint_coordinate_le_dist (contactGridPoint a) (contactGridPoint b) 1
    change |17 * (a.2 : ℝ) - 17 * b.2| ≤ _ at hd
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)] at hd
    linarith
  · have ha := int_abs_difference_one h₀
    have hd := contactPoint_coordinate_le_dist (contactGridPoint a) (contactGridPoint b) 0
    change |17 * (a.1 : ℝ) - 17 * b.1| ≤ _ at hd
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 17)] at hd
    linarith

/-- A lattice vertex outside the two endpoints is far from the entire
horizontal internal strip, before any adjustment. -/
theorem horizontalContact_external_vertex (a c : ℤ × ℤ) (p : ContactStripSite)
    (h₀ : c ≠ a) (h₁ : c ≠ (a.1 + 1, a.2)) :
    7 / 5 < dist (horizontalContact a.1 a.2 p) (contactGridPoint c) := by
  by_cases hb : c.2 = a.2
  · have hc₀ : c.1 ≠ a.1 := fun h => h₀ (Prod.ext h hb)
    have hc₁ : c.1 ≠ a.1 + 1 := fun h => h₁ (Prod.ext h hb)
    have hd := contactPoint_coordinate_le_dist
      (horizontalContact a.1 a.2 p) (contactGridPoint c) 0
    change |17 * (a.1 : ℝ) + p.axial - 17 * c.1| ≤ _ at hd
    have hc : c.1 ≤ a.1 - 1 ∨ a.1 + 2 ≤ c.1 := by omega
    rcases hc with hc | hc
    · have hc' : (c.1 : ℝ) ≤ a.1 - 1 := by exact_mod_cast hc
      have hp := p.axial_lower
      have hx := le_abs_self (17 * (a.1 : ℝ) + p.axial - 17 * c.1)
      linarith
    · have hc' : (a.1 : ℝ) + 2 ≤ c.1 := by exact_mod_cast hc
      have hp := p.axial_upper
      have hx := neg_le_abs (17 * (a.1 : ℝ) + p.axial - 17 * c.1)
      linarith
  · have hd := contactPoint_coordinate_le_dist
      (horizontalContact a.1 a.2 p) (contactGridPoint c) 1
    change |17 * (a.2 : ℝ) + p.transverse - 17 * c.2| ≤ _ at hd
    have hsep := contact_parallel_line_separation a.2 c.2 (Ne.symm hb)
      p.transverse_lower p.transverse_upper (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 4 / 3 by norm_num)
    simp only [add_zero] at hsep
    linarith

theorem verticalContact_external_vertex (a c : ℤ × ℤ) (p : ContactStripSite)
    (h₀ : c ≠ a) (h₁ : c ≠ (a.1, a.2 + 1)) :
    7 / 5 < dist (verticalContact a.1 a.2 p) (contactGridPoint c) := by
  have hc₀ : (c.2, -c.1) ≠ (a.2, -a.1) := by
    intro h
    apply h₀
    exact Prod.ext (by have := congrArg Prod.snd h; dsimp at this; omega)
      (congrArg Prod.fst h)
  have hc₁ : (c.2, -c.1) ≠ (a.2 + 1, -a.1) := by
    intro h
    apply h₁
    exact Prod.ext (by have := congrArg Prod.snd h; dsimp at this; omega)
      (congrArg Prod.fst h)
  have hs := horizontalContact_external_vertex (a.2, -a.1) (c.2, -c.1) p hc₀ hc₁
  have hd : dist (verticalContact a.1 a.2 p) (contactGridPoint c) =
      dist (horizontalContact a.2 (-a.1) p) (contactGridPoint (c.2, -c.1)) := by
    apply contact_dist_eq_of_sq_eq
    simp only [verticalContact, horizontalContact, contactGridPoint, contactPoint_dist_sq,
      Int.cast_neg]
    ring
  rw [hd]
  exact hs

theorem ContactGridEdge.external_vertex_separation (e : ContactGridEdge)
    (c : ℤ × ℤ) (hc₀ : c ≠ e.left) (hc₁ : c ≠ e.right) (p : ContactStripSite) :
    7 / 5 < dist (e.place (contactPoint p.axial p.transverse)) (contactGridPoint c) := by
  have ha : c ≠ e.anchor := by
    cases h : e.reversed
    · simpa [ContactGridEdge.left, h] using hc₀
    · simpa [ContactGridEdge.right, h] using hc₁
  have hu : c ≠ e.upper := by
    cases h : e.reversed
    · simpa [ContactGridEdge.right, h] using hc₁
    · simpa [ContactGridEdge.left, h] using hc₀
  obtain ⟨q, hq⟩ := e.place_strip p
  rw [hq]
  cases h : e.vertical
  · simp only [Bool.false_eq_true, ite_false, if_false]
    exact horizontalContact_external_vertex e.anchor c q ha
      (by simpa [ContactGridEdge.upper, h] using hu)
  · simp only [ite_true, if_true]
    exact verticalContact_external_vertex e.anchor c q ha
      (by simpa [ContactGridEdge.upper, h] using hu)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactSourceGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every edge of the actual signed square-lattice source has a canonical
geometric strip, and the source's simple-edge promise makes these strips
pairwise distinct. -/

noncomputable section
namespace ContinuumCoulomb

theorem ContactGridEdge.same_key_endpoints {e f : ContactGridEdge} (h : e.key = f.key) :
    (e.left = f.left ∧ e.right = f.right) ∨
      (e.left = f.right ∧ e.right = f.left) := by
  have hv : e.vertical = f.vertical := congrArg Prod.fst h
  have ha : e.anchor = f.anchor := congrArg Prod.snd h
  have hu : e.upper = f.upper := by simp only [ContactGridEdge.upper, hv, ha]
  cases he : e.reversed <;> cases hf : f.reversed <;>
    simp [ContactGridEdge.left, ContactGridEdge.right, he, hf, ha, hu]

/-- Distinct source edges cannot share a canonical strip, even when their
listed orientations are opposite. -/
theorem SquareLatticeHeisenberg.contactEdge_key_injective (F : SquareLatticeHeisenberg) :
    Function.Injective (fun e => (F.contactEdge e).key) := by
  intro e f h
  by_contra hne
  have hs := F.edge_simple e f hne
  rcases ContactGridEdge.same_key_endpoints h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · apply hs.1
    exact ⟨F.coordinate_injective (by simpa using hl),
      F.coordinate_injective (by simpa using hr)⟩
  · apply hs.2
    exact ⟨F.coordinate_injective (by simpa using hl),
      F.coordinate_injective (by simpa using hr)⟩

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_internal _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_one _root_.OAI.ContinuumCoulomb.ContactMediator.localVertex_old_zero _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.contactGridPoint_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing the independently adjusted nineteen-link gadgets along the
actual original lattice vertices. All fresh sites retain their source-edge
label under the explicit final-graph permutation. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

/-- Anchoring a local gadget at zero and seventeen makes its two old
vertices agree with the unique global positions of the original spins. -/
theorem globalPosition_local (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (e : Fin d.edges) (x : LocalSite) :
    globalPosition d P (localVertex (d.left e) (d.right e) e x) =
      (d.contactEdge e).place (P e x) := by
  cases x with
  | inl s =>
    fin_cases s
    · change globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl (d.left e))) =
        (d.contactEdge e).place (P e (localOld 0))
      rw [globalPosition_old, h₀ e, ContactGridEdge.place_zero, d.contactEdge_left]
    · change globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl (d.right e))) =
        (d.contactEdge e).place (P e (localOld 1))
      rw [globalPosition_old, h₁ e, ContactGridEdge.place_end, d.contactEdge_right]
  | inr u => simp [localVertex]

/-- The independent local adjustments stay close to points in the exact
canonical strip belonging to their original source edge. -/
theorem globalPosition_internal_near_strip (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (e : Fin d.edges) (u : LocalInternal) :
    ∃ p : ContactStripSite, dist ((d.contactEdge e).place
      (contactPoint p.axial p.transverse))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u)))) < 1 / 20 := by
  have hleft : localToContact (Sum.inr u) ≠ Sum.inl 0 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    simp only [contactToLocal, Matrix.cons_val_zero, localOld, reduceCtorEq] at heq
  have hright : localToContact (Sum.inr u) ≠
      contactGadgetRightNode (edgeNegative d.bonds e) 9 := by
    intro h
    have heq := congrArg contactToLocal h
    rw [contact_local_inverse] at heq
    cases hn : edgeNegative d.bonds e <;>
      simp [contactToLocal, contactGadgetRightNode, localOld] at heq
  obtain ⟨p, hp⟩ := contactBaseGadget_internal_strip (edgeNegative d.bonds e)
    (localToContact (Sum.inr u)) hleft hright
  refine ⟨p, ?_⟩
  rw [globalPosition_internal, ContactGridEdge.place_dist, ← hp, dist_comm]
  exact hP e (Sum.inr u)

/-- All fresh sites belonging to distinct original edges have the fixed
nonedge margin, uniformly in the size of the original lattice graph. -/
theorem globalPosition_distinct_gadgets (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (e f : Fin d.edges) (hef : e ≠ f) (u v : LocalInternal) :
    6 / 5 < dist (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (f, v)))) := by
  obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
  obtain ⟨q, hq⟩ := globalPosition_internal_near_strip d P hP f v
  exact ContactGridEdge.distinct_perturbed_separation (d.contactEdge e) (d.contactEdge f)
    (fun h => hef (d.contactEdge_key_injective h)) p q _ _ hp.le hq.le

/-- A nonincident original spin is separated from every fresh site of a
gadget, including after its independent contact-length adjustment. -/
theorem globalPosition_nonincident (d : SquareLatticeHeisenberg)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (i : Fin d.vertices) (e : Fin d.edges) (hi₀ : i ≠ d.left e) (hi₁ : i ≠ d.right e)
    (u : LocalInternal) :
    6 / 5 < dist (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
      (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inl i))) := by
  obtain ⟨p, hp⟩ := globalPosition_internal_near_strip d P hP e u
  have hs := ContactGridEdge.external_vertex_separation (d.contactEdge e) (d.coordinate i)
    (by simpa using fun h => hi₀ (d.coordinate_injective h))
    (by simpa using fun h => hi₁ (d.coordinate_injective h)) p
  rw [globalPosition_old]
  have ht := dist_triangle ((d.contactEdge e).place (contactPoint p.axial p.transverse))
    (globalPosition d P (siteEquiv d.vertices d.edges (Sum.inr (e, u))))
    (contactGridPoint (d.coordinate i))
  linarith

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGlobalSeparation
attribute [-simp] _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.ContinuumCoulomb.contactGridPoint_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform all-site and nonedge separation for the actual final graph. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator
open MediatorIteration

theorem globalPosition_local_nonedge (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (hsep : ∀ e x y, x ≠ y → Nonedge d W G
      (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y) → 6 / 5 < dist (P e x) (P e y))
    (e : Fin d.edges) (x y : LocalSite) (hne : x ≠ y)
    (hn : Nonedge d W G (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y)) :
    6 / 5 < dist (globalPosition d P (localVertex (d.left e) (d.right e) e x))
      (globalPosition d P (localVertex (d.left e) (d.right e) e y)) := by
  rw [globalPosition_local d P h₀ h₁, globalPosition_local d P h₀ h₁,
    ContactGridEdge.place_dist]
  exact hsep e x y hne hn

/-- Combining the local nonedge theorem with distinct-strip and external
vertex estimates gives the fixed margin on every nonedge of finalGraph. -/
theorem globalPosition_nonedge (d : SquareLatticeHeisenberg) (W G : ℕ)
    (P : Fin d.edges → LocalSite → ContactPoint)
    (h₀ : ∀ e, P e (localOld 0) = contactPoint 0 0)
    (h₁ : ∀ e, P e (localOld 1) = contactPoint 17 0)
    (hsep : ∀ e x y, x ≠ y → Nonedge d W G
      (localVertex (d.left e) (d.right e) e x)
      (localVertex (d.left e) (d.right e) e y) → 6 / 5 < dist (P e x) (P e y))
    (hP : ∀ e x, dist (P e x)
      (contactBaseGadgetPosition (edgeNegative d.bonds e) (localToContact x)) < 1 / 20)
    (x y : GlobalSite d) (hne : x ≠ y) (hn : Nonedge d W G x y) :
    6 / 5 < dist (globalPosition d P x) (globalPosition d P y) := by
  obtain ⟨x, rfl⟩ := (siteEquiv d.vertices d.edges).surjective x
  obtain ⟨y, rfl⟩ := (siteEquiv d.vertices d.edges).surjective y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : i ≠ j := fun h => hne (by subst j; rfl)
      simpa only [globalPosition_old] using
        lt_of_lt_of_le (by norm_num : (6 / 5 : ℝ) < 17)
          (contactGridPoint_separation (fun h => hij (d.coordinate_injective h)))
    | inr eu =>
      rcases eu with ⟨e, u⟩
      by_cases hi₀ : i = d.left e
      · subst i
        simpa only [localVertex_old_zero, localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (localOld 0) (Sum.inr u)
            (by simp [localOld]) (by simpa only [localVertex_old_zero, localVertex_internal] using hn)
      · by_cases hi₁ : i = d.right e
        · subst i
          simpa only [localVertex_old_one, localVertex_internal] using
            globalPosition_local_nonedge d W G P h₀ h₁ hsep e (localOld 1) (Sum.inr u)
              (by simp [localOld]) (by simpa only [localVertex_old_one, localVertex_internal] using hn)
        · rw [dist_comm]
          exact globalPosition_nonincident d P hP i e hi₀ hi₁ u
  | inr eu =>
    rcases eu with ⟨e, u⟩
    cases y with
    | inl i =>
      by_cases hi₀ : i = d.left e
      · subst i
        simpa only [localVertex_old_zero, localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (localOld 0)
            (by simp [localOld]) (by simpa only [localVertex_old_zero, localVertex_internal] using hn)
      · by_cases hi₁ : i = d.right e
        · subst i
          simpa only [localVertex_old_one, localVertex_internal] using
            globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (localOld 1)
              (by simp [localOld]) (by simpa only [localVertex_old_one, localVertex_internal] using hn)
        · exact globalPosition_nonincident d P hP i e hi₀ hi₁ u
    | inr fv =>
      rcases fv with ⟨f, v⟩
      by_cases hef : e = f
      · subst f
        have huv : u ≠ v := fun h => hne (by subst v; rfl)
        simpa only [localVertex_internal] using
          globalPosition_local_nonedge d W G P h₀ h₁ hsep e (Sum.inr u) (Sum.inr v)
            (by simpa using huv) (by simpa only [localVertex_internal] using hn)
      · exact globalPosition_distinct_gadgets d P hP e f hef u v

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGlobal
attribute [-simp] _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_left _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_right _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_toList _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.castSites_weight _root_.OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList_length _root_.OAI.ContinuumCoulomb.SourceMetadataProgram.geometricSource_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_bonds _root_.OAI.ContinuumCoulomb.SourceNormalizedSpectrum.lattice_coordinate _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_edges _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_lower _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_upper _root_.OAI.ContinuumCoulomb.SquareLatticeHeisenberg.binary_vertices _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational local gadgets are glued through the exact final-graph
permutation. All old lattice sites remain fixed; all nineteen edges per
source edge retain a controlled error and all nonedges retain the margin. -/

noncomputable section
namespace ContinuumCoulomb.ContactRationalGlobal
open ContactMediator MediatorIteration

theorem local_start (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (e : Fin d.edges) : localPoints d P ℓ e (localOld 0) = contactPoint 0 0 :=
  (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun _ => hℓ _)).1

theorem local_end (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (e : Fin d.edges) : localPoints d P ℓ e (localOld 1) = contactPoint 17 0 :=
  (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun _ => hℓ _)).2.1

theorem edge_error (d : SquareLatticeHeisenberg) (W G P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (a : GlobalEdge d) :
    |dist (point d P ℓ ((finalGraph d.bonds W G).left a))
      (point d P ℓ ((finalGraph d.bonds W G).right a)) - (ℓ a : ℝ)| ≤
        72 * ((P : ℝ) + 1)⁻¹ := by
  obtain ⟨⟨e, a⟩, rfl⟩ := (edgeEquiv d.edges).surjective a
  change |dist (globalPosition d (localPoints d P ℓ)
      ((finalGraph d.bonds W G).left (encodeEdge d.edges e a)))
    (globalPosition d (localPoints d P ℓ)
      ((finalGraph d.bonds W G).right (encodeEdge d.edges e a))) -
        (ℓ (encodeEdge d.edges e a) : ℝ)| ≤ _
  rw [finalGraph_left, finalGraph_right]
  change |dist (globalPosition d (localPoints d P ℓ)
      (localVertex (d.left e) (d.right e) e (localLeft (member (d.coefficient e)) a)))
    (globalPosition d (localPoints d P ℓ)
      (localVertex (d.left e) (d.right e) e (localRight a))) -
        (ℓ (encodeEdge d.edges e a) : ℝ)| ≤ _
  rw [globalPosition_local d _ (local_start d P ℓ hℓ) (local_end d P ℓ hℓ),
    globalPosition_local d _ (local_start d P ℓ hℓ) (local_end d P ℓ hℓ),
    ContactGridEdge.place_dist]
  have hm : member (d.coefficient e) = if edgeNegative d.bonds e then 0 else 1 :=
    member_edgeNegative d.bonds e
  rw [hm]
  exact (ContactRationalLocal.exists_link_approximation P (edgeNegative d.bonds e)
    (fun a => ℓ (encodeEdge d.edges e a)) (fun a => hℓ _)).2.2.1 a

theorem nonedge_separation (d : SquareLatticeHeisenberg) (W G P : ℕ)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) (hn : Nonedge d W G x y) :
    6 / 5 < dist (point d P ℓ x) (point d P ℓ y) := by
  apply globalPosition_nonedge d W G (localPoints d P ℓ)
    (local_start d P ℓ hℓ) (local_end d P ℓ hℓ) _ _ x y hne hn
  · intro e s t hst hnon
    exact ContactRationalLocal.nonedge_separation P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) (by omega) (fun a => hℓ _) s t hst
      (finalGraph_nonedge_contactNonlink d.bonds W G e s t hnon)
  · intro e s
    exact ContactRationalLocal.near_base P (edgeNegative d.bonds e)
      (fun a => ℓ (encodeEdge d.edges e a)) hP (fun a => hℓ _) s

theorem separation (d : SquareLatticeHeisenberg) (W G P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) :
    9 / 10 ≤ dist (point d P ℓ x) (point d P ℓ y) := by
  by_cases hn : Nonedge d W G x y
  · exact (by norm_num : (9 / 10 : ℝ) ≤ 6 / 5).trans
      (nonedge_separation d W G P ℓ hP hℓ x y hne hn).le
  · simp only [Nonedge, not_not] at hn
    obtain ⟨a, ha⟩ := hn
    have he := (abs_le.mp (edge_error d W G P ℓ hℓ a)).1
    have hsmall : 72 * ((P : ℝ) + 1)⁻¹ ≤ 1 / 50 := by
      apply (mul_inv_le_iff₀ (by positivity)).mpr
      have hPR : (7200 : ℝ) ≤ P := by exact_mod_cast hP
      linarith
    have hl := (hℓ a).1
    unfold contactLengthTolerance at hl
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · rw [dist_comm]
      linarith

end ContinuumCoulomb.ContactRationalGlobal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactCalibratedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scaled rational contact coordinates retain the actual Coulomb
calibration, with the coordinate and scalar-evaluation errors added
explicitly. The gap follows from the proved separated-density estimate. -/

noncomputable section
namespace ContinuumCoulomb.ContactCalibratedGeometry
open ContactMediator MediatorIteration
open scoped BigOperators

theorem distance (d : SquareLatticeHeisenberg) (P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (x y : GlobalSite d) :
    dist (point d P q ℓ x) (point d P q ℓ y) =
      (q : ℝ) * dist (ContactRationalGlobal.point d P ℓ x)
        (ContactRationalGlobal.point d P ℓ y) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [point, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hqr]

theorem separation_oai (d : SquareLatticeHeisenberg) (W G P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (x y : GlobalSite d) (hne : x ≠ y) :
    (9 / 10 : ℝ) * q ≤ dist (point d P q ℓ x) (point d P q ℓ y) := by
  rw [distance d P hq]
  have h := mul_le_mul_of_nonneg_left
    (ContactRationalGlobal.separation d W G P ℓ hP hℓ x y hne)
    (show (0 : ℝ) ≤ q by exact_mod_cast hq.le)
  simpa only [mul_comm] using h

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation_oai := @OAI.ContinuumCoulomb.ContactCalibratedGeometry.separation_oai
