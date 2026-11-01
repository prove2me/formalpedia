-- Prove2me | solution 1 for OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:54:54.728401+00:00
-- url     : https://prove2.me/submissions/66c11e0c-1ef9-4839-8e0c-53346b1e8c73

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
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A008
import Definitions.Def_OAIQ092A009
import Theorems.Thm_OAI_ContinuumCoulomb_ContactCalibratedGeometry_separation

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
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_Axis
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom

theorem norm_sq_axis_shift (x : Position) (a : Fin 3) (t : ℝ) :
    ‖x+t • axis a‖^2 = ‖x‖^2 + 2*t*x a + t^2 := by
  rw [norm_add_sq_real]
  simp [axis, inner_smul_right, EuclideanSpace.inner_single_right, norm_smul,
    Real.norm_eq_abs, sq_abs]
  ring

theorem second_deriv_quadratic_rpow {q b p : ℝ} (hq : 0 < q) :
    deriv (deriv (fun t : ℝ => (q+2*t*b+t^2)^p)) 0 =
      p*(p-1)*q^(p-2)*(2*b)^2 + 2*p*q^(p-1) := by
  let Q : ℝ → ℝ := fun t => q+2*t*b+t^2
  have hQ (t : ℝ) : HasDerivAt Q (2*b+2*t) t := by
    convert (((hasDerivAt_const t q).add
      (((hasDerivAt_id t).const_mul 2).mul_const b)).add
      ((hasDerivAt_id t).pow 2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  have hQ0 : Q 0 = q := by simp [Q]
  have hQe : ∀ᶠ t in 𝓝 (0 : ℝ), Q t ≠ 0 :=
    (hQ 0).continuousAt.eventually_ne (by simpa [hQ0] using ne_of_gt hq)
  have hder : deriv (fun t => Q t ^ p) =ᶠ[𝓝 0]
      fun t => p*Q t^(p-1)*(2*b+2*t) := by
    filter_upwards [hQe] with t ht
    convert ((hQ t).rpow_const (Or.inl ht)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hder.deriv_eq]
  have hh := (((hQ 0).rpow_const (p := p-1)
      (Or.inl (by simpa [hQ0] using ne_of_gt hq))).const_mul p).mul
    ((hasDerivAt_const 0 (2*b)).add ((hasDerivAt_id 0).const_mul 2))
  have hh' : HasDerivAt (fun t => p*Q t^(p-1)*(2*b+2*t))
      (p*((2*b)*(p-1)*q^(p-1-1))*(2*b)+p*q^(p-1)*2) 0 := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | norm_num [Q]
  rw [hh'.deriv]
  rw [show p-1-1 = p-2 by ring]
  ring

open scoped Convolution
open ContinuousLinearMap

theorem contDiff_partial {f : Position → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ (n+1) f) (v : Position) : ContDiff ℝ n (dirPartial f v) := by
  exact (hf.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasCompactSupport_partial {f : Position → ℝ} (hf : HasCompactSupport f)
    (v : Position) : HasCompactSupport (dirPartial f v) := hf.fderiv_apply ℝ v

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Variational_WeakLaplacian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem integrable_mul_compact_of_continuousAt {f g : Position → ℝ}
    (hf : ∀ x ∈ tsupport g, ContinuousAt f x) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hc : Continuous (fun x => f x*g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hf x hx).mul hg.continuousAt
    · have he : (fun y => f y*g y) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change g y = 0 at hy
        simp only [hy, mul_zero]
      exact continuousAt_const.congr_of_eventuallyEq he
  exact hc.integrable_of_hasCompactSupport (hgc.mono (Function.support_mul_subset_right f g))

theorem tsupport_dirPartial_subset (f : Position → ℝ) (v : Position) :
    tsupport (dirPartial f v) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v

theorem integral_mul_coordinateLaplacian_eq {f φ : Position → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, f x * coordinateLaplacian φ x) =
      ∫ x, coordinateLaplacian f x * φ x := by
  have hpφ (v : Position) : ContDiff ℝ ∞ (dirPartial φ v) :=
    contDiff_partial (by simpa using hφ) v
  have hppφ (v : Position) : ContDiff ℝ ∞ (dirPartial (dirPartial φ v) v) :=
    contDiff_partial (by simpa using hpφ v) v
  have hdφ (v : Position) := (hpφ v).differentiable (by simp)
  have hiφ (v : Position) := hasCompactSupport_partial hφc v
  have hpcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (dirPartial f v) x :=
    ((hf x hx).fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply
      contDiffAt_const
  have hppcont (v : Position) (x : Position) (hx : x ∈ tsupport φ) :
      ContinuousAt (dirPartial (dirPartial f v) v) x :=
    (((hpcont v x hx).fderiv_right (show (0 : WithTop ℕ∞)+1 ≤ 1 by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hleft (v : Position) : Integrable (fun x => f x*dirPartial (dirPartial φ v) v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x ((tsupport_dirPartial_subset φ v)
        (tsupport_dirPartial_subset (dirPartial φ v) v hx))).continuousAt)
      (hppφ v).continuous
      (hasCompactSupport_partial (hiφ v) v)
  have hright (v : Position) : Integrable (fun x => dirPartial (dirPartial f v) v x*φ x) :=
    integrable_mul_compact_of_continuousAt (hppcont v) hφ.continuous hφc
  have hcross (v : Position) : Integrable (fun x => dirPartial f v x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hpcont v x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfg (v : Position) : Integrable (fun x => f x*dirPartial φ v x) :=
    integrable_mul_compact_of_continuousAt
      (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).continuousAt)
      (hpφ v).continuous (hiφ v)
  have hfpg (v : Position) : Integrable (fun x => dirPartial f v x*φ x) :=
    integrable_mul_compact_of_continuousAt (fun x hx => (hpcont v x hx).continuousAt)
      hφ.continuous hφc
  have hby (v : Position) :
      (∫ x, f x*dirPartial (dirPartial φ v) v x) = ∫ x, dirPartial (dirPartial f v) v x*φ x := by
    calc
      _ = -(∫ x, dirPartial f v x*dirPartial φ v x) :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (hcross v) (hleft v) (hfg v)
          (fun x hx => (hf x (tsupport_dirPartial_subset φ v hx)).differentiableAt (by norm_num))
          (fun x _ => hdφ v x)
      _ = _ := by
        have he : (∫ x, dirPartial f v x*dirPartial φ v x) =
            -(∫ x, dirPartial (dirPartial f v) v x*φ x) :=
          integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
            (hright v) (hcross v) (hfpg v)
            (fun x hx => (hpcont v x hx).differentiableAt (by norm_num))
            (fun x _ => hφ.differentiable (by simp) x)
        rw [he, neg_neg]
  calc
    _ = ∫ x, ∑ a : Fin 3, f x*dirPartial (dirPartial φ (axis a)) (axis a) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [coordinateLaplacian_eq_partials (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt, Finset.mul_sum]
    _ = ∑ a : Fin 3, ∫ x, f x*dirPartial (dirPartial φ (axis a)) (axis a) x :=
      integral_finsetSum _ (fun a _ => hleft (axis a))
    _ = ∑ a : Fin 3, ∫ x, dirPartial (dirPartial f (axis a)) (axis a) x*φ x := by
      simp_rw [hby]
    _ = ∫ x, ∑ a : Fin 3, dirPartial (dirPartial f (axis a)) (axis a) x*φ x :=
      (integral_finsetSum _ (fun a _ => hright (axis a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [coordinateLaplacian_eq_partials (hf x hx), Finset.sum_mul]
      · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]

theorem hasCompactSupport_coordinateLaplacian {f : Position → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (coordinateLaplacian f) := by
  apply hf.mono'
  intro x hx
  by_contra hn
  exact hx (coordinateLaplacian_eq_zero_of_notMem_tsupport hn)

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Packets_CoulombKernel
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem contDiff_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (regularizedKernel ε) := by
  apply ContDiff.rpow_const_of_ne
  · exact (contDiff_norm_sq ℝ).add contDiff_const
  · intro x
    exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)).ne'

theorem laplacian_regularizedKernel {ε : ℝ} (hε : ε ≠ 0) (x : Position) :
    coordinateLaplacian (regularizedKernel ε) x = -regularizedCharge ε x := by
  have hq : 0 < ‖x‖^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)
  have he : ∀ a : Fin 3, (fun t : ℝ => regularizedKernel ε (x+t • axis a)) =
      (fun t => ((‖x‖^2+ε^2)+2*t*x a+t^2)^(-1/2 : ℝ)) := by
    intro a
    ext t
    unfold regularizedKernel
    rw [norm_sq_axis_shift]
    congr 1
    ring
  unfold coordinateLaplacian
  simp_rw [he, second_deriv_quadratic_rpow hq]
  norm_num
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hpow : (‖x‖^2+ε^2)^(-5/2 : ℝ)*(‖x‖^2+ε^2) =
      (‖x‖^2+ε^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hq.ne']
    norm_num
  calc
    _ = 3*(‖x‖^2+ε^2)^(-5/2 : ℝ)*(∑ a : Fin 3, (x a)^2) -
        3*(‖x‖^2+ε^2)^(-3/2 : ℝ) := by
      rw [Finset.mul_sum]
      congr 1
      all_goals ring_nf
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      unfold regularizedCharge
      rw [← hpow]
      ring

theorem hasDerivAt_chargePrimitive (r : ℝ) :
    HasDerivAt chargePrimitive (3*r^2*(1+r^2)^(-5/2 : ℝ)) r := by
  have hp : 0 < 1+r^2 := by positivity
  have hd := ((hasDerivAt_id r).pow 3).mul
    (((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)).rpow_const
      (p := (-3/2 : ℝ)) (Or.inl hp.ne'))
  unfold chargePrimitive
  apply hd.congr_deriv
  norm_num
  have he : (1+r^2)^(-5/2 : ℝ)*(1+r^2) = (1+r^2)^(-3/2 : ℝ) := by
    rw [← Real.rpow_add_one hp.ne']; norm_num
  norm_num at he
  rw [← he]
  ring

theorem chargePrimitive_eq_ratio {r : ℝ} (hr : 0 ≤ r) :
    chargePrimitive r = (1-(1+r^2)⁻¹)^(3/2 : ℝ) := by
  have hp : 0 < 1+r^2 := by positivity
  have hh : 1-(1+r^2)⁻¹ = r^2/(1+r^2) := by field_simp; ring
  rw [hh, Real.div_rpow (sq_nonneg _) hp.le]
  have hn : (r^2)^(3/2 : ℝ) = r^3 := by
    rw [← Real.rpow_natCast_mul hr]
    norm_num
  rw [hn]
  unfold chargePrimitive
  rw [show (-3/2:ℝ) = -(3/2:ℝ) by ring, Real.rpow_neg hp.le]
  rfl

theorem tendsto_chargePrimitive : Tendsto chargePrimitive atTop (𝓝 1) := by
  have hp : Tendsto (fun r : ℝ => 1+r^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  have hi := tendsto_inv_atTop_zero.comp hp
  have hh := (tendsto_const_nhds.sub hi).rpow tendsto_const_nhds
    (Or.inl (by norm_num : (1:ℝ)-0 ≠ 0) : (1:ℝ)-0 ≠ 0 ∨ 0 < (3/2:ℝ))
  apply Filter.Tendsto.congr' _ (by simpa using hh)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  exact (chargePrimitive_eq_ratio hr).symm

theorem integrable_radial_regularizedCharge_one :
    IntegrableOn (fun r : ℝ => 3*r^2*(1+r^2)^(-5/2 : ℝ)) (Set.Ioi 0) := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity) tendsto_chargePrimitive

theorem integral_radial_regularizedCharge_one :
    (∫ r : ℝ in Set.Ioi 0, 3*r^2*(1+r^2)^(-5/2 : ℝ)) = 1 := by
  have hder := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0:ℝ)) (fun r _ => hasDerivAt_chargePrimitive r)
    (fun r _ => by positivity : ∀ r ∈ Set.Ioi (0:ℝ), 0 ≤ 3*r^2*(1+r^2)^(-5/2 : ℝ))
    tendsto_chargePrimitive
  simpa [chargePrimitive] using hder

theorem regularizedCharge_one_eq : regularizedCharge 1 =
    fun x : Position => 3*(1+‖x‖^2)^(-5/2 : ℝ) := by
  ext x
  simp [regularizedCharge, add_comm]

theorem integrable_regularizedCharge_one : Integrable (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq, integrable_fun_norm_addHaar volume
    (f := fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simpa [finrank_euclideanSpace_fin, smul_eq_mul, mul_comm, mul_assoc,
    mul_left_comm] using integrable_radial_regularizedCharge_one

theorem integral_regularizedCharge_one : (∫ x, regularizedCharge 1 x) = 4*Real.pi := by
  rw [regularizedCharge_one_eq, integral_fun_norm_addHaar volume
    (fun r : ℝ => 3*(1+r^2)^(-5/2:ℝ))]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  norm_num
  have hi : (∫ r : ℝ in Set.Ioi 0, r^2*(3*(1+r^2)^(-(5/2): ℝ))) = 1 := by
    simpa only [neg_div, mul_assoc, mul_comm, mul_left_comm] using
      integral_radial_regularizedCharge_one
  rw [hi]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  ring

theorem regularizedCharge_smul {ε : ℝ} (hε : 0 < ε) (x : Position) :
    regularizedCharge ε (ε • x) = (ε^3)⁻¹*regularizedCharge 1 x := by
  unfold regularizedCharge
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have he : (ε*‖x‖)^2+ε^2 = ε^2*(‖x‖^2+1) := by ring
  rw [he, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (ε^2)^(-5/2:ℝ) = (ε^5)⁻¹ := by
    rw [← Real.rpow_natCast_mul hε.le]
    norm_num [Real.rpow_neg hε.le]
  rw [hp]
  norm_num
  field_simp

theorem integral_regularizedCharge_scale {ε : ℝ} (hε : 0 < ε) (φ : Position → ℝ) :
    (∫ x, regularizedCharge ε x*φ x) = ∫ x, regularizedCharge 1 x*φ (ε • x) := by
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (fun x => regularizedCharge ε x*φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace_fin, smul_eq_mul] at hs
  have ht : (∫ x, regularizedCharge ε (ε • x)*φ (ε • x)) =
      (ε^3)⁻¹*(∫ x, regularizedCharge 1 x*φ (ε • x)) := by
    simp_rw [regularizedCharge_smul hε, mul_assoc]
    exact integral_const_mul _ _
  rw [ht] at hs
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hε.ne')) hs).symm

theorem regularizedCharge_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedCharge ε x := by unfold regularizedCharge; positivity

theorem continuous_regularizedCharge_one : Continuous (regularizedCharge 1) := by
  rw [regularizedCharge_one_eq]
  apply Continuous.const_mul
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    left
    positivity

theorem regularizedCharge_tendsto_dirac {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedCharge (ε n) x*φ x)
      atTop (𝓝 (4*Real.pi*φ 0)) := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hD := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Position)) (fun x => regularizedCharge 1 x*C)
    (F := fun n x => regularizedCharge 1 x*φ (ε n • x))
    (f := fun x => regularizedCharge 1 x*φ 0)
    (fun n => (continuous_regularizedCharge_one.mul
      (hφ.comp (show Continuous (fun x : Position => ε n • x) by fun_prop))).aestronglyMeasurable)
    (integrable_regularizedCharge_one.mul_const C)
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedCharge_nonneg 1 x)]
      exact mul_le_mul_of_nonneg_left (hC _) (regularizedCharge_nonneg 1 x)))
    (Filter.Eventually.of_forall (fun x => by
      have he : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Position)) := by
        simpa using hlim.smul_const x
      exact tendsto_const_nhds.mul (hφ.continuousAt.tendsto.comp he)))
  simp only [integral_mul_const, integral_regularizedCharge_one] at hD
  simpa only [integral_regularizedCharge_scale (hε _)] using hD

theorem locallyIntegrable_coulombKernel : LocallyIntegrable coulombKernel volume := by
  intro x
  refine ⟨Metric.ball 0 (‖x‖+1), IsOpen.mem_nhds Metric.isOpen_ball ?_,
    coulombKernel_integrableOn_ball _⟩
  simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖

theorem coulombKernel_eq_rpow (x : Position) :
    coulombKernel x = (‖x‖^2)^(-1/2 : ℝ) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg x)]
  norm_num [coulombKernel, Real.rpow_neg_one]

theorem regularizedKernel_le {ε : ℝ} {x : Position} (hx : x ≠ 0) :
    regularizedKernel ε x ≤ coulombKernel x := by
  rw [coulombKernel_eq_rpow]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (le_add_of_nonneg_right (sq_nonneg ε)) (by norm_num)

theorem regularizedKernel_nonneg (ε : ℝ) (x : Position) :
    0 ≤ regularizedKernel ε x := by unfold regularizedKernel; positivity

theorem regularizedKernel_tendsto {ε : ℕ → ℝ} (hlim : Tendsto ε atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedKernel (ε n) x) atTop (𝓝 (coulombKernel x)) := by
  have hh : Tendsto (fun n => ‖x‖^2+(ε n)^2) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add (hlim.pow 2)
  have hr := hh.rpow tendsto_const_nhds
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)) : ‖x‖^2 ≠ 0 ∨ 0 < (-1/2:ℝ))
  simpa only [regularizedKernel, coulombKernel_eq_rpow] using hr

theorem regularizedKernel_integral_tendsto {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0))
    {φ : Position → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, regularizedKernel (ε n) x*φ x)
      atTop (𝓝 (∫ x, coulombKernel x*φ x)) := by
  have hae : ∀ᵐ x : Position ∂volume, x ≠ 0 := volume.ae_ne 0
  have hb : Integrable (fun x => coulombKernel x*‖φ x‖) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hφ.norm hφc.norm
  apply tendsto_integral_of_dominated_convergence (fun x => coulombKernel x*‖φ x‖)
  · intro n
    exact ((contDiff_regularizedKernel (hε n).ne').continuous.mul hφ).aestronglyMeasurable
  · exact hb
  · intro n
    filter_upwards [hae] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (regularizedKernel_nonneg _ _)]
    exact mul_le_mul_of_nonneg_right (regularizedKernel_le hx) (norm_nonneg _)
  · filter_upwards [hae] with x hx
    exact (regularizedKernel_tendsto hlim hx).mul_const (φ x)

theorem integral_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, coulombKernel x*coordinateLaplacian φ x) = -(4*Real.pi*φ 0) := by
  let ε : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hleft := regularizedKernel_integral_tendsto hε hεlim
    (continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top)))
    (hasCompactSupport_coordinateLaplacian hφc)
  have hright := (regularizedCharge_tendsto_dirac hε hεlim hφ.continuous hφc).neg
  have he : (fun n => ∫ x, regularizedKernel (ε n) x*coordinateLaplacian φ x) =
      (fun n => -(∫ x, regularizedCharge (ε n) x*φ x)) := by
    funext n
    rw [integral_mul_coordinateLaplacian_eq
      (fun x _ => ((contDiff_regularizedKernel (hε n).ne').of_le
        (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt) hφ hφc]
    simp_rw [laplacian_regularizedKernel (hε n).ne', neg_mul, integral_neg]
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem coordinateLaplacian_translate (φ : Position → ℝ) (x y : Position) :
    coordinateLaplacian (fun z => φ (z+y)) x = coordinateLaplacian φ (x+y) := by
  unfold coordinateLaplacian
  simp only [add_right_comm _ _ y]

theorem integral_translated_coulombKernel_laplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (y : Position) :
    (∫ x, coulombKernel (x-y)*coordinateLaplacian φ x) = -(4*Real.pi*φ y) := by
  have ht : ContDiff ℝ ∞ (fun z => φ (z+y)) := hφ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have he := integral_coulombKernel_laplacian ht hc
  simp only [coordinateLaplacian_translate, zero_add] at he
  rw [← integral_add_right_eq_self (fun x => coulombKernel (x-y)*coordinateLaplacian φ x) y]
  simpa only [add_sub_cancel_right] using he

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeProperties
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_VerticalMode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized Gaussian in the transverse direction. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem verticalMode_normalized {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z : ℝ, verticalMode freq z ^ 2) = 1 := by
  simp_rw [verticalMode_square hfreq]
  rw [integral_div, integral_gaussian, div_self]
  exact (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq)).ne'

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual localized modes in planar/transverse coordinates. The measure is
the product of planar Euclidean volume and one-dimensional Lebesgue measure.
The split Laplacian below is the sum of the three coordinate derivatives. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ p, localizedMode freq u p ^ 2) = 1 := by
  simp_rw [localizedMode, mul_pow]
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun r => normalizedPlanarMode (r - u) ^ 2)
      (fun z => verticalMode freq z ^ 2),
    integral_sub_right_eq_self (fun r => normalizedPlanarMode r ^ 2) u,
    normalizedPlanarMode_normalized, verticalMode_normalized hfreq, one_mul]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_SplitCoordinates
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Volume-preserving planar/transverse coordinates for the actual
three-dimensional Coulomb space. The intermediate product has its Euclidean
L² norm; the final ordinary product carries the same product volume. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_integral (f : SplitPosition → ℝ) :
    (∫ x : Position, f (positionSplitCoordinates x)) = ∫ p, f p :=
  positionSplitCoordinates_measurePreserving.integral_comp
    positionSplitCoordinates.toHomeomorph.measurableEmbedding f

theorem positionSplitCoordinates_norm_sq (x : Position) :
    ‖x‖ ^ 2 = ‖(positionSplitCoordinates x).1‖ ^ 2 +
      (positionSplitCoordinates x).2 ^ 2 := by
  change ‖x‖ ^ 2 = ‖(positionSplitIsometry x).fst‖ ^ 2 + (positionSplitIsometry x).snd ^ 2
  have h := WithLp.prod_norm_sq_eq_of_L2 (positionSplitIsometry x)
  rw [positionSplitIsometry.norm_map] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem continuumLocalizedMode_normalized {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : (∫ x : Position, continuumLocalizedMode freq u x ^ 2) = 1 := by
  change (∫ x : Position, (localizedMode freq u (positionSplitCoordinates x)) ^ 2) = 1
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p ^ 2),
    localizedMode_normalized hfreq]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulomb
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedDensity_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < localizedDensity freq u x :=
  sq_pos_of_pos (continuumLocalizedMode_positive hfreq u x)

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombSymmetry
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual strict positivity and symmetry of the direct Coulomb coefficients. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedCoulomb_product_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun p : Position × Position => localizedDensity freq u p.1 *
      (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Position × Position => localizedDensity freq u p.1 *
        (NeutralAtom.coulombKernel (p.1 - p.2) * localizedDensity freq v p.2))
      ((volume : Measure Position).prod volume) :=
    (((localizedDensity_continuous freq u).measurable.comp measurable_fst).mul
      ((NeutralAtom.measurable_coulombKernel.comp (measurable_fst.sub measurable_snd)).mul
        ((localizedDensity_continuous freq v).measurable.comp measurable_snd))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x =>
      (localizedDensity_coulomb_integrable_bound hfreq v x).1.const_mul
        (localizedDensity freq u x))
  · have hn (x y : Position) :
        ‖localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y)‖ =
        localizedDensity freq u x *
          (NeutralAtom.coulombKernel (x - y) * localizedDensity freq v y) :=
      Real.norm_of_nonneg (mul_nonneg (localizedDensity_nonnegative freq u x)
        (mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
          (localizedDensity_nonnegative freq v y)))
    simp_rw [hn, integral_const_mul]
    exact localizedCoulombCoeff_integrable hfreq u v

theorem localizedCoulombCoeff_symmetric {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) : localizedCoulombCoeff freq u v = localizedCoulombCoeff freq v u := by
  unfold localizedCoulombCoeff NeutralAtom.potentialOf
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (localizedCoulomb_product_integrable hfreq u v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      simp only [NeutralAtom.coulombKernel, norm_sub_rev x y]
      ring))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombTranslation
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Direct Coulomb coefficients as actual translated-density profiles. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarCenter_norm (u : PlanarPosition) : ‖planarCenter u‖ = ‖u‖ := by
  have h := positionSplitCoordinates_norm_sq (planarCenter u)
  simp only [planarCenter, ContinuousLinearEquiv.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem planarCenter_sub (u v : PlanarPosition) : planarCenter (u - v) = planarCenter u - planarCenter v := by
  change positionSplitCoordinates.symm (u - v, 0) =
    positionSplitCoordinates.symm (u, 0) - positionSplitCoordinates.symm (v, 0)
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_self]

theorem planarCenter_norm_sub (u v : PlanarPosition) : ‖planarCenter u - planarCenter v‖ = ‖u - v‖ := by
  rw [← planarCenter_sub, planarCenter_norm]

theorem continuumLocalizedMode_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x = continuumLocalizedMode freq 0 (x - planarCenter u) := by
  simp only [continuumLocalizedMode, localizedMode, map_sub, planarCenter,
    ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]

theorem localizedDensity_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x = localizedDensity freq 0 (x - planarCenter u) := by
  simp only [localizedDensity, continuumLocalizedMode_translate freq u]

theorem localizedDensity_potential_translate (freq : ℝ) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq u) x =
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) := by
  unfold NeutralAtom.potentialOf
  rw [← integral_add_right_eq_self
    (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) (planarCenter u)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [localizedDensity_translate freq u, add_sub_cancel_right]
    congr 2
    abel)

theorem localizedCoulombProfileAt_eq (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombCoeff freq 0 u := by
  unfold localizedCoulombProfileAt localizedCoulombCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x).symm)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarModeDecay
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit exponential tail of the actual positive planar mode. Splitting
the Gaussian exponent avoids any assumed asymptotics for a special function. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_double_time (t : ℝ) (b : PlanarPosition) :
    planarHeatKernel t b =
      2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b := by
  unfold planarHeatKernel
  have h1 : -‖b‖ ^ 2 / (4 * t) = -‖b‖ ^ 2 / (8 * t) + -‖b‖ ^ 2 / (8 * t) := by ring
  have h2 : -‖b‖ ^ 2 / (4 * (2 * t)) = -‖b‖ ^ 2 / (8 * t) := by ring
  rw [h1, h2, Real.exp_add]
  ring

theorem planarHeatForcing_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖)
    (b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) * planarHeatKernel (2 * t) b := by
  by_cases hf : planarForcing (r - b) = 0
  · rw [hf, mul_zero]
    exact mul_nonneg (by positivity) (planarHeatKernel_positive (by positivity) b).le
  · have hs : ‖r - b‖ < 1 := lt_of_not_ge
      (fun h => hf (planarForcing_zero_of_norm_ge_one h))
    have hn : ‖r‖ - 1 ≤ ‖b‖ := by
      have htriangle := norm_add_le (r - b) b
      rw [sub_add_cancel] at htriangle
      linarith
    have hsq : (‖r‖ - 1) ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
    have he : Real.exp (-‖b‖ ^ 2 / (8 * t)) ≤
        Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      gcongr
    calc
      _ ≤ planarHeatKernel t b :=
        mul_le_of_le_one_right (planarHeatKernel_positive ht b).le (planarForcing_le_one _)
      _ = 2 * Real.exp (-‖b‖ ^ 2 / (8 * t)) * planarHeatKernel (2 * t) b :=
        planarHeatKernel_double_time t b
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
        (planarHeatKernel_positive (by positivity) b).le

theorem planarHeatAverage_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarHeatAverage t r ≤ 2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)) := by
  have hi := (planarHeatKernel_integrable (by positivity : 0 < 2 * t)).const_mul
    (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t)))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tail ht hr)
  simpa only [integral_const_mul, planarHeatKernel_integral (by positivity : 0 < 2 * t),
    mul_one, planarHeatAverage] using h

theorem planar_heat_tail_exponent {t d : ℝ} (ht : 0 < t) :
    d / 2 ≤ t / 2 + d ^ 2 / (8 * t) := by
  have he : t / 2 + d ^ 2 / (8 * t) - d / 2 = (2 * t - d) ^ 2 / (8 * t) := by
    field_simp
    ring
  have hp : 0 ≤ (2 * t - d) ^ 2 / (8 * t) := by positivity
  linarith

theorem planarHeatResolvent_tail {t : ℝ} (ht : 0 < t) {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    Real.exp (-t) * planarHeatAverage t r ≤
      (2 * Real.exp (-(‖r‖ - 1) / 2)) * Real.exp (-(1 / 2 : ℝ) * t) := by
  have he : -t + (-((‖r‖ - 1) ^ 2) / (8 * t)) ≤ -(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t := by
    have hA : (‖r‖ - 1) / 2 ≤ t / 2 + (‖r‖ - 1) ^ 2 / (8 * t) :=
      planar_heat_tail_exponent ht
    rw [neg_div]
    linarith
  calc
    _ ≤ Real.exp (-t) * (2 * Real.exp (-((‖r‖ - 1) ^ 2) / (8 * t))) :=
      mul_le_mul_of_nonneg_left (planarHeatAverage_tail ht hr) (Real.exp_pos _).le
    _ = 2 * Real.exp (-t + (-((‖r‖ - 1) ^ 2) / (8 * t))) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-(‖r‖ - 1) / 2 + -(1 / 2 : ℝ) * t) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem planarResolventMode_exponential_tail {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ 4 * Real.exp (-(‖r‖ - 1) / 2) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (2 * Real.exp (-(‖r‖ - 1) / 2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact planarHeatResolvent_tail ht hr)
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 / 2 : ℝ) * t)) = 2 := by
    rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0)]
    norm_num
  rw [integral_const_mul, he] at h
  nlinarith

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarHopping
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.planarHeatResolventPrimitive_zero _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positive contact hopping integral. Its Lipschitz control is
inherited from the compact forcing through the mass-one resolvent kernel. -/

noncomputable section
open MeasureTheory
open scoped NNReal
namespace ContinuumCoulomb

theorem planarForcing_lipschitz : LipschitzWith planarForcingLipschitzConstant planarForcing :=
  Classical.choose_spec forcing_lipschitz_exists

theorem planarResolventMode_integrand_integrable (r : PlanarPosition) :
    Integrable (fun b => planarResolventKernel b * planarForcing (r - b)) := by
  apply planarResolventKernel_integrable.mul_bdd (c := 1)
    (planarForcing_C7.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun b => by
    change ‖planarForcing (r - b)‖ ≤ (1 : ℝ)
    rw [Real.norm_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

theorem planarResolventMode_norm_sub (x y : PlanarPosition) :
    ‖planarResolventMode x - planarResolventMode y‖ ≤
      planarForcingLipschitzConstant * ‖x - y‖ := by
  unfold planarResolventMode
  rw [← integral_sub (planarResolventMode_integrand_integrable x)
    (planarResolventMode_integrand_integrable y)]
  have h := norm_integral_le_of_norm_le
    (f := fun b => planarResolventKernel b * planarForcing (x - b) -
      planarResolventKernel b * planarForcing (y - b))
    (planarResolventKernel_integrable.mul_const
      ((planarForcingLipschitzConstant : ℝ) * ‖x - y‖))
    (Filter.Eventually.of_forall (fun b => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarResolventKernel_nonnegative b)]
      apply mul_le_mul_of_nonneg_left _ (planarResolventKernel_nonnegative b)
      have h := planarForcing_lipschitz.norm_sub_le (x - b) (y - b)
      simpa only [show x - b - (y - b) = x - y by abel] using h))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul] using h

theorem planarAxis_zero_norm : ‖planarAxis 0‖ = 1 := by
  simp [planarAxis]

theorem planarHopping_norm_sub (d e : ℝ) :
    ‖planarHopping d - planarHopping e‖ ≤ planarHoppingLipschitzConstant * ‖d - e‖ := by
  have hden : 0 < 2 * ∫ r, planarResolventMode r ^ 2 :=
    mul_pos (by norm_num) planarResolventMode_square_integral_positive
  have hb (r : PlanarPosition) :
      ‖planarHoppingIntegrand d r - planarHoppingIntegrand e r‖ ≤
        planarForcing r * (planarForcingLipschitzConstant * ‖d - e‖) := by
    unfold planarHoppingIntegrand
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (planarForcing_nonnegative r)]
    apply mul_le_mul_of_nonneg_left _ (planarForcing_nonnegative r)
    have h := planarResolventMode_norm_sub (r - d • planarAxis 0) (r - e • planarAxis 0)
    have heq : ‖r - d • planarAxis 0 - (r - e • planarAxis 0)‖ = ‖d - e‖ := by
      rw [show r - d • planarAxis 0 - (r - e • planarAxis 0) =
        (e - d) • planarAxis 0 by rw [sub_smul]; abel,
        norm_smul, planarAxis_zero_norm, mul_one, Real.norm_eq_abs, abs_sub_comm]
      rfl
    simpa only [heq] using h
  have hi := norm_integral_le_of_norm_le
    (planarForcing_integrable.mul_const ((planarForcingLipschitzConstant : ℝ) * ‖d - e‖))
    (Filter.Eventually.of_forall hb)
  rw [integral_sub (planarHoppingIntegrand_integrable d) (planarHoppingIntegrand_integrable e),
    integral_mul_const] at hi
  unfold planarHopping
  rw [← sub_div, norm_div, Real.norm_of_nonneg hden.le]
  change _ ≤ (planarForcingLipschitzConstant * (∫ r, planarForcing r) /
    (2 * ∫ r, planarResolventMode r ^ 2)) * ‖d - e‖
  calc
    _ ≤ ((∫ r, planarForcing r) * (planarForcingLipschitzConstant * ‖d - e‖)) /
        (2 * ∫ r, planarResolventMode r ^ 2) := div_le_div_of_nonneg_right hi hden.le
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_Localization_TruncatedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma coulombKernel_nonneg (x : Space) : 0 ≤ coulombKernel x := inv_nonneg.mpr (norm_nonneg _)
lemma coulombKernel_measurable : Measurable coulombKernel := measurable_norm.inv
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

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
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_Gaussian
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.Coulomb.complexWindow_apply _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma gaussian_pos (a : ℝ) (x : Space) : 0 < gaussian a x := Real.exp_pos _
lemma gaussian_le_one {a : ℝ} (ha : 0 ≤ a) (x : Space) : gaussian a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖x‖]
lemma gaussian_continuous (a : ℝ) : Continuous (gaussian a) := by unfold gaussian; fun_prop
lemma gaussian_integrable {a : ℝ} (ha : 0 < a) : Integrable (gaussian a) := by
  change Integrable (fun x : Space => Real.exp (-a*‖x‖^2))
  have H := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V:=Space)
    (show 0 < (a : ℂ).re from ha) 0 0).re
  change Integrable (fun x : Space => (Complex.exp (-(a:ℂ)*↑‖x‖^2 + 0 * ↑(inner ℝ (0:Space) x))).re) at H
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re, gaussian] using H
lemma gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x, gaussian a x) = (Real.pi/a)^(3/2:ℝ) := by
  simpa [gaussian] using GaussianFourier.integral_rexp_neg_mul_sq_norm (V:=Space) ha
lemma kernel_gaussian_integral {d : Space} (hd : d ≠ 0) :
    ‖d‖⁻¹ = (Real.sqrt Real.pi)⁻¹ * ∫ t : ℝ, gaussian (t^2) d := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  rw [integral_gaussian, Real.sqrt_div (by positivity), Real.sqrt_sq (norm_nonneg _)]
  field_simp

lemma gaussian_product (a : ℝ) (x y z : Space) :
    gaussian (2*a) (x-z)*gaussian (2*a) (y-z) =
      gaussian a (x-y)*gaussian (4*a) (z-(1/2:ℝ) • (x+y)) := by
  unfold gaussian
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2),
    inner_smul_right, inner_add_right]
  rw [mul_pow, norm_add_sq_real]
  rw [real_inner_comm z x, real_inner_comm z y]
  ring

lemma gaussian_product_integrable {a : ℝ} (ha : 0 < a) (x y : Space) :
    Integrable (fun z => gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) := by
  simp_rw [gaussian_product]
  exact ((gaussian_integrable (by positivity : 0 < 4*a)).comp_sub_right _).const_mul _

lemma gaussian_convolution_identity {a : ℝ} (ha : 0 < a) (x y : Space) :
    (∫ z, gaussian (2*a) (x-z)*gaussian (2*a) (y-z)) =
      gaussian a (x-y)*(Real.pi/(4*a))^(3/2:ℝ) := by
  simp_rw [gaussian_product]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma integrable_gaussian_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p : Space × Space => f p.1*f p.2*gaussian a (p.1-p.2)) := by
  apply (hf.norm.mul_prod hf.norm).mono' (by
    apply Measurable.aestronglyMeasurable
    exact ((hm.comp measurable_fst).mul (hm.comp measurable_snd)).mul
      ((gaussian_continuous a).measurable.comp (by fun_prop)))
  exact Filter.Eventually.of_forall (fun p => by
    simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos a _).le]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (gaussian_le_one ha _))

lemma gaussian_square_integrable {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
  have hm' : Measurable (fun q : (Space × Space) × Space =>
      (f q.1.1*f q.1.2)*(gaussian (2*a) (q.1.1-q.2)*gaussian (2*a) (q.1.2-q.2))) := by
    have h1 : Measurable (fun q : (Space × Space) × Space => f q.1.1*f q.1.2) :=
      (hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))
    apply h1.mul
    exact ((gaussian_continuous _).measurable.comp (by fun_prop)).mul
      ((gaussian_continuous _).measurable.comp (by fun_prop))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => (gaussian_product_integrable ha p.1 p.2).const_mul (f p.1*f p.2))
  · have he (p : Space × Space) :
        (∫ z, ‖(f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))‖) =
          (‖f p.1‖*‖f p.2‖*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
      simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
      rw [integral_const_mul, gaussian_convolution_identity ha]
      ring
    simp_rw [he]
    exact (integrable_gaussian_pair hf.norm hm.norm ha.le).mul_const _

lemma gaussian_form_nonneg {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2) := by
  have hi := gaussian_square_integrable hf hm ha
  have H := integral_integral_swap (f := fun (p : Space × Space) (z : Space) =>
    (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) hi
  have hleft (p : Space × Space) :
      (∫ z, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (f p.1*f p.2*gaussian a (p.1-p.2))*(Real.pi/(4*a))^(3/2:ℝ) := by
    rw [integral_const_mul, gaussian_convolution_identity ha]
    ring
  have hright (z : Space) :
      (∫ p : Space × Space, (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z))) =
        (∫ x, f x*gaussian (2*a) (x-z))^2 := by
    simp_rw [show ∀ p : Space × Space,
      (f p.1*f p.2)*(gaussian (2*a) (p.1-z)*gaussian (2*a) (p.2-z)) =
      (f p.1*gaussian (2*a) (p.1-z))*(f p.2*gaussian (2*a) (p.2-z)) from fun p => by ring]
    exact (integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Space => f x*gaussian (2*a) (x-z))
      (fun x : Space => f x*gaussian (2*a) (x-z))).trans (pow_two _).symm
  simp_rw [hleft, hright] at H
  rw [integral_mul_const] at H
  have hnonneg : 0 ≤ (∫ p : Space × Space, f p.1*f p.2*gaussian a (p.1-p.2)) *
      (Real.pi/(4*a))^(3/2:ℝ) := H.symm ▸ integral_nonneg (fun z => sq_nonneg _)
  exact nonneg_of_mul_nonneg_left hnonneg (Real.rpow_pos_of_pos (by positivity) _)
lemma space_ae_distinct : ∀ᵐ p : Space × Space, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall (fun x => by
    rw [ae_iff]
    simp only [not_not]
    have he : {y : Space | x = y} = {x} := by ext y; simp [eq_comm]
    change volume {y : Space | x = y} = 0
    rw [he, measure_singleton])

lemma gaussian_parameter_integrable {d : Space} (hd : d ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t^2) d) := by
  have he (t : ℝ) : gaussian (t^2) d = Real.exp (-(‖d‖^2)*t^2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hd))

lemma gaussian_parameter_integral {d : Space} (hd : d ≠ 0) :
    (∫ t : ℝ, gaussian (t^2) d) = coulombKernel d * Real.sqrt Real.pi := by
  have H := kernel_gaussian_integral hd
  unfold coulombKernel
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  calc
    _ = ((Real.sqrt Real.pi)⁻¹*(∫ t : ℝ, gaussian (t^2) d))*Real.sqrt Real.pi := by field_simp
    _ = _ := by rw [← H]

lemma coulomb_gaussian_integrable_of_pair {f : Space → ℝ} (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    Integrable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
  have hm' : Measurable (fun q : (Space × Space) × ℝ =>
      (f q.1.1*f q.1.2)*gaussian (q.2^2) (q.1.1-q.1.2)) := by
    apply ((hm.comp (by fun_prop)).mul (hm.comp (by fun_prop))).mul
    unfold gaussian
    fun_prop
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [space_ae_distinct] with p hp
    exact (gaussian_parameter_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1*f p.2)
  · have hi := hp.norm.mul_const (Real.sqrt Real.pi)
    apply hi.congr
    filter_upwards [space_ae_distinct] with p hp
    simp_rw [norm_mul, Real.norm_of_nonneg (gaussian_pos ..).le]
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
    ring

lemma coulomb_form_nonneg_of_pair {f : Space → ℝ} (hf : Integrable f) (hm : Measurable f)
    (hp : Integrable (fun p : Space × Space => f p.1*f p.2*coulombKernel (p.1-p.2))) :
    0 ≤ ∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2) := by
  have hi := coulomb_gaussian_integrable_of_pair hm hp
  have H := integral_integral_swap (f := fun (p : Space × Space) (t : ℝ) =>
    f p.1*f p.2*gaussian (t^2) (p.1-p.2)) hi
  have hl : (∫ p : Space × Space, ∫ t : ℝ, f p.1*f p.2*gaussian (t^2) (p.1-p.2)) =
      (∫ p : Space × Space, f p.1*f p.2*coulombKernel (p.1-p.2))*Real.sqrt Real.pi := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [space_ae_distinct] with p hp
    rw [integral_const_mul, gaussian_parameter_integral (sub_ne_zero.mpr hp)]
    ring
  rw [hl] at H
  have ht : ∀ᵐ t : ℝ, t ≠ 0 := by rw [ae_iff]; simp
  have hn : 0 ≤ ∫ t : ℝ, ∫ p : Space × Space, f p.1*f p.2*gaussian (t^2) (p.1-p.2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ht] with t ht
    exact gaussian_form_nonneg hf hm (sq_pos_of_ne_zero ht)
  rw [← H] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.CoulombRadii_FieldAnalysis_CoulombTest
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_zero {χ : Space → ℝ} {x : Space} (hx : x∉tsupport χ) :
    testCharge χ x=0 := by
  simp only [testCharge,NeutralAtom.coordinateLaplacian_eq_zero_of_notMem_tsupport hx,neg_zero,zero_div]

omit hΩ [IsFiniteMeasure (volume.restrict Ω)] in
lemma testCharge_potential {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (y : Space) :
    (∫ x, coulombKernel (y-x)*testCharge χ x)=χ y := by
  have H := NeutralAtom.integral_translated_coulombKernel_laplacian hχ hc y
  have he : (fun x => coulombKernel (y-x)*testCharge χ x)=
      (fun x => -(NeutralAtom.coulombKernel (x-y)*NeutralAtom.coordinateLaplacian χ x)/(4*Real.pi)) := by
    funext x
    simp only [testCharge,coulombKernel,NeutralAtom.coulombKernel,norm_sub_rev]
    ring
  rw [he,integral_div,integral_neg,H]
  field_simp

end Coulomb

end

end
end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global Coulomb pairing for the bounded integrable packets used in
the mode construction. Existing Gaussian-kernel positivity applies directly
once the elementary bounded-density estimate supplies joint integrability. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

namespace CoulombPacket

theorem joint_integrable (f g : CoulombPacket) :
    Integrable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) := by
  have hg (x : Position) := NeutralAtom.bounded_density_convolution
    NeutralAtom.measurable_coulombKernel NeutralAtom.coulombKernel_nonneg
    (NeutralAtom.coulombKernel_integrableOn_ball 1) (fun _ => NeutralAtom.coulombKernel_le_one)
    g.integrable.norm (fun _ => norm_nonneg _) g.bound_spec x
  let C := g.bound * NeutralAtom.kernelBallMass 1 + ∫ y, ‖g y‖
  have hm : Measurable (fun p : Position × Position =>
      f p.1 * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) :=
    ((f.continuous.measurable.comp measurable_fst).mul
      (g.continuous.measurable.comp measurable_snd)).mul
      (Coulomb.coulombKernel_measurable.comp (measurable_fst.sub measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => by
      have hi := (hg x).1.const_mul ‖f x‖
      apply hi.mono' ((hm.comp ((measurable_const : Measurable (fun _ : Position => x)).prodMk
        measurable_id)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [Function.comp_def, Prod.fst, Prod.snd, id_eq]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
        change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ ≤ ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
        ring_nf
        exact le_rfl))
  · apply (f.integrable.norm.const_mul C).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun x => by
      have he : (∫ y, ‖f x * g y * Coulomb.coulombKernel (x - y)‖) =
          ‖f x‖ * ∫ y, NeutralAtom.coulombKernel (x - y) * ‖g y‖ := by
        have hp (y : Position) : ‖f x * g y * Coulomb.coulombKernel (x - y)‖ =
            ‖f x‖ * (NeutralAtom.coulombKernel (x - y) * ‖g y‖) := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg (Coulomb.coulombKernel_nonneg _)]
          change ‖f x‖ * ‖g y‖ * ‖x - y‖⁻¹ = ‖f x‖ * (‖x - y‖⁻¹ * ‖g y‖)
          ring
        simp_rw [hp, integral_const_mul]
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
      calc
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hg x).2 (norm_nonneg (f x))
        _ = _ := mul_comm _ _)

theorem pair_nonnegative (f : CoulombPacket) : 0 ≤ pair f f :=
  Coulomb.coulomb_form_nonneg_of_pair f.integrable f.continuous.measurable (joint_integrable f f)

theorem pair_symmetric (f g : CoulombPacket) : pair f g = pair g f := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f g),
    integral_prod _ (joint_integrable g f), integral_integral_swap (joint_integrable f g)]
  apply integral_congr_ae
  filter_upwards [] with y
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Coulomb.coulombKernel, norm_sub_rev x y]
  ring

theorem pair_add_left (f g h : CoulombPacket) : pair (add f g) h = pair f h + pair g h := by
  unfold pair
  change (∫ p : Position × Position, (f p.1 + g p.1) * h p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [add_mul]
  exact integral_add (joint_integrable f h) (joint_integrable g h)

theorem pair_smul_left (t : ℝ) (f g : CoulombPacket) : pair (smul t f) g = t * pair f g := by
  unfold pair
  change (∫ p : Position × Position, (t * f p.1) * g p.2 * Coulomb.coulombKernel (p.1 - p.2)) = _
  simp_rw [mul_assoc]
  exact integral_const_mul t _

theorem pair_add_right (f g h : CoulombPacket) : pair f (add g h) = pair f g + pair f h := by
  rw [pair_symmetric, pair_add_left, pair_symmetric g f, pair_symmetric h f]

theorem pair_smul_right (t : ℝ) (f g : CoulombPacket) : pair f (smul t g) = t * pair f g := by
  rw [pair_symmetric, pair_smul_left, pair_symmetric g f]

theorem pair_cauchy (f g : CoulombPacket) : pair f g ^ 2 ≤ pair f f * pair g g := by
  have h (t : ℝ) : 0 ≤ pair g g * (t * t) + (2 * pair f g) * t + pair f f := by
    have hn := pair_nonnegative (add f (smul t g))
    rw [pair_add_left, pair_add_right, pair_add_right, pair_smul_left,
      pair_smul_right, pair_smul_right, pair_symmetric g f, pair_smul_left] at hn
    nlinarith only [hn]
  have hd := discrim_le_zero h
  dsimp only [discrim] at hd
  nlinarith only [hd]

end CoulombPacket
end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketTests
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet combinations and the exact global Poisson duality for
smooth compact tests. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem pair_zero_left (f : CoulombPacket) : pair zero f = 0 := by
  simp [pair, zero]

theorem pair_sumList_left (fs : List CoulombPacket) (g : CoulombPacket) :
    pair (sumList fs) g = (fs.map (fun f => pair f g)).sum := by
  induction fs with
  | nil => exact pair_zero_left g
  | cons f fs ih => simp only [sumList, pair_add_left, ih, List.map_cons, List.sum_cons]

theorem pair_combination_left {m : ℕ} (f : Fin m → CoulombPacket) (d : Fin m → ℝ)
    (g : CoulombPacket) : pair (combination f d) g = ∑ i, d i * pair (f i) g := by
  rw [combination, pair_sumList_left, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, pair_smul_left]

theorem pair_combination_right {m : ℕ} (f : CoulombPacket) (g : Fin m → CoulombPacket)
    (d : Fin m → ℝ) : pair f (combination g d) = ∑ j, d j * pair f (g j) := by
  calc
    _ = pair (combination g d) f := pair_symmetric _ _
    _ = ∑ j, d j * pair (g j) f := pair_combination_left g d f
    _ = _ := Finset.sum_congr rfl (fun j _ => congrArg (fun a => d j * a) (pair_symmetric (g j) f))

theorem pair_combinations {m n : ℕ} (f : Fin m → CoulombPacket) (g : Fin n → CoulombPacket)
    (d : Fin m → ℝ) (e : Fin n → ℝ) :
    pair (combination f d) (combination g e) =
      ∑ i, ∑ j, d i * e j * pair (f i) (g j) := by
  rw [pair_combination_left]
  simp_rw [pair_combination_right, Finset.mul_sum, mul_assoc]

theorem pair_test (f : CoulombPacket) (χ : Position → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    pair f (test χ hχ hc) = ∫ x, f x * χ x := by
  unfold pair
  rw [Measure.volume_eq_prod, integral_prod _ (joint_integrable f (test χ hχ hc))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ y, f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) = _
  rw [show (fun y => f x * Coulomb.testCharge χ y * Coulomb.coulombKernel (x - y)) =
      (fun y => f x * (Coulomb.coulombKernel (x - y) * Coulomb.testCharge χ y)) by funext y; ring,
    integral_const_mul, Coulomb.testCharge_potential hχ hc]

theorem test_pair_test (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ) :
    pair (test χ hχ hcχ) (test ψ hψ hcψ) = ∫ x, Coulomb.testCharge χ x * ψ x :=
  pair_test _ _ hψ hcψ

theorem test_pair_orthogonal (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hd : Disjoint (tsupport χ) (tsupport ψ)) : pair (test χ hχ hcχ) (test ψ hψ hcψ) = 0 := by
  rw [test_pair_test]
  have hz (x : Position) : Coulomb.testCharge χ x * ψ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [image_eq_zero_of_notMem_tsupport (fun hy => Set.disjoint_left.mp hd hx hy), mul_zero]
    · rw [Coulomb.testCharge_zero hx, zero_mul]
  simp_rw [hz, integral_zero]

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombPacketCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Coulomb coercivity from disjoint compact tests and approximate
local duality. All integrals range over the whole Euclidean space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem test_combination_energy {m : ℕ} (χ : Fin m → Position → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K : ℝ} (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    pair (combination (fun i => test (χ i) (hχ i) (hc i)) d)
      (combination (fun i => test (χ i) (hχ i) (hc i)) d) ≤ K * ∑ i, d i ^ 2 := by
  classical
  rw [pair_combinations]
  have hentry (i j : Fin m) : pair (test (χ i) (hχ i) (hc i)) (test (χ j) (hχ j) (hc j)) =
      if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, if_true] using test_pair_test (χ i) (χ i) (hχ i) (hχ i) (hc i) (hc i)
    · rw [ite_eq_right hij]
      exact test_pair_orthogonal (χ i) (χ j) (hχ i) (hχ j) (hc i) (hc j) (hd i j hij)
  simp_rw [hentry]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  calc
    _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem gram_coercive_of_dual_lower {m : ℕ} (f : Fin m → CoulombPacket)
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdual : ∀ d : Fin m → ℝ, a * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, d i * d j * ∫ x, f i x * χ j x)
    (d : Fin m → ℝ) :
    (a ^ 2 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, pair (f i) (f j) * d i * d j := by
  let ρ := combination f d
  let η := combination (fun i => test (χ i) (hχ i) (hc i)) d
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : a * S ≤ pair ρ η := by
    rw [pair_combinations]
    simp_rw [pair_test]
    exact hdual d
  have hpair0 : 0 ≤ pair ρ η := (mul_nonneg ha hS).trans hpair
  have hsquare : (a * S) ^ 2 ≤ pair ρ η ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha hS) hpair0).mpr hpair
  have htest := test_combination_energy χ hχ hc hd henergy d
  have hQ : 0 ≤ pair ρ ρ := pair_nonnegative ρ
  have hbound : (a * S) ^ 2 ≤ pair ρ ρ * (K * S) :=
    hsquare.trans ((pair_cauchy ρ η).trans (mul_le_mul_of_nonneg_left htest hQ))
  have hcoercive : (a ^ 2 / K) * S ≤ pair ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have hcancel := (mul_le_mul_iff_left₀ hSpos).mp
        (show (a ^ 2 * S) * S ≤ (pair ρ ρ * K) * S by nlinarith only [hbound])
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hK).mpr hcancel
  change (a ^ 2 / K) * S ≤ pair (combination f d) (combination f d) at hcoercive
  rw [pair_combinations] at hcoercive
  convert hcoercive using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ContinuumCoulomb.CoulombPacket

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombGramApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombLipschitz
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform Lipschitz estimate for the actual direct-Coulomb profile. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedCoulombLipschitzConstant_nonnegative (freq : ℝ) :
    0 ≤ localizedCoulombLipschitzConstant freq :=
  add_nonneg (mul_nonneg (sq_nonneg _)
    (integral_nonneg (fun _ => sq_nonneg _))) zero_le_one

theorem localizedDensity_potential_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x y : Position) :
    ‖NeutralAtom.potentialOf (localizedDensity freq u) x -
      NeutralAtom.potentialOf (localizedDensity freq u) y‖ ≤
        localizedCoulombLipschitzConstant freq * ‖x - y‖ := by
  simpa only [localizedDensity_mass hfreq u, localizedCoulombLipschitzConstant] using
    NeutralAtom.potentialOf_lipschitz_bound (localizedDensity_integrable hfreq u)
      (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x y

theorem localizedCoulombProfileAt_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => localizedDensity freq 0 x *
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u)) := by
  apply (localizedCoulombCoeff_integrable hfreq 0 u).congr
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x))

theorem localizedCoulombProfileAt_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    ‖localizedCoulombProfileAt freq u - localizedCoulombProfileAt freq v‖ ≤
      localizedCoulombLipschitzConstant freq * ‖u - v‖ := by
  have hpt (x : Position) :
      ‖localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
        localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v)‖ ≤
      (localizedCoulombLipschitzConstant freq * ‖u - v‖) * localizedDensity freq 0 x := by
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq 0 x)]
    have h := localizedDensity_potential_norm_sub hfreq 0 (x - planarCenter u) (x - planarCenter v)
    rw [show (x - planarCenter u) - (x - planarCenter v) = planarCenter v - planarCenter u by abel,
      norm_sub_rev (planarCenter v) (planarCenter u), planarCenter_norm_sub] at h
    calc
      _ ≤ localizedDensity freq 0 x *
          (localizedCoulombLipschitzConstant freq * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left h (localizedDensity_nonnegative freq 0 x)
      _ = _ := mul_comm _ _
  unfold localizedCoulombProfileAt
  rw [← integral_sub (localizedCoulombProfileAt_integrable hfreq u)
    (localizedCoulombProfileAt_integrable hfreq v)]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
      localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v))
    ((localizedDensity_integrable hfreq 0).const_mul
      (localizedCoulombLipschitzConstant freq * ‖u - v‖))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, localizedDensity_mass hfreq 0, mul_one] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_PlanarRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rotation/reflection invariance of the actual manufactured planar data.
The hopping between arbitrary translated centers depends only on distance. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarForcing_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (r : PlanarPosition) :
    planarForcing (L r) = planarForcing r := by
  simp only [planarForcing, L.norm_map]

theorem planarResolventKernel_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventKernel (L r) = planarResolventKernel r := by
  simp only [planarResolventKernel, planarResolventIntegrand, planarHeatKernel, L.norm_map]

theorem planarResolventMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : planarResolventMode (L r) = planarResolventMode r := by
  unfold planarResolventMode
  rw [← MeasureTheory.integral_comp L
    (fun b => planarResolventKernel b * planarForcing (L r - b))]
  apply integral_congr_ae
  filter_upwards [] with b
  rw [planarResolventKernel_isometry, ← L.map_sub, planarForcing_isometry]

theorem normalizedPlanarMode_isometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition)
    (r : PlanarPosition) : normalizedPlanarMode (L r) = normalizedPlanarMode r := by
  simp only [normalizedPlanarMode, planarResolventMode_isometry]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombRadial
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedLeakage
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential off-site density leakage for the actual localized modes. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem positionSplitCoordinates_fst_norm_le (x : Position) :
    ‖(positionSplitCoordinates x).1‖ ≤ ‖x‖ := by
  have h := positionSplitCoordinates_norm_sq x
  nlinarith [sq_nonneg (positionSplitCoordinates x).2, norm_nonneg x,
    norm_nonneg (positionSplitCoordinates x).1]

theorem continuumLocalizedMode_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    continuumLocalizedMode freq u x ≤ 4 * localizedAmplitudeBound freq *
      Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) := by
  have hp := div_le_div_of_nonneg_right (planarResolventMode_exponential_tail hr)
    (Real.sqrt_nonneg (∫ r, planarResolventMode r ^ 2))
  have hv : verticalMode freq (positionSplitCoordinates x).2 ≤
      1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (positionSplitCoordinates x).2])
  change (planarResolventMode ((positionSplitCoordinates x).1 - u) /
    Real.sqrt (∫ r, planarResolventMode r ^ 2)) * verticalMode freq (positionSplitCoordinates x).2 ≤ _
  calc
    _ ≤ (4 * Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) /
        Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
          (1 / Real.sqrt (Real.sqrt (Real.pi / freq))) :=
      mul_le_mul hp hv (verticalMode_positive hfreq _).le (by positivity)
    _ = _ := by unfold localizedAmplitudeBound; ring

theorem localizedTailConstant_nonnegative (freq : ℝ) : 0 ≤ localizedTailConstant freq :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem localizedDensity_planar_tail {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) (hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq *
      Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
  have h := (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (localizedAmplitudeBound_positive hfreq).le) (Real.exp_pos _).le)).mpr
    (continuumLocalizedMode_planar_tail hfreq u x hr)
  have he : Real.exp (-(‖(positionSplitCoordinates x).1 - u‖ - 1) / 2) ^ 2 =
      Real.exp 1 * Real.exp (-‖(positionSplitCoordinates x).1 - u‖) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he] at h
  simpa only [localizedDensity, localizedTailConstant, mul_assoc] using h

theorem localizedDensity_near_other_center {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) (hx : ‖x - planarCenter v‖ ≤ R)
    (hsep : R + 1 ≤ ‖u - v‖) :
    localizedDensity freq u x ≤ localizedTailConstant freq * Real.exp (R - ‖u - v‖) := by
  have hp : ‖(positionSplitCoordinates x).1 - v‖ ≤ R := by
    have h := (positionSplitCoordinates_fst_norm_le (x - planarCenter v)).trans hx
    simpa only [map_sub, planarCenter, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub] using h
  have ht : ‖u - v‖ ≤ ‖u - (positionSplitCoordinates x).1‖ +
      ‖(positionSplitCoordinates x).1 - v‖ := by
    simpa only [dist_eq_norm] using dist_triangle u (positionSplitCoordinates x).1 v
  rw [norm_sub_rev u (positionSplitCoordinates x).1] at ht
  have hr : 1 ≤ ‖(positionSplitCoordinates x).1 - u‖ := by linarith
  exact (localizedDensity_planar_tail hfreq u x hr).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDuality
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual compact local dual tests: a common positive diagonal mass,
disjoint supports and exponentially small off-site pairings. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace ContinuumCoulomb

theorem localizedTest_smooth {χ : Position → ℝ} (hχ : ContDiff ℝ ∞ χ) (u : PlanarPosition) :
    ContDiff ℝ ∞ (localizedTest χ u) := hχ.comp (contDiff_id.sub contDiff_const)

theorem localizedTest_hasCompactSupport {χ : Position → ℝ} (hc : HasCompactSupport χ)
    (u : PlanarPosition) : HasCompactSupport (localizedTest χ u) :=
  hc.comp_homeomorph (Homeomorph.subRight (planarCenter u))

theorem localizedTest_support {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u : PlanarPosition) :
    tsupport (localizedTest χ u) ⊆ Metric.closedBall (planarCenter u) R := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  have hχx : χ (x - planarCenter u) ≠ 0 := hx
  have h := hs (subset_tsupport χ hχx)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using h

theorem localizedTest_disjoint {χ : Position → ℝ} {R : ℝ}
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (u v : PlanarPosition)
    (hsep : 2 * R < ‖u - v‖) : Disjoint (tsupport (localizedTest χ u)) (tsupport (localizedTest χ v)) := by
  apply Set.disjoint_left.mpr
  intro x hxu hxv
  have hu := localizedTest_support hs u hxu
  have hv := localizedTest_support hs v hxv
  simp only [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have h : ‖planarCenter u - planarCenter v‖ ≤ ‖planarCenter u - x‖ + ‖x - planarCenter v‖ := by
    simpa only [dist_eq_norm] using dist_triangle (planarCenter u) x (planarCenter v)
  rw [norm_sub_rev (planarCenter u) x, planarCenter_norm_sub] at h
  linarith

theorem localizedDualPair_diagonal (freq : ℝ) (u : PlanarPosition) (χ : Position → ℝ) :
    localizedDualPair freq u u χ = ∫ x, localizedDensity freq 0 x * χ x := by
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter u)) (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right]

theorem localizedDualPair_diagonal_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hn : ∀ x, 0 ≤ χ x) (h0 : 0 < χ 0) : 0 < localizedDualPair freq u u χ := by
  rw [localizedDualPair_diagonal]
  exact integral_pos_of_integrable_nonneg_nonzero
    ((localizedDensity_continuous freq 0).mul hχ)
    (((localizedDensity_continuous freq 0).mul hχ).integrable_of_hasCompactSupport hc.mul_left)
    (fun x => mul_nonneg (localizedDensity_nonnegative freq 0 x) (hn x))
    (mul_pos (localizedDensity_positive hfreq 0 0) h0).ne'

theorem localizedDualPair_offsite {freq R : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) {χ : Position → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 R) (hsep : R + 1 ≤ ‖u - v‖) :
    |localizedDualPair freq u v χ| ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * (∫ x, |χ x|) := by
  have hpt (x : Position) : ‖localizedDensity freq u (x + planarCenter v) * χ x‖ ≤
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)) * |χ x| := by
    by_cases hx : χ x = 0
    · simp only [hx, mul_zero, norm_zero, abs_zero, le_refl]
    have hn : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hx)
    have hb := localizedDensity_near_other_center hfreq u v (x + planarCenter v)
      (by simpa only [add_sub_cancel_right] using hn) hsep
    rw [norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  unfold localizedDualPair localizedTest
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * χ (x - planarCenter v)) (planarCenter v)]
  simp only [add_sub_cancel_right]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u (x + planarCenter v) * χ x)
    ((hχ.integrable_of_hasCompactSupport (μ := volume) hc).norm.const_mul
      (localizedTailConstant freq * Real.exp (R - ‖u - v‖)))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, Real.norm_eq_abs] using h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedDualMatrix
attribute [-instance] _root_.OAI.ContinuumCoulomb.CoulombPacket.instCoeFunForallPositionReal
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete compact bumps supply local duality for the actual mode densities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localDualBump_smooth : ContDiff ℝ ∞ (localDualBump : Position → ℝ) :=
  localDualBump.contDiff

theorem localDualBump_support : tsupport (localDualBump : Position → ℝ) ⊆ Metric.closedBall 0 2 := by
  rw [localDualBump.tsupport_eq]
  exact Set.Subset.rfl

theorem localDualMass_positive {freq : ℝ} (hfreq : 0 < freq) : 0 < localDualMass freq := by
  have h0 : localDualBump (0 : Position) = 1 :=
    localDualBump.one_of_mem_closedBall (by simp [localDualBump])
  have h := localizedDualPair_diagonal_positive hfreq 0 localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump.nonneg' (by rw [h0]; norm_num)
  simpa only [localizedDualPair_diagonal, localDualMass] using h

theorem localLeakageBound_nonnegative (freq D : ℝ) : 0 ≤ localLeakageBound freq D :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem localDualPair_offsite {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    |localizedDualPair freq u v localDualBump| ≤ localLeakageBound freq D := by
  have h := localizedDualPair_offsite hfreq u v localDualBump_smooth.continuous
    localDualBump.hasCompactSupport localDualBump_support (by linarith : (2 : ℝ) + 1 ≤ ‖u - v‖)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq)) (integral_nonneg (fun _ => abs_nonneg _)))

theorem localDualTests_disjoint {D : ℝ} (hD : 5 ≤ D)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    Disjoint (tsupport (localizedTest localDualBump u)) (tsupport (localizedTest localDualBump v)) :=
  localizedTest_disjoint localDualBump_support u v (by linarith)

theorem localizedDualMatrix_lower {freq D : ℝ} (hfreq : 0 < freq) (hD : 3 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (s : Fin m → ℝ) :
    (localDualMass freq - m * localLeakageBound freq D) * ∑ i, s i ^ 2 ≤
      ∑ i, ∑ j, localizedDualPair freq (u i) (u j) localDualBump * s i * s j := by
  apply dualMatrix_quadratic_lower _ (localLeakageBound_nonnegative freq D)
  · intro i
    rw [localizedDualPair_diagonal]
    exact le_rfl
  · intro i j hij
    exact localDualPair_offsite hfreq hD (u i) (u j) (hsep i j hij)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coercivity of the actual full Coulomb Gram matrix of the localized
resolvent--Gaussian modes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem localizedPacket_pair {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    CoulombPacket.pair (localizedPacket hfreq u) (localizedPacket hfreq v) =
      localizedCoulombCoeff freq u v := by
  unfold CoulombPacket.pair localizedCoulombCoeff NeutralAtom.potentialOf
  rw [Measure.volume_eq_prod, integral_prod _ (CoulombPacket.joint_integrable _ _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change localizedDensity freq u x * localizedDensity freq v y * ‖x - y‖⁻¹ =
    localizedDensity freq u x * (‖x - y‖⁻¹ * localizedDensity freq v y)
  ring

theorem testCharge_localizedTest (χ : Position → ℝ) (u : PlanarPosition) (x : Position) :
    Coulomb.testCharge (localizedTest χ u) x = Coulomb.testCharge χ (x - planarCenter u) := by
  unfold Coulomb.testCharge localizedTest
  simp only [sub_eq_add_neg, NeutralAtom.coordinateLaplacian_translate]

theorem localizedTest_energy (χ : Position → ℝ) (u : PlanarPosition) :
    (∫ x, Coulomb.testCharge (localizedTest χ u) x * localizedTest χ u x) =
      ∫ x, Coulomb.testCharge χ x * χ x := by
  simp_rw [testCharge_localizedTest]
  exact integral_sub_right_eq_self (fun x => Coulomb.testCharge χ x * χ x) (planarCenter u)

theorem localDualEnergyBound_positive : 0 < localDualEnergyBound := by
  unfold localDualEnergyBound
  positivity

theorem localizedGram_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D) (d : Fin m → ℝ) :
    ((localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound) *
      ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have h := CoulombPacket.gram_coercive_of_dual_lower (fun i => localizedPacket hfreq (u i))
    (fun i => localizedTest localDualBump (u i))
    (fun i => localizedTest_smooth localDualBump_smooth (u i))
    (fun i => localizedTest_hasCompactSupport localDualBump.hasCompactSupport (u i))
    (fun i j hij => localDualTests_disjoint hD (u i) (u j) (hsep i j hij))
    localDualEnergyBound_positive hmargin ?_ ?_ d
  · simpa only [localizedPacket_pair] using h
  · intro i
    rw [localizedTest_energy]
    exact (le_abs_self _).trans (by unfold localDualEnergyBound; linarith)
  · intro e
    have he := localizedDualMatrix_lower hfreq (by linarith : (3 : ℝ) ≤ D) u hsep e
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change e i * e j * localizedDualPair freq (u i) (u j) localDualBump = _
    ring

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedGramConstants
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed positive coercivity constant once the total off-site leakage is
at most half the common diagonal dual mass. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedGramConstant_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedGramConstant freq :=
  div_pos (sq_pos_of_pos (localDualMass_positive hfreq))
    (mul_pos (by norm_num) localDualEnergyBound_positive)

theorem localizedGram_uniform_coercive {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    {m : ℕ} (u : Fin m → PlanarPosition) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i - u j‖)
    (hleak : m * localLeakageBound freq D ≤ localDualMass freq / 2) (d : Fin m → ℝ) :
    localizedGramConstant freq * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  have ha := localDualMass_positive hfreq
  have hb : localDualMass freq / 2 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hmargin : 0 ≤ localDualMass freq - m * localLeakageBound freq D := by linarith
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ localDualMass freq / 2) hmargin).mpr hb
  have hc : localizedGramConstant freq ≤
      (localDualMass freq - m * localLeakageBound freq D) ^ 2 / localDualEnergyBound := by
    calc
      _ = (localDualMass freq / 2) ^ 2 / localDualEnergyBound := by
        unfold localizedGramConstant
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hs localDualEnergyBound_positive.le
  exact (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun i _ => sq_nonneg (d i)))).trans
    (localizedGram_coercive hfreq hD u hsep hmargin d)

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_LocalizedCoulombGap
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-site specialization gives the positive denominator `U-v`
used by the Hubbard superexchange calibration. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem localizedCoulombCoeff_gap {freq D : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (u v : PlanarPosition) (hsep : D ≤ ‖u - v‖) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombCoeff freq u v := by
  let centers : Fin 2 → PlanarPosition := ![u, v]
  let d : Fin 2 → ℝ := ![1, -1]
  have hs : ∀ i j : Fin 2, i ≠ j → D ≤ ‖centers i - centers j‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hsep
    · change D ≤ ‖v - u‖
      simpa only [norm_sub_rev] using hsep
    · exact False.elim (hij rfl)
  have h := localizedGram_uniform_coercive hfreq hD centers hs (by simpa using hleak) d
  simp only [Fin.sum_univ_two, centers, d, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, neg_one_sq, mul_one, mul_neg, neg_neg] at h
  rw [localizedCoulombCoeff_symmetric hfreq v u,
    localizedCoulombCoeff_distance freq u u, localizedCoulombCoeff_distance freq v v] at h
  simp only [sub_self, norm_zero] at h
  nlinarith only [h]

theorem localizedCoulombProfile_gap {freq D d : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2) (hd : D ≤ d) :
    localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombProfile freq d := by
  have hn : ‖(0 : PlanarPosition) - d • planarAxis 0‖ = d := by
    rw [zero_sub, norm_neg, norm_smul, planarAxis_zero_norm,
      Real.norm_of_nonneg (by linarith : 0 ≤ d), mul_one]
  have h := localizedCoulombCoeff_gap hfreq hD hleak 0 (d • planarAxis 0) (by rw [hn]; exact hd)
  rwa [localizedCoulombCoeff_distance, hn] at h

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_CoulombTargetLipschitz
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative modulus for the actual calibrated hopping residual.
The Coulomb gap keeps the square root away from zero, so ordinary dyadic
bisection needs no lower derivative bound. -/

noncomputable section
namespace ContinuumCoulomb

private theorem sqrt_abs_sub_le_of_lower {c a b : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    |Real.sqrt a-Real.sqrt b| ≤ |a-b|/(2*Real.sqrt c) := by
  have hc' : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have ha' : 0 ≤ a := hc.le.trans ha
  have hb' : 0 ≤ b := hc.le.trans hb
  have hsa := Real.sqrt_le_sqrt ha
  have hsb := Real.sqrt_le_sqrt hb
  have he : (Real.sqrt a-Real.sqrt b)*(Real.sqrt a+Real.sqrt b) = a-b := by
    nlinarith [Real.sq_sqrt ha', Real.sq_sqrt hb']
  have hab : |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) = |a-b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ← abs_mul, he]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hc')).mpr
  nlinarith [mul_le_mul_of_nonneg_left (show 2*Real.sqrt c ≤ Real.sqrt a+Real.sqrt b by linarith)
    (abs_nonneg (Real.sqrt a-Real.sqrt b))]

theorem localizedCoulombProfile_abs_sub {freq : ℝ} (hfreq : 0 < freq) (d e : ℝ) :
    |localizedCoulombProfile freq d-localizedCoulombProfile freq e| ≤
      localizedCoulombLipschitzConstant freq*|d-e| := by
  have h := localizedCoulombProfileAt_norm_sub hfreq (d • planarAxis 0) (e • planarAxis 0)
  rw [← sub_smul, norm_smul, planarAxis_zero_norm, mul_one] at h
  simpa only [localizedCoulombProfile, Real.norm_eq_abs] using h

theorem coulombTargetLipschitzConstant_nonnegative (freq K : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ coulombTargetLipschitzConstant freq τ K := by
  unfold coulombTargetLipschitzConstant
  exact div_nonneg
    (mul_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))
      (localizedCoulombLipschitzConstant_nonnegative freq))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem coulombHoppingTarget_abs_sub {freq τ K : ℝ} (hfreq : 0 < freq)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) (d e : ℝ)
    (hd : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq d)
    (he : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq e) :
    |coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e| ≤
      coulombTargetLipschitzConstant freq τ K*|d-e| := by
  have hc := localizedGramConstant_positive hfreq
  have hs := sqrt_abs_sub_le_of_lower hc hd he
  rw [show (localizedCoulombProfile freq 0-localizedCoulombProfile freq d) -
      (localizedCoulombProfile freq 0-localizedCoulombProfile freq e) =
      localizedCoulombProfile freq e-localizedCoulombProfile freq d by ring,
    abs_sub_comm (localizedCoulombProfile freq e) (localizedCoulombProfile freq d)] at hs
  have hl := div_le_div_of_nonneg_right (localizedCoulombProfile_abs_sub hfreq d e)
    (show 0 ≤ 2*Real.sqrt (localizedGramConstant freq) by positivity)
  unfold coulombHoppingTarget
  rw [Real.sqrt_mul hK, Real.sqrt_mul hK]
  rw [show τ*(Real.sqrt K*Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq d)) -
      τ*(Real.sqrt K*Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq e)) =
      (τ*Real.sqrt K)*(Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq d) -
        Real.sqrt (localizedCoulombProfile freq 0-localizedCoulombProfile freq e)) by ring,
    abs_mul, abs_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))]
  calc
    _ ≤ (τ*Real.sqrt K) *
        (localizedCoulombLipschitzConstant freq*|d-e|/(2*Real.sqrt (localizedGramConstant freq))) :=
      mul_le_mul_of_nonneg_left (hs.trans hl) (mul_nonneg hτ (Real.sqrt_nonneg _))
    _ = _ := by unfold coulombTargetLipschitzConstant; ring

theorem calibratedResidual_abs_sub {freq τ K scale : ℝ} (hfreq : 0 < freq)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) (hscale : 0 ≤ scale) (d e : ℝ)
    (hd : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq d)
    (he : localizedGramConstant freq ≤ localizedCoulombProfile freq 0-localizedCoulombProfile freq e) :
    |(scale*planarHopping d-coulombHoppingTarget freq τ K d) -
      (scale*planarHopping e-coulombHoppingTarget freq τ K e)| ≤
      (scale*(planarHoppingLipschitzConstant : ℝ)+coulombTargetLipschitzConstant freq τ K)*|d-e| := by
  have hh : |scale*(planarHopping d-planarHopping e)| ≤
      scale*(planarHoppingLipschitzConstant : ℝ)*|d-e| := by
    rw [abs_mul, abs_of_nonneg hscale]
    have h := planarHopping_norm_sub d e
    simp only [Real.norm_eq_abs] at h
    exact (mul_le_mul_of_nonneg_left h hscale).trans_eq (by ring)
  have ht := coulombHoppingTarget_abs_sub hfreq hτ hK d e hd he
  calc
    _ = |scale*(planarHopping d-planarHopping e) -
        (coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e)| := by congr 1; ring
    _ ≤ |scale*(planarHopping d-planarHopping e)| +
        |coulombHoppingTarget freq τ K d-coulombHoppingTarget freq τ K e| := abs_sub _ _
    _ ≤ _ := (add_le_add hh ht).trans_eq (by ring)

end ContinuumCoulomb

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

end ContinuumCoulomb.ContactRationalLocal

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactLattice
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

end ContinuumCoulomb

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactGrid
attribute [-simp] _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_divNat _root_.OAI.ContinuumCoulomb.ContactMediator.finProd_modNat _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_internal _root_.OAI.ContinuumCoulomb.ContactMediator.globalPosition_old _root_.OAI.MinUncutGames.Foundations.Complexity.Runtime.haltedOutputLength
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

end ContinuumCoulomb.ContactMediator

end

end OAI
end

section
-- module Solutions.OAIQ092_CC.ContinuumCoulomb_OneParticle_ContactRationalGlobal
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

theorem edge_error (d : SquareLatticeHeisenberg) (W G P : ℕ) {q : ℚ} (hq : 0 < q)
    (ℓ : GlobalEdge d → ℚ)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    (a : GlobalEdge d) :
    |dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
      (point d P q ℓ ((finalGraph d.bonds W G).right a)) - (q : ℝ) * ℓ a| ≤
        (q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹) := by
  rw [distance d P hq, ← mul_sub, abs_mul, abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]
  exact mul_le_mul_of_nonneg_left (ContactRationalGlobal.edge_error d W G P ℓ hℓ a)
    (by exact_mod_cast hq.le)

theorem calibrated_edge_residual_oai (d : SquareLatticeHeisenberg) (W G P : ℕ)
    {q : ℚ} (hq : 0 < q) (ℓ : GlobalEdge d → ℚ) (hP : 7200 ≤ P)
    (hℓ : ∀ a, (ℓ a : ℝ) ∈ Set.Icc (1 - contactLengthTolerance) (1 + contactLengthTolerance))
    {freq D scale τ ε : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2)
    (hDq : D ≤ (9 / 10 : ℝ) * q) (hscale : 0 ≤ scale) (hτ : 0 ≤ τ)
    (K : GlobalEdge d → ℝ) (hK : ∀ a, 0 ≤ K a)
    (hres : ∀ a, |scale * planarHopping ((q : ℝ) * ℓ a) -
      coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)| ≤ ε)
    (a : GlobalEdge d)
    (hne : (finalGraph d.bonds W G).left a ≠ (finalGraph d.bonds W G).right a) :
    let r := dist (point d P q ℓ ((finalGraph d.bonds W G).left a))
      (point d P q ℓ ((finalGraph d.bonds W G).right a))
    |scale * planarHopping r - coulombHoppingTarget freq τ (K a) r| ≤
      ε + (scale * (planarHoppingLipschitzConstant : ℝ) +
        coulombTargetLipschitzConstant freq τ (K a)) * ((q : ℝ) * (72 * ((P : ℝ) + 1)⁻¹)) := by
  intro r
  have hr : D ≤ r := hDq.trans (separation d W G P hq ℓ hP hℓ _ _ hne)
  have ht : D ≤ (q : ℝ) * ℓ a := by
    have hl := (hℓ a).1
    have htol : (9 / 10 : ℝ) ≤ ℓ a := by
      unfold contactLengthTolerance at hl
      linarith
    exact hDq.trans (by nlinarith [show (0 : ℝ) < q by exact_mod_cast hq])
  have hrgap := localizedCoulombProfile_gap hfreq hD hleak hr
  have htgap := localizedCoulombProfile_gap hfreq hD hleak ht
  have hdiff := calibratedResidual_abs_sub hfreq hτ (hK a) hscale r ((q : ℝ) * ℓ a)
    hrgap htgap
  have hc : 0 ≤ scale * (planarHoppingLipschitzConstant : ℝ) +
      coulombTargetLipschitzConstant freq τ (K a) :=
    add_nonneg (mul_nonneg hscale (by positivity))
      (coulombTargetLipschitzConstant_nonnegative freq (K a) hτ)
  have hd := mul_le_mul_of_nonneg_left (edge_error d W G P hq ℓ hℓ a) hc
  have htri := abs_add_le
    (scale * planarHopping r - coulombHoppingTarget freq τ (K a) r -
      (scale * planarHopping ((q : ℝ) * ℓ a) - coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a)))
    (scale * planarHopping ((q : ℝ) * ℓ a) - coulombHoppingTarget freq τ (K a) ((q : ℝ) * ℓ a))
  rw [sub_add_cancel] at htri
  linarith [hres a]

end ContinuumCoulomb.ContactCalibratedGeometry

end

end OAI
end

theorem solution : type_of% @OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual_oai := @OAI.ContinuumCoulomb.ContactCalibratedGeometry.calibrated_edge_residual_oai
