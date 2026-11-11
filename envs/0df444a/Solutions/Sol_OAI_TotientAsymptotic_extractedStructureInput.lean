-- Prove2me | solution 1 for OAI.TotientAsymptotic.extractedStructureInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:38:31.421732+00:00
-- url     : https://prove2.me/submissions/d1be32b1-2b39-4fe3-96a5-9524f805812c

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_ford_structure_value_count
import Theorems.Thm_OAI_TotientAsymptotic_ppt_fixed_bad_coordinate_value_count
import Theorems.Thm_OAI_TotientAsymptotic_small_head_real_gaussian
import Theorems.Thm_OAI_TotientAsymptotic_terminal_band_value_count

section
-- module Solutions.OAIQ233_TA.Compat
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Basic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arithmetic data and renewal coefficients for counting totient values. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma ell_spec {d : ℕ} (hd : IsTotient d) : 0 < ell d ∧ (ell d).totient = d := by
  classical
  simpa only [ell, dite_eq_left hd] using Nat.find_spec hd

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Existence, uniqueness and positivity of the renewal parameters. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma renewalSeries_rho : renewalSeries rho = 1 := rho_mem.2.2

lemma summable_moment :
    Summable (fun n : ℕ => (n+1 : ℝ) * a (n+1) * rho^(n+1)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _))
    (fun n => mul_le_mul_of_nonneg_right ?_ (pow_nonneg rho_pos.le _))
    (summable_index_geometric rho_pos.le rho_lt_one 2)
  have h := mul_le_mul_of_nonneg_left (a_le_index (j := n+1) (by omega))
    (show (0 : ℝ) ≤ n+1 by positivity)
  simpa [pow_two] using h

lemma gamma_pos : 0 < gamma := by
  apply inv_pos.mpr
  apply summable_moment.tsum_pos (i := 0)
  · intro n
    exact mul_nonneg (mul_nonneg (by positivity) (a_pos (by omega)).le)
      (pow_nonneg rho_pos.le _)
  · simpa using mul_pos (a_pos (j := 1) le_rfl) rho_pos

lemma alpha_pos (s : ℝ) : 0 < alpha s := mul_pos lam_pos (Real.exp_pos _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Phase
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cofinal logarithmic phases and convergence of the coefficient approximants. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma self_sub_log_tendsto :
    Tendsto (fun t : ℝ => t - Real.log t) atTop atTop := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hone : Tendsto (fun t : ℝ => 1 - Real.log t / t) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hlog
  have hmul : Tendsto (fun t : ℝ => t * (1-Real.log t / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_pos zero_lt_one tendsto_id hone
  apply hmul.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

lemma psi_tendsto : Tendsto psi atTop atTop := by
  exact (self_sub_log_tendsto.comp Real.tendsto_log_atTop).atTop_div_const lam_pos



lemma theta_eventually_mem : ∀ᶠ x : ℝ in atTop, theta x ∈ Set.Ico (0 : ℝ) 1 := by
  have hp : Tendsto (fun x => psi (B x)) atTop atTop :=
    psi_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hp.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (psi (B x))
    change psi (B x) - (⌊psi (B x)⌋₊ : ℕ) < 1
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuralInput
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal structural inputs from Ford, *The distribution of totients*,
arXiv:1104.3264v2 (14 July 2013), Theorems 10 and 16.

The exceptional sets count values with **some** failing preimage, as in the
convention preceding Theorem 10, p. 5.  Consequently every preimage of a value
outside the exceptional set satisfies the property.  Ford's coordinates in
(4.2), p. 17, are clamped double logarithms.  Theorem 16, (6.1)--(6.2), p. 29,
also supplies the terminal lower bound that allows removing this clamp.

The band center below is Ford's B*rho^i*(1-i/m), not the phase-dependent
`bandScale` in Basic.lean.  Passing between these two centers is an additional
analytic step, governed by the manuscript's equation alpha-comparison.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma preimageExceptionCount_mono {x : ℝ} {P Q : ℕ → Prop}
    (hPQ : ∀ n : ℕ, P n → Q n) :
    preimageExceptionCount x Q ≤ preimageExceptionCount x P := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, n, hn, hφ, hQ⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, n, hn, hφ, fun hP => hQ (hPQ n hP)⟩

lemma fordPrimeCoordinate_eq_raw_of_pos {n i : ℕ}
    (h : 0 < fordPrimeCoordinate n i) :
    fordPrimeCoordinate n i = primeDoubleLog n i := by
  have hraw : 0 < primeDoubleLog n i :=
    (lt_max_iff.mp h).resolve_left (lt_irrefl 0)
  exact max_eq_right hraw.le

lemma fordSimplexCondition_implies_extracted {x : ℝ} {Ψ n : ℕ}
    (hΨ : Ψ < m x) (h : fordSimplexCondition x Ψ n) :
    extractedSimplexCondition x Ψ n := by
  let J := m x-Ψ
  have hJ : 0 < J := Nat.sub_pos_of_lt hΨ
  change 2 < fordPrimeCoordinate n J ∧ _ at h
  obtain ⟨hterminal, horder, hinequalities⟩ := h
  have hraw (i : ℕ) (hi : i ∈ Finset.Icc 1 J) :
      fordPrimeCoordinate n i = primeDoubleLog n i :=
    fordPrimeCoordinate_eq_raw_of_pos
      (lt_of_lt_of_le (by linarith : (0 : ℝ) < fordPrimeCoordinate n J) (horder i hi).1)
  have hcoord (i : ℕ) (hi : i ≤ J) :
      fordSimplexCoordinate x n i = rawSimplexCoordinate x n i := by
    by_cases hi0 : i = 0
    · simp [fordSimplexCoordinate, rawSimplexCoordinate, hi0]
    · simp only [fordSimplexCoordinate, rawSimplexCoordinate, ite_eq_right hi0]
      exact hraw i (Finset.mem_Icc.mpr ⟨by omega, hi⟩)
  have hterminalraw : 2 < primeDoubleLog n J := by
    rwa [hraw J (Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩)] at hterminal
  change 2 < primeDoubleLog n J ∧ _
  refine ⟨hterminalraw, ?_⟩
  intro i hi
  have hiJ : i < J := (Finset.mem_Ico.mp hi).2
  have hsource := hinequalities i hi
  rw [hcoord i hiJ.le] at hsource
  by_cases hlast : i+1 = J
  · rw [ite_eq_left hlast, hcoord J le_rfl] at hsource
    have hdiff : J-i = 1 := by omega
    rw [hlast, Finset.Icc_self, Finset.sum_singleton, hdiff]
    have hnonneg : 0 ≤ rawSimplexCoordinate x n J := by
      simp only [rawSimplexCoordinate, ite_eq_right (Nat.ne_of_gt hJ)]
      exact (lt_trans (by norm_num) hterminalraw).le
    have hmul : a 1 * rawSimplexCoordinate x n J ≤ rawSimplexCoordinate x n J := by
      simpa using mul_le_mul_of_nonneg_right (a_le_index (j := 1) le_rfl) hnonneg
    exact hmul.trans hsource
  · rw [ite_eq_right hlast] at hsource
    convert hsource using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro r hr
    rw [hcoord r (Finset.mem_Icc.mp hr).2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The comparison of the exact Ford band centers with the phase-dependent
centers in the manuscript, equation `alpha-comparison`.  The ratio is
independent of the retained prime index, so its convergence gives a
uniform comparison over all indices below `m`.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma rho_pow_eq_exp (j : ℕ) : rho^j = Real.exp (-lam * j) := by
  have hlog : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [mul_comm, ← hlog, Real.exp_nat_mul, Real.exp_log rho_pos]

lemma alpha_theta_eq {x : ℝ} (hB : 1 < B x) :
    alpha (theta x) = lam * (B x / Real.log (B x)) * rho^(m x) := by
  have hlog : 0 < Real.log (B x) := Real.log_pos hB
  have he : lam * theta x =
      (Real.log (B x) - Real.log (Real.log (B x))) - lam * m x := by
    unfold theta psi
    field_simp [lam_pos.ne']
  rw [alpha, he, Real.exp_sub, Real.exp_sub,
    Real.exp_log (zero_lt_one.trans hB), Real.exp_log hlog, rho_pow_eq_exp]
  rw [neg_mul, Real.exp_neg]
  ring

lemma bandScale_pos {x : ℝ} {i : ℕ} (hi : i < m x) : 0 < bandScale x i := by
  unfold bandScale
  exact mul_pos (mul_pos (alpha_pos _) (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hi)))
    (inv_pos.mpr (pow_pos rho_pos _))

lemma fordBandScale_eq_ratio_mul {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i = bandCenterRatio x * bandScale x i := by
  have hm : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  have hpow : rho^(m x) = rho^(m x-i) * rho^i := by
    rw [← pow_add, Nat.sub_add_cancel hi.le]
  unfold fordBandScale bandCenterRatio bandScale
  rw [alpha_theta_eq hB, Nat.cast_sub hi.le, hpow]
  field_simp [hm, hl, lam_pos.ne', rho_pos.ne']

lemma fordBandScale_div_bandScale {x : ℝ} {i : ℕ}
    (hB : 1 < B x) (hi : i < m x) :
    fordBandScale x i / bandScale x i = bandCenterRatio x := by
  rw [fordBandScale_eq_ratio_mul hB hi, mul_div_cancel_right₀ _ (bandScale_pos hi).ne']

lemma B_tendsto : Tendsto B atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma m_tendsto : Tendsto m atTop atTop :=
  tendsto_nat_floor_atTop.comp (psi_tendsto.comp B_tendsto)

lemma bandCenterRatio_tendsto : Tendsto bandCenterRatio atTop (nhds 1) := by
  have hlogB : Tendsto (fun x => Real.log (B x)) atTop atTop :=
    Real.tendsto_log_atTop.comp B_tendsto
  have hsmall : Tendsto (fun x => Real.log (Real.log (B x)) / Real.log (B x))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlogB
  have hpsi : Tendsto (fun x => psi (B x) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh : Tendsto
        (fun x => (1 - Real.log (Real.log (B x)) / Real.log (B x)) / lam)
        atTop (nhds (1 / lam)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).div_const lam
    apply hh.congr'
    filter_upwards [hlogB.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    unfold psi
    field_simp [hx.ne', lam_pos.ne']
  have hfloor : Tendsto (fun x => (m x : ℝ) / psi (B x)) atTop (nhds 1) :=
    tendsto_nat_floor_div_atTop.comp (psi_tendsto.comp B_tendsto)
  have hmratio : Tendsto (fun x => (m x : ℝ) / Real.log (B x))
      atTop (nhds (1 / lam)) := by
    have hh := hfloor.mul hpsi
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [(psi_tendsto.comp B_tendsto).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    change 0 < psi (B x) at hx
    field_simp [hx.ne']
  have hlm : Tendsto (fun x => lam * ((m x : ℝ) / Real.log (B x)))
      atTop (nhds 1) := by
    simpa only [mul_one_div_cancel lam_pos.ne'] using hmratio.const_mul lam
  have hh := hlm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun x => Real.log (B x) / (lam * m x)) atTop (nhds 1)
  simpa only [inv_one, mul_inv_rev, inv_div, inv_inv, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hh

/-- The error bound is simultaneous over every retained index. -/
theorem fordBandScale_uniform_comparison {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x →
      |fordBandScale x i / bandScale x i - 1| < ε := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    Metric.tendsto_nhds.mp bandCenterRatio_tendsto ε hε] with x hB hx
  intro i hi
  rw [fordBandScale_div_bandScale hB hi]
  simpa only [Real.dist_eq] using hx

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandExtraction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-union and geometric-tail argument behind the manuscript's
`ford-bands` estimate.  Only Ford's explicitly stated Theorems 10 and 16
remain hypotheses; the summation and the passage to model bands are proved.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma preimageExceptionCount_and_le (x : ℝ) (Q R : ℕ → Prop) :
    preimageExceptionCount x (fun n => Q n ∧ R n) ≤
      preimageExceptionCount x Q + preimageExceptionCount x R := by
  classical
  have hsub : preimageExceptionValues x (fun n => Q n ∧ R n) ⊆
      preimageExceptionValues x Q ∪ preimageExceptionValues x R := by
    intro v hv
    obtain ⟨hv, n, hn, hφ, hQR⟩ := Finset.mem_filter.mp hv
    by_cases hQ : Q n
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, fun hR => hQR ⟨hQ, hR⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, hQ⟩)
  unfold preimageExceptionCount
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Normalization
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of totient counts and uniform coefficient asymptotics. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma g_pos (j : ℕ) : 0 < g j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [g]
    | succ n =>
      rw [g]
      apply Finset.sum_pos'
      · intro d hd
        exact (mul_pos (a_pos (by omega)) (ih (n-d) (by omega))).le
      · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (a_pos (by omega)) (ih n (by omega))

lemma G_pos {x : ℝ} (hx : 0 < B x) (j : ℕ) : 0 < G x j := by
  unfold G
  apply div_pos (pow_pos hx _)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos j)
    (Finset.prod_pos (fun i _ => g_pos i))

lemma scale_eventually_pos : ∀ᶠ x : ℝ in atTop,
    0 < x / Real.log x * G x (m x) := by
  have hb : Tendsto B atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ), hb.eventually (eventually_gt_atTop 0)]
    with x hx hB
  exact mul_pos (div_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)) (G_pos hB _)

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConvolution
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The dominated convolution limit needed for the finite-tail volume asymptotic.
The sole published input here is Ford's bounded renewal error, Lemma 3.7 of
*The distribution of totients*, arXiv:1104.3264v2 (2013), with Ford's constant
lambda denoted by gamma in this development.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_properties (hford : FordRenewalInput) :
    Tendsto normalizedRenewal atTop (nhds gamma) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖normalizedRenewal n‖ ≤ K := by
  obtain ⟨C, hC, herr⟩ := hford
  have hb (n : ℕ) : |normalizedRenewal n-gamma| ≤ C*rho^n := by
    have he : normalizedRenewal n-gamma = (g n-gamma*(rho^n)⁻¹)*rho^n := by
      unfold normalizedRenewal
      field_simp [rho_pos.ne']
    rw [he, abs_mul, abs_of_pos (pow_pos rho_pos _)]
    exact mul_le_mul_of_nonneg_right (herr n) (pow_nonneg rho_pos.le _)
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (g := fun n => C*rho^n) (fun n => dist_nonneg) ?_ ?_
    · intro n
      simpa only [Real.dist_eq] using hb n
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  · refine ⟨gamma+C, add_nonneg gamma_pos.le hC, fun n => ?_⟩
    have hg : 0 ≤ normalizedRenewal n := mul_nonneg (g_pos n).le (pow_nonneg rho_pos.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hg]
    have hpow : rho^n ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
    have h := (abs_le.mp (hb n)).2
    nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailRenewal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized finite-tail budget and its renewal-convolution limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma alpha_ge_lam {s : ℝ} (hs : 0 ≤ s) : lam ≤ alpha s := by
  unfold alpha
  have he : 1 ≤ Real.exp (lam*s) := Real.one_le_exp (mul_nonneg lam_pos.le hs)
  nlinarith [lam_pos]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Prefactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-tail prefactor, including its dependence on the moving phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma G_step {x : ℝ} (hB : 0 < B x) (j : ℕ) :
    G x j = ((j+1 : ℝ)*g (j+1)/B x)*G x (j+1) := by
  have hp : (∏ i ∈ Finset.Icc 1 j, g i) ≠ 0 :=
    (Finset.prod_pos (fun i _ => g_pos i)).ne'
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hj : (j+1 : ℝ) ≠ 0 := by positivity
  unfold G
  rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hB.ne', hp, hf, hj, (g_pos (j+1)).ne']

lemma G_sub_eq_product {x : ℝ} (hB : 0 < B x) (n H : ℕ) (hH : H ≤ n) :
    G x (n-H) = G x n *
      ∏ k ∈ Finset.range H, ((n-k : ℕ) : ℝ)*g (n-k)/B x := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hH' : H ≤ n := by omega
    have hidx : n-(H+1)+1 = n-H := by omega
    have hcast : ((n-(H+1) : ℕ) : ℝ)+1 = ((n-H : ℕ) : ℝ) := by
      exact_mod_cast hidx
    rw [G_step hB (n-(H+1)), hidx, ih hH', Finset.prod_range_succ]
    rw [hcast]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordFactorization
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical finite prime-factor decomposition for the Ford coordinates. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordPrime_eq_get {n i : ℕ} (hi : i < n.primeFactorsList.length) :
    fordPrime n i = n.primeFactorsList.reverse[i]'(by simpa using hi) := by
  unfold fordPrime
  rw [show n.primeFactorsList.reverse[i]? = some (n.primeFactorsList.reverse[i]'(by simpa using hi)) from
    List.getElem?_eq_getElem _]
  rfl

lemma fordPrime_prime {n i : ℕ} (hi : i < n.primeFactorsList.length) : (fordPrime n i).Prime := by
  rw [fordPrime_eq_get hi]
  exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.getElem_mem _))

lemma fordPrime_antitone {n i j : ℕ} (hi : i < n.primeFactorsList.length)
    (hj : j < n.primeFactorsList.length) (hij : i ≤ j) : fordPrime n j ≤ fordPrime n i := by
  rw [fordPrime_eq_get hi,fordPrime_eq_get hj]
  exact (Nat.primeFactorsList_sorted n).reverse.getElem_ge_getElem_of_le hij

lemma fordPrime_index_of_doubleLog_pos {n i : ℕ} (h : 0 < primeDoubleLog n i) :
    i < n.primeFactorsList.length := by
  by_contra! hi
  have he : fordPrime n i=1 := by
    unfold fordPrime
    rw [show n.primeFactorsList.reverse[i]? = none from List.getElem?_eq_none (by simpa using hi)]
    rfl
  simp [primeDoubleLog,he] at h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous bound for all projected prefix volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma inverse_scale_eq {x : ℝ} (hB : 1 < B x) (hm : 0 < m x) :
    (m x : ℝ)/(B x*rho^(m x)) = (alpha (theta x)*bandCenterRatio x)⁻¹ := by
  rw [alpha_theta_eq hB]
  unfold bandCenterRatio
  field_simp [(Real.log_pos hB).ne', (zero_lt_one.trans hB).ne',
    lam_pos.ne', Nat.cast_ne_zero.mpr hm.ne', rho_pos.ne']

lemma inverse_scale_bound : ∀ᶠ x : ℝ in atTop,
    (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam := by
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0),
    bandCenterRatio_tendsto.eventually
      (eventually_gt_nhds (show (1/2 : ℝ) < 1 by norm_num))] with x hx hB hm hv
  rw [inverse_scale_eq hB hm]
  have ha := alpha_ge_lam hx.1
  have hprod : lam/2 ≤ alpha (theta x)*bandCenterRatio x := by
    nlinarith [lam_pos, alpha_pos (theta x)]
  calc
    _ ≤ (lam/2)⁻¹ := inv_anti₀ (div_pos lam_pos (by norm_num)) hprod
    _ = _ := by ring

lemma uniform_step_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ i ≤ m x,
      ((m x-i : ℕ) : ℝ)*g (m x-i)/B x ≤ C*rho^i := by
  obtain ⟨_, K, hK, hg⟩ := normalizedRenewal_properties hford
  let C := 2*(K+1)/lam
  refine ⟨C, div_pos (mul_pos (by norm_num) (by linarith)) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro i hi
  have hgn : g (m x-i)*rho^(m x-i) ≤ K+1 := by
    have hh := hg (m x-i)
    change |g (m x-i)*rho^(m x-i)| ≤ K at hh
    exact (le_abs_self _).trans (hh.trans (by linarith))
  have hg' : g (m x-i) ≤ (K+1)/rho^(m x-i) :=
    (le_div_iff₀ (pow_pos rho_pos _)).mpr hgn
  have hm' : ((m x-i : ℕ) : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) i
  have hpow : rho^(m x-i)*rho^i = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  calc
    _ ≤ (m x : ℝ)*((K+1)/rho^(m x-i))/B x := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul hm' hg' (g_pos _).le (Nat.cast_nonneg _)
    _ = ((K+1)*((m x : ℝ)/(B x*rho^(m x))))*rho^i := by
      rw [← hpow]
      field_simp [rho_pos.ne']
    _ ≤ ((K+1)*(2/lam))*rho^i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by linarith))
        (pow_nonneg rho_pos.le _)
    _ = C*rho^i := by dsimp [C] <;> ring

/-- Ford's bounded renewal error yields the manuscript's simultaneous
projected-volume majorant, including prefixes whose length moves with `x`. -/
theorem uniform_projected_volume_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      G x (m x-H)/G x (m x) ≤ C^H*rho^(H*(H-1)/2) := by
  obtain ⟨C, hC, hstep⟩ := uniform_step_bound hford
  refine ⟨C, hC, ?_⟩
  filter_upwards [hstep, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hB
  intro H hH
  rw [G_sub_eq_product hB (m x) H hH, mul_div_cancel_left₀ _ (G_pos hB _).ne']
  calc
    _ ≤ ∏ i ∈ Finset.range H, C*rho^i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le) hB.le
      · intro i hi
        exact hx i (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCofactorStep
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of the ordered largest primes, including short factorizations. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_pos (n k : ℕ) : 0 < fordPrime n k := by
  by_cases hk : k < n.primeFactorsList.length
  · exact (fordPrime_prime hk).pos
  · unfold fordPrime
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    norm_num

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalConcavity
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete concavity of the coefficients in Ford's renewal recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_shift_integral (j k : ℕ) :
    a (j+k)=∫ t in (j : ℝ)..(j+1 : ℝ), Real.log (t+k) := by
  rw [a_eq_integral,intervalIntegral.integral_comp_add_right]
  push_cast
  congr 1
  ring

lemma log_shift_intervalIntegrable {j : ℕ} (hj : 1≤j) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.log (t+k)) MeasureTheory.volume j (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
  intro t ht
  have hn : t+(k : ℝ)≠0 := by
    have hk : (0 : ℝ)≤k := Nat.cast_nonneg _
    linarith [ht.1]
  exact ((continuousAt_id.add continuousAt_const).log hn).continuousWithinAt

lemma log_second_difference_pos {t : ℝ} (ht : 0<t) :
    0<2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
  have ht2 : 0<t+2 := by linarith
  have hh := Real.log_lt_log (mul_pos ht ht2)
    (show t*(t+2)<(t+1)^2 by nlinarith)
  rw [Real.log_mul ht.ne' ht2.ne',Real.log_pow] at hh
  norm_num at hh
  linarith

/-- The strict second difference used in Ford Lemma 3.7. -/
lemma a_second_difference_neg {j : ℕ} (hj : 1≤j) :
    a (j+2)-2*a (j+1)+a j<0 := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hc : ContinuousOn
      (fun t : ℝ => 2*Real.log (t+1)-(Real.log t+Real.log (t+2)))
      (Set.Icc (j : ℝ) (j+1)) := by
    intro t ht
    have ht0 : t≠0 := by linarith [ht.1]
    have ht1 : t+1≠0 := by linarith [ht.1]
    have ht2 : t+2≠0 := by linarith [ht.1]
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht1)).sub
      ((continuousAt_id.log ht0).add ((continuousAt_id.add continuousAt_const).log ht2))).continuousWithinAt
  have hi : 0<∫ t in (j : ℝ)..(j+1 : ℝ),
      2*Real.log (t+1)-(Real.log t+Real.log (t+2)) := by
    apply intervalIntegral.integral_pos (by linarith) hc
    · intro t ht
      exact (log_second_difference_pos (by linarith [ht.1])).le
    · refine ⟨j+1,⟨by linarith,le_rfl⟩,?_⟩
      exact log_second_difference_pos (by linarith)
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have h2 := log_shift_intervalIntegrable hj 2
  have he1 := a_shift_integral j 1
  have he2 := a_shift_integral j 2
  simp only [Nat.cast_one,Nat.cast_ofNat] at h1 h2 he1 he2
  simp only [Nat.cast_zero,add_zero] at h0
  rw [intervalIntegral.integral_sub (h1.const_mul 2) (h0.add h2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_add h0 h2,
    ← he1,← he2,← a_eq_integral j] at hi
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeparation
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small root separation for the sign of Ford's transformed coefficients. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalSeries_three_sevenths_lt_one : renewalSeries (3/7)<1 := by
  let r : ℝ := 3/7
  have hr0 : 0 ≤ r := by norm_num [r]
  have hr1 : r<1 := by norm_num [r]
  have hs := summable_renewal hr0 hr1
  have hg := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := r) (by norm_num [r])
  have hsg : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1)) (21/16 : ℝ) := by
    have h2 := hg.mul_right r
    have e1 : (fun i : ℕ => (((i + 1).choose 1 : ℕ) : ℝ) * r ^ i * r) =
        fun n : ℕ => ((n+1 : ℕ) : ℝ)*r^(n+1) := by
      ext n
      simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,pow_succ]
      ring
    have e2 : (1 / (1 - r) ^ (1 + 1)) * r = (21/16 : ℝ) := by norm_num [r]
    rw [e1, e2] at h2
    exact h2
  have htail : (∑' n : ℕ, a (n+2+1)*r^(n+2+1)) ≤
      ∑' n : ℕ, ((n+2+1 : ℕ) : ℝ)*r^(n+2+1) := by
    apply ((summable_nat_add_iff 2).mpr hs).tsum_le_tsum
    · intro n
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast a_le_index (j := n+2+1) (by omega)) (pow_nonneg hr0 _)
    · exact (summable_nat_add_iff 2).mpr hsg.summable
  have hf := hs.sum_add_tsum_nat_add 2
  have hi := hsg.summable.sum_add_tsum_nat_add 2
  rw [hsg.tsum_eq] at hi
  change _=renewalSeries r at hf
  norm_num [Finset.sum_range_succ,r] at hf hi htail
  have ha1 : a 1<1/2 := by
    norm_num [a]
    linarith [Real.log_two_lt_d9]
  have ha2 : a 2<1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  change renewalSeries r<1
  nlinarith

lemma rho_gt_three_sevenths : (3/7 : ℝ) < rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho∈Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩)
    (show (3/7 : ℝ)∈Set.Ico (0 : ℝ) 1 by norm_num) hh
  rw [renewalSeries_rho] at hm
  linarith [renewalSeries_three_sevenths_lt_one]

lemma renewal_first_transformed_negative : rho⁻¹-a 1-2<0 := by
  have hr : rho⁻¹<(7/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_sevenths]
  have ha : (1/3 : ℝ)<a 1 := by
    norm_num [a]
    linarith [Real.log_two_gt_d9]
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalTail
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail coefficients in (1-F(z))/(1-z/rho). -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma a_le_a_succ {j : ℕ} (hj : 1≤j) : a j≤a (j+1) := by
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have h0 := log_shift_intervalIntegrable hj 0
  have h1 := log_shift_intervalIntegrable hj 1
  have he1 := a_shift_integral j 1
  simp only [Nat.cast_zero,add_zero] at h0
  simp only [Nat.cast_one] at h1 he1
  rw [a_eq_integral,he1]
  apply intervalIntegral.integral_mono_on (by linarith) h0 h1
  intro t ht
  apply Real.log_le_log (by linarith [ht.1])
  linarith

lemma summable_renewalTail (n : ℕ) :
    Summable (fun k : ℕ => a (n+k+1)*rho^(k+1)) := by
  have hgeo : Summable (fun k : ℕ => rho^(k+1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one rho_pos.le rho_lt_one)
  have hmajor := (hgeo.mul_left (n : ℝ)).add
    (summable_index_geometric rho_pos.le rho_lt_one 1)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le) _ hmajor
  intro k
  have hh := mul_le_mul_of_nonneg_right (a_le_index (j := n+k+1) (by omega))
    (pow_pos rho_pos (k+1)).le
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma renewalTail_zero : renewalTail 0=1 := by
  simpa only [renewalTail,Nat.zero_add,renewalSeries] using renewalSeries_rho

lemma renewalTail_nonneg (n : ℕ) : 0 ≤ renewalTail n :=
  tsum_nonneg (fun k => mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le)

lemma renewalTail_le_succ (n : ℕ) : renewalTail n ≤ renewalTail (n+1) := by
  apply (summable_renewalTail n).tsum_le_tsum _ (summable_renewalTail (n+1))
  intro k
  apply mul_le_mul_of_nonneg_right _ (pow_pos rho_pos _).le
  convert a_le_a_succ (j := n+k+1) (by omega) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

lemma renewalTail_recurrence (n : ℕ) :
    renewalTail n=rho*a (n+1)+rho*renewalTail (n+1) := by
  have hs := (summable_renewalTail n).sum_add_tsum_nat_add 1
  have he : (∑' k : ℕ, a (n+(k+1)+1)*rho^(k+1+1))=rho*renewalTail (n+1) := by
    rw [renewalTail,← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    have hn : n+(k+1)+1=(n+1)+k+1 := by omega
    rw [hn]
    ring
  change _=renewalTail n at hs
  simp only [Finset.sum_range_one,Nat.add_zero,Nat.zero_add,pow_one] at hs
  rw [he] at hs
  simpa only [mul_comm] using hs.symm

lemma renewalTail_second_difference_neg (n : ℕ) :
    renewalTail (n+2)-2*renewalTail (n+1)+renewalTail n<0 := by
  have hs0 := summable_renewalTail n
  have hs1 := summable_renewalTail (n+1)
  have hs2 := summable_renewalTail (n+2)
  have he : renewalTail (n+2)+renewalTail n<2*renewalTail (n+1) := by
    rw [renewalTail,renewalTail,renewalTail,← hs2.tsum_add hs0,← tsum_mul_left]
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      have hd := a_second_difference_neg (j := n+k+1) (by omega)
      have hpow := pow_pos rho_pos (k+1)
      have he1 : n+k+1+1=n+1+k+1 := by omega
      have he2 : n+k+1+2=n+2+k+1 := by omega
      rw [he1,he2] at hd
      nlinarith
    · have hd := a_second_difference_neg (j := n+1) (by omega)
      simp only [Nat.add_zero,Nat.zero_add,pow_one]
      have he1 : n+1+1=n+2 := by omega
      rw [he1] at hd
      have hp := mul_lt_mul_of_pos_right hd rho_pos
      nlinarith [hp]
    · exact hs2.add hs0
    · exact hs1.mul_left 2
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMoment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of the tail generating series at its renewal root. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma momentPair_nonneg (p : ℕ×ℕ) : 0 ≤ momentPair p :=
  mul_nonneg (a_pos (by omega)).le (pow_pos rho_pos _).le

private lemma momentPair_diagonal (n : ℕ) :
    (∑ p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p)=
      (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
  rw [Finset.sum_coe_sort]
  have he : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, momentPair p)=
      ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal n, a (n+1)*rho^(n+1) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [momentPair,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

private lemma summable_momentPair : Summable momentPair := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hs : Summable (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2) := by
    apply (summable_sigma_of_nonneg
      (f := fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) => momentPair p.2)
      (fun p => momentPair_nonneg p.2)).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,momentPair_diagonal] using summable_moment
  exact e.summable_iff.mp hs

lemma renewalTail_weighted_sum :
    Summable (fun n : ℕ => renewalTail n*rho^n) ∧
      (∑' n : ℕ, renewalTail n*rho^n)=gamma⁻¹ := by
  let e : (Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n)) ≃ ℕ×ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have he (n : ℕ) : renewalTail n*rho^n=∑' k : ℕ, momentPair (n,k) := by
    rw [renewalTail,← tsum_mul_right]
    apply tsum_congr
    intro k
    dsimp [momentPair]
    rw [mul_assoc,← pow_add]
    congr 2
    omega
  have hsum := (summable_prod_of_nonneg momentPair_nonneg).mp summable_momentPair
  refine ⟨?_,?_⟩
  · simpa only [he] using hsum.2
  · calc
      _ = ∑' n : ℕ, ∑' k : ℕ, momentPair (n,k) := tsum_congr he
      _ = ∑' p : ℕ×ℕ, momentPair p := summable_momentPair.tsum_prod.symm
      _ = ∑' p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p.2 :=
        (e.tsum_eq momentPair).symm
      _ = ∑' n : ℕ, ∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n), momentPair p :=
        (e.summable_iff.mpr summable_momentPair).tsum_sigma
      _ = ∑' n : ℕ, (n+1 : ℝ)*a (n+1)*rho^(n+1) := by
        apply tsum_congr
        intro n
        rw [tsum_fintype,momentPair_diagonal]
      _ = gamma⁻¹ := by simp [gamma]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalKernel
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative transformed kernel in Ford's renewal argument. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewalIncrement_nonneg (n : ℕ) : 0 ≤ renewalIncrement n :=
  sub_nonneg.mpr (renewalTail_le_succ n)

lemma renewalKernel_pos (n : ℕ) : 0 < renewalKernel n := by
  cases n with
  | zero =>
    have hh := renewalTail_recurrence 0
    rw [renewalTail_zero] at hh
    have he : renewalTail 1=rho⁻¹-a 1 := by
      apply (mul_left_cancel₀ rho_pos.ne')
      calc
        rho*renewalTail 1=1-rho*a 1 := by linarith
        _ = rho*(rho⁻¹-a 1) := by field_simp [rho_pos.ne']
    simpa only [renewalKernel,renewalIncrement,renewalTail_zero,he] using
      (show 0<1-((rho⁻¹-a 1)-1) by linarith [renewal_first_transformed_negative])
  | succ n =>
    have hh := renewalTail_second_difference_neg n
    change 0<(renewalTail (n+1)-renewalTail n)-
      (renewalTail (n+1+1)-renewalTail (n+1))
    have he : n+1+1=n+2 := by omega
    rw [he]
    linarith

lemma renewalKernel_partial_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalKernel j)=1-renewalIncrement n := by
  induction n with
  | zero => simp [renewalKernel]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,renewalKernel]
    ring

lemma renewalKernel_sum_le_one (n : ℕ) :
    (∑ j ∈ Finset.range n, renewalKernel j)≤1 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [renewalKernel_partial_sum]
    linarith [renewalIncrement_nonneg n]

lemma renewalResolvent_bounds (n : ℕ) : 0 ≤ renewalResolvent n ∧ renewalResolvent n≤1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [renewalResolvent]
    | succ n =>
      have hindex (j : ℕ) (hj : j∈Finset.range (n+1)) : n-j<n+1 := by omega
      constructor
      · rw [renewalResolvent]
        exact Finset.sum_nonneg (fun j hj => mul_nonneg (renewalKernel_pos j).le
          (ih (n-j) (hindex j hj)).1)
      · rw [renewalResolvent]
        calc
          _ ≤ ∑ j ∈ Finset.range (n+1), renewalKernel j := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_of_le_one_right (renewalKernel_pos j).le (ih (n-j) (hindex j hj)).2
          _ ≤ 1 := renewalKernel_sum_le_one (n+1)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalSeriesAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal coefficient identities for Ford's transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma U_kernel_identity : Useries*(1-PowerSeries.X*Pseries)=1 := by
  have he : Useries*(1-PowerSeries.X*Pseries)=Useries-PowerSeries.X*(Pseries*Useries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Useries,renewalResolvent]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,Pseries,renewalResolvent,sub_self]

private lemma kernel_factorization : (1-PowerSeries.X)^2*Lseries=1-PowerSeries.X*Pseries := by
  have he : (1-PowerSeries.X)^2*Lseries=
      Lseries-PowerSeries.X*Lseries-PowerSeries.X*Lseries+
        PowerSeries.X*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,renewalTail_zero]
  | succ n =>
    cases n with
    | zero =>
      simp [PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,Lseries,Pseries,
        renewalKernel,renewalIncrement,renewalTail_zero]
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Lseries,Pseries,
        PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false,
        renewalKernel,renewalIncrement]
      ring

private lemma L_H_identity : Lseries*Hseries=1 := by
  calc
    _ = Useries*((1-PowerSeries.X)^2*Lseries) := by dsimp [Hseries] <;> ring
    _ = Useries*(1-PowerSeries.X*Pseries) := by rw [kernel_factorization]
    _ = 1 := U_kernel_identity

private lemma L_A_identity : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=1-Aseries := by
  have he : (1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries=
      Lseries-PowerSeries.C rho⁻¹*(PowerSeries.X*Lseries) := by ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Lseries,Aseries,renewalTail_zero]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,Lseries,Aseries,
      PowerSeries.coeff_mk,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    have he := renewalTail_recurrence n
    have hh : rho⁻¹*renewalTail n=a (n+1)+renewalTail (n+1) := by
      rw [he]
      field_simp [rho_pos.ne']
    linarith

private lemma G_A_identity : Gseries*(1-Aseries)=1 := by
  have he : Gseries*(1-Aseries)=Gseries-PowerSeries.X*(PowerSeries.mk (fun n => a (n+1))*Gseries) := by
    dsimp [Aseries]
    ring
  rw [he]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [Gseries,g]
  | succ n =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,Gseries,PowerSeries.coeff_mk,
      PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false, if_false]
    rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk,g,sub_self]

private lemma G_H_identity : Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)=Hseries := by
  calc
    _ = Gseries*(1-PowerSeries.C rho⁻¹*PowerSeries.X)*(Lseries*Hseries) := by rw [L_H_identity,mul_one]
    _ = (Gseries*((1-PowerSeries.C rho⁻¹*PowerSeries.X)*Lseries))*Hseries := by ring
    _ = (Gseries*(1-Aseries))*Hseries := by rw [L_A_identity]
    _ = Hseries := by rw [G_A_identity,one_mul]

lemma renewalRegular_bound (n : ℕ) : |renewalRegular n|≤4 := by
  have he : Hseries=Useries-PowerSeries.X*Useries-PowerSeries.X*Useries+
        PowerSeries.X*(PowerSeries.X*Useries) := by dsimp [Hseries] <;> ring
  rw [renewalRegular,he]
  cases n with
  | zero => norm_num [PowerSeries.coeff_zero_X_mul,Useries,renewalResolvent]
  | succ n =>
    cases n with
    | zero =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_zero_X_mul,
        Useries,PowerSeries.coeff_mk]
      norm_num only [show renewalResolvent 0=1 by rw [renewalResolvent],zero_add,add_zero]
      have hb := renewalResolvent_bounds 1
      rw [abs_le]
      constructor <;> linarith
    | succ n =>
      simp only [map_add,map_sub,PowerSeries.coeff_succ_X_mul,Useries,PowerSeries.coeff_mk]
      have h0 := renewalResolvent_bounds n
      have h1 := renewalResolvent_bounds (n+1)
      have h2 := renewalResolvent_bounds (n+1+1)
      rw [abs_le]
      constructor <;> linarith

lemma renewalRegular_zero : renewalRegular 0=1 := by
  simp [renewalRegular,Hseries,Useries,renewalResolvent]

lemma renewalRegular_recurrence (n : ℕ) :
    renewalRegular (n+1)=g (n+1)-rho⁻¹*g n := by
  have h := congrArg (PowerSeries.coeff (n+1)) G_H_identity
  rw [mul_sub,mul_one] at h
  have he : Gseries*(PowerSeries.C rho⁻¹*PowerSeries.X)=
      PowerSeries.C rho⁻¹*(Gseries*PowerSeries.X) := by ring
  rw [he] at h
  simpa only [map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_mul_X,Gseries,
    PowerSeries.coeff_mk,renewalRegular] using h.symm

lemma renewalTail_regular_convolution (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))=
      if n=0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff n) L_H_identity
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Lseries,PowerSeries.coeff_mk,renewalRegular,PowerSeries.coeff_one] using h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalRegularSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constant term at the renewal pole, using absolutely convergent sums. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma summable_norm_regular_weighted :
    Summable (fun n : ℕ => ‖renewalRegular n*rho^n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left 4)
  intro n
  rw [norm_mul,Real.norm_eq_abs (rho^n),abs_of_pos (pow_pos rho_pos n),Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (renewalRegular_bound n) (pow_pos rho_pos n).le

lemma regular_weighted_sum_eq_gamma :
    (∑' n : ℕ, renewalRegular n*rho^n)=gamma := by
  have hL : Summable (fun n : ℕ => ‖renewalTail n*rho^n‖) := by
    convert renewalTail_weighted_sum.1 using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact Real.norm_of_nonneg (mul_nonneg (renewalTail_nonneg n) (pow_pos rho_pos n).le)
  have ht := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hL summable_norm_regular_weighted
  have he (n : ℕ) : (∑ j ∈ Finset.range (n+1),
      (renewalTail j*rho^j)*(renewalRegular (n-j)*rho^(n-j)))=
      if n=0 then 1 else 0 := by
    calc
      _ = (∑ j ∈ Finset.range (n+1), renewalTail j*renewalRegular (n-j))*rho^n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
        have hp : rho^j*rho^(n-j)=rho^n := by rw [← pow_add,Nat.add_sub_of_le hjn]
        calc
          _ = (renewalTail j*renewalRegular (n-j))*(rho^j*rho^(n-j)) := by ring
          _ = _ := by rw [hp]
      _ = _ := by rw [renewalTail_regular_convolution]; split_ifs with hn <;> simp [hn]
  simp only [he] at ht
  rw [renewalTail_weighted_sum.2] at ht
  have hs : (∑' n : ℕ, if n=0 then (1 : ℝ) else 0)=1 := by simp
  rw [hs] at ht
  have hmul := congrArg (fun x : ℝ => gamma*x) ht
  simpa only [← mul_assoc,mul_inv_cancel₀ gamma_pos.ne',one_mul,mul_one] using hmul

lemma normalized_renewal_eq_regular_partial (n : ℕ) :
    g n*rho^n=∑ j ∈ Finset.range (n+1), renewalRegular j*rho^j := by
  induction n with
  | zero => simp [g,renewalRegular_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih,renewalRegular_recurrence,pow_succ]
    field_simp [rho_pos.ne']
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalInput
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of Ford Lemma 3.7 by the concrete transformed recurrence. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

private lemma regular_tail_bound (n : ℕ) :
    |∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)|≤4*rho/(1-rho) := by
  have hg : HasSum (fun k : ℕ => 4*rho^(k+1)) (4*rho/(1-rho)) := by
    have h2 := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).mul_left (4*rho)
    have e1 : (fun k : ℕ => 4*rho * rho^k) = fun k : ℕ => 4*rho^(k+1) := by
      ext k
      rw [pow_succ]
      ring
    have e2 : 4*rho*(1-rho)⁻¹ = 4*rho/(1-rho) := by rw [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  have hb (k : ℕ) : ‖renewalRegular (k+n+1)*rho^(k+1)‖≤4*rho^(k+1) := by
    rw [norm_mul,Real.norm_eq_abs (rho^(k+1)),abs_of_pos (pow_pos rho_pos _),Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (renewalRegular_bound _) (pow_pos rho_pos _).le
  have hs : Summable (fun k : ℕ => ‖renewalRegular (k+n+1)*rho^(k+1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hg.summable
  calc
    _ = ‖∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖renewalRegular (k+n+1)*rho^(k+1)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, 4*rho^(k+1) := hs.tsum_le_tsum hb hg.summable
    _ = _ := hg.tsum_eq

/-- The bounded renewal error assumed throughout the conditional development
is now proved. A coarse explicit constant suffices for every application. -/
theorem fordRenewalInput : FordRenewalInput := by
  refine ⟨4*rho/(1-rho),div_nonneg (mul_nonneg (by norm_num) rho_pos.le) (by linarith [rho_lt_one]),?_⟩
  intro n
  have hp : rho^n≠0 := (pow_pos rho_pos n).ne'
  have hs := summable_norm_regular_weighted.of_norm.sum_add_tsum_nat_add (n+1)
  rw [regular_weighted_sum_eq_gamma,← normalized_renewal_eq_regular_partial n] at hs
  have he : (∑' k : ℕ, renewalRegular (k+(n+1))*rho^(k+(n+1)))=
      (∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1))*rho^n := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro k
    have hpow : rho^(k+(n+1))=rho^(k+1)*rho^n := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hn : k+(n+1)=k+n+1 := by omega
    rw [hn]
    ring
  rw [he] at hs
  have herror : g n-gamma*(rho^n)⁻¹= -∑' k : ℕ, renewalRegular (k+n+1)*rho^(k+1) := by
    apply (mul_right_cancel₀ hp)
    calc
      (g n-gamma*(rho^n)⁻¹)*rho^n=g n*rho^n-gamma := by field_simp
      _ = _ := by nlinarith [hs]
  rw [herror,abs_neg]
  exact regular_tail_bound n

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ThirdPrimeSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complement of the two-coordinate exception has a small third prime. -/
noncomputable section
namespace TotientAsymptotic

lemma ford_coordinate_antitone (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    fordPrimeCoordinate n j ≤ fordPrimeCoordinate n i := by
  by_cases hj : j < n.primeFactorsList.length
  · have hi : i < n.primeFactorsList.length := by omega
    have hp := fordPrime_prime hj
    have horder := fordPrime_antitone hi hj hij
    have hB : primeDoubleLog n j ≤ primeDoubleLog n i :=
      Real.log_le_log (Real.log_pos (by exact_mod_cast hp.one_lt))
        (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast horder))
    exact max_le_max le_rfl hB
  · have he : fordPrime n j=1 := by
      unfold fordPrime
      rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hj)]
      rfl
    simp only [fordPrimeCoordinate,primeDoubleLog,he,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstFailedRow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first failed row strictly separates the retained primes from the tail. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma clamped_doubleLog_mono {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    max 0 (Real.log (Real.log (p:ℝ))) ≤ max 0 (Real.log (Real.log (q:ℝ))) := by
  by_cases hp1 : p=1
  · simp only [hp1,Nat.cast_one,Real.log_one,Real.log_zero,max_self]
    exact le_max_left _ _
  · have hp' : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos hp')
    exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpq)

lemma fordPrime_lt_of_coordinate_lt {n i j : ℕ}
    (h : fordPrimeCoordinate n i < fordPrimeCoordinate n j) :
    fordPrime n i < fordPrime n j := by
  by_contra hh
  have hh := clamped_doubleLog_mono (fordPrime_pos n j) (Nat.le_of_not_gt hh)
  exact (not_lt_of_ge hh) h

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FailedRowPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual prime prefix before a first failed row belongs to the unbanded simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma fordRowSum_truncate {K L j : ℕ} (hKL : K ≤ L) (u : ℕ → ℝ)
    (hu : ∀ r, 0 ≤ u r) : fordRowSum K u j ≤ fordRowSum L u j := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    have hr := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.trans hKL⟩
  · intro r hr _
    have hr := Finset.mem_Icc.mp hr
    exact mul_nonneg (a_pos (by omega)).le (hu r)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedModelTransfer
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five-percent Ford interval lies inside the ten-percent model
interval once the uniform center ratio is sufficiently close to one. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_model_band_failure_transfer : ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ,i < m x → ∀ u : ℝ,
    (u < (9/10:ℝ)*bandScale x i ∨ (11/10:ℝ)*bandScale x i < u) →
    (u < (19/20:ℝ)*fordBandScale x i ∨ (21/20:ℝ)*fordBandScale x i < u) := by
  filter_upwards [fordBandScale_uniform_comparison (ε:=1/25) (by norm_num)] with x hx
  intro i hi u hu
  have hs := bandScale_pos hi
  have hr := abs_lt.mp (hx i hi)
  have hlo : (24/25:ℝ)*bandScale x i < fordBandScale x i := by
    have hh := (lt_div_iff₀ hs).mp (show (24/25:ℝ) < fordBandScale x i/bandScale x i by linarith only [hr.1])
    linarith only [hh]
  have hhi : fordBandScale x i < (26/25:ℝ)*bandScale x i := by
    have hh := (div_lt_iff₀ hs).mp (show fordBandScale x i/bandScale x i < (26/25:ℝ) by linarith only [hr.2])
    linarith only [hh]
  rcases hu with hu|hu
  · left
    nlinarith only [hu,hlo,hs]
  · right
    nlinarith only [hu,hhi,hs]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexFullRows
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the full natural dimension, Ford's special final row implies the full row. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_simplex_full_rows {x : ℝ} {n : ℕ}
    (hs : fordSimplexCondition x 0 n) :
    ∀ i < m x,fordRowSum (m x) (fordPrimeCoordinate n) i ≤
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i) := by
  intro i hi
  have hh := hs.2.2 i (Finset.mem_Ico.mpr ⟨Nat.zero_le _,by simpa using hi⟩)
  simp only [Nat.sub_zero] at hh
  have hlast : fordSimplexCoordinate x n (m x)=fordPrimeCoordinate n (m x) := by
    rw [fordSimplexCoordinate,ite_eq_right (by omega : m x≠0)]
  by_cases he : i+1=m x
  · rw [ite_eq_left he,hlast] at hh
    have hrow : fordRowSum (m x) (fordPrimeCoordinate n) i=
        a 1*fordPrimeCoordinate n (m x) := by
      unfold fordRowSum
      rw [he,Finset.Icc_self,Finset.sum_singleton,show m x-i=1 by omega]
    rw [hrow]
    have hbound : a 1*fordPrimeCoordinate n (m x) ≤ fordPrimeCoordinate n (m x) := by
      have hh := mul_le_mul_of_nonneg_right (a_le_index (j:=1) le_rfl)
        (show 0 ≤ fordPrimeCoordinate n (m x) from le_max_left _ _)
      simpa using hh
    exact hbound.trans hh
  · rw [ite_eq_right he] at hh
    have hsum : (∑ r ∈ Finset.Icc (i+1) (m x),a (r-i)*fordSimplexCoordinate x n r)=
        fordRowSum (m x) (fordPrimeCoordinate n) i := by
      unfold fordRowSum
      apply Finset.sum_congr rfl
      intro r hr
      rw [fordSimplexCoordinate,ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega : r≠0)]
    rwa [hsum] at hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordTruncatedRows
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A truncated Ford simplex gives the complete row sums up to its own
terminal index, which suffices for the retained prime-prefix count. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_simplex_truncated_rows {x : ℝ} {H n : ℕ}
    (hs : fordSimplexCondition x H n) :
    ∀ i < m x-H,fordRowSum (m x-H) (fordPrimeCoordinate n) i ≤ 
      xi x i*(if i=0 then B x else fordPrimeCoordinate n i) := by
  intro i hi
  have hh := hs.2.2 i (Finset.mem_Ico.mpr ⟨Nat.zero_le _,hi⟩)
  have hlast : fordSimplexCoordinate x n (m x-H)=fordPrimeCoordinate n (m x-H) := by
    rw [fordSimplexCoordinate,ite_eq_right (by omega : m x-H≠0)]
  by_cases he : i+1=m x-H
  · rw [ite_eq_left he,hlast] at hh
    have hrow : fordRowSum (m x-H) (fordPrimeCoordinate n) i=
        a 1*fordPrimeCoordinate n (m x-H) := by
      unfold fordRowSum
      rw [he,Finset.Icc_self,Finset.sum_singleton,show m x-H-i=1 by omega]
    rw [hrow]
    have hbound : a 1*fordPrimeCoordinate n (m x-H) ≤ fordPrimeCoordinate n (m x-H) := by
      simpa using mul_le_mul_of_nonneg_right (a_le_index (j:=1) le_rfl)
        (show 0 ≤ fordPrimeCoordinate n (m x-H) from le_max_left _ _)
    exact hbound.trans hh
  · rw [ite_eq_right he] at hh
    have hsum : (∑ r∈Finset.Icc (i+1) (m x-H),a (r-i)*fordSimplexCoordinate x n r)=
        fordRowSum (m x-H) (fordPrimeCoordinate n) i := by
      unfold fordRowSum
      apply Finset.sum_congr rfl
      intro r hr
      rw [fordSimplexCoordinate,ite_eq_right (by
        have := (Finset.mem_Icc.mp hr).1
        omega : r≠0)]
    rw [hsum] at hh
    simpa only [fordSimplexCoordinate] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalPrimeGap
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A valid Ford row forbids three consecutive equal positive coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_first_two_coefficient_sum : (32/25:ℝ) ≤ a 1+a 2 := by
  have he : a 1+a 2=3*Real.log 3-2 := by norm_num [a] <;> ring
  rw [he]
  linarith [Real.log_three_gt_d9]

lemma ford_row_forbids_flat_triple {x : ℝ} {n L i : ℕ}
    (hi : i+2 ≤ L) (hpos : 0 < fordPrimeCoordinate n i)
    (h1 : fordPrimeCoordinate n (i+1)=fordPrimeCoordinate n i)
    (h2 : fordPrimeCoordinate n (i+2)=fordPrimeCoordinate n i)
    (hrow : fordRowSum L (fordPrimeCoordinate n) i ≤ xi x i*fordPrimeCoordinate n i) : False := by
  have hs : a 1*fordPrimeCoordinate n (i+1)+a 2*fordPrimeCoordinate n (i+2) ≤
      fordRowSum L (fordPrimeCoordinate n) i := by
    calc
      _ = ∑ r ∈ ({i+1,i+2}:Finset ℕ),a (r-i)*fordPrimeCoordinate n r := by
        simp
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          rcases Finset.mem_insert.mp hr with rfl | hr
          · exact Finset.mem_Icc.mpr (by omega)
          · have he := Finset.mem_singleton.mp hr
            subst r
            exact Finset.mem_Icc.mpr (by omega)
        · intro r hr _
          have hr := Finset.mem_Icc.mp hr
          exact mul_nonneg (a_pos (by omega)).le (le_max_left _ _)
  have hxi : xi x i ≤ (10001/10000:ℝ) := by
    have he : Real.exp (-((m x-i:ℕ):ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have := Nat.cast_nonneg (α:=ℝ) (m x-i); linarith)
    unfold xi
    linarith only [he]
  rw [h1,h2] at hs
  have ha := mul_le_mul_of_nonneg_right ford_first_two_coefficient_sum hpos.le
  have hb := mul_le_mul_of_nonneg_right hxi hpos.le
  nlinarith only [hs,hrow,ha,hb,hpos]

/-- At one of the last two boundaries there is a strict prime gap, and the
residual largest coordinate is exactly the final one. -/
lemma terminal_strict_prime_gap {x : ℝ} {n L : ℕ} (hL : 3 ≤ L)
    (hpos : 0 < fordPrimeCoordinate n L)
    (hrow : fordRowSum L (fordPrimeCoordinate n) (L-2) ≤
      xi x (L-2)*fordPrimeCoordinate n (L-2)) :
    ∃ j : ℕ,L-1 ≤ j ∧ j ≤ L ∧
      fordPrime n j < fordPrime n (j-1) ∧
      fordPrimeCoordinate n j=fordPrimeCoordinate n L := by
  have hprev := ford_coordinate_antitone n (show L-1 ≤ L by omega)
  by_cases hgap : fordPrimeCoordinate n L < fordPrimeCoordinate n (L-1)
  · exact ⟨L,by omega,le_rfl,fordPrime_lt_of_coordinate_lt hgap,rfl⟩
  have he : fordPrimeCoordinate n (L-1)=fordPrimeCoordinate n L := le_antisymm (le_of_not_gt hgap) hprev
  have hprev' := ford_coordinate_antitone n (show L-2 ≤ L-1 by omega)
  have hgap' : fordPrimeCoordinate n (L-1) < fordPrimeCoordinate n (L-2) := by
    by_contra hh
    have he' : fordPrimeCoordinate n (L-2)=fordPrimeCoordinate n (L-1) :=
      le_antisymm (le_of_not_gt hh) hprev'
    apply ford_row_forbids_flat_triple (i:=L-2) (by omega) (by linarith only [he,he',hpos])
      ?_ ?_ hrow
    · simpa only [show L-2+1=L-1 by omega] using he'.symm
    · simpa only [show L-2+2=L by omega] using (he'.trans he).symm
  refine ⟨L-1,le_rfl,by omega,?_,he⟩
  have hh := fordPrime_lt_of_coordinate_lt hgap'
  simpa only [Nat.sub_sub] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedSimplexTerminal
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The last two boundaries of a truncated Ford simplex supply a strict
prime gap and the row system required by the residual counting bridge. -/
noncomputable section
namespace TotientAsymptotic

lemma fixed_simplex_terminal_data {x : ℝ} {H n : ℕ}
    (hs : fordSimplexCondition x H n) (hL : 3 ≤ m x-H) :
    ∃ j : ℕ, (j=m x-H ∨ j=m x-H-1) ∧
      j ≤ n.primeFactorsList.length ∧
      fordPrime n j < fordPrime n (j-1) ∧
      2 < fordPrimeCoordinate n j ∧
      ∀ i < j,fordRowSum j (fordPrimeCoordinate n) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate n i) := by
  have hrows := ford_simplex_truncated_rows hs
  have hrow : fordRowSum (m x-H) (fordPrimeCoordinate n) (m x-H-2) ≤
      xi x (m x-H-2)*fordPrimeCoordinate n (m x-H-2) := by
    simpa only [ite_eq_right (show m x-H-2≠0 by omega)] using
      hrows (m x-H-2) (by omega)
  obtain ⟨j,hlo,hhi,hgap,he⟩ := terminal_strict_prime_gap hL
    (by linarith only [hs.1]) hrow
  have hj : j=m x-H ∨ j=m x-H-1 := by omega
  have hlarge : 2 < fordPrimeCoordinate n j := by rw [he]; exact hs.1
  have hlen : j < n.primeFactorsList.length := by
    apply fordPrime_index_of_doubleLog_pos
    rw [←fordPrimeCoordinate_eq_raw_of_pos (by linarith only [hlarge])]
    linarith only [hlarge]
  refine ⟨j,hj,hlen.le,hgap,hlarge,?_⟩
  intro i hi
  exact (fordRowSum_truncate hhi _ (fun _=>le_max_left _ _)).trans (hrows i (by omega))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_QuarterPowerBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary logarithmic budgets at a power-four-thirds threshold. -/
noncomputable section
namespace TotientAsymptotic

lemma logarithm_square_quarter_bound {b : ℝ} (hb : 1 ≤ b) :
    (Real.log (b+4))^2 ≤ 320*b^(1/4:ℝ) := by
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_rpow_div (show 0 ≤ b+4 by linarith)
    (by norm_num : (0:ℝ)<1/8)
  have hq : ((b+4)^(1/8:ℝ))^2=(b+4)^(1/4:ℝ) := by
    rw [pow_two,← Real.rpow_add (by linarith : 0 < b+4)]
    norm_num
  have hp := Real.rpow_nonneg (show 0 ≤ b+4 by linarith) (1/8:ℝ)
  have hs : (Real.log (b+4))^2 ≤ 64*(b+4)^(1/4:ℝ) := by
    norm_num at hlog
    nlinarith only [hlog,hq,hl,hp]
  have ht : (b+4)^(1/4:ℝ) ≤ 5*b^(1/4:ℝ) := by
    calc
      _ ≤ (5*b)^(1/4:ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      _ = (5:ℝ)^(1/4:ℝ)*b^(1/4:ℝ) := Real.mul_rpow (by norm_num) hb0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤5) (by norm_num))
        (Real.rpow_nonneg hb0.le _)
  linarith only [hs,ht]

lemma logarithm_budget_quarter_bound {b F : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) :
    100*(Real.log (b+4)+F+30)^2 ≤ (10000*(F+31)^2)*b^(1/4:ℝ) := by
  have hlog := logarithm_square_quarter_bound hb
  have hs := Real.one_le_rpow hb (by norm_num : (0:ℝ)≤1/4)
  have hsum : (Real.log (b+4)+F+30)^2 ≤ 2*(Real.log (b+4))^2+2*(F+30)^2 := by
    nlinarith only [sq_nonneg (Real.log (b+4)-(F+30))]
  have hc : 64000+200*(F+30)^2 ≤ 10000*(F+31)^2 := by
    nlinarith only [hF,sq_nonneg F]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (F+30))
  have hfinal := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith : 0 ≤ b) (1/4:ℝ))
  nlinarith only [hlog,hsum,hmul,hfinal]

lemma four_thirds_threshold_budget {b F δ : ℝ} (hb : 1 ≤ b) (hF : 0 ≤ F) (hδ : 0 < δ)
    (hthreshold : ((10000*(F+31)^2)/δ)^(4/3:ℝ) ≤ b) :
    100*(Real.log (b+4)+F+30)^2 ≤ δ*b := by
  have hb0 : 0 < b := by linarith
  have hK : 0 ≤ 10000*(F+31)^2 := by positivity
  have hs : (10000*(F+31)^2)/δ ≤ b^(3/4:ℝ) := by
    have hh := Real.rpow_le_rpow
      (Real.rpow_nonneg (div_nonneg hK hδ.le) (4/3:ℝ)) hthreshold
      (by norm_num : (0:ℝ)≤3/4)
    rw [← Real.rpow_mul (div_nonneg hK hδ.le)] at hh
    norm_num at hh
    exact hh
  have hc : 10000*(F+31)^2 ≤ δ*b^(3/4:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hs
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hb0.le (1/4:ℝ))
  have he : δ*b^(3/4:ℝ)*b^(1/4:ℝ)=δ*b := by
    rw [mul_assoc,← Real.rpow_add hb0]
    norm_num
  exact (logarithm_budget_quarter_bound hb hF).trans (by simpa only [he] using hm)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalMassSeries
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth residual mass is summable against terminal-coordinate decay. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma terminalMassWeight_pos (c : ℝ) (k : ℕ) : 0 < terminalMassWeight c k := Real.exp_pos _

theorem summable_terminalMassWeight {c : ℝ} (hc : 0 < c) :
    Summable (terminalMassWeight c) := by
  let q := Real.exp (-c/2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded_eventually_nat
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ))),
    eventually_ge_atTop (1:ℕ)] with k hk hk1
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hb : 1 ≤ (k:ℝ)+1 := by linarith only [hk0]
  have hthreshold : ((10000*((0:ℝ)+31)^2)/(c/4))^(4/3:ℝ) ≤ (k:ℝ)+1 := by
    linarith only [hk]
  have hbudget := four_thirds_threshold_budget hb (le_refl (0:ℝ))
    (show 0 < c/4 by linarith only [hc]) hthreshold
  have hlog : 0 ≤ Real.log ((k:ℝ)+5) := Real.log_nonneg (by linarith only [hk0])
  have he : 10*(Real.log ((k:ℝ)+5))^2-c*k ≤ -(c/2)*(k:ℝ) := by
    simp only [add_zero] at hbudget
    rw [show (k:ℝ)+1+4=(k:ℝ)+5 by ring] at hbudget
    have hh : c/4*((k:ℝ)+1) ≤ (c/2)*(k:ℝ) := by nlinarith only [hc,hk0]
    nlinarith only [hbudget,hh,hlog,sq_nonneg (Real.log ((k:ℝ)+5))]
  rw [Real.norm_eq_abs,abs_of_pos (terminalMassWeight_pos c k)]
  dsimp only [terminalMassWeight,q]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith only [he]

lemma finite_terminal_mass_bound {c : ℝ} (hc : 0 < c) (I : Finset ℕ) :
    (∑ k ∈ I,terminalMassWeight c k) ≤ ∑' k : ℕ,terminalMassWeight c k :=
  (summable_terminalMassWeight hc).sum_le_tsum _ (fun k _ => (terminalMassWeight_pos c k).le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TerminalSliceCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual terminal-coordinate strips using their finite residual masses. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem terminal_slice_value_count (H : ℕ) : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,N+2+H=m x →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      N+2 ≤ (n v).primeFactorsList.length ∧
      fordPrime (n v) (N+2) < fordPrime (n v) (N+1) ∧
      2 < fordPrimeCoordinate (n v) (N+2) ∧
      ∀ i < N+2,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+1) := by
  classical
  obtain ⟨A,c,hA,hc,hcount⟩ := terminal_band_value_count H
  let T := ∑' k : ℕ,terminalMassWeight c k
  have hT : 0 ≤ T := tsum_nonneg (fun k => (terminalMassWeight_pos c k).le)
  refine ⟨A*(T+1),by positivity,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm Q n hQ
  let key : ℕ → ℕ := fun v => ⌊fordPrimeCoordinate (n v) (N+2)⌋₊
  let I := Q.image key
  let R (k : ℕ) := Q.filter (fun v => key v=k)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨key v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
      Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ k ∈ I,((R k).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (k : ℕ) (hk : k ∈ I) : ((R k).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+1)*terminalMassWeight c k := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    have hk2 : 2 ≤ key v := Nat.le_floor (hQ v hv).2.2.2.2.2.2.1.le
    apply hx N hNm (key v) hk2 (R (key v)) n
    intro w hw
    obtain ⟨hw,hkey⟩ := Finset.mem_filter.mp hw
    obtain ⟨hn,hφ,hhead,hwx,hlen,hgap,hlarge,hrows⟩ := hQ w hw
    refine ⟨hn,hφ,hhead,hwx,hlen,hgap,?_,?_,hrows⟩
    · rw [← hkey]
      exact Nat.floor_le (le_max_left _ _)
    · rw [← hkey]
      exact (Nat.lt_floor_add_one _).le
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+1) := by
    have hlog := Real.log_pos hx1
    have hG := G_pos hB (N+1)
    positivity
  calc
    _ ≤ ∑ k ∈ I,((R k).card:ℝ) := hcard
    _ ≤ ∑ k ∈ I,A*(x/Real.log x)*G x (N+1)*terminalMassWeight c k :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+1))*(∑ k ∈ I,terminalMassWeight c k) := by
      rw [Finset.mul_sum]
    _ ≤ (A*(x/Real.log x)*G x (N+1))*T :=
      mul_le_mul_of_nonneg_left (finite_terminal_mass_bound hc I) hfac
    _ ≤ (A*(x/Real.log x)*G x (N+1))*(T+1) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedSimplexBandCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For each fixed terminal truncation, count all values having a bad
retained coordinate by the last two strict prime boundaries. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_simplex_bad_band_count (H : ℕ) :
    ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ Q : Finset ℕ,∀ n : ℕ→ℕ,
    (∀ v∈Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
      fordSimplexCondition x H (n v)) →
    (∀ v∈Q,∃ j∈Finset.Icc 1 (m x-P),
      primeDoubleLog (n v) j < (19/20:ℝ)*fordBandScale x j ∨
      (21/20:ℝ)*fordBandScale x j < primeDoubleLog (n v) j) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-c*(P:ℝ)) := by
  classical
  obtain ⟨A,a,hA,ha,hcountA⟩ := ppt_fixed_bad_coordinate_value_count H
  obtain ⟨D,d,hD,hd,hcountD⟩ := ppt_fixed_bad_coordinate_value_count (H+1)
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  let c := min a d
  refine ⟨A*J^(H+1)+D*J^(H+2),c,by positivity,lt_min ha hd,?_⟩
  filter_upwards [hcountA,hcountD] with P hPA hPD
  filter_upwards [hPA,hPD,hproj,m_tendsto.eventually (eventually_ge_atTop (H+4)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hxA hxD hproj hm hB hx1
  intro Q n hQ hbad
  have hdata (v) (hv : v∈Q) := fixed_simplex_terminal_data (hQ v hv).2.2.2.2
    (show 3 ≤ m x-H by omega)
  choose j hj using hdata
  let U := Q.filter (fun v => ∃ hv : v∈Q,j v hv=m x-H)
  let W := Q\U
  have hUj (v) (hv : v∈U) : ∃ hvQ : v∈Q,j v hvQ=m x-H :=
    (Finset.mem_filter.mp hv).2
  have hWj (v) (hv : v∈W) : ∃ hvQ : v∈Q,j v hvQ=m x-H-1 := by
    obtain ⟨hvQ,hout⟩ := Finset.mem_sdiff.mp hv
    refine ⟨hvQ,?_⟩
    rcases (hj v hvQ).1 with hh|hh
    · exact False.elim (hout (Finset.mem_filter.mpr ⟨hvQ,hvQ,hh⟩))
    · exact hh
  have hU0 := hxA (m x-H-3) (by omega) U n (by
    intro v hv
    obtain ⟨hvQ,hjv⟩ := hUj v hv
    obtain ⟨hn,hphi,hhead,hvx,_⟩ := hQ v hvQ
    have ht := (hj v hvQ).2
    rw [hjv] at ht
    have hi : m x-H-3+3=m x-H := by omega
    refine ⟨hn,hphi,hhead,hvx,?_,?_,?_,?_⟩
    · simpa only [hi] using ht.1
    · simpa only [hi,show m x-H-3+2=m x-H-1 by omega] using ht.2.1
    · simpa only [hi] using ht.2.2.1
    · simpa only [hi] using ht.2.2.2) (by
      intro v hv
      exact hbad v (Finset.mem_filter.mp hv).1)
  have hW0 := hxD (m x-H-4) (by omega) W n (by
    intro v hv
    obtain ⟨hvQ,hjv⟩ := hWj v hv
    obtain ⟨hn,hphi,hhead,hvx,_⟩ := hQ v hvQ
    have ht := (hj v hvQ).2
    rw [hjv] at ht
    have hi : m x-H-4+3=m x-H-1 := by omega
    refine ⟨hn,hphi,hhead,hvx,?_,?_,?_,?_⟩
    · simpa only [hi] using ht.1
    · convert ht.2.1 using 1
      all_goals try with_reducible_and_instances rfl
      all_goals congr 1
      all_goals omega
    · simpa only [hi] using ht.2.2.1
    · simpa only [hi] using ht.2.2.2) (by
      intro v hv
      exact hbad v (Finset.mem_sdiff.mp hv).1)
  have hU : (U.card:ℝ) ≤ A*(x/Real.log x)*G x (m x-(H+1))*Real.exp (-a*(P:ℝ)) := by
    simpa only [show m x-H-3+2=m x-(H+1) by omega] using hU0
  have hW : (W.card:ℝ) ≤ D*(x/Real.log x)*G x (m x-(H+2))*Real.exp (-d*(P:ℝ)) := by
    simpa only [show m x-H-4+2=m x-(H+2) by omega] using hW0
  have hnorm : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hg (R : ℕ) (hR : R ≤ m x) : G x (m x-R) ≤ J^R*G x (m x) := by
    have hh := (div_le_iff₀ (G_pos hB (m x))).mp (hproj R hR)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (pow_nonneg hJ.le R) (pow_le_one₀ rho_pos.le rho_lt_one.le))
      (G_pos hB (m x)).le)
  have heA : Real.exp (-a*(P:ℝ)) ≤ Real.exp (-c*(P:ℝ)) :=
    Real.exp_le_exp.mpr (by
      dsimp only [c]
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left a d) (Nat.cast_nonneg P)))
  have heD : Real.exp (-d*(P:ℝ)) ≤ Real.exp (-c*(P:ℝ)) :=
    Real.exp_le_exp.mpr (by
      dsimp only [c]
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg P)))
  have hG : 0 ≤ G x (m x) := (G_pos hB _).le
  have hbA := hU.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (hg (H+1) (by omega)) (mul_nonneg hA.le hnorm))
    heA (Real.exp_pos _).le (by positivity))
  have hbD := hW.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (hg (H+2) (by omega)) (mul_nonneg hD.le hnorm))
    heD (Real.exp_pos _).le (by positivity))
  have hcard : (Q.card:ℝ)=(U.card:ℝ)+(W.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show U⊆Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=U.card+W.card by dsimp [W]; omega)
  rw [hcard]
  exact (add_le_add hbA hbD).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordStructureCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete unnormalized exceptional-value bound in Ford Theorem 16. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem ford_structure_exception_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ < m x →
    preimageExceptionCount x (fordSimplexCondition x Ψ) ≤
      C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨C,hC,hcount⟩ := ford_structure_value_count
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (0:ℝ)] with x hx hx0
  intro Ψ hΨ
  let Q := preimageExceptionValues x (fordSimplexCondition x Ψ)
  have hw (v : {v // v ∈ Q}) : ∃ n : ℕ,0 < n ∧ n.totient=v.val ∧
      ¬fordSimplexCondition x Ψ n := (Finset.mem_filter.mp v.property).2
  choose n hn using hw
  let f : ℕ → ℕ := fun v => if hv : v ∈ Q then n ⟨v,hv⟩ else 1
  apply hx Ψ hΨ Q f
  intro v hv
  have hvx : (v:ℝ) ≤ x := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hx0)
  have hh := hn ⟨v,hv⟩
  simpa only [f,dite_eq_left hv] using ⟨hh.1,hh.2.1,hvx,hh.2.2⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedBandExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed terminal truncation first, then a growing retained-coordinate
cutoff: this order makes the actual model-band exception count negligible. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_model_band_exception_bound : ∃ D : ℝ,0 < D ∧
    ∀ H : ℕ,∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (modelBandsCondition x P) ≤
        (D*Real.exp (-(H:ℝ)^2/4)+C*Real.exp (-c*(P:ℝ)))*tupleNormalization x := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,hstruct⟩ := ford_structure_value_count
  refine ⟨A+D,add_pos hA hD,?_⟩
  intro H
  obtain ⟨C,c,hC,hc,hgood⟩ := fixed_simplex_bad_band_count H
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hgood,eventually_ge_atTop (1:ℕ)] with P hP hP1
  filter_upwards [hP,hsmall,hstruct,fixed_model_band_failure_transfer,
    m_tendsto.eventually (eventually_gt_atTop H),eventually_gt_atTop (1:ℝ)]
    with x hx hs ht htransfer hm hx1
  let Q := preimageExceptionValues x (modelBandsCondition x P)
  have hw (v : {v // v∈Q}) : ∃ n : ℕ,0 < n ∧ n.totient=v.val ∧
      ¬modelBandsCondition x P n := (Finset.mem_filter.mp v.property).2
  choose f hf using hw
  let n : ℕ→ℕ := fun v => if hv : v∈Q then f ⟨v,hv⟩ else 1
  have hn (v) (hv : v∈Q) : 0 < n v ∧ (n v).totient=v ∧
      ¬modelBandsCondition x P (n v) := by
    simpa only [n,dite_eq_left hv] using hf ⟨v,hv⟩
  have hvx (v) (hv : v∈Q) : (v:ℝ) ≤ x :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2).trans
      (Nat.floor_le (by linarith only [hx1]))
  let S := Q.filter (fun v => (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ))
  let T := Q.filter (fun v => ¬fordSimplexCondition x H (n v))
  let R := Q\(S∪T)
  have hS := hs H hm.le S (by
    intro v hv
    obtain ⟨hv,hsmall⟩ := Finset.mem_filter.mp hv
    exact ⟨⟨n v,(hn v hv).1,(hn v hv).2.1⟩,hvx v hv,
      n v,(hn v hv).1,(hn v hv).2.1,hsmall⟩)
  have hT := ht H hm T n (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    exact ⟨(hn v hv).1,(hn v hv).2.1,hvx v hv,hbad⟩)
  have hR := hx R n (by
    intro v hv
    obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp hv
    have hns : ¬(fordPrime (n v) 0:ℝ) < x^(1/4:ℝ) := by
      intro hh
      exact hout (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,hh⟩))
    have hst : fordSimplexCondition x H (n v) := by
      by_contra hh
      exact hout (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hh⟩))
    exact ⟨(hn v hv).1,(hn v hv).2.1,le_of_not_gt hns,hvx v hv,hst⟩) (by
      intro v hv
      have hvQ := (Finset.mem_sdiff.mp hv).1
      have hb := (hn v hvQ).2.2
      change ¬∀ i∈Finset.Icc 1 (m x-P),_ at hb
      push Not at hb
      obtain ⟨i,hi,hbi⟩ := hb
      refine ⟨i,hi,?_⟩
      have hi' := Finset.mem_Icc.mp hi
      have him : i < m x := by omega
      apply htransfer i him
      by_cases hlo : (9/10:ℝ)*bandScale x i ≤ primeDoubleLog (n v) i
      · exact Or.inr (hbi hlo)
      · exact Or.inl (lt_of_not_ge hlo))
  have hcover : Q⊆S∪T∪R := by
    intro v hv
    by_cases hh : v∈S∪T
    · exact Finset.mem_union_left _ hh
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,hh⟩)
  have hcard : (Q.card:ℝ) ≤ (S.card:ℝ)+T.card+R.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change (Q.card:ℝ) ≤ _
  exact hcard.trans ((add_le_add (add_le_add hS hT) hR).trans_eq (by unfold tupleNormalization; ring))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexGoodCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Count all full-simplex values by the final two strict prime boundaries. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem ford_simplex_good_value_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧
      x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧ fordSimplexCondition x 0 (n v)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x) := by
  classical
  obtain ⟨A,hA,hcountA⟩ := terminal_slice_value_count 0
  obtain ⟨D,hD,hcountD⟩ := terminal_slice_value_count 1
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  have hr := rho_pos
  refine ⟨A*J+D*J^2*rho,by positivity,?_⟩
  filter_upwards [hcountA,hcountD,hproj,m_tendsto.eventually (eventually_ge_atTop 4),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hcountA hcountD hproj hm hB hx1
  intro Q n hQ
  let U := Q.filter (fun v => fordPrime (n v) (m x) < fordPrime (n v) (m x-1))
  let W := Q\U
  have hrows (v) (hv : v ∈ Q) := ford_simplex_full_rows (hQ v hv).2.2.2.2
  have hlast (v) (hv : v ∈ Q) : 2 < fordPrimeCoordinate (n v) (m x) := by
    simpa only [Nat.sub_zero] using (hQ v hv).2.2.2.2.1
  have hlen (v) (hv : v ∈ Q) : m x < (n v).primeFactorsList.length := by
    apply fordPrime_index_of_doubleLog_pos
    rw [← fordPrimeCoordinate_eq_raw_of_pos (by linarith only [hlast v hv])]
    linarith only [hlast v hv]
  have hU0 := hcountA (m x-2) (by omega) U n (by
    intro v hv
    obtain ⟨hv,hgap⟩ := Finset.mem_filter.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    have hindex : m x-2+2=m x := by omega
    have hprev : m x-2+1=m x-1 := by omega
    refine ⟨hn,hφ,hhead,hvx,?_,?_,?_,?_⟩
    · rw [hindex]; exact (hlen v hv).le
    · simpa only [hindex,hprev] using hgap
    · simpa only [hindex] using hlast v hv
    · simpa only [hindex] using hrows v hv)
  have hW0 := hcountD (m x-3) (by omega) W n (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hn,hφ,hhead,hvx,_⟩ := hQ v hv
    have hnotgap : ¬fordPrime (n v) (m x) < fordPrime (n v) (m x-1) := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hv,hh⟩)
    have hrow : fordRowSum (m x) (fordPrimeCoordinate (n v)) (m x-2) ≤
        xi x (m x-2)*fordPrimeCoordinate (n v) (m x-2) := by
      simpa only [ite_eq_right (show m x-2 ≠ 0 by omega)] using
        hrows v hv (m x-2) (by omega)
    have hh := terminal_strict_prime_gap (by omega : 3 ≤ m x)
      (by linarith only [hlast v hv]) hrow
    obtain ⟨j,hjlo,hjhi,hgap,heq⟩ := hh
    have hj : j=m x-1 := by
      have hjne : j≠m x := by intro he; subst j; exact hnotgap hgap
      omega
    rw [hj] at hgap heq
    have hindex : m x-3+2=m x-1 := by omega
    have hprev : m x-3+1=m x-2 := by omega
    refine ⟨hn,hφ,hhead,hvx,?_,?_,?_,?_⟩
    · have hh := hlen v hv
      rw [hindex]
      omega
    · simpa only [hindex,hprev,Nat.sub_sub] using hgap
    · rw [hindex,heq]; exact hlast v hv
    · intro i hi
      exact hrows v hv i (by omega))
  have hU : (U.card:ℝ) ≤ A*(x/Real.log x)*G x (m x-1) := by
    simpa only [show m x-2+1=m x-1 by omega] using hU0
  have hW : (W.card:ℝ) ≤ D*(x/Real.log x)*G x (m x-2) := by
    simpa only [show m x-3+1=m x-2 by omega] using hW0
  have hg1 := (div_le_iff₀ (G_pos hB (m x))).mp (hproj 1 (by omega))
  have hg2 := (div_le_iff₀ (G_pos hB (m x))).mp (hproj 2 (by omega))
  norm_num only [pow_one,Nat.sub_self,zero_div,pow_zero,mul_one] at hg1
  norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reduceDiv,pow_one] at hg2
  have hnormal : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  have hUb := hU.trans (mul_le_mul_of_nonneg_left hg1 (mul_nonneg hA.le hnormal))
  have hWb := hW.trans (mul_le_mul_of_nonneg_left hg2 (mul_nonneg hD.le hnormal))
  have hcard : (Q.card:ℝ)=(U.card:ℝ)+(W.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show U ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=U.card+W.card by dsimp [W]; omega)
  rw [hcard]
  calc
    _ ≤ A*(x/Real.log x)*(J*G x (m x))+D*(x/Real.log x)*(J^2*rho*G x (m x)) := add_le_add hUb hWb
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordScaleUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper half of Ford's counting scale, assembled on actual totient values. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem ford_scale_upper : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, V x ≤ C*(x/Real.log x)*G x (m x) := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,hbad⟩ := ford_structure_value_count
  obtain ⟨E,hE,hgood⟩ := ford_simplex_good_value_count
  refine ⟨A+D+E,by positivity,?_⟩
  filter_upwards [hsmall,hbad,hgood,eventually_ge_atTop (0:ℝ),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hs hb hg hx hm
  let Q := (Finset.Icc 1 ⌊x⌋₊).filter IsTotient
  let U := Q.filter (fun v => (fordPrime (ell v) 0:ℝ) < x^(1/4:ℝ))
  let W := Q.filter (fun v => ¬fordSimplexCondition x 0 (ell v))
  let T := Q.filter (fun v => x^(1/4:ℝ) ≤ fordPrime (ell v) 0 ∧
    fordSimplexCondition x 0 (ell v))
  have hmem (v) (hv : v ∈ Q) : IsTotient v ∧ (v:ℝ) ≤ x := by
    obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
    exact ⟨ht,(Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le hx)⟩
  have hU := hs 0 (by omega) U (by
    intro v hv
    obtain ⟨hv,hhead⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨ht,hvx,ell v,(ell_spec ht).1,(ell_spec ht).2,hhead⟩)
  have hW := hb 0 hm W ell (by
    intro v hv
    obtain ⟨hv,hfail⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨(ell_spec ht).1,(ell_spec ht).2,hvx,hfail⟩)
  have hT := hg T ell (by
    intro v hv
    obtain ⟨hv,hhead,hsimplex⟩ := Finset.mem_filter.mp hv
    obtain ⟨ht,hvx⟩ := hmem v hv
    exact ⟨(ell_spec ht).1,(ell_spec ht).2,hhead,hvx,hsimplex⟩)
  have hcover : Q ⊆ U ∪ W ∪ T := by
    intro v hv
    by_cases hu : (fordPrime (ell v) 0:ℝ) < x^(1/4:ℝ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hv,hu⟩))
    by_cases hw : fordSimplexCondition x 0 (ell v)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,le_of_not_gt hu,hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hv,hw⟩))
  have hc : (Q.card:ℝ) ≤ (U.card:ℝ)+W.card+T.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  norm_num only [Nat.cast_zero,zero_pow (by norm_num : 2≠0),neg_zero,
    zero_div,Real.exp_zero,mul_one] at hU hW
  change (Q.card:ℝ) ≤ _
  calc
    _ ≤ (U.card:ℝ)+W.card+T.card := hc
    _ ≤ A*(x/Real.log x)*G x (m x)+D*(x/Real.log x)*G x (m x)+
        E*(x/Real.log x)*G x (m x) := add_le_add (add_le_add hU hW) hT
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTErrorEnvelope
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual vanishing envelope for an iterated eventual error bound. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- Turn an iterated small-error estimate into one envelope valid at every
fixed index. The infimum is taken over eventual normalized upper bounds;
its approximation needs no attainment or uniform threshold in the index. -/
theorem ppt_iterated_error_envelope (E : ℕ→ℝ→ℝ) (S : ℝ→ℝ)
    (hS : ∀ᶠ x : ℝ in atTop, 0 < S x)
    (hbound : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ P : ℕ, E P x ≤ C*S x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop,
      ∀ᶠ x : ℝ in atTop, E P x ≤ ε*S x) :
    ∃ δ : ℕ→ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ P : ℕ, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ x : ℝ in atTop, E P x ≤ (δ P+ε)*S x := by
  obtain ⟨C,hC⟩:=hbound
  let U : ℕ→Set ℝ := fun P => {b | 0 ≤ b ∧ ∀ᶠ x : ℝ in atTop,E P x ≤ b*S x}
  have hne (P : ℕ) : (U P).Nonempty := by
    refine ⟨max C 0,le_max_right _ _,?_⟩
    filter_upwards [hC,hS] with x hx hSx
    exact (hx P).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hSx.le)
  have hbdd (P : ℕ) : BddBelow (U P) := ⟨0,fun _ hb=>hb.1⟩
  let δ : ℕ→ℝ := fun P => sInf (U P)
  have hnonneg (P : ℕ) : 0 ≤ δ P := le_csInf (hne P) (fun _ hb=>hb.1)
  refine ⟨δ,?_,?_⟩
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun P=>ha.trans_le (hnonneg P))
    · intro b hb
      filter_upwards [hsmall (b/2) (half_pos hb)] with P hP
      have hbU : b/2∈U P := ⟨(half_pos hb).le,hP⟩
      have hh : δ P ≤ b/2 := csInf_le (hbdd P) hbU
      linarith only [hh,hb]
  · intro P ε hε
    obtain ⟨b,hb,hlt⟩:=exists_lt_of_csInf_lt (hne P)
      (show sInf (U P) < δ P+ε by change δ P < δ P+ε; linarith only [hε])
    filter_upwards [hb.2,hS] with x hx hSx
    exact hx.trans (mul_le_mul_of_nonneg_right hlt.le hSx.le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTStructureInput
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The qualitative all-preimage structural condition. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma preimageExceptionCount_le_totientCount (x : ℝ) (Q : ℕ → Prop) :
    preimageExceptionCount x Q ≤ V x := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv,n,hn,hphi,_⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv,n,hn,hphi⟩

lemma ppt_natural_exponential_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℕ => Real.exp (-c*(P:ℝ))) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hc))

lemma ppt_natural_gaussian_tendsto :
    Tendsto (fun P : ℕ => Real.exp (-(P:ℝ)^2/4)) atTop (𝓝 0) := by
  have hp : Tendsto (fun P : ℕ => (P:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_atBot.comp
    (hp.const_mul_atTop_of_neg (by norm_num : -(1/4:ℝ) < 0))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext P
  congr 1
  ring

theorem extractedStructureInput_of_small
    (hupper : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, V x ≤ C*tupleNormalization x)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        ε*tupleNormalization x) : ExtractedStructureInput := by
  obtain ⟨C,hC⟩ := hupper
  apply ppt_iterated_error_envelope
    (fun P x => preimageExceptionCount x (extractedStructureCondition x P))
    tupleNormalization scale_eventually_pos _ hsmall
  refine ⟨C,?_⟩
  filter_upwards [hC] with x hx
  intro P
  exact (preimageExceptionCount_le_totientCount x _).trans hx

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PPTFixedBandLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Let the fixed terminal cutoff grow before the retained-coordinate
cutoff, then package the resulting all-preimage error in one envelope. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_model_band_exception_small :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (modelBandsCondition x P) ≤
        ε*tupleNormalization x := by
  obtain ⟨D,_hD,hbound⟩ := fixed_model_band_exception_bound
  intro ε hε
  have hlim : Tendsto (fun H : ℕ => D*Real.exp (-(H:ℝ)^2/4)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ppt_natural_gaussian_tendsto.const_mul D
  obtain ⟨H,hH⟩ := (hlim.eventually (eventually_lt_nhds (half_pos hε))).exists
  obtain ⟨C,c,_hC,hc,hcount⟩ := hbound H
  have hdecay : Tendsto (fun P : ℕ => C*Real.exp (-c*(P:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (ppt_natural_exponential_tendsto hc).const_mul C
  filter_upwards [hcount,hdecay.eventually (eventually_lt_nhds (half_pos hε))]
    with P hP hsmall
  filter_upwards [hP,scale_eventually_pos] with x hx hn
  exact hx.trans (mul_le_mul_of_nonneg_right (by linarith only [hH,hsmall]) hn.le)

theorem extracted_structure_exception_small :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        ε*tupleNormalization x := by
  obtain ⟨C,_hC,hcount⟩ := ford_structure_exception_count
  intro ε hε
  have hlim : Tendsto (fun P : ℕ => C*Real.exp (-(P:ℝ)^2/4)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ppt_natural_gaussian_tendsto.const_mul C
  filter_upwards [fixed_model_band_exception_small (ε/2) (half_pos hε),
    hlim.eventually (eventually_lt_nhds (half_pos hε))] with P hband hsmall
  filter_upwards [hband,hcount,scale_eventually_pos,
    m_tendsto.eventually (eventually_gt_atTop P)] with x hb hx hn hm
  have hs : preimageExceptionCount x (extractedSimplexCondition x P) ≤
      (ε/2)*tupleNormalization x := by
    calc
      _ ≤ preimageExceptionCount x (fordSimplexCondition x P) :=
        preimageExceptionCount_mono (fun _ hh => fordSimplexCondition_implies_extracted hm hh)
      _ ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(P:ℝ)^2/4) := hx P hm
      _ = (C*Real.exp (-(P:ℝ)^2/4))*tupleNormalization x := by
        unfold tupleNormalization
        ring
      _ ≤ (ε/2)*tupleNormalization x := mul_le_mul_of_nonneg_right hsmall.le hn.le
  calc
    _ ≤ preimageExceptionCount x (modelBandsCondition x P)+
        preimageExceptionCount x (extractedSimplexCondition x P) :=
      preimageExceptionCount_and_le x _ _
    _ ≤ (ε/2)*tupleNormalization x+(ε/2)*tupleNormalization x := add_le_add hb hs
    _ = ε*tupleNormalization x := by ring

theorem extractedStructureInput_oai : ExtractedStructureInput := by
  obtain ⟨C,_hC,hupper⟩ := ford_scale_upper
  apply extractedStructureInput_of_small _ extracted_structure_exception_small
  refine ⟨C,?_⟩
  filter_upwards [hupper] with x hx
  simpa only [tupleNormalization,mul_assoc] using hx

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.extractedStructureInput_oai := @OAI.TotientAsymptotic.extractedStructureInput_oai
