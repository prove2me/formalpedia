-- Prove2me | solution 1 for OAI.TotientAsymptotic.fixed_coordinate_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:33:03.422202+00:00
-- url     : https://prove2.me/submissions/eca60197-7957-47ce-abd9-c1dbd2f059df

import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000

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
end OAICompat434

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

lemma fordBandScale_pos {x : ℝ} {i : ℕ} (hB : 0 < B x) (hi : i < m x) :
    0 < fordBandScale x i := by
  have hm : (0 : ℝ) < m x := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have hi' : (i : ℝ) < m x := Nat.cast_lt.mpr hi
  exact mul_pos (mul_pos hB (pow_pos rho_pos _))
    (sub_pos.mpr ((div_lt_one hm).mpr hi'))

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

end TotientAsymptotic
end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGeometry
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The triangular slack calculation underlying `lem:simplex` and
`eq:intersection-volume` in the manuscript. These are identities for the
actual renewal coefficients, with no volume or counting estimate assumed.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma g_convolution {j : ℕ} (hj : 0 < j) :
    g j = ∑ i ∈ Finset.range j, g i * a (j-i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [g]
  apply Finset.sum_bij (fun d _ => n-d)
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    exact Finset.mem_range.mpr (by omega)
  · intro d hd e he hde
    have hd' := Finset.mem_range.mp hd
    have he' := Finset.mem_range.mp he
    omega
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    refine ⟨n-i, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro d hd
    have hd' := Finset.mem_range.mp hd
    have he : n+1-(n-d) = d+1 := by omega
    rw [he, mul_comm]

lemma weighted_slack_identity (N : ℕ) (u : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N+1), g i * prefixSlack N u i = u 0 := by
  have inner (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        g j * u j - if j = 0 then u 0 else 0 := by
    have hsub : Finset.range j ⊆ Finset.range (N+1) :=
      Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hj))
    have he : (∑ i ∈ Finset.range (N+1), if i < j then g i * (a (j-i) * u j) else 0) =
        ∑ i ∈ Finset.range j, g i * (a (j-i) * u j) := by
      symm
      calc
        _ = ∑ i ∈ Finset.range j, if i < j then g i * (a (j-i) * u j) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ite_eq_left (Finset.mem_range.mp hi)]
        _ = _ := Finset.sum_subset hsub (by
          intro i _ hi
          rw [ite_eq_right (by simpa using hi)])
    rw [he]
    by_cases hj0 : j = 0
    · subst j
      simp [g]
    · rw [ite_eq_right hj0, sub_zero, g_convolution (Nat.pos_of_ne_zero hj0), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  simp only [prefixSlack, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  have hs : (∑ i ∈ Finset.range (N+1),
      ∑ j ∈ Finset.range (N+1), g i * (if i < j then a (j-i)*u j else 0)) =
      ∑ j ∈ Finset.range (N+1), (g j * u j - if j = 0 then u 0 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [mul_ite, mul_zero] using inner j hj
  rw [hs, Finset.sum_sub_distrib]
  simp

lemma prefixLinear_preserves_volume (N : ℕ) :
    MeasureTheory.Measure.map (prefixLinear N) MeasureTheory.volume = MeasureTheory.volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [prefixLinear_det]; norm_num),
    prefixLinear_det]
  simp

lemma prefixLinear_apply (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    prefixLinear N u i = u i - ∑ j : Fin N,
      if i < j then a (j.val-i.val) * u j else 0 := by
  change (∑ j : Fin N, prefixMatrix N i j * u j) = _
  have he (j : Fin N) : prefixMatrix N i j * u j =
      (if j = i then u j else 0) -
        (if i < j then a (j.val-i.val) * u j else 0) := by
    by_cases hij : i = j
    · subst j
      simp [prefixMatrix]
    · by_cases hij' : i < j <;> simp [prefixMatrix, hij, Ne.symm hij, hij']
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  simp

lemma prefixLinear_vector (N : ℕ) (u : ℕ → ℝ) (i : Fin N) :
    prefixLinear N (prefixVector N u) i = prefixSlack N u (i.val+1) := by
  rw [prefixLinear_apply]
  unfold prefixSlack prefixVector
  rw [Finset.sum_range_succ']
  simp only [Fin.lt_def, not_lt_zero, ite_false, if_false, add_zero]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => if i.val < k then a (k-i.val) * u (k+1) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixSlack_zero (N : ℕ) (u : ℕ → ℝ) :
    prefixSlack N u 0 = u 0 - ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  unfold prefixSlack
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_lt_succ, ite_true, if_true, Nat.sub_zero, lt_self_iff_false, ite_false, if_false, add_zero]
  rw [Fin.sum_univ_eq_sum_range (fun k => a (k+1) * u (k+1))]

lemma weighted_prefix_vector (N : ℕ) (u : ℕ → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N (prefixVector N u) i =
      ∑ i : Fin N, a (i.val+1) * u (i.val+1) := by
  have h := weighted_slack_identity N u
  rw [Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range,
    prefixSlack_zero] at h
  have hg0 : g 0 = 1 := by simp [g]
  rw [hg0, one_mul] at h
  simp_rw [prefixLinear_vector]
  linarith

lemma prefixVector_extend (N : ℕ) (u : Fin N → ℝ) :
    prefixVector N (extendPrefix N u) = u := by
  funext i
  simp [prefixVector, extendPrefix]

lemma weighted_prefixLinear (N : ℕ) (u : Fin N → ℝ) :
    ∑ i : Fin N, g (i.val+1) * prefixLinear N u i =
      ∑ i : Fin N, a (i.val+1) * u i := by
  have h := weighted_prefix_vector N (extendPrefix N u)
  simpa [prefixVector_extend, extendPrefix] using h

/-- The available slack is the top budget minus all weighted tail thresholds. -/
lemma prefixRegion_eq_simplex_preimage (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    prefixRegion N B C₀ C =
      (fun u => prefixLinear N u - C) ⁻¹'
        weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i) := by
  ext u
  simp only [prefixRegion, weightedSimplex, Set.mem_ofPred_eq, Set.mem_preimage,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, weighted_prefixLinear]
  constructor
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mpr (hlo i), sub_le_sub_right hsum _⟩
  · rintro ⟨hlo, hsum⟩
    exact ⟨fun i => sub_nonneg.mp (hlo i), (sub_le_sub_iff_right _).mp hsum⟩

lemma prefixAffine_preserves_volume (N : ℕ) (C : Fin N → ℝ) :
    MeasureTheory.MeasurePreserving (fun u => prefixLinear N u - C)
      MeasureTheory.volume MeasureTheory.volume := by
  have hlin : MeasureTheory.MeasurePreserving (prefixLinear N)
      MeasureTheory.volume MeasureTheory.volume :=
    ⟨(prefixLinear N).continuous_of_finiteDimensional.measurable,
      prefixLinear_preserves_volume N⟩
  simpa only [sub_eq_add_neg, Function.comp_def] using
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-C)).comp hlin

lemma measurableSet_weightedSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (weightedSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, g (i.val+1) * v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

/-- Exact reduction of the prefix volume, valid for every fixed tail threshold. -/
theorem volume_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasureTheory.volume (prefixRegion N B C₀ C) =
      MeasureTheory.volume
        (weightedSimplex N (B-C₀-∑ i : Fin N, g (i.val+1)*C i)) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume N C).measure_preimage
    (measurableSet_weightedSimplex _ _).nullMeasurableSet

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary simplex volume used by the prefix mass calculation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_standardSimplex (N : ℕ) (T : ℝ) :
    MeasurableSet (standardSimplex N T) := by
  change MeasurableSet ({v : Fin N → ℝ | ∀ i, 0 ≤ v i} ∩
    {v : Fin N → ℝ | (∑ i, v i) ≤ T})
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const (continuous_apply i)).measurableSet)
  · exact measurableSet_le (by fun_prop) measurable_const

lemma measurableSet_simplexSection (N : ℕ) (T : ℝ) :
    MeasurableSet (simplexSection N T) := by
  change MeasurableSet ({p : ℝ × (Fin N → ℝ) | p.1 ∈ Set.Icc 0 T} ∩
    ({p : ℝ × (Fin N → ℝ) | ∀ i, 0 ≤ p.2 i} ∩
      {p : ℝ × (Fin N → ℝ) | (∑ i, p.2 i) ≤ T-p.1}))
  apply MeasurableSet.inter (measurable_fst measurableSet_Icc)
  apply MeasurableSet.inter
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i =>
      (isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)).measurableSet)
  · exact measurableSet_le (by fun_prop) (by fun_prop)

lemma standardSimplex_succ_preimage (N : ℕ) (T : ℝ) :
    standardSimplex (N+1) T =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0) ⁻¹'
        simplexSection N T := by
  ext u
  simp only [standardSimplex, simplexSection, Set.mem_preimage, Set.mem_ofPred_eq,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
    Fin.removeNth, Fin.succAbove_zero, Set.mem_Icc]
  simp only [Fin.sum_univ_succ, Fin.forall_fin_succ]
  constructor
  · rintro ⟨⟨h0, hn⟩, hs⟩
    have hn' : 0 ≤ ∑ i : Fin N, u i.succ := Finset.sum_nonneg (fun i _ => hn i)
    exact ⟨⟨h0, by linarith⟩, ⟨hn, by linarith⟩⟩
  · rintro ⟨⟨h0, _⟩, hn, hs⟩
    exact ⟨⟨h0, hn⟩, by linarith⟩

lemma volume_standardSimplex_succ (N : ℕ) (T : ℝ) :
    volume (standardSimplex (N+1) T) =
      ∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x)) := by
  rw [standardSimplex_succ_preimage]
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0).measure_preimage
    (measurableSet_simplexSection N T).nullMeasurableSet]
  change (volume.prod volume) (simplexSection N T) = _
  rw [Measure.prod_apply (measurableSet_simplexSection N T)]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Set.Icc 0 T
  · have hx' := hx
    simp only [Set.mem_Icc] at hx'
    simp [simplexSection, hx, hx'.1, hx'.2]
  · have hx' : ¬ (0 ≤ x ∧ x ≤ T) := hx
    simp [simplexSection, hx, hx']

lemma volume_standardSimplex_zero {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex 0 T) = 1 := by
  have he : standardSimplex 0 T = Set.univ := by
    ext u
    simp [standardSimplex, hT]
  rw [he]
  change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1
  simp

lemma integral_simplex_power (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in Set.Icc 0 T, (T-x)^N / (N.factorial : ℝ)) =
      T^(N+1) / ((N+1).factorial : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^N)]
  simp only [sub_zero, sub_self]
  rw [integral_pow]
  simp only [zero_pow (by omega : N+1 ≠ 0), sub_zero,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_div]

theorem volume_standardSimplex (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (standardSimplex N T) = ENNReal.ofReal (T^N / (N.factorial : ℝ)) := by
  induction N generalizing T with
  | zero => simpa using volume_standardSimplex_zero hT
  | succ N ih =>
    rw [volume_standardSimplex_succ]
    have he : (∫⁻ x in Set.Icc 0 T, volume (standardSimplex N (T-x))) =
        ∫⁻ x in Set.Icc 0 T, ENNReal.ofReal ((T-x)^N / (N.factorial : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      exact ih (sub_nonneg.mpr hx.2)
    rw [he, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_simplex_power N hT]
    · exact (show Continuous (fun x : ℝ => (T-x)^N / (N.factorial : ℝ)) by
        fun_prop).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact div_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _) (Nat.cast_nonneg _)

lemma weightedScale_apply (N : ℕ) (v : Fin N → ℝ) (i : Fin N) :
    weightedScale N v i = g (i.val+1) * v i := by
  simp [weightedScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma weightedScale_det (N : ℕ) :
    LinearMap.det (weightedScale N) = ∏ i : Fin N, g (i.val+1) := by
  rw [weightedScale, LinearMap.det_toLin', Matrix.det_diagonal]

lemma weightedScale_det_pos (N : ℕ) : 0 < LinearMap.det (weightedScale N) := by
  rw [weightedScale_det]
  exact Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))

lemma weightedSimplex_eq_preimage (N : ℕ) (T : ℝ) :
    weightedSimplex N T = weightedScale N ⁻¹' standardSimplex N T := by
  ext v
  simp only [weightedSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    weightedScale_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (g_pos _)).symm)
    Iff.rfl

lemma volume_weightedSimplex_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [weightedSimplex_eq_preimage, ← Measure.map_apply
    (weightedScale N).continuous_of_finiteDimensional.measurable
    (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (weightedScale_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    weightedScale_det, abs_inv, abs_of_pos (Finset.prod_pos (fun (i : Fin N) _ => g_pos (i.val+1))),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Finset.prod_nonneg (fun (i : Fin N) _ => (g_pos (i.val+1)).le)))]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma volume_weightedSimplex (N : ℕ) (hN : 0 < N) (T : ℝ) :
    volume (weightedSimplex N T) =
      ENNReal.ofReal ((max T 0)^N / ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  by_cases hT : 0 ≤ T
  · rw [max_eq_left hT]
    exact volume_weightedSimplex_nonneg N hT
  · have he : weightedSimplex N T = ∅ := by
      ext v
      simp only [weightedSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hv, hs⟩
      have hn : 0 ≤ ∑ i : Fin N, g (i.val+1) * v i :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (g_pos _).le (hv i))
      linarith
    rw [he, measure_empty, max_eq_right (le_of_not_ge hT), zero_pow hN.ne', zero_div,
      ENNReal.ofReal_zero]

/-- The explicit determinant-one prefix volume formula from the manuscript. -/
theorem volume_prefixRegion_explicit (N : ℕ) (hN : 0 < N)
    (B C₀ : ℝ) (C : Fin N → ℝ) :
    volume (prefixRegion N B C₀ C) =
      ENNReal.ofReal ((max (B-C₀-∑ i : Fin N, g (i.val+1)*C i) 0)^N /
        ((N.factorial : ℝ) * ∏ i : Fin N, g (i.val+1))) := by
  rw [volume_prefixRegion, volume_weightedSimplex N hN]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexShell
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit slack-shell bounds for the prefix simplexes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasurableSet (prefixRegion N B C₀ C) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable (measurableSet_weightedSimplex _ _)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniformPrefactor
attribute [-instance] _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorShellDecay
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cofactor envelope is absorbed by every polynomial-geometric shell tail. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma polynomialGeometricTail_tendsto (k : ℕ) (r : ℝ) :
    Tendsto (polynomialGeometricTail k r) atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, ((H+n : ℕ) : ℝ)^k*r^(H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (fun n : ℕ => (n : ℝ)^k*r^n))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalLower
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform lower bounds for renewal coefficients and unbanded prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normalizedRenewal_pos (n : ℕ) : 0 < normalizedRenewal n :=
  mul_pos (g_pos _) (pow_pos rho_pos _)

lemma renewal_uniform_lower (hford : FordRenewalInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c*(rho^n)⁻¹ ≤ g n := by
  have hlim := (normalizedRenewal_properties hford).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_gt_nhds (show gamma/2 < gamma by linarith [gamma_pos])))
  let T := insert (gamma/2) ((Finset.range N).image normalizedRenewal)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  let c := T.min' hT
  have hc : 0 < c := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact div_pos gamma_pos (by norm_num)
    · obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hy
      exact normalizedRenewal_pos n
  refine ⟨c, hc, fun n => ?_⟩
  have hh : c ≤ normalizedRenewal n := by
    by_cases hn : n < N
    · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hN n (by omega)).le
  have hp := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  simpa only [normalizedRenewal, mul_assoc, mul_inv_cancel₀ (pow_pos rho_pos n).ne', mul_one]
    using hp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalRatios
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient ratios for the simplex coordinate estimates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_ratio_error : ∃ C : ℝ, 0<C ∧ ∀ i k : ℕ,
    |g k/(rho^i*g (i+k))-1|≤C*rho^k := by
  obtain ⟨E,hE,he⟩ := fordRenewalInput
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  refine ⟨2*(E+1)/c,by positivity,?_⟩
  intro i k
  have hr : 0 < rho^i := pow_pos rho_pos i
  have hrk : 0 < rho^k := pow_pos rho_pos k
  have hi1 : rho^i≤1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hD : 0 < rho^i*g (i+k) := mul_pos hr (g_pos _)
  have hnorm : |g k-rho^i*g (i+k)|≤2*(E+1) := by
    have hid : g k-rho^i*g (i+k)=
        (g k-gamma*(rho^k)⁻¹)-rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹) := by
      rw [pow_add]
      field_simp [hr.ne',hrk.ne']
      ring
    rw [hid]
    calc
      _ ≤ |g k-gamma*(rho^k)⁻¹|+|rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹)| := abs_sub _ _
      _ ≤ E+rho^i*E := by
        rw [abs_mul,abs_of_pos hr]
        exact add_le_add (he k) (mul_le_mul_of_nonneg_left (he (i+k)) hr.le)
      _ ≤ 2*(E+1) := by nlinarith
  have hden : c*(rho^k)⁻¹ ≤ rho^i*g (i+k) := by
    have hh := mul_le_mul_of_nonneg_left (hg (i+k)) hr.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [pow_add]
    field_simp [hr.ne',hrk.ne']
  have hi : (rho^i*g (i+k))⁻¹ ≤ rho^k/c := by
    have hh := inv_anti₀ (mul_pos hc (inv_pos.mpr hrk)) hden
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_inv_rev,inv_inv,div_eq_mul_inv]
  have hid : g k/(rho^i*g (i+k))-1=(g k-rho^i*g (i+k))/(rho^i*g (i+k)) := by
    field_simp [hD.ne', (g_pos (i+k)).ne', hr.ne']
  rw [hid,abs_div,abs_of_pos hD,div_eq_mul_inv]
  calc
    _ ≤ 2*(E+1)*(rho^k/c) := mul_le_mul hnorm hi (inv_pos.mpr hD).le (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentrationExponents
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical exponent saving for fixed one-fortieth deviations. -/
noncomputable section
namespace TotientAsymptotic

lemma concentrationTilt_pos {M : ℝ} (hM : 1 ≤ M) : 0 < concentrationTilt M := by
  unfold concentrationTilt
  positivity

lemma concentrationTilt_mul {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M*M = 1/320 := by
  unfold concentrationTilt
  field_simp

lemma concentrationTilt_le {M : ℝ} (hM : 1 ≤ M) : concentrationTilt M ≤ 1/320 := by
  have hs := concentrationTilt_pos hM
  have hm := concentrationTilt_mul hM
  nlinarith

lemma concentration_exponents {M K m S Q : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K)
    (hm : 1 ≤ m) (hS : |S-m| ≤ K) (hQ : Q ≤ M*(m+K)) :
    let s := concentrationTilt M
    (s*(39/40)*(m-1)-s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) ∧
    (-s*(41/40)*(m-1)+s*S+2*s^2*Q ≤ 3*s*(K+1)-(s/100)*(m-1)) := by
  dsimp only
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hquad : 2*s^2*Q ≤ (s/160)*(m+K) := by
    have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2*s^2 by positivity)
    have he : 2*s^2*(M*(m+K)) = (s/160)*(m+K) := by
      calc
        _ = 2*s*(s*M)*(m+K) := by ring
        _ = _ := by rw [hsm]; ring
    exact hh.trans_eq he
  have hSm := abs_le.mp hS
  have hSl := mul_le_mul_of_nonneg_left hSm.1 hs.le
  have hSu := mul_le_mul_of_nonneg_left hSm.2 hs.le
  have hsk : 0 ≤ s*K := mul_nonneg hs.le hK
  have hsm' : s ≤ s*m := le_mul_of_one_le_right hs.le hm
  constructor <;> dsimp only [s] at * <;> nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixCoordinates
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinates of the triangular prefix simplex in its slack variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSlack_shift (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) (k : ℕ) :
    prefixSlack (N-i) (fun j => u (i+j)) k = prefixSlack N u (i+k) := by
  have hs : (∑ j ∈ Finset.range (N+1),
      if i+k < j then a (j-(i+k))*u j else 0) =
      ∑ j ∈ Finset.range (N-i+1), if k < j then a (j-k)*u (i+j) else 0 := by
    rw [show N+1 = i+(N-i+1) by omega, Finset.sum_range_add]
    have hz : (∑ j ∈ Finset.range i,
        if i+k < j then a (j-(i+k))*u j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.add_lt_add_iff_left, Nat.add_sub_add_left]
  simp only [prefixSlack, hs]

lemma prefix_coordinate_slacks (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    u i = ∑ k ∈ Finset.range (N-i+1), g k*prefixSlack N u (i+k) := by
  have hh := weighted_slack_identity (N-i) (fun j => u (i+j))
  simp only [prefixSlack_shift N u hi, Nat.add_zero] at hh
  exact hh.symm

lemma prefix_coordinate_full_sum (N : ℕ) (u : ℕ → ℝ) {i : ℕ} (hi : i < N) :
    u (i+1) = ∑ j ∈ Finset.range N,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0 := by
  rw [prefix_coordinate_slacks N u (by omega : i+1 ≤ N)]
  have hsplit := Finset.sum_range_add
    (fun j => if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) i (N-i)
  rw [Nat.add_sub_of_le hi.le] at hsplit
  rw [hsplit]
  have hz : (∑ j ∈ Finset.range i,
      if i ≤ j then g (j-i)*prefixSlack N u (j+1) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  have he : N-(i+1)+1 = N-i := by omega
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.le_add_right, ite_true, if_true, Nat.add_sub_cancel_left]
  congr 2
  omega

/-- The inverse of the determinant-one triangular slack map. -/
theorem prefixLinear_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*prefixLinear N u j else 0 := by
  have hh := prefix_coordinate_full_sum N (extendPrefix N u) i.isLt
  have hv : extendPrefix N u (i.val+1) = u i := by simp [extendPrefix]
  rw [hv] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  rw [← prefixLinear_vector, prefixVector_extend]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixWeights
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded weights expressing each prefix coordinate in standard-simplex variables. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefixSimplexMap_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i/rho^(i.val+1) = ∑ j, prefixWeight N i j*prefixSimplexMap N u j := by
  conv_lhs => rw [prefixLinear_coordinate N u i]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [prefixWeight, prefixSimplexMap, LinearMap.comp_apply, weightedScale_apply]
  split_ifs
  · field_simp [(g_pos (j.val+1)).ne']
  · simp

lemma sum_suffix_weights (N : ℕ) (i : Fin N) (f : ℕ → ℝ) :
    (∑ j : Fin N, if i ≤ j then f (j.val-i.val) else 0) =
      ∑ k ∈ Finset.range (N-i.val), f k := by
  change (∑ j : Fin N, if i.val ≤ j.val then f (j.val-i.val) else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j => if i.val ≤ j then f (j-i.val) else 0)]
  have hs := Finset.sum_range_add (fun j => if i.val ≤ j then f (j-i.val) else 0)
    i.val (N-i.val)
  rw [Nat.add_sub_of_le (Nat.le_of_lt i.isLt)] at hs
  rw [hs]
  have hz : (∑ j ∈ Finset.range i.val, if i.val ≤ j then f (j-i.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have := Finset.mem_range.mp hj; omega)]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma prefixWeight_nonneg (N : ℕ) (i j : Fin N) : 0 ≤ prefixWeight N i j := by
  unfold prefixWeight
  split_ifs
  · exact div_nonneg (g_pos _).le (mul_pos (pow_pos rho_pos _) (g_pos _)).le
  · rfl

lemma prefixWeight_error {C : ℝ}
    (hC : ∀ i k : ℕ, |g k/(rho^i*g (i+k))-1| ≤ C*rho^k)
    (N : ℕ) (i j : Fin N) (hij : i ≤ j) :
    |prefixWeight N i j-1| ≤ C*rho^(j.val-i.val) := by
  have hh := hC (i.val+1) (j.val-i.val)
  have he : i.val+1+(j.val-i.val) = j.val+1 := by
    have : i.val ≤ j.val := hij
    omega
  simpa only [he, prefixWeight, ite_eq_left hij] using hh

/-- Uniform first- and second-moment bounds; the error is independent of dimension. -/
theorem prefixWeight_bounds : ∃ M K : ℝ, 1 ≤ M ∧ 0 < K ∧
    ∀ (N : ℕ) (i : Fin N),
      (∀ j, 0 ≤ prefixWeight N i j ∧ prefixWeight N i j ≤ M) ∧
      |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K ∧
      (∑ j, (prefixWeight N i j)^2) ≤ M*((N-i.val:ℕ)+K) := by
  obtain ⟨C,hC,he⟩ := renewal_ratio_error
  let M := C+1
  let K := C/(1-rho)
  have hK : 0 < K := div_pos hC (sub_pos.mpr rho_lt_one)
  refine ⟨M,K,by dsimp [M] <;> linarith,hK,?_⟩
  intro N i
  have hpoint (j : Fin N) : |prefixWeight N i j-(if i ≤ j then 1 else 0)| ≤
      if i ≤ j then C*rho^(j.val-i.val) else 0 := by
    by_cases hij : i ≤ j
    · simpa only [ite_eq_left hij] using prefixWeight_error he N i j hij
    · simp [prefixWeight, hij]
  have hupper (j : Fin N) : prefixWeight N i j ≤ M := by
    by_cases hij : i ≤ j
    · have hh := (abs_le.mp (prefixWeight_error he N i j hij)).2
      have hp := pow_le_one₀ rho_pos.le rho_lt_one.le (n := j.val-i.val)
      dsimp [M]
      nlinarith
    · simp only [prefixWeight, ite_eq_right hij]
      dsimp [M]
      linarith
  have herror : |(∑ j, prefixWeight N i j)-(N-i.val:ℕ)| ≤ K := by
    have hone : (∑ j : Fin N, if i ≤ j then (1:ℝ) else 0) = (N-i.val:ℕ) := by
      rw [sum_suffix_weights N i (fun _ => 1)]
      simp
    rw [← hone, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |prefixWeight N i j-(if i ≤ j then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin N, if i ≤ j then C*rho^(j.val-i.val) else 0 := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = C*∑ k ∈ Finset.range (N-i.val), rho^k := by rw [sum_suffix_weights N i (fun k => C*rho^k), Finset.mul_sum]
      _ ≤ K := by
        have hg := (hasSum_geometric_of_lt_one rho_pos.le rho_lt_one).summable.sum_le_tsum
          (Finset.range (N-i.val)) (fun k _ => (pow_pos rho_pos k).le)
        rw [tsum_geometric_of_lt_one rho_pos.le rho_lt_one] at hg
        exact mul_le_mul_of_nonneg_left hg hC.le
  refine ⟨fun j => ⟨prefixWeight_nonneg N i j,hupper j⟩,herror,?_⟩
  calc
    _ ≤ M*(∑ j, prefixWeight N i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hn := prefixWeight_nonneg N i j
      have hu := hupper j
      nlinarith
    _ ≤ M*((N-i.val:ℕ)+K) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [M] <;> positivity)
      have hh := (abs_le.mp herror).2
      linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedConcentration
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The fixed-deviation consequence of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 6.1, (6.6)--(6.8), pp. 30--31.
We use deviation 1/40 only. For the lower tail take
`theta = (1/40)/(1-1/40)` in (6.6); for the upper tail take
`theta = -(1/40)/(1+1/40)` in (6.7) or (6.8), splitting at
`-i*lambda_i/L`. The uniform bounds (6.4) give positive absolute
constants in `exp (-c*(L-i))`. Letting the terminal cutoff decrease to
zero and rescaling the simplex gives precisely the input below.
The transfer from Ford's terminal coefficient 1 to our coefficient a_1
is proved here using `shrinkLast`, rather than assumed in this input.
-/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_fordCoordinateBad (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    MeasurableSet (fordCoordinateBad N B i) := by
  apply measurableSet_lt measurable_const
  exact ((measurable_pi_apply i).div_const _ |>.sub_const 1).abs

lemma prefixRegion_volume_ne_top {N : ℕ} (hN : 0 < N) (B : ℝ) :
    volume (prefixRegion N B 0 0) ≠ ⊤ := by
  rw [volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixSimplexMap
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transporting the coordinate events through the exact simplex map. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_det (N : ℕ) :
    LinearMap.det (prefixSimplexMap N) = ∏ i : Fin N, g (i.val+1) := by
  rw [prefixSimplexMap, LinearMap.det_comp, prefixLinear_det, mul_one, weightedScale_det]

lemma prefixSimplexMap_det_pos (N : ℕ) : 0 < LinearMap.det (prefixSimplexMap N) := by
  rw [prefixSimplexMap_det]
  exact Finset.prod_pos (fun i _ => g_pos _)

lemma prefixSimplexMap_preimage (N : ℕ) (B : ℝ) :
    prefixRegion N B 0 0 = prefixSimplexMap N ⁻¹' standardSimplex N B := by
  rw [prefixRegion_eq_simplex_preimage]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
    weightedSimplex_eq_preimage]
  rfl

lemma volume_prefixSimplexMap_preimage (N : ℕ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T) :
    volume (prefixSimplexMap N ⁻¹' T) =
      ENNReal.ofReal ((LinearMap.det (prefixSimplexMap N))⁻¹)*volume T := by
  rw [← Measure.map_apply (prefixSimplexMap N).continuous_of_finiteDimensional.measurable hT,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (prefixSimplexMap_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr (prefixSimplexMap_det_pos N))]

lemma prefixSimplexMap_ford_ratio (N : ℕ) (B : ℝ) (u : Fin (N+2) → ℝ)
    (i : Fin (N+2)) :
    (∑ j, prefixWeight (N+2) i j*prefixSimplexMap (N+2) u j)/
        (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) = u i/fordSimplexCenter N B i := by
  rw [← prefixSimplexMap_coordinate]
  have hi : i.val ≤ N+2 := by omega
  have hden : fordSimplexCenter N B i = rho^(i.val+1)*
      (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) := by
    unfold fordSimplexCenter
    rw [Nat.cast_sub hi]
    push_cast
    field_simp
    ring
  rw [hden, div_div]

lemma prefixSimplexMap_bad_preimage (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i =
      prefixSimplexMap (N+2) ⁻¹'
        (standardSimplex (N+2) B ∩
          {v | (1/40:ℝ) < |(∑ j, prefixWeight (N+2) i j*v j)/
            (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ))-1|}) := by
  rw [prefixSimplexMap_preimage]
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage, fordCoordinateBad, Set.mem_ofPred_eq,
    prefixSimplexMap_ford_ratio]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexTilt
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal changes of variables bounding a linear cap of the standard simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplexDiagonal_apply (N : ℕ) (w v : Fin N → ℝ) (i : Fin N) :
    simplexDiagonal N w v i = w i*v i := by
  simp [simplexDiagonal, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma simplexDiagonal_det (N : ℕ) (w : Fin N → ℝ) :
    LinearMap.det (simplexDiagonal N w) = ∏ i, w i := by
  rw [simplexDiagonal, LinearMap.det_toLin', Matrix.det_diagonal]

lemma positiveSimplex_eq_preimage (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (T : ℝ) :
    positiveSimplex N w T = simplexDiagonal N w ⁻¹' standardSimplex N T := by
  ext v
  simp only [positiveSimplex, standardSimplex, Set.mem_preimage, Set.mem_ofPred_eq,
    simplexDiagonal_apply]
  exact and_congr (forall_congr' fun i => (mul_nonneg_iff_of_pos_left (hw i)).symm) Iff.rfl

lemma volume_positiveSimplex (N : ℕ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) {T : ℝ} (hT : 0 ≤ T) :
    volume (positiveSimplex N w T) =
      ENNReal.ofReal (T^N / ((N.factorial : ℝ)*∏ i, w i)) := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [positiveSimplex_eq_preimage N w hw,
    ← Measure.map_apply (simplexDiagonal N w).continuous_of_finiteDimensional.measurable
      (measurableSet_standardSimplex N T),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [simplexDiagonal_det]; exact hp.ne'),
    simplexDiagonal_det, Measure.smul_apply, smul_eq_mul, volume_standardSimplex N hT,
    abs_inv, abs_of_pos hp, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le)]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma simplex_lower_cap_subset (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) :
    standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t} ⊆
      positiveSimplex N (fun i => 1+s*w i) (B+s*t) := by
  rintro v ⟨⟨hv,hB⟩,ht⟩
  refine ⟨hv,?_⟩
  calc
    _ = (∑ i, v i)+s*(∑ i, w i*v i) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ B+s*t := add_le_add hB (mul_le_mul_of_nonneg_left ht hs)

/-- A finite-dimensional Chernoff bound, before logarithmic estimation. -/
theorem volume_simplex_lower_cap_le (N : ℕ) (B t s : ℝ) (w : Fin N → ℝ)
    (hs : 0 ≤ s) (hw : ∀ i, 0 < 1+s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      (B+s*t)^N / ((N.factorial : ℝ)*∏ i, (1+s*w i)) := by
  have hb : volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t}) ≤
      volume (positiveSimplex N (fun i => 1+s*w i) (B+s*t)) :=
    measure_mono (simplex_lower_cap_subset N B t s w hs)
  rw [volume_positiveSimplex N _ hw hT] at hb
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hT _)
    (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hw i).le))))] at hh
  exact hh

lemma simplex_upper_cap_eq_lower (N : ℕ) (w : Fin N → ℝ) (t : ℝ) :
    {v : Fin N → ℝ | t ≤ ∑ i, w i*v i} =
      {v | (∑ i, (-w i)*v i) ≤ -t} := by
  ext v
  simp only [Set.mem_ofPred_eq, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexExponential
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential estimates for linear caps, using only a diagonal volume change. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma log_one_add_quadratic_lower {x : ℝ} (hx : -(1/2 : ℝ) ≤ x) :
    x-2*x^2 ≤ Real.log (1+x) := by
  have hp : 0 < 1+x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  apply le_trans _ hl
  have hm : 0 ≤ x^2*(1+2*x) := mul_nonneg (sq_nonneg x) (by linarith)
  have hid : 1-(1+x)⁻¹ = x/(1+x) := by field_simp <;> ring
  rw [hid]
  exact (le_div_iff₀ hp).mpr (by nlinarith)

lemma tilted_product_lower (N : ℕ) (w : Fin N → ℝ) (s : ℝ)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) :
    Real.exp (s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2)) ≤
      ∏ i, (1+s*w i) := by
  have he : s*(∑ i, w i)-2*s^2*(∑ i, (w i)^2) =
      ∑ i, (s*w i-2*(s*w i)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Real.exp_sum]
  apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
  intro i _
  have hp : 0 < 1+s*w i := by have := hw i; linarith
  exact (Real.exp_le_exp.mpr (log_one_add_quadratic_lower (hw i))).trans_eq (Real.exp_log hp)

lemma simplex_tilt_power (N : ℕ) {B : ℝ} (hB : 0 < B) (s t : ℝ)
    (hT : 0 ≤ B+s*t) :
    (B+s*t)^N ≤ B^N*Real.exp ((N:ℝ)*(s*t/B)) := by
  have hbase : B+s*t ≤ B*Real.exp (s*t/B) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*t/B)) hB.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp [hB.ne']
    ring
  calc
    _ ≤ (B*Real.exp (s*t/B))^N := pow_le_pow_left₀ hT hbase N
    _ = _ := by rw [mul_pow, Real.exp_nat_mul]

/-- An explicit Chernoff estimate for the lower cap of a uniform simplex. -/
theorem volume_simplex_lower_cap_exp (N : ℕ) {B : ℝ} (hB : 0 < B)
    (t s : ℝ) (w : Fin N → ℝ) (hs : 0 ≤ s)
    (hw : ∀ i, -(1/2 : ℝ) ≤ s*w i) (hT : 0 ≤ B+s*t) :
    (volume (standardSimplex N B ∩ {v | (∑ i, w i*v i) ≤ t})).toReal ≤
      Real.exp ((N:ℝ)*(s*t/B)-s*(∑ i, w i)+2*s^2*(∑ i, (w i)^2))*
        (volume (standardSimplex N B)).toReal := by
  have hp : ∀ i, 0 < 1+s*w i := fun i => by have := hw i; linarith
  have hprod := tilted_product_lower N w s hw
  have hpow := simplex_tilt_power N hB s t hT
  have hfac : 0 < (N.factorial:ℝ) := by positivity
  have hden : 0 < (N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) := by positivity
  apply (volume_simplex_lower_cap_le N B t s w hs hp hT).trans
  calc
    _ ≤ (B^N*Real.exp ((N:ℝ)*(s*t/B)))/
        ((N.factorial:ℝ)*Real.exp (s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2))) := by
      apply div_le_div₀ (by positivity) hpow hden
      exact mul_le_mul_of_nonneg_left hprod hfac.le
    _ = _ := by
      rw [volume_standardSimplex N hB.le, ENNReal.toReal_ofReal (by positivity)]
      conv_rhs => rw [show (N:ℝ)*(s*t/B)-s*(∑ i,w i)+2*s^2*(∑ i,(w i)^2) =
        (N:ℝ)*(s*t/B)-(s*(∑ i,w i)-2*s^2*(∑ i,(w i)^2)) by ring, Real.exp_sub]
      ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexFixedCaps
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-deviation cap estimates with constants uniform in the dimension. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplex_fixed_caps (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    let t := B*((m:ℝ)-1)/(N:ℝ)
    let s := concentrationTilt M
    let E := Real.exp (3*s*(K+1)-(s/100)*((m:ℝ)-1))*(volume (standardSimplex N B)).toReal
    (volume (standardSimplex N B ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t})).toReal ≤ E ∧
    (volume (standardSimplex N B ∩ {v | (41/40)*t ≤ ∑ j,w j*v j})).toReal ≤ E := by
  dsimp only
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let s := concentrationTilt M
  have hs : 0 < s := concentrationTilt_pos hM
  have hsle : s ≤ 1/320 := concentrationTilt_le hM
  have hsm : s*M = 1/320 := concentrationTilt_mul hM
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m:ℝ) ≤ N := by exact_mod_cast hmN
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have htB : t ≤ B := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hl : 0 ≤ B+s*((39/40)*t) := by positivity
  have hu : 0 ≤ B+s*(-((41/40)*t)) := by
    have hh : s*((41/40)*t) ≤ (1/320)*((41/40)*B) :=
      mul_le_mul hsle (mul_le_mul_of_nonneg_left htB (by norm_num)) (by positivity) (by norm_num)
    nlinarith
  have hwl (j : Fin N) : -(1/2:ℝ) ≤ s*w j := by
    have := mul_nonneg hs.le (hw j).1
    linarith
  have hwu (j : Fin N) : -(1/2:ℝ) ≤ s*(-w j) := by
    have hh := mul_le_mul_of_nonneg_left (hw j).2 hs.le
    rw [hsm] at hh
    nlinarith
  have he := concentration_exponents hM hK (show (1:ℝ) ≤ m by linarith) hS hQ
  have hel : (N:ℝ)*(s*((39/40)*t)/B)-s*(∑ j,w j)+2*s^2*(∑ j,(w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*((39/40)*t)/B) = s*(39/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    exact he.1
  have heu : (N:ℝ)*(s*(-((41/40)*t))/B)-s*(∑ j,(-w j))+2*s^2*(∑ j,(-w j)^2) ≤
      3*s*(K+1)-(s/100)*((m:ℝ)-1) := by
    have hid : (N:ℝ)*(s*(-((41/40)*t))/B) = -s*(41/40)*((m:ℝ)-1) := by
      dsimp [t]
      field_simp
    rw [hid]
    simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, neg_sq]
    exact he.2
  constructor
  · exact (volume_simplex_lower_cap_exp N hB ((39/40)*t) s w hs.le hwl hl).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hel) ENNReal.toReal_nonneg)
  · rw [simplex_upper_cap_eq_lower]
    exact (volume_simplex_lower_cap_exp N hB (-((41/40)*t)) s (fun j => -w j) hs.le hwu hu).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr heu) ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexConcentration
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform two-sided concentration of bounded linear forms on a simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma volume_simplex_fixed_deviation (M K : ℝ) (hM : 1 ≤ M) (hK : 0 ≤ K)
    (N m : ℕ) (hm : 2 ≤ m) (hmN : m ≤ N) (B : ℝ) (hB : 0 < B)
    (w : Fin N → ℝ) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ M)
    (hS : |(∑ j,w j)-(m:ℝ)| ≤ K) (hQ : (∑ j,(w j)^2) ≤ M*((m:ℝ)+K)) :
    (volume (standardSimplex N B ∩
      {v | (1/40:ℝ) < |(∑ j,w j*v j)/(B*((m:ℝ)-1)/(N:ℝ))-1|})).toReal ≤
      2*Real.exp (3*concentrationTilt M*(K+1))*
        Real.exp (-(concentrationTilt M/100)*(m-1:ℕ))*
          (volume (standardSimplex N B)).toReal := by
  let t := B*((m:ℝ)-1)/(N:ℝ)
  let S := standardSimplex N B
  let L := S ∩ {v | (∑ j,w j*v j) ≤ (39/40)*t}
  let U := S ∩ {v | (41/40)*t ≤ ∑ j,w j*v j}
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have ht : 0 < t := div_pos (mul_pos hB (by linarith)) hn
  have hsub : S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|} ⊆ L ∪ U := by
    rintro v ⟨hv,hbad⟩
    by_cases hl : (∑ j,w j*v j) ≤ (39/40)*t
    · exact Or.inl ⟨hv,hl⟩
    · refine Or.inr ⟨hv,?_⟩
      by_contra hu
      have hlo : 39/40 < (∑ j,w j*v j)/t := (lt_div_iff₀ ht).mpr (lt_of_not_ge hl)
      have hup : (∑ j,w j*v j)/t < 41/40 := (div_lt_iff₀ ht).mpr (lt_of_not_ge hu)
      have habs : |(∑ j,w j*v j)/t-1| ≤ (1/40:ℝ) := abs_le.mpr ⟨by linarith,by linarith⟩
      exact (not_lt_of_ge habs) hbad
  have hfin : volume S ≠ ⊤ := by
    dsimp [S]
    rw [volume_standardSimplex N hB.le]
    exact ENNReal.ofReal_ne_top
  have hL : volume L ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hU : volume U ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hh : volume (S ∩ {v | (1/40:ℝ) < |(∑ j,w j*v j)/t-1|}) ≤ volume L+volume U :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hL,hU⟩) hh
  rw [ENNReal.toReal_add hL hU] at hr
  have hcaps := simplex_fixed_caps M K hM hK N m hm hmN B hB w hw hS hQ
  apply hr.trans
  calc
    _ ≤ 2*(Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal) := by
      have hl : (volume L).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.1
      have hu : (volume U).toReal ≤ Real.exp (3*concentrationTilt M*(K+1)-
        (concentrationTilt M/100)*((m:ℝ)-1))*(volume S).toReal := hcaps.2
      linarith only [hl,hu]
    _ = _ := by
      dsimp only [S]
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      ring_nf

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixConcentration
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unconditional coordinate concentration for the exact prefix simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_transfer (N : ℕ) (B R : ℝ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T)
    (hbound : (volume T).toReal ≤ R*(volume (standardSimplex N B)).toReal) :
    (volume (prefixSimplexMap N ⁻¹' T)).toReal ≤
      R*(volume (prefixRegion N B 0 0)).toReal := by
  rw [volume_prefixSimplexMap_preimage N T hT, ENNReal.toReal_mul,
    prefixSimplexMap_preimage, volume_prefixSimplexMap_preimage N _
      (measurableSet_standardSimplex N B), ENNReal.toReal_mul]
  exact (mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg).trans_eq (by ring)

theorem prefix_coordinate_concentration_unconditional :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨M,K,hM,hK,hweights⟩ := prefixWeight_bounds
  let s := concentrationTilt M
  refine ⟨2*Real.exp (3*s*(K+1)),s/100,by positivity,
    div_pos (concentrationTilt_pos hM) (by norm_num),?_⟩
  intro N B hB i hi
  obtain ⟨hw,hS,hQ⟩ := hweights (N+2) i
  have hm : 2 ≤ N+2-i.val := by omega
  have hmN : N+2-i.val ≤ N+2 := Nat.sub_le _ _
  have hc := volume_simplex_fixed_deviation M K hM hK.le (N+2) (N+2-i.val) hm hmN B hB
    (prefixWeight (N+2) i) hw hS hQ
  have he : N+2-i.val-1 = N+2-(i.val+1) := by omega
  rw [he] at hc
  rw [prefixSimplexMap_bad_preimage]
  apply prefixSimplexMap_transfer
  · apply (measurableSet_standardSimplex _ _).inter
    apply measurableSet_lt measurable_const
    fun_prop
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hc

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridVolume
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric volumes of the same disjoint boxes used in the prime sum. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma measurableSet_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    MeasurableSet (unitGridCell m) := by
  exact MeasurableSet.pi (Set.to_countable Set.univ) (fun _ _ => measurableSet_Ico)

lemma volume_unitGridCell {N : ℕ} (m : Fin N → ℕ) :
    volume (unitGridCell m) = 1 := by
  unfold unitGridCell
  rw [Real.volume_pi_Ico]
  simp

lemma unitGridCell_disjoint {N : ℕ} {m n : Fin N → ℕ} (hmn : m ≠ n) :
    Disjoint (unitGridCell m) (unitGridCell n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Set.disjoint_left.mpr
  intro u hum hun
  have hm := hum i (Set.mem_univ _)
  have hn := hun i (Set.mem_univ _)
  rcases lt_or_gt_of_ne hi with hi | hi
  · have h : (m i : ℝ)+1 ≤ n i := by exact_mod_cast (show m i+1 ≤ n i by omega)
    linarith [hm.2, hn.1]
  · have h : (n i : ℝ)+1 ≤ m i := by exact_mod_cast (show n i+1 ≤ m i by omega)
    linarith [hn.2, hm.1]

lemma volume_gridRegion {N : ℕ} (K : Finset (Fin N → ℕ)) :
    volume (gridRegion K) = K.card := by
  unfold gridRegion
  rw [measure_biUnion_finset
    (fun m _ n _ hmn => unitGridCell_disjoint hmn)
    (fun m _ => measurableSet_unitGridCell m)]
  simp only [volume_unitGridCell, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma gridRegion_volume_real {N : ℕ} (K : Finset (Fin N → ℕ)) :
    (volume (gridRegion K)).toReal = K.card := by
  rw [volume_gridRegion]
  simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CubeBoundary
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes meeting the boundary lie in explicit prefix-slack shells. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitGridCell_coordinate_distance {N : ℕ} {m : Fin N → ℕ}
    {u v : Fin N → ℝ} (hu : u ∈ unitGridCell m) (hv : v ∈ unitGridCell m) :
    ∀ i, |u i-v i| ≤ 1 := by
  intro i
  have hui := hu i (Set.mem_univ _)
  have hvi := hv i (Set.mem_univ _)
  exact abs_le.mpr ⟨by linarith [hui.1, hvi.2], by linarith [hui.2, hvi.1]⟩

lemma prefixLinear_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) (i : Fin N) :
    |prefixLinear N u i-prefixLinear N v i| ≤ ((N-i.val : ℕ) : ℝ)^2 := by
  have he : prefixLinear N u i-prefixLinear N v i =
      (u i-v i)-∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
    rw [prefixLinear_apply, prefixLinear_apply]
    have hs : (∑ j : Fin N, ((if i < j then a (j.val-i.val)*u j else 0)-
        (if i < j then a (j.val-i.val)*v j else 0))) =
        ∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j) := by
      have heach (j : Fin N) :
          ((if i < j then a (j.val-i.val)*u j else 0)-
            (if i < j then a (j.val-i.val)*v j else 0)) =
          if i < j then a (j.val-i.val)*(u j-v j) else 0 := by
        split_ifs <;> ring
      simp_rw [heach]
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp
    calc
      _ = (u i-v i)-((∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0)-
          ∑ j : Fin N, if i < j then a (j.val-i.val)*v j else 0) := by ring
      _ = _ := by rw [← Finset.sum_sub_distrib, hs]
  rw [he]
  have hcoef (j : Fin N) (hj : j ∈ Finset.Ioi i) :
      0 ≤ a (j.val-i.val) ∧ a (j.val-i.val) ≤ (N-i.val : ℕ) := by
    have hji : i < j := Finset.mem_Ioi.mp hj
    have hji' : i.val < j.val := hji
    refine ⟨(a_pos (by omega)).le, (a_le_index (by omega)).trans ?_⟩
    exact_mod_cast (show j.val-i.val ≤ N-i.val by omega)
  calc
    _ ≤ |u i-v i|+|∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j)| := by simpa using abs_sub_le (u i-v i) 0 (∑ j ∈ Finset.Ioi i, a (j.val-i.val)*(u j-v j))
    _ ≤ 1+∑ j ∈ Finset.Ioi i, |a (j.val-i.val)*(u j-v j)| :=
      add_le_add (hdist i) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1+∑ _j ∈ Finset.Ioi i, ((N-i.val : ℕ) : ℝ) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hcoef j hj).1]
      exact (mul_le_of_le_one_right (hcoef j hj).1 (hdist j)).trans (hcoef j hj).2
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Ioi]
      have hi : i.val < N := i.isLt
      have he : N-1-i.val = N-i.val-1 := by omega
      rw [he, Nat.cast_sub (by omega : 1 ≤ N-i.val), Nat.cast_one]
      have hn : (1 : ℝ) ≤ (N-i.val : ℕ) := by exact_mod_cast (show 1 ≤ N-i.val by omega)
      nlinarith

lemma prefixBudget_cube_error {N : ℕ} (u v : Fin N → ℝ)
    (hdist : ∀ j, |u j-v j| ≤ 1) :
    |(∑ j, a (j.val+1)*u j)-(∑ j, a (j.val+1)*v j)| ≤ (N : ℝ)^2 := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |a (j.val+1)*u j-a (j.val+1)*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, (N : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul, abs_of_pos (a_pos (by omega))]
      apply (mul_le_of_le_one_right (a_pos (by omega)).le (hdist j)).trans
      exact (a_le_index (by omega)).trans (by exact_mod_cast (show j.val+1 ≤ N by omega))
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexScaling
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal normalization of the enlarged simplexes used by prime boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma simplexScale_apply {N : ℕ} (κ u : Fin N → ℝ) (i : Fin N) :
    simplexScale κ u i = u i/κ i := by
  simp [simplexScale, Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

lemma simplexScale_det {N : ℕ} (κ : Fin N → ℝ) :
    LinearMap.det (simplexScale κ) = (∏ i, κ i)⁻¹ := by
  rw [simplexScale, LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_inv_distrib]

lemma enlargedSimplex_mapsTo {N : ℕ} {B β₀ : ℝ} {β κ : Fin N → ℝ}
    (hβ₀ : 0 < β₀) (hβ : ∀ i, 0 < β i) (hκ : ∀ i, 0 < κ i)
    (htop : ∀ i, β₀ ≤ κ i) (hstep : ∀ i j, i < j → β i*κ i ≤ κ j) :
    Set.MapsTo (simplexScale κ) (enlargedSimplex N B β₀ β) (prefixRegion N B 0 0) := by
  intro u hu
  constructor
  · intro i
    rw [prefixLinear_apply, simplexScale_apply]
    simp only [simplexScale_apply]
    have hsum : (∑ j : Fin N, if i < j then a (j.val-i.val)*(u j/κ j) else 0) ≤
        (∑ j : Fin N, if i < j then a (j.val-i.val)*u j else 0)/(β i*κ i) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · have hnonneg := mul_nonneg (a_pos (j := j.val-i.val) (by have := hij; simp only [Fin.lt_def] at this; omega)).le (hu.1 j)
        calc
          _ = (a (j.val-i.val)*u j)/κ j := by ring
          _ ≤ _ := div_le_div_of_nonneg_left hnonneg (mul_pos (hβ i) (hκ i)) (hstep i j hij)
      · simp
    have hb := div_le_div_of_nonneg_right (hu.2.1 i) (mul_pos (hβ i) (hκ i)).le
    have he : (β i*u i)/(β i*κ i) = u i/κ i := by field_simp [(hβ i).ne', (hκ i).ne']
    rw [he] at hb
    have hh := hsum.trans hb
    change 0 ≤ u i/κ i-_
    linarith
  · simp only [simplexScale_apply, sub_zero]
    calc
      _ ≤ (∑ i : Fin N, a (i.val+1)*u i)/β₀ := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro i _
        calc
          _ = (a (i.val+1)*u i)/κ i := by ring
          _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (a_pos (by omega)).le (hu.1 i)) hβ₀ (htop i)
      _ ≤ (β₀*B)/β₀ := div_le_div_of_nonneg_right hu.2.2 hβ₀.le
      _ = B := by field_simp

lemma enlargementScale_pos {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    0 < enlargementScale β i :=
  Finset.prod_pos (fun r _ => lt_of_lt_of_le zero_lt_one (hβ r))

lemma enlargementScale_top {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    β 0 ≤ enlargementScale β i := by
  have hh : (∏ r ∈ Finset.range 1, β r) ≤ ∏ r ∈ Finset.range (i.val+1), β r := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono (by omega))
    · intro r _
      exact (zero_le_one.trans (hβ r))
    · intro r _ _
      exact hβ r
  simpa [enlargementScale] using hh

lemma enlargementScale_step {N : ℕ} {β : ℕ → ℝ} (hβ : ∀ r, 1 ≤ β r)
    (i j : Fin N) (hij : i < j) :
    β (i.val+1)*enlargementScale β i ≤ enlargementScale β j := by
  have hh : (∏ r ∈ Finset.range (i.val+2), β r) ≤ ∏ r ∈ Finset.range (j.val+1), β r := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono (by have := hij; simp only [Fin.lt_def] at this; omega))
    · intro r _
      exact (zero_le_one.trans (hβ r))
    · intro r _ _
      exact hβ r
  rw [show i.val+2=(i.val+1)+1 by omega, Finset.prod_range_succ] at hh
  simpa only [enlargementScale, mul_comm] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedCube
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit boxes around a simplex prefix, without coordinate-band hypotheses. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixCubeCost_nonneg (N : ℕ) : 0 ≤ prefixCubeCost N := by
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (g_pos _).le (sq_nonneg _)))

lemma prefixRegion_unit_cube {N : ℕ} {B : ℝ} {u v : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (hd : ∀ i, |u i-v i| ≤ 1) :
    v ∈ prefixRegion N (B+(N:ℝ)^2) 0
      (fun i => -((N-i.val:ℕ):ℝ)^2) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hh := (le_abs_self _).trans (prefixLinear_cube_error u v hd i)
    have hi := hu.1 i
    change 0 ≤ prefixLinear N u i at hi
    linarith
  · have hh := (neg_le_abs _).trans (prefixBudget_cube_error u v hd)
    have hi := hu.2
    simp only [sub_zero] at hi ⊢
    linarith

lemma simplexScale_unit_distance {N : ℕ} {κ u v : Fin N → ℝ}
    (hκ : ∀ i, 1 ≤ κ i) (hd : ∀ i, |u i-v i| ≤ 1) :
    ∀ i, |simplexScale κ u i-simplexScale κ v i| ≤ 1 := by
  intro i
  simp only [simplexScale_apply, ← sub_div, abs_div, abs_of_pos (zero_lt_one.trans_le (hκ i))]
  exact (div_le_iff₀ (zero_lt_one.trans_le (hκ i))).mpr (by
    simpa only [one_mul] using (hd i).trans (hκ i))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine correction for the unit boxes in a coordinate-deviation count. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma coordinateCubeShift_slack (N : ℕ) (i : Fin N) :
    prefixLinear N (coordinateCubeShift N) i = ((N-i.val:ℕ):ℝ)^2 := by
  have hh := ((prefixLinear N).equivOfDetNeZero
    (by rw [prefixLinear_det]; norm_num)).apply_symm_apply
      (fun i : Fin N => ((N-i.val:ℕ):ℝ)^2)
  exact congrFun hh i

lemma coordinateCubeShift_coordinate (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*((N-j.val:ℕ):ℝ)^2 else 0 := by
  rw [prefixLinear_coordinate N (coordinateCubeShift N) i]
  simp only [coordinateCubeShift_slack]

lemma coordinateCubeShift_nonneg (N : ℕ) (i : Fin N) :
    0 ≤ coordinateCubeShift N i := by
  rw [coordinateCubeShift_coordinate]
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (g_pos _).le (sq_nonneg _)
  · exact le_rfl

lemma coordinateCubeShift_budget (N : ℕ) :
    ∑ i : Fin N,a (i.val+1)*coordinateCubeShift N i =
      ∑ i : Fin N,g (i.val+1)*((N-i.val:ℕ):ℝ)^2 := by
  rw [←weighted_prefixLinear]
  simp only [coordinateCubeShift_slack]

lemma coordinateCubeShift_mem {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N (B+(N:ℝ)^2) 0
      (fun i => -((N-i.val:ℕ):ℝ)^2)) :
    u+coordinateCubeShift N ∈ prefixRegion N (B+prefixCubeCost N) 0 0 := by
  refine ⟨fun i => ?_,?_⟩
  · rw [map_add,Pi.add_apply,coordinateCubeShift_slack]
    have hh := hu.1 i
    change -((N-i.val:ℕ):ℝ)^2 ≤ prefixLinear N u i at hh
    change 0 ≤ prefixLinear N u i+((N-i.val:ℕ):ℝ)^2
    linarith only [hh]
  · simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,coordinateCubeShift_budget]
    have hh := hu.2
    simp only [sub_zero] at hh ⊢
    unfold prefixCubeCost
    linarith only [hh]

/-- A measurable coordinate event can be counted on the corrected simplex.
The pointwise premise will be supplied by the fixed-tolerance band arithmetic. -/
theorem coordinate_grid_volume_bound {N : ℕ} (hN : 0<N)
    (B β₀ : ℝ) (β κ : Fin N → ℝ) (K : Finset (Fin N → ℕ))
    (T : Set (Fin N → ℝ)) (hT : MeasurableSet T)
    (hβ₀ : 0<β₀) (hβ : ∀ i,0<β i) (hκ : ∀ i,1 ≤ κ i)
    (htop : ∀ i,β₀ ≤ κ i)
    (hstep : ∀ i j,i<j → β i*κ i ≤ κ j)
    (hK : ∀ b∈K,∃ u∈unitGridCell b,u∈enlargedSimplex N B β₀ β ∧
      ∀ v∈unitGridCell b,simplexScale κ v+coordinateCubeShift N∈T) :
    (K.card:ℝ) ≤ (∏ i,κ i)*
      (volume (prefixRegion N (B+prefixCubeCost N) 0 0 ∩ T)).toReal := by
  let S := prefixRegion N (B+prefixCubeCost N) 0 0 ∩ T
  have hκpos (i) : 0<κ i := zero_lt_one.trans_le (hκ i)
  have hp : 0<∏ i,κ i := Finset.prod_pos (fun i _ => hκpos i)
  have hd : LinearMap.det (simplexScale κ)≠0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hS : MeasurableSet S := (measurableSet_prefixRegion _ _ _ _).inter hT
  have hsub : gridRegion K ⊆ simplexScale κ ⁻¹'
      ((fun u => u+coordinateCubeShift N) ⁻¹' S) := by
    intro v hv
    obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hub,hu,hevent⟩ := hK b hb
    refine ⟨?_,hevent v hvb⟩
    apply coordinateCubeShift_mem
    exact prefixRegion_unit_cube (enlargedSimplex_mapsTo hβ₀ hβ hκpos htop hstep hu)
      (simplexScale_unit_distance hκ (unitGridCell_coordinate_distance hub hvb))
  have hvol : volume (gridRegion K) ≤ ENNReal.ofReal (∏ i,κ i)*volume S := by
    apply (measure_mono hsub).trans_eq
    rw [←Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable
      (hS.preimage (by fun_prop)),
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd,simplexScale_det,
      inv_inv,abs_of_pos hp,Measure.smul_apply,smul_eq_mul,
      measure_preimage_add_right]
  have hfin : volume S≠⊤ := ne_top_of_le_ne_top
    (prefixRegion_volume_ne_top hN _) (measure_mono Set.inter_subset_left)
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hvol
  simpa only [gridRegion_volume_real,ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateBandTransfer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-tolerance arithmetic for transferring the simplex concentration event
through diagonal normalization and the unit-box correction. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_band_transfer {u v S T κ : ℝ} (_hS : 0<S) (hT : 0<T)
    (hκ : 0 ≤ κ)
    (hcenter : (99/100:ℝ)*S ≤ κ*T ∧ κ*T ≤ (101/100:ℝ)*S)
    (hdist : |u-κ*v| ≤ S/100)
    (hgood : |v/T-1| ≤ (1/40:ℝ)) :
    (19/20:ℝ)*S ≤ u ∧ u ≤ (21/20:ℝ)*S := by
  have hvlo : (39/40:ℝ)*T ≤ v := by
    have hh := (abs_le.mp hgood).1
    have hh' : (39/40:ℝ) ≤ v/T := by linarith only [hh]
    exact (le_div_iff₀ hT).mp hh'
  have hvhi : v ≤ (41/40:ℝ)*T := by
    have hh := (abs_le.mp hgood).2
    have hh' : v/T ≤ (41/40:ℝ) := by linarith only [hh]
    exact (div_le_iff₀ hT).mp hh'
  have hlo := mul_le_mul_of_nonneg_left hvlo hκ
  have hhi := mul_le_mul_of_nonneg_left hvhi hκ
  have hdist' := abs_le.mp hdist
  constructor <;> nlinarith only [hcenter.1,hcenter.2,hlo,hhi,hdist'.1,hdist'.2]

lemma coordinate_cube_band_transfer {N : ℕ} {b : Fin N → ℕ}
    {u v κ : Fin N → ℝ} {i : Fin N} {S T : ℝ}
    (hu : u∈unitGridCell b) (hv : v∈unitGridCell b)
    (hS : 0<S) (hT : 0<T) (hκ : 1 ≤ κ i)
    (hcenter : (99/100:ℝ)*S ≤ κ i*T ∧ κ i*T ≤ (101/100:ℝ)*S)
    (herror : 1+κ i*coordinateCubeShift N i ≤ S/100)
    (hgood : |(simplexScale κ v+coordinateCubeShift N) i/T-1| ≤ (1/40:ℝ)) :
    (19/20:ℝ)*S ≤ u i ∧ u i ≤ (21/20:ℝ)*S := by
  apply coordinate_band_transfer hS hT (zero_le_one.trans hκ) hcenter _ hgood
  have hκpos : 0<κ i := zero_lt_one.trans_le hκ
  have he : u i-κ i*(simplexScale κ v+coordinateCubeShift N) i =
      (u i-v i)-κ i*coordinateCubeShift N i := by
    simp only [Pi.add_apply,simplexScale_apply]
    field_simp
    ring
  rw [he]
  have hh : |(u i-v i)-κ i*coordinateCubeShift N i| ≤
      |u i-v i|+|κ i*coordinateCubeShift N i| := by
    simpa using abs_sub_le (u i-v i) 0 (κ i*coordinateCubeShift N i)
  apply hh.trans
  have hnon : 0 ≤ κ i*coordinateCubeShift N i :=
    mul_nonneg hκpos.le (coordinateCubeShift_nonneg N i)
  rw [abs_of_nonneg hnon]
  have hdist := unitGridCell_coordinate_distance hu hv i
  linarith only [hdist,herror]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedCubeCost
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additive unit-box cost is uniformly comparable to one renewal coefficient. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma summable_shifted_square_geometric :
    Summable (fun n : ℕ => ((n:ℝ)+1)^2*rho^n) := by
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 := summable_geometric_of_lt_one rho_pos.le rho_lt_one
  convert (h2.add (h1.mul_left 2)).add h0 using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simp only [pow_one]
  ring

theorem prefixCubeCost_normalized_bound : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, prefixCubeCost N*rho^N ≤ C := by
  obtain ⟨K,hK,hg⟩ := (normalizedRenewal_properties fordRenewalInput).2
  let S := ∑' n : ℕ, ((n:ℝ)+1)^2*rho^n
  have hS : 0 < S := by
    have hh := summable_shifted_square_geometric.le_tsum 0
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
    norm_num at hh
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hh
  refine ⟨(1+K)*S, mul_pos (by linarith) hS, fun N => ?_⟩
  have hfirst : (N:ℝ)^2*rho^N ≤ S := by
    apply le_trans _ (summable_shifted_square_geometric.le_tsum N
      (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _)))
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg rho_pos.le _)
    nlinarith [Nat.cast_nonneg N (α:=ℝ)]
  have hsum : (∑ i : Fin N, g (i.val+1)*((N-i.val:ℕ):ℝ)^2)*rho^N ≤ K*S := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i : Fin N, K*(((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) := by
        apply Finset.sum_le_sum
        intro i _
        have hi : i.val+1+(N-i.val-1)=N := by omega
        have he : ((N-i.val:ℕ):ℝ)=((N-i.val-1:ℕ):ℝ)+1 := by
          exact_mod_cast (show N-i.val=N-i.val-1+1 by omega)
        have hh : g (i.val+1)*rho^(i.val+1) ≤ K := by
          have hh := hg (i.val+1)
          rw [Real.norm_eq_abs, abs_of_pos (normalizedRenewal_pos _)] at hh
          exact hh
        have hm := mul_le_mul_of_nonneg_right hh
          (show 0 ≤ (((N-i.val-1:ℕ):ℝ)+1)^2*rho^(N-i.val-1) by exact mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
        have hp : rho^N = rho^(i.val+1)*rho^(N-i.val-1) := by
          rw [← pow_add, hi]
        rw [hp, he]
        nlinarith only [hm]
      _ = K*∑ j ∈ Finset.range N, ((j:ℝ)+1)^2*rho^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_bij (fun i _ => N-i.val-1)
        · intro i _
          exact Finset.mem_range.mpr (by omega)
        · intro i _ j _ hij
          apply Fin.ext
          have := i.isLt
          have := j.isLt
          omega
        · intro j hj
          have hj := Finset.mem_range.mp hj
          exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
        · intro i _
          ring
      _ ≤ K*S := mul_le_mul_of_nonneg_left
        (summable_shifted_square_geometric.sum_le_tsum _
          (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))) hK
  unfold prefixCubeCost
  rw [add_mul]
  nlinarith only [hfirst,hsum]

/-- For prefixes ending `H` coordinates before the natural dimension, the
unit-box enlargement has a uniformly bounded relative volume cost. -/
theorem prefixCubeCost_relative_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ N ≤ m x,
      (N:ℝ)*prefixCubeCost N/B x ≤ C*rho^(m x-N) := by
  obtain ⟨A,hA,ha⟩ := prefixCubeCost_normalized_bound
  refine ⟨2*A/lam, div_pos (mul_pos (by norm_num) hA) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound, B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hN
  have hcost : prefixCubeCost N ≤ A/rho^N :=
    (le_div_iff₀ (pow_pos rho_pos N)).mpr (ha N)
  have hNm : (N:ℝ) ≤ m x := by exact_mod_cast hN
  have hp : rho^N*rho^(m x-N)=rho^(m x) := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  calc
    _ ≤ (m x:ℝ)*(A/rho^N)/B x := by
      apply div_le_div_of_nonneg_right _ hB.le
      exact mul_le_mul hNm hcost (prefixCubeCost_nonneg N) (Nat.cast_nonneg _)
    _ = A*((m x:ℝ)/(B x*rho^(m x)))*rho^(m x-N) := by
      rw [← hp]
      field_simp [rho_pos.ne']
    _ ≤ A*(2/lam)*rho^(m x-N) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hx hA.le) (pow_nonneg rho_pos.le _)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCubeSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine unit-box error at one coordinate depends only on its remaining
dimension, with the same renewal bound as the total box cost. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma coordinateCubeShift_sum (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i = ∑ k∈Finset.range (N-i.val),
      g k*((N-i.val-k:ℕ):ℝ)^2 := by
  rw [coordinateCubeShift_coordinate,←Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val-i.val)
  · intro j hj
    have hj := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (by have := j.isLt; change i.val ≤ j.val at hj; omega)
  · intro j hj k hk he
    have hj := (Finset.mem_filter.mp hj).2
    have hk := (Finset.mem_filter.mp hk).2
    apply Fin.ext
    change i.val ≤ j.val at hj
    change i.val ≤ k.val at hk
    omega
  · intro k hk
    have hk := Finset.mem_range.mp hk
    let j : Fin N := ⟨i.val+k,by omega⟩
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · change i.val ≤ i.val+k
      omega
    · dsimp only [j]
      omega
  · intro j hj
    have hj := (Finset.mem_filter.mp hj).2
    have he : N-i.val-(j.val-i.val)=N-j.val := by
      have := j.isLt
      change i.val ≤ j.val at hj
      omega
    rw [he]

lemma coordinateCubeShift_le_cost (N : ℕ) (i : Fin N) :
    coordinateCubeShift N i ≤ prefixCubeCost (N-i.val) := by
  let t:=N-i.val
  have ht : 0<t := by dsimp only [t]; exact Nat.sub_pos_of_lt i.isLt
  rw [coordinateCubeShift_sum]
  change (∑ k∈Finset.range t,g k*((t-k:ℕ):ℝ)^2) ≤ prefixCubeCost t
  rw [show Finset.range t=Finset.range ((t-1)+1) by congr 1; omega,
    Finset.sum_range_succ']
  have hs : (∑ k∈Finset.range (t-1),g (k+1)*((t-(k+1):ℕ):ℝ)^2) ≤
      ∑ k∈Finset.range t,g (k+1)*((t-k:ℕ):ℝ)^2 := by
    apply le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le t 1)) ?_)
    · intro k _
      apply mul_le_mul_of_nonneg_left _ (g_pos _).le
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
      exact_mod_cast (show t-(k+1) ≤ t-k by omega)
    · intro k _ _
      exact mul_nonneg (g_pos _).le (sq_nonneg _)
  have he : (∑ k∈Finset.range t,g (k+1)*((t-k:ℕ):ℝ)^2)=
      ∑ k : Fin t,g (k.val+1)*((t-k.val:ℕ):ℝ)^2 :=
    (Fin.sum_univ_eq_sum_range _ _).symm
  rw [he] at hs
  simp only [Nat.sub_zero,show g 0=1 by simp [g],one_mul]
  unfold prefixCubeCost
  linarith only [hs]

theorem coordinateCubeShift_normalized_bound : ∃ C : ℝ,0<C ∧
    ∀ (N : ℕ) (i : Fin N),coordinateCubeShift N i*rho^(N-i.val) ≤ C := by
  obtain ⟨C,hC,hcost⟩ := prefixCubeCost_normalized_bound
  refine ⟨C,hC,fun N i => ?_⟩
  exact (mul_le_mul_of_nonneg_right (coordinateCubeShift_le_cost N i)
    (pow_pos rho_pos _).le).trans (hcost _)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateBoxError
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The relative affine box error vanishes uniformly away from the last
coordinates, even when the retained dimension varies. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem coordinateCubeShift_natural_bound : ∃ C : ℝ,0 < C ∧
    ∀ (M N : ℕ) (j : Fin N),N ≤ M →
      coordinateCubeShift N j*rho^(M-(j.val+1)) ≤ C := by
  obtain ⟨A,hA,hbound⟩ := coordinateCubeShift_normalized_bound
  refine ⟨A/rho,div_pos hA rho_pos,?_⟩
  intro M N j hNM
  have he : N-j.val ≤ M-(j.val+1)+1 := by have := j.isLt; omega
  have hh := (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le he)
    (coordinateCubeShift_nonneg N j)).trans (hbound N j)
  rw [pow_succ] at hh
  apply (le_div_iff₀ rho_pos).mpr
  simpa only [mul_assoc] using hh

theorem fordBandScale_scaled_lower : ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ,i < m x →
      (lam/2)*(m x-i:ℕ) ≤ fordBandScale x i*rho^(m x-i) := by
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro i hi
  have hm : (0:ℝ) < m x := by exact_mod_cast (show 0 < m x by omega)
  have hden : 0 < B x*rho^(m x) := mul_pos hB (pow_pos rho_pos _)
  have hb : (lam/2)*(m x:ℝ) ≤ B x*rho^(m x) := by
    have hh := (div_le_div_iff₀ hden lam_pos).mp hx
    nlinarith only [hh]
  have hb' : lam/2 ≤ B x*rho^(m x)/(m x:ℝ) := (le_div_iff₀ hm).mpr hb
  have he : fordBandScale x i*rho^(m x-i) =
      (B x*rho^(m x)/(m x:ℝ))*(m x-i:ℕ) := by
    unfold fordBandScale
    calc
      _ = B x*(rho^i*rho^(m x-i))*(1-(i:ℝ)/m x) := by ring
      _ = B x*rho^(m x)*(1-(i:ℝ)/m x) := by
        rw [←pow_add,Nat.add_sub_of_le hi.le]
      _ = _ := by
        rw [Nat.cast_sub hi.le]
        field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg _)

theorem coordinate_box_error_small {E : ℝ} (_hE : 0 < E) :
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ (N : ℕ) (j : Fin N),N ≤ m x → P ≤ m x-(j.val+1) →
      ∀ κ : ℝ,0 ≤ κ → κ ≤ E →
        1+κ*coordinateCubeShift N j ≤ fordBandScale x (j.val+1)/100 := by
  obtain ⟨C,hC,hbound⟩ := coordinateCubeShift_natural_bound
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (200*(1+E*C)/lam)),eventually_ge_atTop (1:ℕ)] with P hP hP1
  filter_upwards [fordBandScale_scaled_lower] with x hx
  intro N j hNM hj κ hκ hκE
  have hjm : j.val+1 < m x := by have := j.isLt; omega
  have hh : (P:ℝ) ≤ (m x-(j.val+1):ℕ) := by exact_mod_cast hj
  have hbudget : 200*(1+E*C) ≤ lam*(m x-(j.val+1):ℕ) := by
    have ht := (div_le_iff₀ lam_pos).mp hP
    have hh' := mul_le_mul_of_nonneg_left hh lam_pos.le
    linarith only [ht,hh']
  have hpow : 0 < rho^(m x-(j.val+1)) := pow_pos rho_pos _
  have hprod := mul_le_mul_of_nonneg_left (hbound (m x) N j hNM) hκ
  have hright := mul_le_mul_of_nonneg_right hκE hC.le
  have hscale := hx (j.val+1) hjm
  have hp1 : rho^(m x-(j.val+1)) ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  apply (mul_le_mul_iff_left₀ hpow).mp
  nlinarith only [hprod,hright,hscale,hbudget,hp1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateCenters
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compare the center in a fixed truncated simplex with Ford's natural center. -/
noncomputable section
namespace TotientAsymptotic

lemma truncated_center_factorization {M N i : ℕ} (hi : i < N) (hNM : N ≤ M)
    {B E κ : ℝ} (hB : 0 < B) :
    κ*((B+E)*rho^i*(1-(i:ℝ)/N)) =
      (κ*(1+E/B)*((M:ℝ)/N)*(1-((M-N:ℕ):ℝ)/(M-i:ℕ)))*
        (B*rho^i*(1-(i:ℝ)/M)) := by
  have hN : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hM : (M:ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  have hMi : (M:ℝ)-i≠0 := sub_ne_zero.mpr (by exact_mod_cast (show M≠i by omega))
  rw [Nat.cast_sub hNM,Nat.cast_sub (show i ≤ M by omega)]
  field_simp [hB.ne',hN,hM,hMi]
  ring

lemma small_center_product {u v w r : ℝ}
    (hu : 1 ≤ u ∧ u ≤ (1001/1000:ℝ))
    (hv : 1 ≤ v ∧ v ≤ (1001/1000:ℝ))
    (hw : 1 ≤ w ∧ w ≤ (1001/1000:ℝ))
    (hr : (999/1000:ℝ) ≤ r ∧ r ≤ 1) :
    (99/100:ℝ) ≤ u*v*w*r ∧ u*v*w*r ≤ (101/100:ℝ) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu.1
  have hv0 : 0 ≤ v := zero_le_one.trans hv.1
  have hw0 : 0 ≤ w := zero_le_one.trans hw.1
  have hr0 : 0 ≤ r := (by norm_num : (0:ℝ) ≤ 999/1000).trans hr.1
  have hprodlo : 1 ≤ u*v*w := by
    simpa using mul_le_mul (mul_le_mul hu.1 hv.1 zero_le_one hu0)
      hw.1 zero_le_one (mul_nonneg hu0 hv0)
  have hprodhi : u*v*w ≤ (1001/1000:ℝ)^3 := by
    calc
      _ ≤ (1001/1000:ℝ)*(1001/1000)*(1001/1000) :=
        mul_le_mul (mul_le_mul hu.2 hv.2 hv0 (by norm_num)) hw.2 hw0 (by norm_num)
      _ = _ := by ring
  constructor
  · have hh := mul_le_mul_of_nonneg_right hprodlo hr0
    nlinarith only [hh,hr.1]
  · have hh := mul_le_mul hprodhi hr.2 hr0 (by positivity : (0:ℝ) ≤ (1001/1000)^3)
    norm_num at hh ⊢
    linarith only [hh]

lemma truncated_center_bounds {M N i : ℕ} (hi : i < N) (hNM : N ≤ M)
    {B E κ : ℝ} (hB : 0 < B)
    (hκ : 1 ≤ κ ∧ κ ≤ (1001/1000:ℝ))
    (hE : 0 ≤ E/B ∧ E/B ≤ (1/1000:ℝ))
    (hMN : 1 ≤ (M:ℝ)/N ∧ (M:ℝ)/N ≤ (1001/1000:ℝ))
    (htail : ((M-N:ℕ):ℝ)/(M-i:ℕ) ≤ (1/1000:ℝ)) :
    (99/100:ℝ)*(B*rho^i*(1-(i:ℝ)/M)) ≤ 
      κ*((B+E)*rho^i*(1-(i:ℝ)/N)) ∧
    κ*((B+E)*rho^i*(1-(i:ℝ)/N)) ≤ 
      (101/100:ℝ)*(B*rho^i*(1-(i:ℝ)/M)) := by
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hscale : 0 ≤ B*rho^i*(1-(i:ℝ)/M) := by
    apply mul_nonneg (mul_nonneg hB.le (pow_pos rho_pos _).le)
    exact sub_nonneg.mpr ((div_le_one hm).mpr (by exact_mod_cast (show i ≤ M by omega)))
  have ht0 : 0 ≤ ((M-N:ℕ):ℝ)/(M-i:ℕ) := by positivity
  have hh := small_center_product hκ (show 1 ≤ 1+E/B ∧ 1+E/B ≤ (1001/1000:ℝ) by
    constructor <;> linarith only [hE.1,hE.2]) hMN
    (show (999/1000:ℝ) ≤ 1-((M-N:ℕ):ℝ)/(M-i:ℕ) ∧
      1-((M-N:ℕ):ℝ)/(M-i:ℕ) ≤ 1 by constructor <;> linarith only [htail,ht0])
  rw [truncated_center_factorization hi hNM hB]
  exact ⟨mul_le_mul_of_nonneg_right hh.1 hscale,mul_le_mul_of_nonneg_right hh.2 hscale⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EnlargementCost
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative Jacobian bounds for the enlarged full-dimensional simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma triangular_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, ∑ r ∈ Finset.range (i+1), f r) =
      ∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*f r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    have hs : (∑ r ∈ Finset.range N, ((N+1-r : ℕ) : ℝ)*f r) =
        (∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*f r)+∑ r ∈ Finset.range N, f r := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have he : N+1-r=(N-r)+1 := by have := Finset.mem_range.mp hr; omega
      rw [he, Nat.cast_add, Nat.cast_one]
      ring
    rw [hs, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
    ring

lemma enlargementScale_le_exp {N : ℕ} {β : ℕ → ℝ}
    (hβ : ∀ r, 1 ≤ β r) (i : Fin N) :
    enlargementScale β i ≤ Real.exp (∑ r ∈ Finset.range (i.val+1), (β r-1)) := by
  rw [enlargementScale, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro r _
    exact zero_le_one.trans (hβ r)
  · intro r _
    have hh := Real.add_one_le_exp (β r-1)
    linarith

/-- The accumulated Jacobian is controlled by the weighted perturbation sum. -/
theorem enlargement_jacobian_bound {N : ℕ} {β : ℕ → ℝ}
    (hβ : ∀ r, 1 ≤ β r) :
    (∏ i : Fin N, enlargementScale β i) ≤
      Real.exp (∑ r ∈ Finset.range N, ((N-r : ℕ) : ℝ)*(β r-1)) := by
  calc
    _ ≤ ∏ i : Fin N, Real.exp (∑ r ∈ Finset.range (i.val+1), (β r-1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact (enlargementScale_pos hβ i).le
      · intro i _
        exact enlargementScale_le_exp hβ i
    _ = Real.exp (∑ i : Fin N, ∑ r ∈ Finset.range (i.val+1), (β r-1)) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i => ∑ r ∈ Finset.range (i+1), (β r-1)),
        triangular_sum]

/-- Perturbations indexed by distance from the top are charged only their
remaining dimension, and can therefore be bounded by one convergent tail. -/
lemma reverse_perturbation_sum_le {m P : ℕ} (hPm : P ≤ m) (e : ℕ → ℝ)
    (he : ∀ h, 0 ≤ e h) (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) :
    (∑ r ∈ Finset.range (m-P), ((m-P-r : ℕ) : ℝ)*e (m-r)) ≤
      ∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n) := by
  have hs : (∑ r ∈ Finset.range (m-P), ((m-P-r : ℕ) : ℝ)*e (m-r)) ≤
      ∑ r ∈ Finset.range (m-P), ((m-r : ℕ) : ℝ)*e (m-r) := by
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_right _ (he _)
    exact_mod_cast (show m-P-r ≤ m-r by omega)
  apply hs.trans
  have heq : (∑ r ∈ Finset.range (m-P), ((m-r : ℕ) : ℝ)*e (m-r)) =
      ∑ r ∈ Finset.range (m-P), ((P+1+r : ℕ) : ℝ)*e (P+1+r) := by
    apply Finset.sum_bij (fun r _ => m-P-1-r)
    · intro r hr
      have := Finset.mem_range.mp hr
      exact Finset.mem_range.mpr (by omega)
    · intro r hr s hs hrs
      have := Finset.mem_range.mp hr
      have := Finset.mem_range.mp hs
      omega
    · intro s hs
      have := Finset.mem_range.mp hs
      refine ⟨m-P-1-s, Finset.mem_range.mpr (by omega), ?_⟩
      omega
    · intro r hr
      have := Finset.mem_range.mp hr
      congr 2 <;> omega
  rw [heq]
  have hshift := hsum.comp_injective (show Function.Injective (fun n : ℕ => P+1+n) by
    intro a b h; exact Nat.add_left_cancel h)
  have htail := hsum.comp_injective (show Function.Injective (fun n : ℕ => P+n) by
    intro a b h; exact Nat.add_left_cancel h)
  apply (hshift.sum_le_tsum _ (fun n _ => mul_nonneg (Nat.cast_nonneg _) (he _))).trans
  have ht : (∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n)) =
      (P : ℝ)*e P + ∑' n : ℕ, ((P+1+n : ℕ) : ℝ)*e (P+1+n) := by
    simpa only [Function.comp_def, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
      htail.tsum_eq_zero_add
  rw [ht]
  exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (he _))

/-- The actual reverse-indexed enlargement has a uniform full Jacobian. -/
theorem reverse_enlargement_jacobian {m P : ℕ} (hPm : P ≤ m)
    (e : ℕ → ℝ) (he : ∀ h, 0 ≤ e h)
    (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) :
    (∏ i : Fin (m-P), enlargementScale (fun r => 1+e (m-r)) i) ≤
      Real.exp (∑' n : ℕ, ((P+n : ℕ) : ℝ)*e (P+n)) := by
  apply (enlargement_jacobian_bound (fun r => by linarith [he (m-r)])).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  exact reverse_perturbation_sum_le hPm e he hsum

/-- Through the retained prefix, each individual scaling factor tends to one
with the prefix cutoff, even when the full dimension grows. -/
theorem reverse_enlargement_coordinate {m H N : ℕ} (hHm : H ≤ m)
    (e : ℕ → ℝ) (he : ∀ h, 0 ≤ e h)
    (hsum : Summable (fun h : ℕ => (h : ℝ)*e h)) (i : Fin N)
    (hi : i.val < m-H) :
    enlargementScale (fun r => 1+e (m-r)) i ≤
      Real.exp (∑' n : ℕ, ((H+n : ℕ) : ℝ)*e (H+n)) := by
  apply (enlargementScale_le_exp (fun r => by linarith [he (m-r)]) i).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  apply le_trans _ (reverse_perturbation_sum_le hHm e he hsum)
  calc
    _ ≤ ∑ r ∈ Finset.range (m-H), e (m-r) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro r _ _
      exact he _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      have hr1 : (1 : ℝ) ≤ (m-H-r : ℕ) := by
        exact_mod_cast (show 1 ≤ m-H-r by have := Finset.mem_range.mp hr; omega)
      exact le_mul_of_one_le_left (he _) hr1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_EnlargementTail
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two perturbations used for full prime boxes have summable weighted
cost, including after multiplication by the smooth-cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma simplexBoxError_nonneg {C : ℝ} (hC : 0 ≤ C) (h : ℕ) :
    0 ≤ simplexBoxError C h := by
  unfold simplexBoxError
  exact add_nonneg (by positivity)
    (mul_nonneg (mul_nonneg hC (sq_nonneg _)) (pow_nonneg rho_pos.le _))

lemma simplexBoxError_weighted (C : ℝ) (h : ℕ) :
    (h : ℝ)*simplexBoxError C h =
      (1/10000 : ℝ)*((h : ℝ)^1*(Real.exp (-(1/40 : ℝ)))^h)+
      C*((h : ℝ)^3*rho^h) := by
  unfold simplexBoxError
  ring

lemma summable_simplexBoxError_weighted (C : ℝ) :
    Summable (fun h : ℕ => (h : ℝ)*simplexBoxError C h) := by
  have hq : ‖Real.exp (-(1/40 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  simp_rw [simplexBoxError_weighted]
  exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left _).add
    ((summable_pow_mul_geometric_of_norm_lt_one 3 hr).mul_left _)

lemma simplexBoxTail_eq_tsum (C : ℝ) (H : ℕ) :
    simplexBoxTail C H = ∑' n : ℕ, ((H+n : ℕ) : ℝ)*simplexBoxError C (H+n) := by
  have hq : ‖Real.exp (-(1/40 : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hr : ‖rho‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one
  have hs (k : ℕ) (r : ℝ) (hr : ‖r‖ < 1) :
      Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)^k*r^(H+n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one k hr).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  simp_rw [simplexBoxError_weighted]
  rw [Summable.tsum_add ((hs 1 _ hq).mul_left _) ((hs 3 _ hr).mul_left _),
    tsum_mul_left, tsum_mul_left]
  unfold simplexBoxTail polynomialGeometricTail
  ring

lemma simplexBoxTail_tendsto (C : ℝ) :
    Tendsto (simplexBoxTail C) atTop (nhds 0) := by
  have ht := ((polynomialGeometricTail_tendsto 1 (Real.exp (-(1/40 : ℝ)))).div_const 10000).add
    ((polynomialGeometricTail_tendsto 3 rho).const_mul C)
  change Tendsto (fun H => polynomialGeometricTail 1 (Real.exp (-(1/40 : ℝ))) H/10000 +
    C*polynomialGeometricTail 3 rho H) atTop (nhds 0)
  simpa only [zero_div, mul_zero, add_zero] using ht

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateEnlargement
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the terminal coordinates, the diagonal enlargement is uniformly
close to one. At fixed truncation the additive budget correction vanishes. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma coordinateEnlargement_one_le (M N : ℕ) (i : Fin N) :
    1 ≤ coordinateEnlargement M N i := by
  have hb (r : ℕ) : 1 ≤ 1+simplexBoxError 0 (M-r) :=
    le_add_of_nonneg_right (simplexBoxError_nonneg (by norm_num) _)
  exact (hb 0).trans (enlargementScale_top hb i)

theorem coordinateEnlargement_close : ∀ᶠ P : ℕ in atTop,
    ∀ (M N : ℕ) (i : Fin N),P ≤ M-(i.val+1) →
      coordinateEnlargement M N i ≤ (1001/1000:ℝ) := by
  have ht : Tendsto (fun P => Real.exp (simplexBoxTail 0 P)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp (simplexBoxTail_tendsto 0)
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (1:ℝ) < 1001/1000)),
    eventually_ge_atTop (1:ℕ)] with P hP hP1
  intro M N i hi
  apply le_trans _ hP
  rw [simplexBoxTail_eq_tsum]
  exact reverse_enlargement_coordinate (by omega : P ≤ M) (simplexBoxError 0)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 0) i
    (by omega)

theorem fixed_coordinate_budget_small (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    0 ≤ prefixCubeCost (m x-H)/B x ∧
    prefixCubeCost (m x-H)/B x ≤ (1/1000:ℝ) := by
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  have ht : Tendsto (fun x : ℝ => m x-H) atTop atTop :=
    (tendsto_sub_atTop_nat H).comp m_tendsto
  filter_upwards [hcost,B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    (tendsto_natCast_atTop_atTop.comp ht).eventually (eventually_ge_atTop (1000*A)),
    ht.eventually (eventually_ge_atTop 1)] with x hx hB hN hN1
  have hn : (0:ℝ) < ((m x-H:ℕ):ℝ) := by exact_mod_cast (show 0 < m x-H by omega)
  have hnn : 0 ≤ prefixCubeCost (m x-H)/B x :=
    div_nonneg (prefixCubeCost_nonneg _) hB.le
  refine ⟨hnn,?_⟩
  have hh := (hx (m x-H) (Nat.sub_le _ _)).trans
    (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hquot : prefixCubeCost (m x-H)/B x ≤ A/((m x-H:ℕ):ℝ) := by
    apply (le_div_iff₀ hn).mpr
    convert hh using 1 <;> first | rfl | ring
  apply hquot.trans
  apply (div_le_iff₀ hn).mpr
  dsimp only [Function.comp_def] at hN
  linarith only [hN]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateGridConcentration
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed bad coordinate has exponentially small mass after the exact
unit-box affine correction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem coordinate_grid_concentration : ∃ C c : ℝ,0<C ∧ 0 < c ∧
    ∀ N : ℕ,∀ B β₀ S : ℝ,∀ β κ : Fin (N+2) → ℝ,
    ∀ i : Fin (N+2),i.val<N →
    0<B → 0<β₀ → 0<S →
    (∀ j,0<β j) → (∀ j,1 ≤ κ j) →
    (∀ j,β₀ ≤ κ j) → (∀ j k,j<k → β j*κ j ≤ κ k) →
    (99/100:ℝ)*S ≤ κ i*fordSimplexCenter N (B+prefixCubeCost (N+2)) i →
    κ i*fordSimplexCenter N (B+prefixCubeCost (N+2)) i ≤ (101/100:ℝ)*S →
    1+κ i*coordinateCubeShift (N+2) i ≤ S/100 →
    ∀ K : Finset (Fin (N+2) → ℕ),
    (∀ b∈K,∃ u∈unitGridCell b,u∈enlargedSimplex (N+2) B β₀ β ∧
      (u i<(19/20:ℝ)*S ∨ (21/20:ℝ)*S<u i)) →
    (K.card:ℝ) ≤ (∏ j,κ j)*
      (C*Real.exp (-c*(N+2-(i.val+1):ℕ)))*
      (volume (prefixRegion (N+2) (B+prefixCubeCost (N+2)) 0 0)).toReal := by
  obtain ⟨C,c,hC,hc,hconc⟩ := prefix_coordinate_concentration_unconditional
  refine ⟨C,c,hC,hc,?_⟩
  intro N B β₀ S β κ i hi hB hβ₀ hS hβ hκ htop hstep hlo hhi herr K hK
  have hB' : 0<B+prefixCubeCost (N+2) := add_pos_of_pos_of_nonneg hB
    (prefixCubeCost_nonneg _)
  have hcenter : 0<fordSimplexCenter N (B+prefixCubeCost (N+2)) i := by
    unfold fordSimplexCenter
    have hN : (0:ℝ)<N+2 := by positivity
    have hi' : (i.val+1:ℝ)<N+2 := by exact_mod_cast (show i.val+1<N+2 by omega)
    exact mul_pos (mul_pos hB' (pow_pos rho_pos _))
      (sub_pos.mpr ((div_lt_one hN).mpr hi'))
  have hgrid := coordinate_grid_volume_bound (N:=N+2) (by omega) B β₀ β κ K
    (fordCoordinateBad N (B+prefixCubeCost (N+2)) i)
    (measurableSet_fordCoordinateBad _ _ _) hβ₀ hβ hκ htop hstep (by
      intro b hb
      obtain ⟨u,hu,hsimplex,hbad⟩ := hK b hb
      refine ⟨u,hu,hsimplex,?_⟩
      intro v hv
      change (1/40:ℝ) < |((simplexScale κ v+coordinateCubeShift (N+2)) i)/
        fordSimplexCenter N (B+prefixCubeCost (N+2)) i-1|
      by_contra hn
      have hh := coordinate_cube_band_transfer hu hv hS hcenter (hκ i)
        ⟨hlo,hhi⟩ herr (le_of_not_gt hn)
      rcases hbad with hbad | hbad <;> linarith only [hh.1,hh.2,hbad])
  apply hgrid.trans
  have hprod : 0 ≤ ∏ j,κ j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (hκ j))
  have hh := mul_le_mul_of_nonneg_left (hconc N _ hB' i hi) hprod
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassMajorant
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing over witnesses is an upper bound, including repeated tail primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma prod_fin_shifted {M : Type*} [CommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∏ i : Fin N, f (i.val+1)) = ∏ r ∈ Finset.Icc 1 N, f r := by
  apply Finset.prod_bij (fun i _ => i.val+1)
  · intro i _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro r hr
    have := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro i _
    rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnbandedGridVolume
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform volume bound for unbanded enlarged prime-prefix grids. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma add_pow_le_exp_ratio {B D : ℝ} (hB : 0 < B) (hD : 0 ≤ D) (N : ℕ) :
    (B+D)^N ≤ Real.exp ((N:ℝ)*D/B)*B^N := by
  have hbase : 1+D/B ≤ Real.exp (D/B) := by
    simpa only [add_comm] using Real.add_one_le_exp (D/B)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+D/B) hbase N
  have he : B+D=(1+D/B)*B := by field_simp
  rw [he,mul_pow]
  apply (mul_le_mul_of_nonneg_right hpow (pow_nonneg hB.le N)).trans_eq
  rw [← Real.exp_nat_mul]
  congr 2
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CoordinateGridPrefactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The affine normalization has a dimension-independent volume cost. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem coordinateEnlargement_product_bound : ∃ E : ℝ,0 < E ∧
    ∀ M N : ℕ,N ≤ M → (∏ i : Fin N,coordinateEnlargement M N i) ≤ E := by
  let E := Real.exp (∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n)
  refine ⟨E,Real.exp_pos _,?_⟩
  intro M N hNM
  have hh := reverse_enlargement_jacobian (m:=M) (P:=M-N) (Nat.sub_le _ _)
    (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
    (summable_simplexBoxError_weighted 0)
  rw [Nat.sub_sub_self hNM] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hs := summable_simplexBoxError_weighted 0
  have he := hs.sum_add_tsum_nat_add (M-N)
  have hn : 0 ≤ ∑ n∈Finset.range (M-N),(n:ℝ)*simplexBoxError 0 n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _)
      (simplexBoxError_nonneg (by norm_num) _))
  have ht : (∑' n : ℕ,((n+(M-N):ℕ):ℝ)*simplexBoxError 0 (n+(M-N))) ≤ 
      ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by linarith only [he,hn]
  simpa only [Nat.add_comm] using ht

theorem fixed_coordinate_grid_prefactor : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,0 < N → N ≤ m x →
      (∏ i : Fin N,coordinateEnlargement (m x) N i)*
        (volume (prefixRegion N (B x+prefixCubeCost N) 0 0)).toReal ≤ C*G x N := by
  obtain ⟨E,hE,hprod⟩ := coordinateEnlargement_product_bound
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  refine ⟨E*Real.exp A,mul_pos hE (Real.exp_pos _),?_⟩
  filter_upwards [hcost,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro N hN hNm
  have hBN : 0 ≤ B x+prefixCubeCost N := add_nonneg hB.le (prefixCubeCost_nonneg N)
  have hden : 0 < ((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  have hvolume : (volume (prefixRegion N (B x+prefixCubeCost N) 0 0)).toReal =
      (B x+prefixCubeCost N)^N/((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) := by
    rw [volume_prefixRegion_explicit N hN]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hBN,
      ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hBN _) hden.le)]
  have hratio : (N:ℝ)*prefixCubeCost N/B x ≤ A :=
    (hx N hNm).trans (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hpower := (add_pow_le_exp_ratio hB (prefixCubeCost_nonneg N) N).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hratio) (pow_nonneg hB.le N))
  rw [hvolume]
  calc
    _ ≤ E*(Real.exp A*(B x)^N/((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1))) :=
      mul_le_mul (hprod (m x) N hNm) (div_le_div_of_nonneg_right hpower hden.le)
        (div_nonneg (pow_nonneg hBN _) hden.le) hE.le
    _ = _ := by rw [G,prod_fin_shifted N g]; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedCoordinateCenters
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform comparison of the two coordinate centers with the order of
choices needed in the application: fix the terminal truncation, then the
retained range, then let the main endpoint grow. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_coordinate_centers_close (H : ℕ) :
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
      (99/100:ℝ)*fordBandScale x (i.val+1) ≤ 
        coordinateEnlargement (m x) (N+2) i*
          fordSimplexCenter N (B x+prefixCubeCost (N+2)) i ∧
      coordinateEnlargement (m x) (N+2) i*
          fordSimplexCenter N (B x+prefixCubeCost (N+2)) i ≤ 
        (101/100:ℝ)*fordBandScale x (i.val+1) := by
  filter_upwards [coordinateEnlargement_close,
    eventually_ge_atTop (max (1000*H) (H+3))] with P hκ hP
  filter_upwards [fixed_coordinate_budget_small H,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (1001*H+3))]
    with x hbudget hB hm
  intro N hN i hi
  have hiN : i.val+1 < N+2 := by have := i.isLt; omega
  have hNM : N+2 ≤ m x := by omega
  have hNpos : (0:ℝ) < ((N+2:ℕ):ℝ) := by positivity
  have hdim : m x-H=N+2 := by omega
  have hratio : 1 ≤ (m x:ℝ)/(N+2:ℕ) ∧
      (m x:ℝ)/(N+2:ℕ) ≤ (1001/1000:ℝ) := by
    constructor
    · apply (le_div_iff₀ hNpos).mpr
      simpa only [one_mul] using (Nat.cast_le.mpr hNM : (N+2:ℕ) ≤ (m x:ℝ))
    · apply (div_le_iff₀ hNpos).mpr
      have hlen : (1000*H:ℝ) ≤ (N+2:ℕ) := by
        exact_mod_cast (show 1000*H ≤ N+2 by omega)
      have he : (m x:ℝ)=(N+2:ℕ)+(H:ℝ) := by exact_mod_cast hN.symm
      linarith only [hlen,he]
  have htail : ((m x-(N+2):ℕ):ℝ)/(m x-(i.val+1):ℕ) ≤ (1/1000:ℝ) := by
    have hden : (0:ℝ) < (m x-(i.val+1):ℕ) := by exact_mod_cast (show 0 < m x-(i.val+1) by omega)
    apply (div_le_iff₀ hden).mpr
    have he : m x-(N+2)=H := by omega
    rw [he]
    have hh : (1000*H:ℝ) ≤ (m x-(i.val+1):ℕ) := by
      exact_mod_cast (show 1000*H ≤ m x-(i.val+1) by omega)
    linarith only [hh]
  have hb : 0 ≤ prefixCubeCost (N+2)/B x ∧
      prefixCubeCost (N+2)/B x ≤ (1/1000:ℝ) := by simpa only [hdim] using hbudget
  have hh := truncated_center_bounds hiN hNM hB
    ⟨coordinateEnlargement_one_le _ _ _,hκ _ _ i hi⟩ hb hratio htail
  simpa only [fordBandScale,fordSimplexCenter,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordUnbandedMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-prefix mass with Ford's literal row parameters. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma xi_eq_simplexBoxError (x : ℝ) (i : ℕ) :
    xi x i = 1+simplexBoxError 0 (m x-i) := by
  have he : (Real.exp (-(1/40:ℝ)))^(m x-i) =
      Real.exp (-((m x-i:ℕ):ℝ)/40) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold xi simplexBoxError
  rw [he]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FixedCoordinateGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration for the actual enlarged prime-prefix grid, at a fixed
terminal truncation and the fixed tolerance used by the application. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem fixed_coordinate_grid_bound_oai (H : ℕ) : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
    ∀ N : ℕ,N+2+H=m x → ∀ i : Fin (N+2),P ≤ m x-(i.val+1) →
    ∀ K : Finset (Fin (N+2) → ℕ),
    (∀ b∈K,∃ u∈unitGridCell b,
      u∈enlargedSimplex (N+2) (B x) (xi x 0) (fun j => xi x (j.val+1)) ∧
      (u i < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < u i)) →
    (K.card:ℝ) ≤ C*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  obtain ⟨C,c,hC,hc,hconc⟩ := coordinate_grid_concentration
  obtain ⟨A,hA,hpref⟩ := fixed_coordinate_grid_prefactor
  refine ⟨C*A,c,mul_pos hC hA,hc,?_⟩
  filter_upwards [fixed_coordinate_centers_close H,coordinateEnlargement_close,
    coordinate_box_error_small (show (0:ℝ) < 2 by norm_num),
    eventually_ge_atTop (H+3)] with P hcent hclose herr hP
  filter_upwards [hcent,herr,hpref,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hcent herr hpref hB
  intro N hN i hi K hK
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 0 (m x-r)
  let κ := coordinateEnlargement (m x) (N+2)
  have hβ (r : ℕ) : 1 ≤ β r :=
    le_add_of_nonneg_right (simplexBoxError_nonneg (by norm_num) _)
  have hκ (j : Fin (N+2)) : 1 ≤ κ j := coordinateEnlargement_one_le _ _ _
  have hκ2 : κ i ≤ 2 := (hclose _ _ i hi).trans (by norm_num)
  have him : i.val+1 < m x := by have := i.isLt; omega
  have hiN : i.val < N := by have := i.isLt; omega
  have hS : 0 < fordBandScale x (i.val+1) := fordBandScale_pos hB him
  have hcent' := hcent N hN i hi
  have herr' := herr (N+2) i (by omega) hi (κ i) (zero_le_one.trans (hκ i)) hκ2
  have hgrid := hconc N (B x) (β 0) (fordBandScale x (i.val+1))
    (fun j => β (j.val+1)) κ i hiN hB (zero_lt_one.trans_le (hβ 0)) hS
    (fun j => zero_lt_one.trans_le (hβ _)) hκ (enlargementScale_top hβ)
    (enlargementScale_step hβ) hcent'.1 hcent'.2 herr' K (by
      intro b hb
      obtain ⟨u,hu,hs,hbad⟩ := hK b hb
      refine ⟨u,hu,?_,hbad⟩
      simpa only [β,xi_eq_simplexBoxError,Nat.sub_zero] using hs)
  have hvolume := hpref (N+2) (by omega) (by omega)
  have hnon : 0 ≤ C*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hvolume hnon
  apply hgrid.trans
  first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.fixed_coordinate_grid_bound_oai := @OAI.TotientAsymptotic.fixed_coordinate_grid_bound_oai
