-- Prove2me | solution 1 for OAI.TotientAsymptotic.omega_internal_reciprocal_discard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:38.01204+00:00
-- url     : https://prove2.me/submissions/2b2b7f3c-7de6-4520-881d-39ad48edec42

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Log
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
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExtractTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_basicRemainderFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite tail witness extracted from a basic remainder. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma extractTail_prime {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hh : h ∈ Finset.Ico (P H) H) :
    tailPrime (extractTail x H η) h = remainderPrime η (m x-h) := by
  have hh' := Finset.mem_Ico.mp hh
  simp [tailPrime, extractTail, hh'.2, not_lt.mpr hh'.1]

lemma extractTail_log {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hHm : H ≤ m x) (hh : h ∈ Finset.Ico (P H) H) :
    tailLog (extractTail x H η) h = remainderCoord x η (m x-h) := by
  have hh' := Finset.mem_Ico.mp hh
  have hi : m x-h ≠ 0 := by omega
  simp only [tailLog, extractTail_prime η hh, remainderCoord, hi, ite_false, if_false]

lemma bandScale_reversed {x : ℝ} {h : ℕ} (hh : h ≤ m x) :
    bandScale x (m x-h) = alpha (theta x)*h*(rho^h)⁻¹ := by
  simp only [bandScale, Nat.sub_sub_self hh]

lemma extractTail_threshold {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hHm : H ≤ m x) (hPh : P H ≤ h) (hhH : h ≤ H) :
    (∑ l ∈ Finset.Ico (P H) h, a (h-l)*tailLog (extractTail x H η) l) =
      ∑ r ∈ Finset.Icc (m x-h+1) (L x H), a (r-(m x-h))*remainderCoord x η r := by
  apply Finset.sum_bij (fun l _ => m x-l)
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    apply Finset.mem_Icc.mpr
    unfold L
    omega
  · intro l hl k hk heq
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    refine ⟨m x-r, ?_, ?_⟩
    · apply Finset.mem_Ico.mpr
      unfold L at hr'
      omega
    · unfold L at hr'
      omega
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlH : l ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    rw [extractTail_log η hHm hlH]
    congr 2
    omega

/-- A basic remainder gives one of the actual phase-dependent finite witnesses,
with exactly the same tail totient; no extra tail representatives are counted. -/
theorem extractTail_isWitness {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hPH : P H < H) (hHm : H ≤ m x) :
    IsWitness H (theta x) (extractTail x H η) := by
  refine ⟨?_, hη.1, ?_, ?_, ?_⟩
  · intro h hh
    simp [extractTail, hh]
  · intro h hh
    have hh' := Finset.mem_Ico.mp hh
    have hi : m x-h ∈ Finset.Icc 1 (L x H) := by
      apply Finset.mem_Icc.mpr
      unfold L
      omega
    have hp := hη.2.1 (m x-h) hi
    have hhm : h ≤ m x := by omega
    rw [bandScale_reversed hhm] at hp
    simp only [← mul_assoc] at hp
    rw [extractTail_prime η hh, extractTail_log η hHm hh]
    refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
    rw [extractTail_threshold η hHm hh'.1 (by omega)]
    have hsum := hη.2.2.1 (m x-h) (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hi).2⟩)
    have hcoord : 0 ≤ remainderCoord x η (m x-h) := by
      have ha := alpha_pos (theta x)
      have hr := rho_pos
      exact (by positivity : (0 : ℝ) ≤ (9/10 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹).trans hp.2.1
    have hxi : (if m x-h = L x H then 1 else xi x (m x-h)) ≤
        1+(1/10000 : ℝ)*Real.exp (-(h : ℝ)/40) := by
      have he : m x-(m x-h) = h := Nat.sub_sub_self hhm
      split_ifs
      · have ht : 0 ≤ (1/10000 : ℝ)*Real.exp (-(h : ℝ)/40) := by positivity
        linarith
      · simp [xi, he]
    exact hsum.trans (mul_le_mul_of_nonneg_right hxi hcoord)
  · change largestPrimeFactor η.cofactor ≤ tailPrime (extractTail x H η) (P H)
    rw [extractTail_prime η (Finset.mem_Ico.mpr ⟨le_rfl, hPH⟩)]
    exact hη.2.2.2.1
  · change Real.log (η.cofactor : ℝ) ≤ _
    have hb := hη.2.2.2.2
    have hPm : P H ≤ m x := hPH.le.trans hHm
    change Real.log (η.cofactor : ℝ) ≤ Real.exp (2*bandScale x (m x-P H)) at hb
    rw [bandScale_reversed hPm] at hb
    simpa only [mul_assoc] using hb

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBox
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Unit-box prime sums. The conditional input is the one-dimensional Mertens
estimate displayed in the proof of Ford, *The distribution of totients*,
arXiv:1104.3264v2 (2013), Lemma 3.1, p. 11: the reciprocal-shift sum over
`exp(exp(m-1)) ≤ p < exp(exp(m))` equals `1 + O(exp(-m))`.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitPrimeWeight_nonneg (m : ℕ) : 0 ≤ unitPrimeWeight m := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2.1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
  exact inv_nonneg.mpr (by linarith)

lemma abs_prod_sub_one_le {ι : Type*} (I : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (he : ∀ i ∈ I, 0 ≤ e i)
    (herr : ∀ i ∈ I, |f i-1| ≤ e i) :
    |(∏ i ∈ I, f i)-1| ≤ (∏ i ∈ I, (1+e i))-1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hfI := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have heI := fun j hj => he j (Finset.mem_insert_of_mem hj)
    have herrI := fun j hj => herr j (Finset.mem_insert_of_mem hj)
    have hrec := ih hfI heI herrI
    have hfprod := Finset.prod_nonneg hfI
    have hP : (∏ j ∈ I, f j) ≤ ∏ j ∈ I, (1+e j) := by
      have hh := (le_abs_self ((∏ j ∈ I, f j)-1)).trans hrec
      linarith
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc
      _ = |(∏ j ∈ I, f j)*(f i-1)+((∏ j ∈ I, f j)-1)| := by congr 1; ring
      _ ≤ |(∏ j ∈ I, f j)*(f i-1)|+|(∏ j ∈ I, f j)-1| := abs_add_le _ _
      _ ≤ (∏ j ∈ I, (1+e j))*e i+((∏ j ∈ I, (1+e j))-1) := by
        rw [abs_mul, abs_of_nonneg hfprod]
        exact add_le_add (mul_le_mul hP (herr i (Finset.mem_insert_self _ _))
          (abs_nonneg _) (Finset.prod_nonneg (fun j hj => by linarith [heI j hj]))) hrec
      _ = _ := by ring

lemma abs_prod_sub_one_le_exp {ι : Type*} (I : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) (he : ∀ i ∈ I, 0 ≤ e i)
    (herr : ∀ i ∈ I, |f i-1| ≤ e i) :
    |(∏ i ∈ I, f i)-1| ≤ Real.exp (∑ i ∈ I, e i)-1 := by
  apply (abs_prod_sub_one_le I f e hf he herr).trans
  apply sub_le_sub_right
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [he i hi]
  · intro i hi
    simpa [add_comm] using Real.add_one_le_exp (e i)

/-- The relative error in a multidimensional unit box depends on the sum of
the one-dimensional errors, rather than directly on the number of coordinates. -/
theorem prime_unit_box_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (I : Finset ι) (m : ι → ℕ),
      (∀ i ∈ I, 1 ≤ m i) →
      |(∏ i ∈ I, unitPrimeWeight (m i))-1| ≤
        Real.exp (C*∑ i ∈ I, Real.exp (-(m i : ℝ)))-1 := by
  obtain ⟨C, hC, hc⟩ := hford
  refine ⟨C, hC, ?_⟩
  intro ι I m hm
  have hh := abs_prod_sub_one_le_exp I (fun i => unitPrimeWeight (m i))
    (fun i => C*Real.exp (-(m i : ℝ)))
    (fun i _ => unitPrimeWeight_nonneg _) (fun i _ => mul_nonneg hC.le (Real.exp_pos _).le)
    (fun i hi => hc (m i) (hm i hi))
  simpa only [Finset.mul_sum] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime mass of finite disjoint unions of unit boxes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma unitPrimeBox_disjoint {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (unitPrimeBox m) (unitPrimeBox n) := by
  suffices ∀ m n : ℕ, m < n → Disjoint (unitPrimeBox m) (unitPrimeBox n) by
    rcases lt_or_gt_of_ne hmn with h | h
    · exact this m n h
    · exact (this n m h).symm
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hm := (Finset.mem_filter.mp hp).2.2.2
  have hn := (Finset.mem_filter.mp hq).2.2.1
  have hmnR : (m : ℝ) ≤ (n : ℝ)-1 := by
    have hh : (m : ℝ)+1 ≤ n := by exact_mod_cast (show m+1 ≤ n by omega)
    linarith
  have hh := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hmnR)
  exact (not_lt_of_ge (hn.trans' hh)) hm

lemma reciprocalShiftWeight_nonneg {N : ℕ} (p : Fin N → ℕ) :
    0 ≤ reciprocalShiftWeight p := by unfold reciprocalShiftWeight; positivity

lemma prime_box_mass {N : ℕ} (m : Fin N → ℕ) :
    (∑ p ∈ primeBoxTuples m, reciprocalShiftWeight p) =
      ∏ i, unitPrimeWeight (m i) := by
  symm
  unfold unitPrimeWeight primeBoxTuples
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Fintype.mem_piFinset.mp hp
  unfold reciprocalShiftWeight
  rw [Nat.cast_prod, Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hpi := (Finset.mem_filter.mp (hp' i)).2.1.two_le
  rw [Nat.cast_sub (by omega : 1 ≤ p i), Nat.cast_one]

lemma primeBoxTuples_disjoint {N : ℕ} {m n : Fin N → ℕ} (hmn : m ≠ n) :
    Disjoint (primeBoxTuples m) (primeBoxTuples n) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hmn
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (unitPrimeBox_disjoint hi)
    (Fintype.mem_piFinset.mp hp i) (Fintype.mem_piFinset.mp hq i)

lemma gridPrimeMass_eq {N : ℕ} (K : Finset (Fin N → ℕ)) :
    gridPrimeMass K = ∑ m ∈ K, ∏ i, unitPrimeWeight (m i) := by
  classical
  unfold gridPrimeMass gridPrimeTuples
  rw [Finset.sum_biUnion (fun m _ n _ hmn => primeBoxTuples_disjoint hmn)]
  exact Finset.sum_congr rfl (fun m _ => prime_box_mass m)

/-- A coordinate-dependent error budget avoids a dimension factor when the
lower band endpoints grow geometrically towards the front of the prefix. -/
theorem grid_prime_mass_error_of_sum (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (K : Finset (Fin N → ℕ)) (e : ℝ),
      (∀ m ∈ K, ∀ i, 1 ≤ m i) →
      (∀ m ∈ K, (∑ i, Real.exp (-(m i : ℝ))) ≤ e) →
      |gridPrimeMass K-K.card| ≤ K.card*(Real.exp (C*e)-1) := by
  obtain ⟨C, hC, hc⟩ := prime_unit_box_error hford
  refine ⟨C, hC, ?_⟩
  intro N K e hm he
  have herr (m) (hmem : m ∈ K) :
      |(∏ i, unitPrimeWeight (m i))-1| ≤ Real.exp (C*e)-1 := by
    apply (hc Finset.univ m (fun i _ => hm m hmem i)).trans
    exact sub_le_sub_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (he m hmem) hC.le)) 1
  rw [gridPrimeMass_eq]
  calc
    _ = |∑ m ∈ K, ((∏ i, unitPrimeWeight (m i))-1)| := by
      rw [Finset.sum_sub_distrib]; simp
    _ ≤ ∑ m ∈ K, |(∏ i, unitPrimeWeight (m i))-1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ K, (Real.exp (C*e)-1) := Finset.sum_le_sum herr
    _ = _ := by simp <;> ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RemainderSplit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the prime prefix from its discrete tail thresholds. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prefix_sum_fin {J i : ℕ} (u : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc (i+1) J, a (r-i)*u r) =
      ∑ j : Fin J, if i < j.val+1 then a (j.val+1-i)*u (j.val+1) else 0 := by
  have hs : Finset.Icc (i+1) J = (Finset.Icc 1 J).filter (fun r => i < r) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  rw [hs, Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩
  · intro j _ k _ he
    apply Fin.ext
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨r-1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro j _
    rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixRelaxation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative control of simultaneous perturbations of all prefix inequalities. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma bandScale_nonneg (x : ℝ) (i : ℕ) : 0 ≤ bandScale x i := by
  unfold bandScale
  exact mul_nonneg (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _))
    (inv_nonneg.mpr (pow_nonneg rho_pos.le _))

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeBoxGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arithmetic prime boxes and their real double-logarithmic cells agree. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_unitPrimeBox_iff {p m : ℕ} :
    p ∈ unitPrimeBox m ↔ p.Prime ∧
      (m : ℝ)-1 ≤ Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) < m := by
  have hlog {p : ℕ} (hp : p.Prime) : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hp.one_lt
  constructor
  · intro hp
    obtain ⟨_, hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    refine ⟨hp, ?_, ?_⟩
    · have h1 := Real.log_le_log (Real.exp_pos _) hlo
      have h2 := Real.log_le_log (Real.exp_pos _) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
    · have h1 := Real.log_lt_log (by exact_mod_cast hp.pos) hhi
      have h2 := Real.log_lt_log (hlog hp) (by simpa only [Real.log_exp] using h1)
      simpa only [Real.log_exp] using h2
  · rintro ⟨hp, hlo, hhi⟩
    have hlo' : Real.exp (Real.exp ((m : ℝ)-1)) ≤ p := by
      have h1 := Real.exp_le_exp.mpr hlo
      have h2 := Real.exp_le_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    have hhi' : (p : ℝ) < Real.exp (Real.exp (m : ℝ)) := by
      have h1 := Real.exp_lt_exp.mpr hhi
      have h2 := Real.exp_lt_exp.mpr (by simpa only [Real.exp_log (hlog hp)] using h1)
      simpa only [Real.exp_log (by exact_mod_cast hp.pos : (0 : ℝ)<p)] using h2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.two_le, ?_⟩, hp, hlo', hhi'⟩
    exact_mod_cast hhi'.le.trans (Nat.le_ceil _)

lemma mem_primeBoxTuples_iff {N : ℕ} {p m : Fin N → ℕ} :
    p ∈ primeBoxTuples m ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ unitGridCell m := by
  simp only [primeBoxTuples, Fintype.mem_piFinset, mem_unitPrimeBox_iff,
    unitGridCell, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
    primePrefixCoord]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hp, hu⟩ i
    exact ⟨hp i, hu i⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite grids covering the actual arithmetic prefix fibers. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma bandGrid_bounds {x : ℝ} {H : ℕ} {m : Fin (R x H) → ℕ} (hm : m ∈ bandGrid x H)
    (i : Fin (R x H)) : 1 ≤ m i ∧ (9/10 : ℝ)*bandScale x (i.val+1) ≤ m i := by
  obtain ⟨hm, hlo⟩ := Finset.mem_filter.mp hm
  exact ⟨(Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)).1, hlo i⟩

lemma prefixBandRegion_covered (x : ℝ) (H : ℕ) :
    prefixBandRegion x H ⊆ gridRegion (bandGrid x H) := by
  intro u hu
  let m : Fin (R x H) → ℕ := fun i => ⌊u i⌋₊+1
  have h0 (i) : 0 ≤ u i :=
    (mul_nonneg (by norm_num) (bandScale_nonneg x (i.val+1))).trans (hu i).1
  have hc : u ∈ unitGridCell m := by
    intro i _
    dsimp [m]
    rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact ⟨Nat.floor_le (h0 i), Nat.lt_floor_add_one (u i)⟩
  have hm : m ∈ bandGrid x H := by
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_), ?_⟩
    · apply Finset.mem_Icc.mpr
      refine ⟨by dsimp [m]; omega, ?_⟩
      exact Nat.add_le_add_right (Nat.floor_mono (hu i).2) 1
    · intro i
      exact (hu i).1.trans (hc i (Set.mem_univ _)).2.le
  exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, hc⟩⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandPrimeError
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dimension-independent prime-box error from the retained lower bands. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma bandScale_lower {x : ℝ} (hs : 0 ≤ theta x) (i : ℕ) :
    lam*(m x-i : ℕ) ≤ bandScale x i := by
  have hα := alpha_ge_lam hs
  have hp : 1 ≤ (rho^(m x-i))⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  unfold bandScale
  calc
    _ ≤ alpha (theta x)*(m x-i : ℕ) :=
      mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _)) hp

lemma sum_reverse_geometric {m H : ℕ} (hHm : H ≤ m) (q : ℝ) :
    (∑ i : Fin (m-H), q^(m-(i.val+1))) =
      ∑ j ∈ Finset.range (m-H), q^(H+j) := by
  apply Finset.sum_bij (fun i _ => m-H-1-i.val)
  · intro i _
    exact Finset.mem_range.mpr (by omega)
  · intro i _ j _ hij
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    refine ⟨⟨m-H-1-j, by omega⟩, Finset.mem_univ _, ?_⟩
    simp only
    omega
  · intro i _
    congr 1
    have := i.isLt
    omega

lemma sum_exp_neg_bandScale_le {x c : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hc : 0 < c) (hHm : H ≤ m x) :
    (∑ i : Fin (R x H), Real.exp (-c*bandScale x (i.val+1))) ≤
      Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)) := by
  let q := Real.exp (-c*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have hg := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin (R x H), q^(m x-(i.val+1)) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left (bandScale_lower hs (i.val+1)) hc.le
      nlinarith
    _ = ∑ j ∈ Finset.range (m x-H), q^(H+j) := sum_reverse_geometric hHm q
    _ ≤ ∑' j : ℕ, q^(H+j) := (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum
      _ (fun _ _ => pow_nonneg hq0 _)
    _ = q^H/(1-q) := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

lemma bandPrimeError_tendsto (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (bandPrimeError C c) atTop (nhds 0) := by
  have hq : Real.exp (-c*lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq).div_const
    (1-Real.exp (-c*lam))
  have hh := ((Real.continuous_exp.tendsto (0 : ℝ)).comp (by
    simpa only [mul_zero, zero_div] using ht.const_mul C)).sub_const 1
  change Tendsto (fun H => Real.exp (C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))))-1)
    atTop (nhds 0)
  simpa only [Real.exp_zero, sub_self, Function.comp_def] using hh

/-- On any finite union of boxes above the retained lower bands, prime mass
and volume have a relative error tending to zero with the tail cut. The
bound is uniform in `x`, the number of prefix coordinates, and the phase. -/
theorem banded_grid_prime_mass_error (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x c : ℝ} {H : ℕ}, 0 ≤ theta x → 0 < c → H ≤ m x →
      ∀ K : Finset (Fin (R x H) → ℕ),
        (∀ b ∈ K, ∀ i, 1 ≤ b i ∧ c*bandScale x (i.val+1) ≤ b i) →
        |gridPrimeMass K-(MeasureTheory.volume (gridRegion K)).toReal| ≤
          (MeasureTheory.volume (gridRegion K)).toReal*bandPrimeError C c H := by
  obtain ⟨C, hC, hc⟩ := grid_prime_mass_error_of_sum hford
  refine ⟨C, hC, ?_⟩
  intro x c H hs hpos hHm K hK
  have he (b) (hb : b ∈ K) : (∑ i, Real.exp (-(b i : ℝ))) ≤
      Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)) := by
    apply le_trans _ (sum_exp_neg_bandScale_le hs hpos hHm)
    exact Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr (by
      have := (hK b hb i).2
      linarith))
  simpa only [gridRegion_volume_real, bandPrimeError] using
    hc K (Real.exp (-c*lam)^H/(1-Real.exp (-c*lam)))
      (fun b hb i => (hK b hb i).1) he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalMagnitude
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coarse numerical separation sufficient for the cofactor envelope. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma renewalSeries_three_eighths_lt_one : renewalSeries (3/8) < 1 := by
  have hh := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
    (r := (3/8 : ℝ)) (by norm_num)
  have hsum : HasSum (fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1)) (24/25 : ℝ) := by
    have h2 := hh.mul_right (3/8 : ℝ)
    have e1 : (fun i : ℕ => ((i + 1).choose 1 : ℝ) * (3/8 : ℝ)^i * (3/8 : ℝ)) =
        fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1) := by
      ext n
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    have e2 : (1 / (1 - 3/8 : ℝ)^(1+1)) * (3/8 : ℝ) = 24/25 := by norm_num
    rw [e1, e2] at h2
    exact h2
  have hbound : renewalSeries (3/8) ≤ (24/25 : ℝ) := by
    rw [← hsum.tsum_eq]
    unfold renewalSeries
    apply (summable_renewal (r := (3/8 : ℝ)) (by norm_num) (by norm_num)).tsum_le_tsum
      (g := fun n : ℕ => (n+1 : ℝ)*(3/8 : ℝ)^(n+1))
    · intro n
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast a_le_index (j := n+1) (by omega))
        (pow_nonneg (by norm_num) _)
    · exact hsum.summable
  linarith

lemma rho_gt_three_eighths : (3/8 : ℝ) < rho := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩)
    (show (3/8 : ℝ) ∈ Set.Ico (0 : ℝ) 1 by norm_num) hh
  have hroot : renewalSeries rho = 1 := rho_mem.2.2
  rw [hroot] at hm
  linarith [renewalSeries_three_eighths_lt_one]

lemma lam_lt_one : lam < 1 := by
  unfold lam
  have hr : 1/rho < (8/3 : ℝ) := by
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [rho_gt_three_eighths]
  have hh := Real.log_lt_log (div_pos zero_lt_one rho_pos) hr
  apply hh.trans
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<8/3)).mpr
  linarith [Real.exp_one_gt_d9]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorGrowth
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small cofactor cost is subpolynomial in the tail cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cofactorScale_nonneg (H : ℕ) : 0 ≤ cofactorScale H := by
  unfold cofactorScale
  exact mul_nonneg (Nat.cast_nonneg _) (inv_pos.mpr (pow_pos rho_pos _)).le

lemma cofactorScale_div_log_tendsto :
    Tendsto (fun H : ℕ => cofactorScale H/Real.log H) atTop (nhds 0) := by
  have hlog : Tendsto (fun H : ℕ => Real.log (H : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Tendsto (fun H : ℕ => Real.log (Real.log (H : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have ht : Tendsto (fun H : ℕ => Real.log (Real.log (H : ℝ))*
      Real.exp (-(1-lam)*Real.log (Real.log (H : ℝ)))) atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1-lam)
        (sub_pos.mpr lam_lt_one)).comp hLL
  apply squeeze_zero' (g := fun H : ℕ => Real.log (Real.log (H : ℝ))*
    Real.exp (-(1-lam)*Real.log (Real.log (H : ℝ))))
  · filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with H hH
    exact div_nonneg (cofactorScale_nonneg H) hH.le
  · filter_upwards [hLL.eventually (eventually_ge_atTop (0 : ℝ)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with H hHH hH
    have hp : (P H : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Nat.floor_le hHH
    have he : (rho^(P H))⁻¹ = Real.exp (lam*(P H : ℝ)) := by
      rw [rho_pow_eq_exp, ← Real.exp_neg]
      congr 1
      ring
    calc
      _ ≤ (Real.log (Real.log (H : ℝ))*Real.exp (lam*Real.log (Real.log (H : ℝ)))) /
          Real.log H := by
        unfold cofactorScale
        rw [he]
        apply div_le_div_of_nonneg_right _ hH.le
        exact mul_le_mul hp (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp lam_pos.le))
          (Real.exp_pos _).le hHH
      _ = Real.log (Real.log (H : ℝ))*(Real.exp (lam*Real.log (Real.log (H : ℝ))) /
          Real.exp (Real.log (Real.log (H : ℝ)))) := by rw [Real.exp_log hH]; ring
      _ = Real.log (Real.log (H : ℝ))*Real.exp
          (lam*Real.log (Real.log (H : ℝ))-Real.log (Real.log (H : ℝ))) := by
        rw [Real.exp_sub]
      _ = _ := by congr 2; ring
  · exact ht

/-- Every fixed negative power of `H` dominates the full allowed cofactor
cost. This is the precise meaning of `K_H = H^{o(1)}` used in the discards. -/
theorem cofactor_envelope_power_decay (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun H : ℕ => Real.exp (C*cofactorScale H-ε*Real.log H)) atTop (nhds 0) := by
  have hlog : Tendsto (fun H : ℕ => Real.log (H : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun H : ℕ => C*(cofactorScale H/Real.log H)) atTop (nhds 0) := by
    simpa using cofactorScale_div_log_tendsto.const_mul C
  have hupper : Tendsto (fun H : ℕ => Real.exp (-(ε/2)*Real.log H)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (by linarith : -(ε/2)<0))
  apply squeeze_zero' (g := fun H : ℕ => Real.exp (-(ε/2)*Real.log H))
  · exact Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · filter_upwards [ht.eventually (eventually_lt_nhds (by linarith : (0 : ℝ)<ε/2)),
      hlog.eventually (eventually_gt_atTop (0 : ℝ))] with H hh hH
    apply Real.exp_le_exp.mpr
    have hc : C*cofactorScale H ≤ (ε/2)*Real.log H := by
      have hfrac : (C*cofactorScale H)/Real.log H ≤ ε/2 := by
        simpa only [mul_div_assoc] using hh.le
      exact (div_le_iff₀ hH).mp hfrac
    linarith
  · exact hupper

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

lemma summable_projectedEnvelope {C : ℝ} (hC : 0 < C) :
    Summable (projectedEnvelope C) := by
  have hh : Tendsto (fun n : ℕ => C*rho^n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul C
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hh.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  let q := C*rho^K
  have hq : 0 < q := mul_pos hC (pow_pos rho_pos _)
  have hq1 : q < 1 := hK K le_rfl
  have hg : Summable (fun n : ℕ => q^n) :=
    summable_geometric_of_lt_one hq.le hq1
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (2*K+1)] with n hn
  have htri : K*n ≤ n*(n-1)/2 := by
    have hn' : 2*K ≤ n-1 := by omega
    have hm := Nat.mul_le_mul_left n hn'
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    nlinarith
  unfold projectedEnvelope
  rw [Real.norm_eq_abs, abs_of_pos
    (mul_pos (pow_pos hC _) (pow_pos rho_pos _))]
  calc
    _ ≤ C^n*rho^(K*n) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le htri) (pow_pos hC _).le
    _ = q^n := by rw [pow_mul, mul_pow]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorShellDecay
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma polynomialGeometricTail_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (H : ℕ) :
    0 ≤ polynomialGeometricTail k r H :=
  tsum_nonneg (fun _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hr _))

lemma polynomialGeometricTail_tendsto (k : ℕ) (r : ℝ) :
    Tendsto (polynomialGeometricTail k r) atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, ((H+n : ℕ) : ℝ)^k*r^(H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (fun n : ℕ => (n : ℝ)^k*r^n))

lemma cofactor_envelope_le_self (C : ℝ) :
    ∀ᶠ H : ℕ in atTop, Real.exp (C*cofactorScale H) ≤ H := by
  have hh := cofactor_envelope_power_decay C (ε := 1) (by norm_num)
  filter_upwards [hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_ge_atTop 1] with H hH hpos
  have hp : (0 : ℝ) < H := by exact_mod_cast hpos
  rw [one_mul, Real.exp_sub, Real.exp_log hp] at hH
  exact ((div_lt_one hp).mp hH).le

lemma self_mul_polynomialGeometricTail_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (H : ℕ) : (H : ℝ)*polynomialGeometricTail k r H ≤ polynomialGeometricTail (k+1) r H := by
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
  have hs (j : ℕ) : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)^j*r^(H+n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one j hnorm).comp_injective
      (fun _ _ h => by omega)
  unfold polynomialGeometricTail
  rw [← tsum_mul_left]
  apply ((hs k).mul_left (H : ℝ)).tsum_le_tsum
  · intro n
    have hh : (H : ℝ) ≤ (H+n : ℕ) := by exact_mod_cast Nat.le_add_right H n
    calc
      _ = ((H : ℝ)*((H+n : ℕ) : ℝ)^k)*r^(H+n) := by ring
      _ ≤ (((H+n : ℕ) : ℝ)*((H+n : ℕ) : ℝ)^k)*r^(H+n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (pow_nonneg hr _)
      _ = _ := by rw [pow_succ]; ring
  · exact hs (k+1)

/-- This absorbs the entire discrete-cofactor sum in the shell estimates. -/
theorem cofactor_polynomialGeometricTail_tendsto (C : ℝ) (k : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun H => Real.exp (C*cofactorScale H)*polynomialGeometricTail k r H)
      atTop (nhds 0) := by
  apply squeeze_zero' (g := polynomialGeometricTail (k+1) r)
  · exact Eventually.of_forall (fun H =>
      mul_nonneg (Real.exp_pos _).le (polynomialGeometricTail_nonneg k hr H))
  · filter_upwards [cofactor_envelope_le_self C] with H hH
    exact (mul_le_mul_of_nonneg_right hH (polynomialGeometricTail_nonneg k hr H)).trans
      (self_mul_polynomialGeometricTail_le k hr hr1 H)
  · exact polynomialGeometricTail_tendsto (k+1) r

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

/-- The Jacobian cost is the product of the coordinate scaling factors. -/
theorem volume_enlargedSimplex_le {N : ℕ} (B β₀ : ℝ) (β κ : Fin N → ℝ)
    (hβ₀ : 0 < β₀) (hβ : ∀ i, 0 < β i) (hκ : ∀ i, 0 < κ i)
    (htop : ∀ i, β₀ ≤ κ i) (hstep : ∀ i j, i < j → β i*κ i ≤ κ j) :
    volume (enlargedSimplex N B β₀ β) ≤
      ENNReal.ofReal (∏ i, κ i)*volume (prefixRegion N B 0 0) := by
  have hp : 0 < ∏ i, κ i := Finset.prod_pos (fun i _ => hκ i)
  have hd : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hsub : enlargedSimplex N B β₀ β ⊆
      (simplexScale κ) ⁻¹' prefixRegion N B 0 0 :=
    enlargedSimplex_mapsTo hβ₀ hβ hκ htop hstep
  apply (measure_mono hsub).trans_eq
  rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable
      (measurableSet_prefixRegion _ _ _ _),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hd,
    simplexScale_det, inv_inv, abs_of_pos hp, Measure.smul_apply, smul_eq_mul]

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

theorem volume_enlargedSimplex_product_bound {N : ℕ} (B : ℝ) (β : ℕ → ℝ)
    (hβ : ∀ r, 1 ≤ β r) :
    volume (enlargedSimplex N B (β 0) (fun i => β (i.val+1))) ≤
      ENNReal.ofReal (∏ i : Fin N, enlargementScale β i)*volume (prefixRegion N B 0 0) :=
  volume_enlargedSimplex_le B (β 0) (fun i => β (i.val+1)) (enlargementScale β)
    (zero_lt_one.trans_le (hβ 0)) (fun i => zero_lt_one.trans_le (hβ (i.val+1)))
    (enlargementScale_pos hβ) (enlargementScale_top hβ) (enlargementScale_step hβ)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every box meeting a basic full prime tuple lies in a controlled
multiplicative enlargement of the full simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma xi_bounds (x : ℝ) (i : ℕ) : 1 ≤ xi x i ∧ xi x i ≤ 2 := by
  have hp := Real.exp_pos (-((m x-i : ℕ) : ℝ)/40)
  have he : Real.exp (-((m x-i : ℕ) : ℝ)/40) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (m x-i) (α := ℝ); linarith)
  constructor <;> dsimp [xi] <;> linarith

lemma remainderCoord_fin {J : ℕ} (x : ℝ) (η : RemainderDatum J) (i : Fin J) :
    remainderCoord x η (i.val+1) = primePrefixCoord η.primes i := by
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ J := ⟨by omega, by have := i.isLt; omega⟩
  simp [remainderCoord, remainderPrime, hi, primePrefixCoord]

lemma basic_remainder_enlargedSimplex {x : ℝ} {H : ℕ}
    (hL : 0 < L x H) {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    primePrefixCoord η.primes ∈
      enlargedSimplex (L x H) (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  have hn (i : Fin (L x H)) : 0 ≤ primePrefixCoord η.primes i := by
    have hh := (hη.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)).2.1
    rw [remainderCoord_fin] at hh
    exact (mul_nonneg (by norm_num) (bandScale_nonneg _ _)).trans hh
  refine ⟨hn, ?_, ?_⟩
  · intro i
    have hi : i.val+1 ≤ L x H := by have := i.isLt; omega
    have hh := hη.2.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega, hi⟩)
    rw [prefix_sum_fin, remainderCoord_fin] at hh
    simp only [remainderCoord_fin, Nat.add_lt_add_iff_right, Nat.add_sub_add_right] at hh
    change (∑ j, if i < j then _ else 0) ≤ _
    apply hh.trans
    by_cases he : i.val+1=L x H
    · rw [ite_eq_left he, one_mul]
      exact le_mul_of_one_le_left (hn i) (xi_bounds x (i.val+1)).1
    · rw [ite_eq_right he]
  · have hh := hη.2.2.1 0 (Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩)
    rw [prefix_sum_fin, ite_eq_right (by omega : 0 ≠ L x H)] at hh
    have hz : remainderCoord x η 0 = B x := by simp [remainderCoord]
    simpa only [Nat.zero_lt_succ, ite_true, if_true, Nat.sub_zero, remainderCoord_fin, hz] using hh

/-- Unit-coordinate perturbations of a simplex point are absorbed by the
indicated row and budget enlargements. -/
lemma enlargedSimplex_cube {N : ℕ} {B β₀ e₀ : ℝ} {β e u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N B β₀ β)
    (hβ : ∀ i, 1 ≤ β i ∧ β i ≤ 2) (hv : ∀ i, 0 ≤ v i)
    (hdist : ∀ i, |u i-v i| ≤ 1)
    (he : ∀ i, ((N-i.val : ℕ) : ℝ)^2+1 ≤ e i*v i)
    (he₀ : (N : ℝ)^2 ≤ e₀*B) :
    v ∈ enlargedSimplex N B (β₀+e₀) (β+e) := by
  refine ⟨hv, ?_, ?_⟩
  · intro i
    have hd := (le_abs_self _).trans (prefixLinear_cube_error u v hdist i)
    have hdiff := (le_abs_self _).trans (hdist i)
    have hterm : (β i-1)*(u i-v i) ≤ 1 := by
      calc
        _ ≤ (β i-1)*1 := mul_le_mul_of_nonneg_left hdiff (by linarith [(hβ i).1])
        _ ≤ 1 := by linarith [(hβ i).2]
    have hh := hu.2.1 i
    rw [prefixLinear_apply, prefixLinear_apply] at hd
    simp only [Pi.add_apply]
    nlinarith [he i]
  · have hd := (neg_le_abs _).trans (prefixBudget_cube_error u v hdist)
    nlinarith [hu.2.2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BasicCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete enclosure of every prime box meeting the basic full tuples. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma simplexBoxError_eq (x : ℝ) (i : ℕ) (C : ℝ) :
    1+simplexBoxError C (m x-i) = xi x i + C*((m x-i : ℕ) : ℝ)^2*rho^(m x-i) := by
  have he : (Real.exp (-(1/40 : ℝ)))^(m x-i) =
      Real.exp (-((m x-i : ℕ) : ℝ)/40) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [simplexBoxError, he, xi]
  ring

lemma cube_band_lower {x : ℝ} {P i : ℕ} {u v : ℝ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P : ℝ)) (hi : i+P ≤ m x)
    (hu : (9/10 : ℝ)*bandScale x i ≤ u) (hv : |u-v| ≤ 1) :
    1 ≤ rho^(m x-i)*v := by
  have hpow : 0 < rho^(m x-i) := pow_pos rho_pos _
  have hpow1 : rho^(m x-i) ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hα := alpha_ge_lam hs
  have hp : (P : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast (show P ≤ m x-i by omega)
  have hdist : u-v ≤ 1 := (le_abs_self _).trans hv
  have hm := mul_le_mul_of_nonneg_left hu hpow.le
  have hb : rho^(m x-i)*((9/10 : ℝ)*bandScale x i) =
      (9/10 : ℝ)*alpha (theta x)*(m x-i : ℕ) := by
    unfold bandScale
    field_simp [hpow.ne']
  rw [hb] at hm
  have hval : rho^(m x-i)*u-rho^(m x-i)*v ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdist hpow.le
    nlinarith
  have hlow := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (m x-i) (α := ℝ))
  have hP := mul_le_mul_of_nonneg_left hp lam_pos.le
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorEnvelope
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The cofactor envelope from Mertens' published prime-product theorem.
We use only its upper bound, stated as Theorem 1.1, equation (1.2), in
J. D. Lichtman, *Mertens' prime product formula, dissected*,
arXiv:2002.03361v3 (2021), citing Mertens (1874),
*J. reine angew. Math.* 78, 46–62. This is an explicit conditional input.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_ratio_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ)/n.totient = ∏ p ∈ n.primeFactors, (p : ℝ)/(p-1) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have hprod : (0 : ℝ) < ∏ p ∈ n.primeFactors, (p-1 : ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    linarith
  have he := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
  push_cast at he
  have he' : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      n*(∏ p ∈ n.primeFactors, (p-1 : ℝ)) := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
  rw [Finset.prod_div_distrib]
  exact (div_eq_div_iff hφ.ne' hprod.ne').mpr (by nlinarith [he'])

lemma totient_ratio_le_eulerProduct {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (n : ℝ)/n.totient ≤ primeEulerProduct N := by
  rw [totient_ratio_product hn]
  unfold primeEulerProduct
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hprime.two_le, (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hnN⟩, hprime⟩
  · intro p hp
    have hpos : (0 : ℝ) < p-1 := by
      have : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
    exact div_nonneg (Nat.cast_nonneg _) hpos.le
  · intro p hp _
    have hprime := (Finset.mem_filter.mp hp).2
    have hpos : (0 : ℝ) < p-1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      linarith
    apply (le_div_iff₀ hpos).mpr
    linarith

/-- A deliberately coarse logarithmic-square envelope is sufficient for the
small discrete cofactor. It avoids imposing any coprimality restrictions. -/
theorem sum_reciprocal_totient_le (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, (n.totient : ℝ)⁻¹) ≤
        C*Real.log N*(1+Real.log N) := by
  obtain ⟨C, hC, hprod⟩ := hmertens
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (n.totient : ℝ)⁻¹ ≤ C*Real.log N*(n : ℝ)⁻¹ := by
    have hn' := Finset.mem_Icc.mp hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn'.1
    have hb := (totient_ratio_le_eulerProduct hn'.1 hn'.2).trans (hprod N hN)
    have hh := mul_le_mul_of_nonneg_right hb (inv_pos.mpr hnR).le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals field_simp
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, C*Real.log N*(n : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = C*Real.log N*∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ C*Real.log N*(1+Real.log N) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hlog)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log N

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionScale
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete renewal bounds needed for the manuscript's collision cutoff.
These are proved from the defining series; no additional numerical input is assumed. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

private lemma small_log_identities :
    Real.log 4 = 2*Real.log 2 ∧ Real.log 6 = Real.log 2+Real.log 3 ∧
    Real.log 8 = 3*Real.log 2 ∧ Real.log 9 = 2*Real.log 3 := by
  refine ⟨Real.log_four_eq, ?_, ?_, ?_⟩
  · convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (2 : ℝ) 3 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert Real.log_pow (3 : ℝ) 2 using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

private lemma log_seven_bounds :
    3*Real.log 2-1/7 ≤ Real.log 7 ∧ Real.log 7 ≤ 3*Real.log 2-1/8 := by
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<7/8)
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<8/7)
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hu
  rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by norm_num : (7 : ℝ) ≠ 0),
    small_log_identities.2.2.1] at hl
  constructor <;> linarith

private lemma renewal_tail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    (∑' n : ℕ, a (n+k+1)*r^(n+k+1)) ≤
      r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by
  have hn : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (k+1 : ℝ))
  have hh : HasSum (fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1))
      (r^(k+1)*(r/(1-r)^2+(k+1)/(1-r))) := by
    have h2 := hs.mul_left (r^(k+1))
    have e1 : (fun b : ℕ => r^(k+1) * ((b : ℝ) * r^b + ((k : ℝ)+1) * r^b)) =
        fun n : ℕ => (n+k+1 : ℝ)*r^(n+k+1) := by
      ext n
      have : r^(n+k+1) = r^(k+1)*r^n := by
        rw [show n+k+1 = n+(k+1) by omega, pow_add]; ring
      rw [this]; ring
    have e2 : r^(k+1) * (r/(1-r)^2 + ((k:ℝ)+1) * (1-r)⁻¹) =
        r^(k+1)*(r/(1-r)^2+(k+1)/(1-r)) := by simp only [div_eq_mul_inv]
    rw [e1, e2] at h2
    exact h2
  rw [← hh.tsum_eq]
  apply Summable.tsum_le_tsum _ _ hh.summable
  · intro n
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast a_le_index (j := n+k+1) (by omega))
      (pow_nonneg hr0 _)
  · simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (f := fun n : ℕ => a (n+1)*r^(n+1)) k).2
        (summable_renewal hr0 hr1)

lemma renewalSeries_thirteen_twentyfifths_lt_one : renewalSeries (13/25) < 1 := by
  have hs := (summable_renewal (r := (13/25 : ℝ)) (by norm_num) (by norm_num)).sum_add_tsum_nat_add 8
  have ht := renewal_tail_majorant (r := (13/25 : ℝ)) (by norm_num) (by norm_num) 8
  change (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) + _ = renewalSeries (13/25) at hs
  have hfinite : (∑ n ∈ Finset.range 8, a (n+1)*(13/25 : ℝ)^(n+1)) < 9/10 := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9,
      log_seven_bounds.2]
  have htail : (∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1)) < 1/10 := by
    exact ht.trans_lt (by norm_num)
  have heq : (∑' n : ℕ, a (n+1+8)*(13/25 : ℝ)^(n+1+8)) =
      ∑' n : ℕ, a (n+8+1)*(13/25 : ℝ)^(n+8+1) := by
    congr 1
  simp only [heq] at hs
  linarith

lemma renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one :
    1 < renewalSeries (137/250) := by
  have hs := summable_renewal (r := (137/250 : ℝ)) (by norm_num) (by norm_num)
  have hl := hs.sum_le_tsum (Finset.range 8)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (137/250) at hl
  have hfinite : 1 < (∑ n ∈ Finset.range 8, a (n+1)*(137/250 : ℝ)^(n+1)) := by
    norm_num [Finset.sum_range_succ, a, small_log_identities.1,
      small_log_identities.2.1, small_log_identities.2.2.1,
      small_log_identities.2.2.2]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9,
      log_seven_bounds.1]
  exact hfinite.trans_le hl

lemma collision_rho_bounds : (13/25 : ℝ) < rho ∧ rho < 137/250 := by
  constructor
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩)
      (show (13/25 : ℝ) ∈ Set.Ico 0 1 by norm_num) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_thirteen_twentyfifths_lt_one]
  · by_contra! h
    have hh := renewalSeries_strictMonoOn.monotoneOn
      (show (137/250 : ℝ) ∈ Set.Ico 0 1 by norm_num)
      (show rho ∈ Set.Ico (0 : ℝ) 1 from ⟨rho_pos.le, rho_lt_one⟩) h
    rw [renewalSeries_rho] at hh
    linarith [renewalSeries_onehundredthirtyseven_twohundredfiftieths_gt_one]

lemma collision_lambda_bounds : (3/5 : ℝ) < lam ∧ lam < 2/3 := by
  have he3 : Real.exp (3/5 : ℝ) < 250/137 := by
    have he : (Real.exp (3/5 : ℝ))^5 < (250/137 : ℝ)^5 := by
      calc
        _ = (Real.exp 1)^3 := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
        _ < (2.7182818286 : ℝ)^3 := pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
        _ < _ := by norm_num
    exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 5 ≠ 0)).mp he
  have he2 : (25/13 : ℝ) < Real.exp (2/3 : ℝ) := by
    have he : (25/13 : ℝ)^3 < (Real.exp (2/3 : ℝ))^3 := by
      calc
        _ < (2.7182818283 : ℝ)^2 := by norm_num
        _ < (Real.exp 1)^2 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
    exact (pow_lt_pow_iff_left₀ (by norm_num) (Real.exp_pos _).le (by norm_num : 3 ≠ 0)).mp he
  unfold lam
  constructor
  · apply (Real.lt_log_iff_exp_lt (div_pos zero_lt_one rho_pos)).mpr
    apply he3.trans
    apply (lt_div_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.2]
  · apply (Real.log_lt_iff_lt_exp (div_pos zero_lt_one rho_pos)).mpr
    apply lt_trans _ he2
    apply (div_lt_iff₀ rho_pos).mpr
    nlinarith [collision_rho_bounds.1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCutoff
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact logarithmic cutoff and polynomially separated collision layers. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collisionCutoff_bounds {h : ℕ} (hh : 1 ≤ h) :
    30*Real.log (h : ℝ) ≤ collisionCutoff h ∧
    (collisionCutoff h : ℝ) < 30*Real.log (h : ℝ)+1 := by
  have hl : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hl)⟩

lemma collisionCutoff_div_tendsto :
    Tendsto (fun h : ℕ => (collisionCutoff h : ℝ)/h) atTop (nhds 0) := by
  have hl : Tendsto (fun h : ℕ => Real.log (h : ℝ)/(h : ℝ)) atTop (nhds 0) := by
    simpa only [one_mul, add_zero, pow_one, Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun h : ℕ => (1 : ℝ)/(h : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (g := fun h : ℕ => 30*(Real.log (h : ℝ)/h)+1/h)
  · exact Eventually.of_forall fun h => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have ht := div_le_div_of_nonneg_right (collisionCutoff_bounds hh).2.le
      (Nat.cast_nonneg (α := ℝ) h)
    exact ht.trans_eq (by ring)
  · simpa using (hl.const_mul 30).add hi

lemma collisionCutoff_eventually_small :
    ∀ᶠ h : ℕ in atTop, 2*collisionCutoff h < h := by
  filter_upwards [collisionCutoff_div_tendsto.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2)), eventually_ge_atTop 1] with h ht hh
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have ht' := (div_lt_iff₀ hhR).mp ht
  have : (2*collisionCutoff h : ℝ) < h := by nlinarith
  exact_mod_cast this

lemma rho_collisionCutoff_bounds {h : ℕ} (hh : 1 ≤ h) :
    rho/(h : ℝ)^20 ≤ rho^(collisionCutoff h) ∧
    rho^(collisionCutoff h) ≤ 1/(h : ℝ)^18 := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have hlog : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast hh)
  have hJ := collisionCutoff_bounds hh
  have hl := collision_lambda_bounds
  have he : Real.exp (-lam) = rho := by simpa using (rho_pow_eq_exp 1).symm
  have hp (k : ℕ) : Real.exp (-(k : ℝ)*Real.log (h : ℝ)) = 1/(h : ℝ)^k := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hhR]
    simp only [one_div]
  rw [rho_pow_eq_exp]
  constructor
  · calc
      _ = Real.exp (-lam-20*Real.log (h : ℝ)) := by
        rw [Real.exp_sub, show Real.exp (20*Real.log (h : ℝ)) = (h : ℝ)^20 by
          simpa only [Nat.cast_ofNat, Real.exp_log hhR] using
            Real.exp_nat_mul (Real.log (h : ℝ)) 20, he]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hJ.2.le lam_pos.le,
          mul_le_mul_of_nonneg_right hl.2.le hlog])
  · calc
      _ ≤ Real.exp (-18*Real.log (h : ℝ)) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hJ.1 lam_pos.le,
          mul_le_mul_of_nonneg_right hl.1.le hlog])
      _ = _ := hp 18

/-- Phase-uniform comparison of the layer at the first collision and the last
layer retained by the logarithmic cutoff. -/
lemma collision_layer_ratio {h : ℕ} (hh : 1 ≤ h)
    (hJ : 2*collisionCutoff h ≤ h) (s : ℝ) :
    rho/(2*(h : ℝ)^20) ≤
      (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) ∧
    (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) ≤ 1/(h : ℝ)^18 := by
  have hhR : (0 : ℝ)<h := by exact_mod_cast hh
  have hJh : collisionCutoff h ≤ h := by omega
  have hpow : rho^(h-collisionCutoff h)*rho^(collisionCutoff h) = rho^h := by
    rw [← pow_add, Nat.sub_add_cancel hJh]
  have heq : (alpha s*(h-collisionCutoff h : ℕ)/(rho^(h-collisionCutoff h))) /
        (alpha s*h/rho^h) = ((h-collisionCutoff h : ℕ) : ℝ)/h*rho^(collisionCutoff h) := by
    field_simp [(alpha_pos s).ne', hhR.ne', (pow_pos rho_pos _).ne']
    rw [mul_assoc, hpow]
  rw [heq]
  have hscale : (1/2 : ℝ) ≤ ((h-collisionCutoff h : ℕ) : ℝ)/h ∧
      ((h-collisionCutoff h : ℕ) : ℝ)/h ≤ 1 := by
    rw [Nat.cast_sub hJh]
    have hjR : 2*(collisionCutoff h : ℝ) ≤ h := by exact_mod_cast hJ
    constructor
    · apply (le_div_iff₀ hhR).mpr
      linarith
    · apply (div_le_iff₀ hhR).mpr
      have := Nat.cast_nonneg (α := ℝ) (collisionCutoff h)
      linarith
  constructor
  · have ht := mul_le_mul hscale.1 (rho_collisionCutoff_bounds hh).1
      (div_nonneg rho_pos.le (by positivity)) ((by norm_num : (0 : ℝ) ≤ 1/2).trans hscale.1)
    exact le_trans (le_of_eq (by ring)) ht
  · exact (mul_le_mul_of_nonneg_right hscale.2 (pow_pos rho_pos _).le).trans
      (by simpa using (rho_collisionCutoff_bounds hh).2)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GridApproximation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime mass versus volume, with all remaining error confined to boundary boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma bandPrimeError_nonneg {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (H : ℕ) :
    0 ≤ bandPrimeError C c H := by
  unfold bandPrimeError
  have hq : Real.exp (-c*lam) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [lam_pos]
  have he : 0 ≤ C*(Real.exp (-c*lam)^H/(1-Real.exp (-c*lam))) := by positivity
  exact sub_nonneg.mpr (Real.one_le_exp he)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailCofactor
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform reciprocal cofactor envelope at the discrete tail cut. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma exponentialCofactorCap_bounds {T : ℝ} (hT : 0 ≤ T) :
    2 ≤ exponentialCofactorCap T ∧
      Real.log (exponentialCofactorCap T : ℝ) ≤ 2*Real.exp T := by
  have he : 1 ≤ Real.exp T := Real.one_le_exp hT
  have hY : 2 ≤ Real.exp (Real.exp T) := by linarith [Real.add_one_le_exp (Real.exp T)]
  have hN : (2 : ℝ) ≤ exponentialCofactorCap T := hY.trans (Nat.le_ceil _)
  have hNpos : (0 : ℝ) < exponentialCofactorCap T := by linarith
  refine ⟨by exact_mod_cast hN, ?_⟩
  have hcap : (exponentialCofactorCap T : ℝ) ≤ 2*Real.exp (Real.exp T) := by
    have hh := Nat.ceil_lt_add_one (Real.exp_pos (Real.exp T)).le
    change (exponentialCofactorCap T : ℝ) < Real.exp (Real.exp T)+1 at hh
    linarith
  calc
    _ ≤ Real.log (2*Real.exp (Real.exp T)) := Real.log_le_log hNpos hcap
    _ = Real.log 2+Real.exp T := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ 2*Real.exp T := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]

theorem exponential_cofactor_sum (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      (∑ a ∈ Finset.Icc 1 (exponentialCofactorCap T), (a.totient : ℝ)⁻¹) ≤
        C*Real.exp (2*T) := by
  obtain ⟨C, hC, hc⟩ := sum_reciprocal_totient_le hmertens
  refine ⟨6*C, by positivity, ?_⟩
  intro T hT
  obtain ⟨hN, hlog⟩ := exponentialCofactorCap_bounds hT
  have he := Real.one_le_exp hT
  have hlog0 : 0 ≤ Real.log (exponentialCofactorCap T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ exponentialCofactorCap T by omega))
  apply (hc _ hN).trans
  calc
    _ ≤ C*(2*Real.exp T)*(3*Real.exp T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlog hC.le
      · linarith
      · linarith
      · positivity
    _ = 6*C*Real.exp (2*T) := by rw [show 2*T=T+T by ring, Real.exp_add]; ring

/-- The entire allowed cofactor sum has the manuscript's exponential envelope
in `P rho^(-P)`, uniformly over the phase. -/
theorem tail_cofactor_sum (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ,
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹) ≤
        C*Real.exp (4*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹) := by
  obtain ⟨C, hC, hc⟩ := exponential_cofactor_sum hmertens
  refine ⟨C, hC, fun H => ?_⟩
  have h := hc (2*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹) (by
    have := lam_pos
    have := rho_pos
    positivity)
  convert h using 1
  · rfl
  · congr 2
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassUpper
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic mass has the required uniform cofactor envelope. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma P_tendsto : Tendsto P atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

lemma P_lt_self {H : ℕ} (hH : 2 ≤ H) : P H < H := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have h1 : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
  by_cases hlog : 0 ≤ Real.log (Real.log (H : ℝ))
  · have hp : (P H : ℝ) ≤ Real.log (Real.log (H : ℝ)) := Nat.floor_le hlog
    have hl := Real.log_le_self (Real.log_nonneg h1)
    have hh := Real.log_le_sub_one_of_pos hpos
    exact_mod_cast (show (P H : ℝ) < H by linarith)
  · have hp : P H=0 := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hlog))
    omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailCutScale
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic tail cut is negligible relative to the retained cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma P_div_self_tendsto :
    Tendsto (fun H : ℕ => (P H : ℝ)/(H : ℝ)) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop :
    Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)
  have hLL := Real.tendsto_log_atTop.comp hlog
  have ht := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)
  apply squeeze_zero' (g := fun H : ℕ => Real.log (H : ℝ)/(H : ℝ))
  · exact Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [hLL.eventually (eventually_ge_atTop (0 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with H hloglog hH
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact (Nat.floor_le hloglog).trans
      (Real.log_le_self (Real.log_nonneg (by exact_mod_cast hH)))
  · exact ht

lemma eventually_tail_cut_separated : ∀ᶠ H : ℕ in atTop,
    1 ≤ P H ∧ P H+2 ≤ H ∧ 100*P H ≤ H ∧ 2*P H ≤ H := by
  filter_upwards [P_tendsto.eventually (eventually_ge_atTop 1),
    P_div_self_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/100)),
    eventually_ge_atTop (1 : ℕ)] with H hP hratio hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hh : (100 : ℝ)*(P H : ℝ) ≤ H := by
    have hx := (div_lt_iff₀ hHpos).mp hratio
    linarith
  have hnat : 100*P H ≤ H := by exact_mod_cast hh
  exact ⟨hP, by omega, hnat, by omega⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionIndices
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Validity of every collision cutoff, uniformly over the retained indices. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma eventually_collision_indices : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, H ≤ m x → ∀ i ≤ R x H,
      H ≤ m x-i ∧ 2*collisionCutoff (m x-i) < m x-i ∧
        i+collisionCutoff (m x-i) < L x H := by
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp collisionCutoff_eventually_small
  filter_upwards [eventually_ge_atTop H₀, eventually_tail_cut_separated] with H hH hsep
  intro x hHm i hi
  have hh : H ≤ m x-i := by unfold R at hi; omega
  have hJ := hH₀ (m x-i) (hH.trans hh)
  have hmi : i ≤ m x := by unfold R at hi; omega
  refine ⟨hh, hJ, ?_⟩
  unfold L
  have hP := hsep.2.2.2
  omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SeparatedBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse bands are ordered and disjoint, including across two witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma bandScale_nonnegative (x : ℝ) (i : ℕ) : 0 ≤ bandScale x i := by
  exact mul_nonneg (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _))
    (inv_nonneg.mpr (pow_pos rho_pos _).le)

lemma bandScale_succ_le (x : ℝ) (i : ℕ) :
    bandScale x (i+1) ≤ rho*bandScale x i := by
  by_cases hi : i < m x
  · let h := m x-(i+1)
    have he : m x-i = h+1 := by dsimp [h]; omega
    have he' : m x-(i+1) = h := rfl
    simp only [bandScale, he, he']
    have hr := pow_pos rho_pos h
    have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg _
    have ha := alpha_pos (theta x)
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp [hr.ne', rho_pos.ne']
    nlinarith
  · have h0 : m x-i = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h1 : m x-(i+1) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [bandScale, h0, h1]

lemma bandScale_antitone (x : ℝ) : Antitone (bandScale x) := by
  apply antitone_nat_of_succ_le
  intro i
  exact (bandScale_succ_le x i).trans (by
    nlinarith [bandScale_nonnegative x i, rho_lt_one])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCollisionCutoffs
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Ford scales satisfy the cutoff hypotheses used for good collisions. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_lower : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) ≤ fordBandScale x i := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num),
    theta_eventually_mem] with x hx hs
  intro i hi
  have hp := bandScale_pos hi
  have hd := (lt_div_iff₀ hp).mp (show (99/100 : ℝ) < fordBandScale x i/bandScale x i by
    linarith [(abs_lt.mp (hx i hi)).1])
  have ha := mul_le_mul_of_nonneg_right (alpha_ge_lam hs.1)
    (div_nonneg (Nat.cast_nonneg (m x-i)) (pow_pos rho_pos (m x-i)).le)
  have he : lam*((m x-i : ℕ) : ℝ)/rho^(m x-i) ≤ bandScale x i := by
    simpa only [bandScale,div_eq_mul_inv,mul_assoc] using ha
  convert (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 99/100)).trans hd.le using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma ford_band_polynomial_lower (k : ℕ) : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i < m x → H ≤ m x-i →
    ((m x-i : ℕ) : ℝ)^k ≤ fordBandScale x i := by
  have hp : (0 : ℝ) < (99/100 : ℝ)*lam := mul_pos (by norm_num) lam_pos
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one k rho_pos.le rho_lt_one).eventually
    (eventually_lt_nhds hp)
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop H₀,eventually_ge_atTop 1] with H hH hH1
  filter_upwards [ford_band_lower] with x hx
  intro i hi hHi
  have hpow := hH₀ (m x-i) (hH.trans hHi)
  have hh : (1 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH1.trans hHi
  have h0 : 0 ≤ ((m x-i : ℕ) : ℝ)^k := by positivity
  have ha : ((m x-i : ℕ) : ℝ)^k ≤
      (99/100 : ℝ)*lam/rho^(m x-i) := by
    apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
    exact hpow.le
  have hc : (99/100 : ℝ)*lam/rho^(m x-i) ≤
      (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) := by
    apply div_le_div_of_nonneg_right _ (pow_pos rho_pos _).le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hp.le
  exact ha.trans (hc.trans (hx i hi))

lemma ford_collision_layer_ratio {x : ℝ} {i : ℕ} (hB : 1 < B x)
    (hi : i < m x) (hJ : 2*collisionCutoff (m x-i) < m x-i) :
    rho/(2*((m x-i : ℕ) : ℝ)^20) ≤
      fordBandScale x (collisionLastIndex x i)/fordBandScale x i ∧
    fordBandScale x (collisionLastIndex x i)/fordBandScale x i ≤
      1/((m x-i : ℕ) : ℝ)^18 := by
  have hh : 1 ≤ m x-i := Nat.sub_pos_of_lt hi
  have hk : collisionLastIndex x i < m x := by unfold collisionLastIndex; omega
  have hc : bandCenterRatio x ≠ 0 := by
    unfold bandCenterRatio
    exact div_ne_zero (Real.log_pos hB).ne' (mul_ne_zero lam_pos.ne'
      (Nat.cast_ne_zero.mpr (by omega)))
  have he : fordBandScale x (collisionLastIndex x i)/fordBandScale x i =
      bandScale x (collisionLastIndex x i)/bandScale x i := by
    rw [fordBandScale_eq_ratio_mul hB hk,fordBandScale_eq_ratio_mul hB hi]
    field_simp
  rw [he]
  have hdim : m x-collisionLastIndex x i = (m x-i)-collisionCutoff (m x-i) := by
    unfold collisionLastIndex
    omega
  have hr := collision_layer_ratio hh hJ.le (theta x)
  simpa only [bandScale,hdim,div_eq_mul_inv,mul_assoc] using hr

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionLogBudget
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic normality losses are smaller than the final collision band. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_log_upper : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    Real.log (6*fordBandScale x i) ≤ 26*(m x-i : ℕ) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1) (by norm_num),theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hx htheta hB
  intro i hi
  have hh : (1 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hi)
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := zero_lt_one.trans_le hh
  have hp := pow_pos rho_pos (m x-i)
  have hb := bandScale_pos hi
  have hf : fordBandScale x i ≤ 2*bandScale x i := by
    have hu := (div_lt_iff₀ hb).mp (show fordBandScale x i/bandScale x i < 2 by
      linarith [(abs_lt.mp (hx i hi)).2])
    exact hu.le
  have ha : alpha (theta x) ≤ 2 := by
    have hl := alpha_le (theta x) htheta
    have hq : lam/rho < 2 := (div_lt_iff₀ rho_pos).mpr (by linarith [lam_lt_one,collision_rho_bounds.1])
    exact hl.trans hq.le
  have hmodel : bandScale x i ≤ 2*(m x-i : ℕ)/rho^(m x-i) := by
    unfold bandScale
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha hh0.le) (inv_pos.mpr hp).le
  have hu : 6*fordBandScale x i ≤ 24*(m x-i : ℕ)/rho^(m x-i) := by
    calc
      _ ≤ 12*bandScale x i := by linarith
      _ ≤ 12*(2*(m x-i : ℕ)/rho^(m x-i)) := mul_le_mul_of_nonneg_left hmodel (by norm_num)
      _ = _ := by ring
  have hf0 := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hl := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 6) hf0) hu
  rw [Real.log_div (mul_pos (by norm_num : (0 : ℝ) < 24) hh0).ne' hp.ne',
    Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) hh0.ne',Real.log_pow] at hl
  have hrho : Real.log rho = -lam := by simp only [lam,one_div,Real.log_inv,neg_neg]
  rw [hrho] at hl
  have hl24 : Real.log (24 : ℝ) ≤ 24 := Real.log_le_self (by norm_num)
  have hlh := Real.log_le_self hh0.le
  have hlam := mul_le_mul_of_nonneg_right lam_lt_one.le hh0.le
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedCube
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unit-box enclosure for a projected banded simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

theorem projected_prime_box_enclosure {x : ℝ} {K : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam)
    (hL : 0 < R x K) {u v : Fin (R x K) → ℝ}
    (hu : u ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hband : ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i)
    (hdist : ∀ i, |u i-v i| ≤ 1) :
    v ∈ enlargedSimplex (R x K) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hP : 1 ≤ K := by
    by_contra hn
    have : K=0 := by omega
    simp only [this, Nat.cast_zero, mul_zero] at hcut
    norm_num at hcut
  have hlower (i : Fin (R x K)) : 1 ≤ rho^(m x-(i.val+1))*v i := by
    apply cube_band_lower hs hcut
    · have := i.isLt; unfold R at this; omega
    · exact hband i
    · exact hdist i
  have hv (i : Fin (R x K)) : 0 ≤ v i := by
    have hp := pow_pos rho_pos (m x-(i.val+1))
    have hh := hlower i
    by_contra hn
    have : rho^(m x-(i.val+1))*v i < 0 := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    linarith
  have herr (i : Fin (R x K)) :
      ((R x K-i.val : ℕ) : ℝ)^2+1 ≤
        (4*((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1)))*v i := by
    have hi := i.isLt
    have hn : 1 ≤ m x-(i.val+1) := by unfold R at hi; omega
    have hnR : (1 : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast hn
    have hh : ((R x K-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show R x K-i.val ≤ m x-(i.val+1) by unfold R; omega)
    have hsq : ((R x K-i.val : ℕ) : ℝ)^2 ≤ ((m x-(i.val+1) : ℕ) : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
    have he := mul_le_mul_of_nonneg_left (hlower i)
      (show 0 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have htop : (R x K : ℝ)^2 ≤ (4*(m x : ℝ)^2*rho^(m x))*B x := by
    have hmP : (K : ℝ) ≤ m x := by exact_mod_cast hPm
    have hm4 : 4 ≤ lam*(m x : ℝ) := hcut.trans (mul_le_mul_of_nonneg_left hmP lam_pos.le)
    have hx := (div_le_div_iff₀ (mul_pos hB (pow_pos rho_pos _)) lam_pos).mp hscale
    have h1 : 1 ≤ B x*rho^(m x) := by nlinarith
    have hsq : (R x K : ℝ)^2 ≤ (m x : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le (m x) (K)) 2
    have he := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4*(m x : ℝ)^2 by positivity)
    nlinarith
  have hh := enlargedSimplex_cube hu
    (fun i => xi_bounds x (i.val+1)) hv hdist herr htop
  have h0 := simplexBoxError_eq x 0 4
  simp only [Nat.sub_zero] at h0
  rw [h0]
  simp_rw [simplexBoxError_eq]
  exact hh


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A projected prime prefix has mass bounded by its own simplex volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma projectedPrimeTuples_subset_grid (x : ℝ) (K : ℕ) (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K) :
    Q ⊆ gridPrimeTuples (projectedPrimeGrid x K Q) := by
  intro p hp
  have hbands := (hQ p hp).2
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (prefixBandRegion_covered x (K) hbands)
  obtain ⟨hb, hc⟩ := Set.mem_iUnion.mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨hb, p, hp, hc⟩, ?_⟩
  apply mem_primeBoxTuples_iff.mpr
  exact ⟨(hQ p hp).1,hc⟩

lemma projectedPrimeGrid_enclosure {x : ℝ} {K : ℕ} (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < R x K) :
    gridRegion (projectedPrimeGrid x K Q) ⊆ enlargedSimplex (R x K) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  intro v hv
  obtain ⟨b, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_, p, hp, hu⟩ := Finset.mem_filter.mp hb
  exact projected_prime_box_enclosure hs hcut hB hscale hL
    (hQ p hp).2 (fun i => ((hQ p hp).1 i).1) (unitGridCell_coordinate_distance hu hv)

lemma projected_volume_zero_prefixRegion {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : 0 < N) :
    volume (prefixRegion N (B x) 0 0) = ENNReal.ofReal (G x N) := by
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, max_eq_left hB]
  rw [G, prod_fin_shifted N g]

theorem projectedPrimeGrid_volume_bound {x : ℝ} {K : ℕ} (Q : Finset (Fin (R x K) → ℕ))
    (hQ : ∀ p ∈ Q, primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(K : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < R x K) :
    volume.real (gridRegion (projectedPrimeGrid x K Q)) ≤
      Real.exp (simplexBoxTail 4 (K))*G x (R x K) := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hj := reverse_enlargement_jacobian hPm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4)
  rw [← simplexBoxTail_eq_tsum] at hj
  have he : volume (gridRegion (projectedPrimeGrid x K Q)) ≤
      ENNReal.ofReal (Real.exp (simplexBoxTail 4 (K))*G x (R x K)) := by
    calc
      _ ≤ volume (enlargedSimplex (R x K) (B x) (β 0)
          (fun i => β (i.val+1))) := by
        apply measure_mono
        simpa only [β, Nat.sub_zero] using projectedPrimeGrid_enclosure Q hQ hs hcut hB hscale hL
      _ ≤ ENNReal.ofReal (∏ i : Fin (R x K), enlargementScale β i)*
          volume (prefixRegion (R x K) (B x) 0 0) :=
        volume_enlargedSimplex_product_bound (B x) β hβ
      _ ≤ ENNReal.ofReal (Real.exp (simplexBoxTail 4 (K)))*
          volume (prefixRegion (R x K) (B x) 0 0) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hj) le_rfl
      _ = _ := by
        rw [projected_volume_zero_prefixRegion hB.le hL, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (G_pos hB _).le))

/-- Full prime mass, before the independent smooth-cofactor sum. -/
theorem projected_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {K : ℕ},
      0 ≤ theta x → 4 ≤ lam*(K : ℝ) → 0 < B x →
      (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam → 0 < R x K →
      ∀ Q : Finset (Fin (R x K) → ℕ),
      (∀ p ∈ Q, (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K ∧
        primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun i => xi x (i.val+1))) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (K))*
          Real.exp (simplexBoxTail 4 (K))*G x (R x K) := by
  obtain ⟨C, hC, hc⟩ := banded_grid_prime_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x K hs hcut hB hscale hL Q hQ
  have hPm : K ≤ m x := by unfold R at hL; omega
  have hh := hc hs (by norm_num : (0 : ℝ)<9/10) hPm (projectedPrimeGrid x K Q) (by
    intro b hb i
    exact bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  change |gridPrimeMass (N := R x K) (projectedPrimeGrid x K Q) -
    (volume (gridRegion (N := R x K) (projectedPrimeGrid x K Q))).toReal| ≤
    (volume (gridRegion (N := R x K) (projectedPrimeGrid x K Q))).toReal *
      bandPrimeError C (9/10) (K) at hh
  have hnon : 0 ≤ 1+bandPrimeError C (9/10) (K) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) (K)]
  calc
    _ ≤ gridPrimeMass (projectedPrimeGrid x K Q) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (projectedPrimeTuples_subset_grid x K Q (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩))
      intro p _ _
      exact reciprocalShiftWeight_nonneg p
    _ ≤ (1+bandPrimeError C (9/10) (K))*volume.real (gridRegion (projectedPrimeGrid x K Q)) := by
      have he := (le_abs_self _).trans hh
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at he
      change gridPrimeMass _ ≤ _*(volume (gridRegion _)).toReal
      calc
        _ ≤ (volume (gridRegion (projectedPrimeGrid x K Q))).toReal +
            (volume (gridRegion (projectedPrimeGrid x K Q))).toReal * bandPrimeError C (9/10) (K) := by
          exact (sub_le_iff_le_add.mp he).trans_eq (add_comm _ _)
        _ = _ := by ring
    _ ≤ (1+bandPrimeError C (9/10) (K))*
        (Real.exp (simplexBoxTail 4 (K))*G x (R x K)) :=
      mul_le_mul_of_nonneg_left (projectedPrimeGrid_volume_bound Q (fun p hp => (hQ p hp).2) hs hcut hB hscale hL) hnon
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixProjection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection preserves the nonnegative simplex inequalities. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma sum_restrict_le {n N : ℕ} (hn : n ≤ N) (f : Fin N → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j : Fin n, f (Fin.castLE hn j)) ≤ ∑ j : Fin N, f j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image (Fin.castLE hn), f j := by
      rw [Finset.sum_image]
      intro j _ k _ he
      exact Fin.ext (congrArg (fun z : Fin N => z.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hf j)

lemma enlargedSimplex_project {n N : ℕ} {x : ℝ} (hn : n ≤ N) {u : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1))) :
    (fun j : Fin n => u (Fin.castLE hn j)) ∈
      enlargedSimplex n (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨fun j => hu.1 _,?_,?_⟩
  · intro i
    have hs := sum_restrict_le hn
      (fun j : Fin N => if Fin.castLE hn i < j then a (j.val-i.val)*u j else 0) (by
        intro j
        split_ifs with hij
        · exact mul_nonneg (a_pos (by have := hij; simp only [Fin.lt_def,Fin.val_castLE] at this; omega)).le (hu.1 j)
        · rfl)
    apply le_trans _ (hu.2.1 (Fin.castLE hn i))
    simpa only [Fin.castLE_mk,Fin.val_castLE,Fin.lt_def] using hs
  · exact (sum_restrict_le hn (fun j : Fin N => a (j.val+1)*u j)
      (fun j => mul_nonneg (a_pos (by omega)).le (hu.1 j))).trans hu.2.2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ProjectedMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform summation over the possible common prime prefixes. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma projectedPrimeFactor_tendsto (C : ℝ) {D : ℝ} (hD : 0 < D) :
    Tendsto (projectedPrimeFactor C D) atTop (nhds 0) := by
  have hb := bandPrimeError_tendsto C (by norm_num : (0 : ℝ)<9/10)
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4)
  have hp := (summable_projectedEnvelope hD).tendsto_atTop_zero
  have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hb).mul he).mul hp
  change Tendsto (fun K => (1+bandPrimeError C (9/10) K)*
    Real.exp (simplexBoxTail 4 K)*projectedEnvelope D K) atTop (nhds 0)
  simpa only [Function.comp_def,add_zero,Real.exp_zero,one_mul,mul_zero] using hh

/-- Uniformly over every late truncation, the whole projected prime mass
is at most the normalizing full-dimensional volume. This includes the empty
prime prefix, whose mass is one. -/
theorem projected_mass_le_G (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ K : ℕ, H ≤ K → K ≤ m x →
    ∀ Q : Finset (Fin (R x K) → ℕ),
    (∀ p ∈ Q, (∀ j, (p j).Prime) ∧ primePrefixCoord p ∈ prefixBandRegion x K ∧
      primePrefixCoord p ∈ enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1))) →
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤ G x (m x) := by
  obtain ⟨C,hC,hprime⟩ := projected_prime_mass_bound hbox
  obtain ⟨D,hD,hproj⟩ := uniform_projected_volume_bound hren
  have hlate : ∀ᶠ K : ℕ in atTop,
      4 ≤ lam*(K : ℝ) ∧ projectedPrimeFactor C D K ≤ 1 ∧ projectedEnvelope D K ≤ 1 := by
    filter_upwards [((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ)),
      (projectedPrimeFactor_tendsto C hD).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
      (summable_projectedEnvelope hD).tendsto_atTop_zero.eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with K hK hf he
    exact ⟨hK,hf.le,he.le⟩
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp hlate
  filter_upwards [eventually_ge_atTop H₀] with H hH
  filter_upwards [hproj,theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),inverse_scale_bound]
    with x hp hs hB hscale
  intro K hHK hKm Q hQ
  obtain ⟨hcut,hfactor,henv⟩ := hH₀ K (hH.trans hHK)
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp K hKm)
  change G x (R x K) ≤ projectedEnvelope D K*G x (m x) at hG
  by_cases hn : 0 < R x K
  · have hmass := hprime hs.1 hcut hB hscale hn Q hQ
    have hpos : 0 ≤ (1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K) :=
      mul_nonneg (by linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) K])
        (Real.exp_pos _).le
    calc
      _ ≤ ((1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K))*G x (R x K) := hmass
      _ ≤ ((1+bandPrimeError C (9/10) K)*Real.exp (simplexBoxTail 4 K))*
          (projectedEnvelope D K*G x (m x)) := mul_le_mul_of_nonneg_left hG hpos
      _ = projectedPrimeFactor C D K*G x (m x) := by unfold projectedPrimeFactor; ring
      _ ≤ G x (m x) := mul_le_of_le_one_left (G_pos hB _).le hfactor
  · have hn0 : R x K=0 := by omega
    have hcard : (Q.card : ℝ) ≤ 1 := by
      have hc : Q.card ≤ 1 := Finset.card_le_one.mpr (by
        intro p _ q _
        funext j
        have hj := j.isLt
        omega)
      exact_mod_cast hc
    have hweight (p : Fin (R x K) → ℕ) : reciprocalShiftWeight p=1 := by
      haveI : IsEmpty (Fin (R x K)) := by rw [hn0]; infer_instance
      simp [reciprocalShiftWeight]
    calc
      _ = (Q.card : ℝ) := by simp [hweight]
      _ ≤ 1 := hcard
      _ = G x (R x K) := by simp [G,hn0]
      _ ≤ projectedEnvelope D K*G x (m x) := hG
      _ ≤ G x (m x) := mul_le_of_le_one_left (G_pos hB _).le henv

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeMassSplit
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split a finite prime family at an arbitrary coordinate without multiplying
by the number of possible prefixes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_parts_injective {N n : ℕ} (hn : n ≤ N) :
    Function.Injective (fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)) := by
  intro p q he
  funext j
  by_cases hj : j.val < n
  · exact congrFun (congrArg Prod.fst he) ⟨j.val,hj⟩
  · have hh := congrFun (congrArg Prod.snd he) ⟨j.val-n,by have := j.isLt; omega⟩
    simpa only [primeFinal,Nat.add_sub_of_le (Nat.le_of_not_gt hj)] using hh

lemma reciprocalShiftWeight_split {N n : ℕ} (hn : n ≤ N) (p : Fin N → ℕ) :
    reciprocalShiftWeight p = reciprocalShiftWeight (primeInitial p n hn)*
      reciprocalShiftWeight (primeFinal p n) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  have ht : (∏ j : Fin (n+d-n), (p ⟨n+j.val,by have := j.isLt; omega⟩-1)) =
      ∏ j : Fin d, (p (Fin.natAdd n j)-1) :=
    by
      have he := Fin.prod_congr' (a := n+d-n) (b := d)
        (fun j : Fin d => p (Fin.natAdd n j)-1) (by omega)
      simpa only [Fin.natAdd,Fin.val_cast] using he
  unfold primeInitial primeFinal reciprocalShiftWeight
  rw [ht,Fin.prod_univ_add,Nat.cast_mul,mul_inv]
  rfl

lemma prime_pi_mass {N : ℕ} (T : Fin N → Finset ℕ) :
    (∑ p ∈ Fintype.piFinset T, reciprocalShiftWeight p) =
      ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [reciprocalShiftWeight,Nat.cast_prod,Finset.prod_inv_distrib]

/-- Each suffix coordinate can have its own arithmetic restriction. The prefix
is counted once, with its original reciprocal mass. -/
theorem prime_mass_split {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (T : Fin (N-n) → Finset ℕ)
    (hT : ∀ p ∈ Q, ∀ j, primeFinal p n j ∈ T j) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
        ∏ j, ∑ q ∈ T j, ((q-1 : ℕ) : ℝ)⁻¹ := by
  classical
  let F := fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)
  have he : (∑ p ∈ Q, reciprocalShiftWeight p) =
      ∑ z ∈ Q.image F, reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun p _ q _ he => prime_parts_injective hn he)]
    exact Finset.sum_congr rfl (fun p _ => reciprocalShiftWeight_split hn p)
  rw [he]
  have hsub : Q.image F ⊆ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Fintype.mem_piFinset.mpr (hT p hp)⟩
  calc
    _ ≤ ∑ z ∈ Q.image (fun p => primeInitial p n hn) ×ˢ Fintype.piFinset T,
        reciprocalShiftWeight z.1*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (reciprocalShiftWeight_nonneg _) (reciprocalShiftWeight_nonneg _))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul,prime_pi_mass]

/-- The same projected geometry used for collisions holds for every basic
remainder, independently of its largest-prime completion. -/
lemma remainderInitial_geometry {x : ℝ} {H K : ℕ} (hn : R x K ≤ L x H)
    (hL : 0 < L x H) {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    (∀ j, (primeInitial η.primes (R x K) hn j).Prime) ∧
    primePrefixCoord (primeInitial η.primes (R x K) hn) ∈ prefixBandRegion x K ∧
    primePrefixCoord (primeInitial η.primes (R x K) hn) ∈
      enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1)) := by
  refine ⟨?_,?_,enlargedSimplex_project hn (basic_remainder_enlargedSimplex hL hη)⟩
  · intro j
    have hh := (hη.2.1 (j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).1
    have he : remainderPrime η (j.val+1)=primeInitial η.primes (R x K) hn j := by
      simp only [remainderPrime,dite_eq_left (show 1 ≤ j.val+1 ∧ j.val+1 ≤ L x H by have := j.isLt; omega),Nat.add_sub_cancel]
      rfl
    exact he ▸ hh
  · intro j
    have hh := (hη.2.1 (j.val+1)
      (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).2
    change (9/10 : ℝ)*bandScale x (j.val+1) ≤ remainderCoord x η ((Fin.castLE hn j).val+1) ∧
      remainderCoord x η ((Fin.castLE hn j).val+1) ≤ (11/10 : ℝ)*bandScale x (j.val+1) at hh
    rw [remainderCoord_fin] at hh
    exact hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ExceptionalPrimeLayer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A restricted coordinate in a late layer costs its own reciprocal mass;
the initial segment retains the projected simplex saving. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prime_mass_one_exception {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (j : Fin (N-n)) (U V : Finset ℕ)
    (hU : ∀ p ∈ Q, ∀ k, primeFinal p n k ∈ U)
    (hV : ∀ p ∈ Q, primeFinal p n j ∈ V) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
  classical
  have hh := prime_mass_split hn Q (fun k => if k=j then V else U) (by
    intro p hp k
    split_ifs with hk
    · subst k; exact hV p hp
    · exact hU p hp k)
  have he : (∏ k : Fin (N-n), ∑ q ∈ (if k=j then V else U), ((q-1 : ℕ) : ℝ)⁻¹) =
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    simp only [ite_true, if_true]
    congr 1
    calc
      _ = ∏ _k ∈ (Finset.univ.erase j), ∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [ite_eq_right (Finset.mem_erase.mp hk).1]
      _ = _ := by simp
  rw [he] at hh
  simpa only [mul_assoc] using hh

theorem basic_prime_initial_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ (n : ℕ) (_hn : n ≤ R x H) (hnL : n ≤ L x H),
    ∀ Q : Finset (Fin (L x H) → ℕ), Q ⊆ fullPrimeTuples x H →
      (∑ p ∈ Q.image (fun p => primeInitial p n hnL),
        reciprocalShiftWeight p) ≤ G x (m x) := by
  filter_upwards [projected_mass_le_G hbox hren,eventually_ge_atTop 2] with H hH hH2
  filter_upwards [hH,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hHm
  intro n hn hnL Q hQ
  have hPH := P_lt_self hH2
  have hL : 0 < L x H := by unfold L; omega
  let K := m x-n
  have hHK : H ≤ K := by dsimp [K]; unfold R at hn; omega
  have hKm : K ≤ m x := Nat.sub_le _ _
  have hd : R x K=n := by unfold R K; omega
  have hKL : R x K ≤ L x H := by rw [hd]; unfold R L at *; omega
  have hh := hx K hHK hKm (Q.image (fun p => primeInitial p (R x K) hKL)) (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp (hQ hq)
    exact remainderInitial_geometry hKL hL (mem_basicRemainderFinset.mp hη))
  revert hh hKL
  rw [hd]
  intro _ hh
  exact hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeReciprocalBound
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The short reciprocal-prime bound needed for the unrestricted suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma shifted_prime_reciprocal_le_log {p : ℕ} (hp : p.Prime) :
    ((p-1 : ℕ) : ℝ)⁻¹ ≤ 2*Real.log ((p : ℝ)/(p-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  rw [hc]
  have ht0 : (0 : ℝ) < (p : ℝ)/(p-1) := div_pos hp0 hs
  have ht1 : (1 : ℝ) ≤ (p : ℝ)/(p-1) := (le_div_iff₀ hs).mpr (by linarith)
  have ht2 : (p : ℝ)/(p-1) ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos ht0
  have hnon := Real.log_nonneg ht1
  have he : ((p-1 : ℝ))⁻¹=((p : ℝ)/(p-1))*(1-((p : ℝ)/(p-1))⁻¹) := by
    field_simp
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hlog ht0.le).trans
    (mul_le_mul_of_nonneg_right ht2 hnon)

lemma prime_reciprocal_mass_log_product (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ 2*Real.log (primeEulerProduct N) := by
  have he : (Nat.primesLE N)=(Finset.Icc 2 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩
  rw [primeEulerProduct,Real.log_prod (by
    intro p hp
    have hh := (Finset.mem_filter.mp hp).2.two_le
    have hh' : (2 : ℝ) ≤ p := by exact_mod_cast hh
    exact (div_pos (by linarith) (by linarith)).ne'),Finset.mul_sum,← he]
  exact Finset.sum_le_sum (fun p hp => shifted_prime_reciprocal_le_log (Nat.mem_primesLE.mp hp).2)

theorem prime_reciprocal_mass_bound (hmertens : MertensProductInput) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, 2 ≤ N → 0 ≤ B N →
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(1+B N) := by
  obtain ⟨C,hC,hprod⟩ := hmertens
  refine ⟨2*(1+|Real.log C|),by positivity,?_⟩
  intro N hN hB
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpos : 0 < primeEulerProduct N := by
    apply Finset.prod_pos
    intro p hp
    have hh : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_pos (by linarith) (by linarith)
  have hh := Real.log_le_log hpos (hprod N hN)
  rw [Real.log_mul hC.ne' hlog.ne'] at hh
  calc
    _ ≤ 2*Real.log (primeEulerProduct N) := prime_reciprocal_mass_log_product N
    _ ≤ 2*(Real.log C+B N) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ _ := by nlinarith [le_abs_self (Real.log C),abs_nonneg (Real.log C)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeDiscardCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common dyadic endpoint for the short suffix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma discardExponent_bounds {b : ℝ} (hb : 2 ≤ b) :
    2 ≤ discardExponent b ∧ Real.log (discardExponent b : ℝ) ≤ 2*b+1 := by
  have he := Real.add_one_le_exp (2*b)
  have hm := Nat.le_ceil (Real.exp (2*b))
  have hm0 : (2 : ℝ) ≤ discardExponent b := by dsimp [discardExponent] <;> linarith
  refine ⟨by exact_mod_cast hm0,?_⟩
  have hc : (discardExponent b : ℝ) ≤ 2*Real.exp (2*b) := by
    have hu := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (2*b) from (Real.exp_pos _).le)
    dsimp [discardExponent]
    linarith
  calc
    _ ≤ Real.log (2*Real.exp (2*b)) := Real.log_le_log (by linarith) hc
    _ = Real.log 2+2*b := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
    _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]

lemma discardPrimeBound_bounds {b : ℝ} (hb : 2 ≤ b) :
    4 ≤ discardPrimeBound b ∧ 0 ≤ B (discardPrimeBound b) ∧
    B (discardPrimeBound b) ≤ 2*b+1 ∧
    Real.exp (Real.exp ((6/5 : ℝ)*b)) ≤ discardPrimeBound b := by
  obtain ⟨hM,hlogM⟩ := discardExponent_bounds hb
  have hM2 : (2 : ℝ) ≤ discardExponent b := by exact_mod_cast hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  have hlog2low : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hB : B (discardPrimeBound b)=Real.log ((discardExponent b : ℝ)*Real.log 2) := by
    simp only [discardPrimeBound,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  refine ⟨?_,?_,?_,?_⟩
  · have he := Nat.pow_le_pow_right (by norm_num : 0<2) hM
    exact he
  · rw [hB]
    apply Real.log_nonneg
    nlinarith
  · rw [hB]
    have hh : (discardExponent b : ℝ)*Real.log 2 ≤ discardExponent b := by nlinarith
    exact (Real.log_le_log (by positivity) hh).trans hlogM
  · have he : (2 : ℝ) ≤ Real.exp ((4/5 : ℝ)*b) := by
      linarith [Real.add_one_le_exp ((4/5 : ℝ)*b)]
    have hsplit : Real.exp (2*b)=Real.exp ((6/5 : ℝ)*b)*Real.exp ((4/5 : ℝ)*b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hceil := Nat.le_ceil (Real.exp (2*b))
    change Real.exp (2*b) ≤ (discardExponent b : ℝ) at hceil
    have hh : Real.exp ((6/5 : ℝ)*b) ≤ (discardExponent b : ℝ)*Real.log 2 := by
      rw [hsplit] at hceil
      nlinarith [Real.exp_pos ((6/5 : ℝ)*b)]
    have hNpos : (0 : ℝ) < discardPrimeBound b := by
      unfold discardPrimeBound
      positivity
    apply (Real.le_log_iff_exp_le hNpos).mp
    simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedWitnessCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting any specified family of full basic witnesses, with their cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma restricted_remainder_weight {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (S : Finset (RemainderDatum (L x H))) (hS : ∀ η ∈ S, IsBasicRemainder x H η) :
    (∑ η ∈ S, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ S.image RemainderDatum.primes, reciprocalShiftWeight p := by
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor,η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F,Prod.mk.injEq,RemainderDatum.mk.injEq,and_comm] using h
  have he : (∑ η ∈ S, remainderReciprocalWeight η) =
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image]
    · rfl
    · intro η _ ξ _ hh
      exact hinj hh
  rw [he]
  have hsub : S.image F ⊆ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes := by
    intro z hz
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (witness_cofactor_bound hs
      (extractTail_isWitness (hS η hη) hPH hHm)),Finset.mem_image.mpr ⟨η,hη,rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalRemainderLayer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford normality applied to each actual positive-index witness layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma primeFinal_remainder {x : ℝ} {H n : ℕ} (η : RemainderDatum (L x H))
    (j : Fin (L x H-n)) :
    primeFinal η.primes n j=remainderPrime η (n+j.val+1) := by
  have hj : 1 ≤ n+j.val+1 ∧ n+j.val+1 ≤ L x H := by have := j.isLt; omega
  simp only [primeFinal,remainderPrime,dite_eq_left hj,Nat.add_sub_cancel]

lemma basic_suffix_discard_bound : ∀ᶠ x : ℝ in atTop, ∀ H i j : ℕ,
    1 ≤ j → i ≤ j → j ≤ L x H → i < m x → 2 ≤ fordBandScale x i →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      remainderPrime η j ∈ Nat.primesLE (discardPrimeBound (fordBandScale x i)) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro H i j hj1 hij hj him hb η hη
  have hp := hη.2.1 j (Finset.mem_Icc.mpr ⟨hj1,hj⟩)
  have hbi := (bandScale_pos him)
  have hf : (99/100 : ℝ)*bandScale x i ≤ fordBandScale x i := by
    have hh := (abs_lt.mp (hx i him)).1
    have hd := (lt_div_iff₀ hbi).mp (by linarith : (99/100 : ℝ)<fordBandScale x i/bandScale x i)
    exact hd.le
  have hcoord : B (remainderPrime η j) ≤ (6/5 : ℝ)*fordBandScale x i := by
    have hm := bandScale_antitone x hij
    have hu0 : B (remainderPrime η j) ≤ (11/10 : ℝ)*bandScale x j := by
      simpa only [remainderCoord,B,ite_eq_right (show j ≠ 0 by omega)] using hp.2.2
    have hu := hu0.trans (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 11/10))
    nlinarith
  have hpR : (1 : ℝ) < remainderPrime η j := by exact_mod_cast hp.1.one_lt
  have hex : (remainderPrime η j : ℝ) ≤ Real.exp (Real.exp ((6/5 : ℝ)*fordBandScale x i)) := by
    exact (Real.log_le_iff_le_exp (zero_lt_one.trans hpR)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hpR)).mp hcoord)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hex.trans (discardPrimeBound_bounds hb).2.2.2,hp.1⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalInternalDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum every non-head normality failure, retaining all basic witnesses. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma nonnegative_sum_biUnion_le {α β : Type*} (I : Finset α) (S : α → Finset β)
    (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ b ∈ I.biUnion S, f b) ≤ ∑ a ∈ I, ∑ b ∈ S a, f b := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have he := Finset.sum_union_inter (s₁ := S a) (s₂ := I.biUnion S) (f := f)
    have hn : 0 ≤ ∑ b ∈ S a ∩ I.biUnion S, f b := Finset.sum_nonneg (fun b _ => hf b)
    linarith

lemma reverse_geometric_sum {M H : ℕ} (hH : H ≤ M) :
    (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) ≤ polynomialGeometricTail 0 rho H := by
  let T := (Finset.Icc 0 (M-H)).image (fun i => M-i-H)
  have hi : Set.InjOn (fun i => M-i-H) (↑(Finset.Icc 0 (M-H)) : Set ℕ) := by
    intro i hi j hj he
    have h1 := Finset.mem_Icc.mp hi
    have h2 := Finset.mem_Icc.mp hj
    change M-i-H=M-j-H at he
    omega
  have he : (∑ i ∈ Finset.Icc 0 (M-H), rho^(M-i)) = ∑ n ∈ T, rho^(H+n) := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have := Finset.mem_Icc.mp hi
    omega
  rw [he]
  have hs : Summable (fun n : ℕ => rho^(H+n)) :=
    (summable_geometric_of_lt_one rho_pos.le rho_lt_one).comp_injective
      (by intro n m hh; omega)
  simpa only [polynomialGeometricTail,pow_zero,one_mul] using
    hs.sum_le_tsum T (fun n _ => (pow_pos rho_pos _).le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaDiscardDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The large factor-count tail dominates the entropy of all suffix choices. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma omega_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b d : ℝ,
      (h : ℝ)^12 ≤ b → Real.log (6*b) ≤ 26*h → d ≤ b/(h : ℝ)^18 →
      ∀ n : ℕ, n ≤ h →
      (h : ℝ)^2*(C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)))*
        (D*(2*b+2))^n ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+30
  have hA : 30 ≤ A := by dsimp [A] <;> linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (12*A+100))] with h hh
  intro b d hb hlog hd n hn
  have hh100 : (100 : ℝ) ≤ h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hb1 : (1 : ℝ) ≤ b := (one_le_pow₀ hh1).trans hb
  have hb0 : 0 < b := by linarith
  have h9 : (72 : ℝ) ≤ (h : ℝ)^9 := by
    have hp := pow_le_pow_right₀ hh1 (show 1 ≤ 9 by omega)
    simp only [pow_one] at hp
    linarith
  have hdsmall : 6*d ≤ b/(12*(h : ℝ)^9) := by
    apply (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 6)).trans
    rw [show 6*(b/(h : ℝ)^18)=(6*b)/(h : ℝ)^18 by ring]
    apply (div_le_div_iff₀ (pow_pos hh0 18) (by positivity : 0 < 12*(h : ℝ)^9)).mpr
    have hp := mul_le_mul_of_nonneg_left h9 (show 0 ≤ b*(h : ℝ)^9 by positivity)
    nlinarith [show (h : ℝ)^18=((h : ℝ)^9)^2 by ring]
  have hlogr : (1/3 : ℝ) ≤ Real.log (3/2) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<3/2)
    norm_num at hh ⊢
    exact hh
  have hT : b/(6*(h : ℝ)^9) ≤ b/(2*(h : ℝ)^9)*Real.log (3/2) := by
    have ht := mul_le_mul_of_nonneg_left hlogr (show 0 ≤ b/(2*(h : ℝ)^9) by positivity)
    convert ht using 1 <;> first | rfl | ring
  have hsaving : 6*d-b/(2*(h : ℝ)^9)*Real.log (3/2) ≤ -(h : ℝ)^3/12 := by
    have hb' : (h : ℝ)^3/12 ≤ b/(12*(h : ℝ)^9) := by
      apply (le_div_iff₀ (by positivity : 0 < 12*(h : ℝ)^9)).mpr
      convert hb using 1 <;> first | rfl | ring
    have he : b/(6*(h : ℝ)^9)=2*(b/(12*(h : ℝ)^9)) := by ring
    linarith
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnR : (n : ℝ) ≤ h := by exact_mod_cast hn
  have hnt : (n : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    (mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hnR (by positivity))
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(2+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hlarge : 12*A ≤ (h : ℝ) := by linarith
  have hextra := mul_nonneg (show 0 ≤ (h : ℝ)^2 by positivity) (sub_nonneg.mpr hlarge)
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+
      (n : ℝ)*(Real.log D+Real.log (2*b+2))+
      (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)) ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2)))*
      (D*(2*b+2))^n = Real.exp (2*Real.log (h : ℝ)+Real.log C+
      (n : ℝ)*(Real.log D+Real.log (2*b+2))+(6*d-b/(2*(h : ℝ)^9)*Real.log (3/2))) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    rw [Real.exp_add,Real.exp_add,Real.exp_add,htwo,Real.exp_nat_mul,Real.exp_add,
      Real.exp_log hC,Real.exp_log hD,Real.exp_log hbase]
    ring
  rw [heq]
  apply (Real.exp_le_exp.mpr hexponent).trans_eq
  have hlogrho : Real.log rho= -lam := by simp [lam,one_div,Real.log_inv]
  rw [show -lam*(h : ℝ)=(h : ℝ)*Real.log rho by rw [hlogrho]; ring,Real.exp_nat_mul,Real.exp_log rho_pos]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaReciprocal
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete Euler-product moment for the remaining-factor exclusion.
The exponent three is sufficient for the application. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omegaReciprocal_nonneg (n : ℕ) : 0 ≤ omegaReciprocal n := by
  change 0 ≤ (3/2 : ℝ)^n.primeFactorsList.length/(n : ℝ)
  positivity

lemma omegaReciprocal_prime {p : ℕ} (hp : p.Prime) : omegaReciprocal p=(3/2 : ℝ)/p := by
  simp [omegaReciprocal,Nat.primeFactorsList_prime hp]

lemma omegaReciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖omegaReciprocal p‖ < 1 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p),omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma omega_euler_factor_le {p : ℕ} (hp : p.Prime) :
    (1-omegaReciprocal p)⁻¹ ≤ ((p : ℝ)/(p-1))^3 := by
  rw [omegaReciprocal_prime hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hs : (0 : ℝ) < p-1 := by linarith
  have ht : (0 : ℝ) < p-3/2 := by linarith
  have he : (1-(3/2 : ℝ)/(p : ℝ))⁻¹=(p : ℝ)/(p-3/2) := by field_simp
  rw [he,div_pow]
  apply (div_le_div_iff₀ ht (pow_pos hs 3)).mpr
  nlinarith [sq_nonneg ((p : ℝ)-2)]

/-- A finite moment over all positive integers below the endpoint; no sieve
or distribution theorem is added to the published hypotheses. -/
theorem omega_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N) :
    (∑ n ∈ Q, omegaReciprocal n) ≤ (primeEulerProduct N)^3 := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (Nat.le_of_mem_primeFactorsList hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, omegaReciprocal n) = ∑ n ∈ T, omegaReciprocal n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    exact (Finset.sum_attach Q (fun n : ℕ => omegaReciprocal n)).symm
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := omegaReciprocal) (fun {_} hp => omegaReciprocal_prime_norm hp) S
  calc
    _ = ∑ n ∈ T, omegaReciprocal n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, omegaReciprocal n :=
      hs.1.of_norm.sum_le_tsum T (fun n _ => omegaReciprocal_nonneg n)
    _ = ∏ p ∈ S with p.Prime, (1-omegaReciprocal p)⁻¹ := hs.2.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, ((p : ℝ)/(p-1))^3 := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpn := omegaReciprocal_prime_norm (Finset.mem_filter.mp hp).2
        rw [Real.norm_eq_abs,abs_of_nonneg (omegaReciprocal_nonneg p)] at hpn
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        exact omega_euler_factor_le (Finset.mem_filter.mp hp).2
    _ = _ := by rw [Finset.prod_pow]; rfl

lemma omega_exceptional_mass {N : ℕ} {T : ℝ} (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ n ≤ N ∧ T ≤ (n.primeFactorsList.length : ℝ)) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ (3/2 : ℝ)^(-T)*(primeEulerProduct N)^3 := by
  have ht : 0 < (3/2 : ℝ)^(-T) := Real.rpow_pos_of_pos (by norm_num) _
  calc
    _ ≤ (3/2 : ℝ)^(-T)*∑ n ∈ Q, omegaReciprocal n := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3/2) (hQ n hn).2.2
      rw [Real.rpow_natCast] at hc
      have hmul : (1 : ℝ) ≤ (3/2 : ℝ)^(-T)*(3/2 : ℝ)^n.primeFactorsList.length := by
        calc
          1 = (3/2 : ℝ)^(-T)*(3/2 : ℝ)^T := by rw [← Real.rpow_add (by norm_num)]; simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hc ht.le
      have hh := mul_le_mul_of_nonneg_right hmul (show 0 ≤ (n : ℝ)⁻¹ by positivity)
      simpa only [omegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,div_eq_mul_inv,mul_assoc,one_mul] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_left (omega_reciprocal_mass N Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)) ht.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaPrimeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete factor-count moment bounds exceptional shifted primes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma omega_shifted_prime_mass (N : ℕ) (T : ℝ) :
    (∑ p ∈ omegaExceptionalPrimes N T, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      (3/2 : ℝ)^(-T)*(primeEulerProduct N)^3 := by
  let Q := omegaExceptionalPrimes N T
  have hp (p : ℕ) (h : p ∈ Q) : p.Prime ∧ p ≤ N ∧ T ≤ ((p-1).primeFactorsList.length : ℝ) := by
    obtain ⟨hN,hT⟩ := Finset.mem_filter.mp h
    obtain ⟨hN,hp⟩ := Nat.mem_primesLE.mp hN
    exact ⟨hp,hN,hT⟩
  have hi : Set.InjOn (fun p : ℕ => p-1) (↑Q : Set ℕ) := by
    intro p hP q hQ he
    have h1 := (hp p hP).1.two_le
    have h2 := (hp q hQ).1.two_le
    change p-1=q-1 at he
    omega
  have hh := omega_exceptional_mass (Q.image (fun p => p-1)) (N := N) (T := T) (by
    intro n hn
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hn
    have h := hp p hpQ
    exact ⟨by have := h.1.two_le; omega,(Nat.sub_le p 1).trans h.2.1,h.2.2⟩)
  rw [Finset.sum_image hi] at hh
  exact hh

lemma omega_prime_mass (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 2 ≤ b → ∀ T : ℝ,
      (∑ p ∈ omegaExceptionalPrimes (discardPrimeBound b) T, ((p-1 : ℕ) : ℝ)⁻¹) ≤
        C*Real.exp (6*b-T*Real.log (3/2)) := by
  obtain ⟨D,hD,hM⟩ := hmertens
  refine ⟨D^3*Real.exp 3,by positivity,?_⟩
  intro b hb T
  obtain ⟨hN,_,hB,_⟩ := discardPrimeBound_bounds hb
  have hN1 : (1 : ℝ) < discardPrimeBound b := by exact_mod_cast (show 1 < discardPrimeBound b by omega)
  have hl : Real.log (discardPrimeBound b : ℝ) ≤ Real.exp (2*b+1) := by
    have hh := Real.exp_le_exp.mpr hB
    simpa only [B,Real.exp_log (Real.log_pos hN1)] using hh
  have hp : 0 ≤ primeEulerProduct (discardPrimeBound b) := by
    unfold primeEulerProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpn : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpn
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)

  have he : primeEulerProduct (discardPrimeBound b) ≤ D*Real.exp (2*b+1) :=
    (hM _ (by omega)).trans (mul_le_mul_of_nonneg_left hl hD.le)
  calc
    _ ≤ (3/2 : ℝ)^(-T)*(primeEulerProduct (discardPrimeBound b))^3 := omega_shifted_prime_mass _ _
    _ ≤ (3/2 : ℝ)^(-T)*(D*Real.exp (2*b+1))^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp he _) (Real.rpow_pos_of_pos (by norm_num) _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<3/2),mul_pow,← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      calc
        _ = D^3*(Real.exp (Real.log (3/2)*(-T))*Real.exp ((3 : ℝ)*(2*b+1))) := by ring
        _ = _ := by
          rw [← Real.exp_add,mul_assoc,← Real.exp_add]
          congr 2
          ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedPrimeLayer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One coordinate restriction in an arbitrary finite family of basic
remainders. The initial segment is charged to its projected simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma restricted_prime_layer_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ (S : Finset (RemainderDatum (L x H))) (n j : ℕ),
      n ≤ R x H → n < j → j ≤ L x H →
      ∀ U V : Finset ℕ,
      (∀ η ∈ S, IsBasicRemainder x H η) →
      (∀ η ∈ S, ∀ l ∈ Finset.Icc (n+1) (L x H), remainderPrime η l ∈ U) →
      (∀ η ∈ S, remainderPrime η j ∈ V) →
      (∑ η ∈ S, remainderReciprocalWeight η) ≤
        (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1) := by
  filter_upwards [basic_prime_initial_mass hbox hren,eventually_ge_atTop 2] with H hpre hH
  filter_upwards [hpre,theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hp hs hHm hB
  intro S n j hn hj hjL U V hS hU hV
  have hPH := P_lt_self hH
  have hnL : n ≤ L x H := by omega
  let Q := S.image RemainderDatum.primes
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  let k : Fin (L x H-n) := ⟨j-(n+1),by omega⟩
  have hk : n+k.val+1=j := by dsimp [k]; omega
  have hall : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ U := by
    intro p hp l
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder]
    exact hU η hη _ (Finset.mem_Icc.mpr ⟨by omega,by have := l.isLt; omega⟩)
  have hbad : ∀ p ∈ Q, primeFinal p n k ∈ V := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    rw [primeFinal_remainder,hk]
    exact hV η hη
  have hm := prime_mass_one_exception hnL Q k U V hall hbad
  have hb := hp n hn hnL Q hQ
  have hw : 0 ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ((∑ p ∈ Q.image (fun p => primeInitial p n hnL), reciprocalShiftWeight p)*
        (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1)) := mul_le_mul_of_nonneg_left hm hw
    _ ≤ _ := by
      have hnonneg : 0 ≤ (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*
          (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(L x H-n-1) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hb hnonneg
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul hw

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaRemainderLayer
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exceptional shifted-prime moment applied to actual remainder layers. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma collision_last_scale_ge_two : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, 2 ≤ fordBandScale x (collisionLastIndex x i) := by
  filter_upwards [eventually_collision_indices,eventually_ge_atTop 8] with H hind hH
  filter_upwards [ford_band_lower,m_tendsto.eventually (eventually_ge_atTop H)] with x hl hm
  intro i hi
  obtain ⟨hHi,hJ,hk⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hkm : collisionLastIndex x i < m x := by unfold collisionLastIndex; omega
  have hrem : 4 ≤ m x-collisionLastIndex x i := by unfold collisionLastIndex; omega
  have hremR : (4 : ℝ) ≤ (m x-collisionLastIndex x i : ℕ) := by exact_mod_cast hrem
  have hnum : 2 ≤ (99/100 : ℝ)*lam*(m x-collisionLastIndex x i : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hremR (show 0 ≤ (99/100 : ℝ)*lam by have := lam_pos; positivity)
    nlinarith [collision_lambda_bounds.1]
  have hpow : rho^(m x-collisionLastIndex x i) ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  apply le_trans _ (hl _ hkm)
  apply (le_div_iff₀ (pow_pos rho_pos _)).mpr
  linarith

theorem omega_remainder_layer_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ i j : ℕ, i ≤ R x H → collisionLastIndex x i < j → j ≤ L x H →
      let b := fordBandScale x i
      let d := fordBandScale x (collisionLastIndex x i)
      (∑ η ∈ omegaExceptionalRemainders x H i j, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*G x (m x)*
        (C*Real.exp (6*d-b/(2*((m x-i : ℕ) : ℝ)^9)*Real.log (3/2)))*
        (D*(2*b+2))^(L x H-i-1) := by
  obtain ⟨C,hC,hbad⟩ := omega_prime_mass hmertens
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [restricted_prime_layer_mass hbox hren,collision_last_scale_ge_two,
    ford_band_polynomial_lower 1,eventually_ge_atTop 2] with H hmass hcut hpoly hH
  filter_upwards [hmass,hcut,hpoly,basic_suffix_discard_bound,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hm hd hp hbound hHm hBx
  intro i j hi hj hjL
  dsimp only
  let b := fordBandScale x i
  let d := fordBandScale x (collisionLastIndex x i)
  let T := b/(2*((m x-i : ℕ) : ℝ)^9)
  let S := omegaExceptionalRemainders x H i j
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hb : 2 ≤ b := by
    have hh := hp i him hHi
    simp only [pow_one] at hh
    exact (show (2 : ℝ) ≤ (m x-i : ℕ) by exact_mod_cast hH.trans hHi).trans hh
  have hd2 : 2 ≤ d := hd i hi
  have hki : i ≤ collisionLastIndex x i := by unfold collisionLastIndex; omega
  have hkm : collisionLastIndex x i < m x := by unfold L at hjL; omega
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hU : ∀ η ∈ S, ∀ l ∈ Finset.Icc (i+1) (L x H),
      remainderPrime η l ∈ Nat.primesLE (discardPrimeBound b) := by
    intro η hη l hl
    obtain ⟨hli,hlL⟩ := Finset.mem_Icc.mp hl
    exact hbound H i l (by omega) (by omega) hlL him hb η (hS η hη)
  have hV : ∀ η ∈ S, remainderPrime η j ∈ omegaExceptionalPrimes (discardPrimeBound d) T := by
    intro η hη
    refine Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp hη).2.le⟩
    exact hbound H (collisionLastIndex x i) j (by omega) hj.le hjL hkm hd2 η (hS η hη)
  have hh := hm S i j hi (by omega) hjL _ _ hS hU hV
  have hbadmass := hbad d hd2 T
  have hgoodmass : (∑ p ∈ Nat.primesLE (discardPrimeBound b), ((p-1 : ℕ) : ℝ)⁻¹) ≤ D*(2*b+2) := by
    obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
    exact (hall _ (by omega) hBN).trans (mul_le_mul_of_nonneg_left (by linarith) hD.le)
  apply hh.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hbadmass
      (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (G_pos hBx _).le)
  · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hgoodmass _
  · positivity
  · exact mul_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (G_pos hBx _).le)
      (by positivity)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OmegaInternalDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite layer summation for the remaining-factor exclusion. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

/-- Sum all exceptional factor-count coordinates after each actual collision cutoff. -/
theorem omega_internal_reciprocal_discard_oai (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        (∑ η ∈ omegaInternalRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨C,D,hC,hD,hlayer⟩ := omega_remainder_layer_mass hbox hren hmertens
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (omega_discard_geometric hC hD)
  filter_upwards [hlayer,ford_band_polynomial_lower 12,eventually_ge_atTop H₀,eventually_ge_atTop 2,eventually_collision_indices,
    P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hL hpoly hH0 hH hind hP
  filter_upwards [hL,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hl hp hlog hHm hB
  let W : ℝ := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => by positivity)
  have hG : 0 ≤ G x (m x) := (G_pos (zero_lt_one.trans hB) _).le
  have hiBound (i : ℕ) (hi : i ∈ Finset.Icc 0 (R x H)) :
      (∑ η ∈ (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i),
        remainderReciprocalWeight η) ≤ W*G x (m x)*rho^(m x-i) := by
    have hiR := (Finset.mem_Icc.mp hi).2
    have him : i < m x := by unfold R at hiR; omega
    have hHi : H ≤ m x-i := by unfold R at hiR; omega
    let h := m x-i
    let b := fordBandScale x i
    let d := fordBandScale x (collisionLastIndex x i)
    let A := C*Real.exp (6*d-b/(2*(h : ℝ)^9)*Real.log (3/2))*(D*(2*b+2))^(L x H-i-1)
    have hb0 : 0 ≤ b := (pow_nonneg (Nat.cast_nonneg (m x-i)) 12).trans (hp i him hHi)
    have hA : 0 ≤ A := by dsimp [A] <;> positivity
    have hbr := fordBandScale_pos (zero_lt_one.trans hB) him
    have hr := (ford_collision_layer_ratio hB him (hind x hHm i hiR).2.1).2
    have hd : d ≤ b/(h : ℝ)^18 := by
      have hh := (div_le_iff₀ hbr).mp hr
      simpa only [d,b,h,one_div,mul_comm,div_eq_mul_inv,one_mul] using hh
    have hk := hH₀ h (hH0.trans hHi) b d (hp i him hHi) (hlog i him) hd
      (L x H-i-1) (by dsimp [h]; unfold L; omega)
    have hk' : (h : ℝ)^2*A ≤ rho^h := by simpa only [A,mul_assoc] using hk
    have hc : ((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ) ≤ (h : ℝ)^2 := by
      have hcn : (Finset.Icc (collisionLastIndex x i+1) (L x H)).card ≤ h := by
        simp only [Nat.card_Icc]
        dsimp [h]
        unfold L collisionLastIndex
        omega
      have hh : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by dsimp [h]; omega)
      have hcR : ((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ) ≤ h := by exact_mod_cast hcn
      nlinarith
    calc
      _ ≤ ∑ j ∈ Finset.Icc (collisionLastIndex x i+1) (L x H),
          ∑ η ∈ omegaExceptionalRemainders x H i j, remainderReciprocalWeight η :=
        nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
      _ ≤ ∑ _j ∈ Finset.Icc (collisionLastIndex x i+1) (L x H), W*G x (m x)*A := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hj1,hjL⟩ := Finset.mem_Icc.mp hj
        have he := hl i j hiR (by omega) hjL
        simpa only [W,A,b,d,h,mul_assoc] using he
      _ = W*G x (m x)*(((Finset.Icc (collisionLastIndex x i+1) (L x H)).card : ℝ)*A) := by simp <;> ring
      _ ≤ W*G x (m x)*((h : ℝ)^2*A) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hA) (mul_nonneg hW hG)
      _ ≤ _ := mul_le_mul_of_nonneg_left hk' (mul_nonneg hW hG)
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  calc
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H),
        ∑ η ∈ (Finset.Icc (collisionLastIndex x i+1) (L x H)).biUnion (omegaExceptionalRemainders x H i), remainderReciprocalWeight η :=
      nonnegative_sum_biUnion_le _ _ _ (fun η => mul_nonneg (by positivity : (0 : ℝ) ≤ (η.cofactor.totient : ℝ)⁻¹) (reciprocalShiftWeight_nonneg η.primes))
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H), W*G x (m x)*rho^(m x-i) := Finset.sum_le_sum hiBound
    _ = W*G x (m x)*(∑ i ∈ Finset.Icc 0 (R x H), rho^(m x-i)) := by rw [Finset.mul_sum]
    _ ≤ (E*Real.exp ((4*(lam/rho))*cofactorScale H))*G x (m x)*polynomialGeometricTail 0 rho H := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hw hG
      · exact reverse_geometric_sum hHm
      · exact Finset.sum_nonneg (fun _ _ => (pow_pos rho_pos _).le)
      · positivity
    _ = _ := by dsimp [ε] <;> ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.omega_internal_reciprocal_discard_oai := @OAI.TotientAsymptotic.omega_internal_reciprocal_discard_oai
