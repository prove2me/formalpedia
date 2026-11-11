-- Prove2me | solution 1 for OAI.TotientAsymptotic.actual_positive_collision_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:32:28.488194+00:00
-- url     : https://prove2.me/submissions/9ca0112d-2335-4653-a1bf-305292e8ee33

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
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_actual_block_count

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral comparison for reciprocal-weighted dyadic collision slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma suffix_power_sum_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n+N+1 : ℕ) : ℝ)^(-1-σ)) ≤ (N : ℝ)^(-σ)/σ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun t : ℝ => t^(-1-σ)) (Set.Ici (N : ℝ)) := by
    intro s hs t _ hst
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hs) hst (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (a := -1-σ) (by linarith) hNR
  have hh := ha.tsum_comp_add_le_integral N hint (fun t ht => Real.rpow_nonneg (hNR.trans ht).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -1-σ < -1) hNR] at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)

lemma dyadicSuffixWeight_eq {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    dyadicSuffixWeight σ n = (Real.log 2)^(-1-σ)*(n : ℝ)^(-1-σ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < (n : ℝ)*Real.log 2 := mul_pos hnR htwo
  rw [← Real.mul_rpow htwo.le hnR.le, mul_comm (Real.log 2), Real.rpow_def_of_pos hp]
  have he : Real.log ((n : ℝ)*Real.log 2)*(-1-σ) =
      -σ*Real.log ((n : ℝ)*Real.log 2)-Real.log ((n : ℝ)*Real.log 2) := by ring
  rw [he, Real.exp_sub, Real.exp_log hp]
  rfl

lemma dyadic_suffix_summable {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Summable (fun n : ℕ => dyadicSuffixWeight σ (n+N+1)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-1-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := (hs.comp_injective (fun n m (he : n+N+1=m+N+1) => by omega)).mul_left
    ((Real.log 2)^(-1-σ))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact dyadicSuffixWeight_eq (by omega)

lemma dyadic_suffix_weight_sum {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, dyadicSuffixWeight σ (n+N+1)) ≤
      ((N : ℝ)*Real.log 2)^(-σ)/(σ*Real.log 2) := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (n : ℕ) : dyadicSuffixWeight σ (n+N+1) =
      (Real.log 2)^(-1-σ)*((n+N+1 : ℕ) : ℝ)^(-1-σ) :=
    dyadicSuffixWeight_eq (by omega)
  simp_rw [he]
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left (suffix_power_sum_le hσ hN)
    (Real.rpow_nonneg htwo.le _)).trans_eq
  rw [Real.mul_rpow hnR.le htwo.le,
    show -1-σ = -1+(-σ) by ring, Real.rpow_add htwo,
    Real.rpow_neg_one]
  field_simp

/-- In logarithmic height the total reciprocal collision mass decays like
`exp (-σ B)/σ`. No factor `exp B` is lost in the dyadic summation. -/
theorem dyadic_suffix_exponential_bound {σ B : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N)
    (hNB : Real.exp B ≤ (N : ℝ)*Real.log 2) :
    (∑' n : ℕ, dyadicSuffixWeight σ (n+N+1)) ≤
      Real.exp (-σ*B)/(σ*Real.log 2) := by
  apply (dyadic_suffix_weight_sum hσ hN).trans
  apply div_le_div_of_nonneg_right _ (mul_pos hσ (Real.log_pos (by norm_num))).le
  have hh := Real.rpow_le_rpow_of_nonpos (Real.exp_pos B) hNB (by linarith : -σ ≤ 0)
  rw [Real.rpow_def_of_pos (Real.exp_pos B), Real.log_exp] at hh
  simpa only [mul_comm] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionDyadicCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From counts in dyadic suffix intervals to their reciprocal mass. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The dyadic count has the exact normalization `C*y/log(y)` times its
strict-slack saving. Weighting each suffix by its reciprocal cancels `y`. -/
theorem collision_dyadic_reciprocal_bound {α : Type*} (Q : Finset α)
    (idx : α → ℕ) (v : α → ℝ) {N : ℕ} (hN : 1 ≤ N) {C σ B : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ) (hB : Real.exp B ≤ (N : ℝ)*Real.log 2)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(idx a+N+1)/2 < v a)
    (hcount : ∀ k : ℕ, ((Q.filter (fun a => idx a=k)).card : ℝ) ≤
      C*(2 : ℝ)^(k+N+1)*dyadicSuffixWeight σ (k+N+1)) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ (2*C)/(σ*Real.log 2)*Real.exp (-σ*B) := by
  classical
  have hmap : ∀ a ∈ Q, idx a ∈ Q.image idx := fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hfiber (k : ℕ) : (∑ a ∈ Q.filter (fun a => idx a=k), (v a)⁻¹) ≤
      2*C*dyadicSuffixWeight σ (k+N+1) := by
    have hy : (0 : ℝ) < (2 : ℝ)^(k+N+1) := by positivity
    calc
      _ ≤ ∑ _a ∈ Q.filter (fun a => idx a=k), 2/(2 : ℝ)^(k+N+1) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha, hk⟩ := Finset.mem_filter.mp ha
        have hl := hlo a ha
        rw [hk] at hl
        have hh := inv_anti₀ (div_pos hy (by norm_num)) hl.le
        simpa only [inv_div] using hh
      _ = ((Q.filter (fun a => idx a=k)).card : ℝ)*(2/(2 : ℝ)^(k+N+1)) := by simp
      _ ≤ (C*(2 : ℝ)^(k+N+1)*dyadicSuffixWeight σ (k+N+1))*(2/(2 : ℝ)^(k+N+1)) :=
        mul_le_mul_of_nonneg_right (hcount k) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ k ∈ Q.image idx, 2*C*dyadicSuffixWeight σ (k+N+1) :=
      Finset.sum_le_sum (fun k _ => hfiber k)
    _ = 2*C*∑ k ∈ Q.image idx, dyadicSuffixWeight σ (k+N+1) := by rw [Finset.mul_sum]
    _ ≤ 2*C*∑' k : ℕ, dyadicSuffixWeight σ (k+N+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (dyadic_suffix_summable hσ N).sum_le_tsum
      intro k _
      unfold dyadicSuffixWeight
      exact div_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg _)
        (Real.log_pos (by norm_num)).le)
    _ ≤ 2*C*(Real.exp (-σ*B)/(σ*Real.log 2)) :=
      mul_le_mul_of_nonneg_left (dyadic_suffix_exponential_bound hσ hN hB) (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_DyadicCollisionMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite dyadic quotient can be integrated from its actual lowest slice. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma dyadic_nat_bounds {v : ℕ} (hv : 1 < v) :
    1 ≤ Nat.clog 2 v ∧ (2 : ℝ)^(Nat.clog 2 v)/2 < v ∧
      (v : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 v) := by
  have hn : 1 ≤ Nat.clog 2 v := by
    have hh := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2) (x := v) (y := 0)).mpr
      (by simpa using hv)
    omega
  refine ⟨hn,?_,?_⟩
  · have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hv
    have he : Nat.clog 2 v=Nat.clog 2 v-1+1 := by omega
    rw [he,pow_succ]
    have hcast : (2 : ℝ)^(Nat.clog 2 v-1) < v := by exact_mod_cast hh
    convert hcast using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) v

lemma dyadic_endpoint_log (n : ℕ) :
    Real.log ((2 : ℝ)^n)=(n : ℝ)*Real.log 2 := by rw [Real.log_pow]

lemma dyadic_endpoint_B (n : ℕ) :
    B ((2 : ℝ)^n)=Real.log ((n : ℝ)*Real.log 2) := by
  rw [B,dyadic_endpoint_log]

/-- The dyadic count can be integrated using only a lower bound at the
occupied slices. Empty slices require no separate counting hypothesis. -/
theorem finite_dyadic_collision_mass {α : Type*} (Q : Finset α)
    (n : α → ℕ) (v : α → ℝ) {C σ B : ℝ}
    (hC : 0 ≤ C) (hσ : 0 < σ)
    (hstart : ∀ a ∈ Q, 2 ≤ n a ∧ Real.exp B ≤ ((n a-1 : ℕ) : ℝ)*Real.log 2)
    (hlo : ∀ a ∈ Q, (2 : ℝ)^(n a)/2 < v a)
    (hcount : ∀ k : ℕ, ((Q.filter (fun a => n a=k)).card : ℝ) ≤
      C*(2 : ℝ)^k*dyadicSuffixWeight σ k) :
    (∑ a ∈ Q, (v a)⁻¹) ≤ (2*C)/(σ*Real.log 2)*Real.exp (-σ*B) := by
  classical
  by_cases hQ : Q.Nonempty
  · let T := Q.image n
    have hT : T.Nonempty := hQ.image n
    let n₀ := T.min' hT
    have hn₀ : n₀ ∈ T := Finset.min'_mem T hT
    obtain ⟨a₀,ha₀,he₀⟩ := Finset.mem_image.mp hn₀
    have hs := hstart a₀ ha₀
    rw [he₀] at hs
    let N := n₀-1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hmin (a : α) (ha : a ∈ Q) : n₀ ≤ n a :=
      Finset.min'_le T (n a) (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    let idx := fun a => n a-N-1
    have he (a : α) (ha : a ∈ Q) : idx a+N+1=n a := by
      have hh := hmin a ha
      dsimp [idx,N]
      omega
    apply collision_dyadic_reciprocal_bound Q idx v hN hC hσ hs.2
    · intro a ha
      simpa only [he a ha] using hlo a ha
    · intro k
      have hf : Q.filter (fun a => idx a=k)=Q.filter (fun a => n a=k+N+1) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨ha,hk⟩
          exact ⟨ha,by rw [← he a ha,hk]⟩
        · rintro ⟨ha,hk⟩
          refine ⟨ha,?_⟩
          have hh := he a ha
          omega
      rw [hf]
      exact hcount _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp only [Finset.sum_empty]
    positivity

lemma dyadic_band_start {b : ℝ} {n : ℕ} (hb : 100 ≤ b) (hn : 1 ≤ n)
    (hband : (87/100 : ℝ)*b ≤ B ((2 : ℝ)^n)) :
    2 ≤ n ∧ Real.exp (b/2) ≤ ((n-1 : ℕ) : ℝ)*Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnl : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow := Real.exp_le_exp.mpr hband
  rw [dyadic_endpoint_B,Real.exp_log (mul_pos hnl hlog2)] at hpow
  have hlarge : Real.log 2 ≤ Real.exp (b/2) := by
    have he := Real.add_one_le_exp (b/2)
    linarith [Real.log_two_lt_d9]
  have hfactor : 2 ≤ Real.exp ((37/100 : ℝ)*b) := by
    have he := Real.add_one_le_exp ((37/100 : ℝ)*b)
    linarith
  have heq : Real.exp ((87/100 : ℝ)*b)=
      Real.exp (b/2)*Real.exp ((37/100 : ℝ)*b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdouble : 2*Real.exp (b/2) ≤ (n : ℝ)*Real.log 2 := by
    rw [heq] at hpow
    nlinarith [Real.exp_pos (b/2)]
  have hsub : ((n-1 : ℕ) : ℝ)=(n : ℝ)-1 := by
    rw [Nat.cast_sub hn,Nat.cast_one]
  have hbnd : Real.exp (b/2) ≤ ((n-1 : ℕ) : ℝ)*Real.log 2 := by
    rw [hsub]
    nlinarith
  refine ⟨?_,hbnd⟩
  by_contra hn2
  have hn1 : n=1 := by omega
  rw [hn1] at hbnd
  norm_num at hbnd
  exact (Real.exp_pos _).not_ge hbnd

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

lemma prod_Icc_split_at {M : Type*} [CommMonoid M] {i R L : ℕ}
    (hi : i ≤ R) (hR : R ≤ L) (f : ℕ → M) :
    (∏ r ∈ Finset.Icc (i+1) L, f r) =
      (∏ r ∈ Finset.Icc (i+1) R, f r) * ∏ r ∈ Finset.Icc (R+1) L, f r := by
  have he : Finset.Icc (i+1) L = Finset.Icc (i+1) R ∪ Finset.Icc (R+1) L := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [he, Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have := Finset.mem_Icc.mp hr
  have := Finset.mem_Icc.mp hs
  omega

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Factor-count additivity and largest-factor alignment for collision pairs. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma primeFactor_le_largest {n p : ℕ} (hp : p ∈ n.primeFactorsList) :
    p ≤ largestPrimeFactor n := by
  have hm : p ∈ n.primeFactors := by
    change p ∈ n.primeFactorsList.toFinset
    exact List.mem_toFinset.mpr hp
  exact (Finset.le_sup (f := id) hm).trans (le_max_right _ _)

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

lemma separated_coarse_bands {x : ℝ} {i j : ℕ} (hij : i < j) (hi : i < m x) :
    (11/10 : ℝ)*bandScale x j < (9/10 : ℝ)*bandScale x i := by
  have hstep := (bandScale_antitone x (show i+1 ≤ j by omega)).trans (bandScale_succ_le x i)
  have hpos := bandScale_pos hi
  have hr := collision_rho_bounds.2
  nlinarith

lemma basic_prime_bands_disjoint {x : ℝ} {H : ℕ}
    {η ξ : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hξ : IsBasicRemainder x H ξ) {i j : ℕ}
    (hi : i ∈ Finset.Icc 1 (L x H)) (hj : j ∈ Finset.Icc 1 (L x H))
    (him : i < m x) (hjm : j < m x)
    (heq : remainderPrime η i = remainderPrime ξ j) : i = j := by
  have hηi := hη.2.1 i hi
  have hξj := hξ.2.1 j hj
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hc : remainderCoord x η i = remainderCoord x ξ j := by
    simp only [remainderCoord, ite_eq_right hi0, ite_eq_right hj0, heq]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hh := separated_coarse_bands hij him
    linarith [hηi.2.1, hξj.2.2]
  · exact hij
  · have hh := separated_coarse_bands hij hjm
    linarith [hηi.2.2, hξj.2.1]

lemma basic_remainder_prime_strictAnti {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    {i j : ℕ} (hi : i ∈ Finset.Icc 1 (L x H))
    (hj : j ∈ Finset.Icc 1 (L x H)) (hij : i < j) (him : i < m x) :
    remainderPrime η j < remainderPrime η i := by
  have hηi := hη.2.1 i hi
  have hηj := hη.2.1 j hj
  have hc : remainderCoord x η j < remainderCoord x η i :=
    lt_of_le_of_lt hηj.2.2 ((separated_coarse_bands hij him).trans_le hηi.2.1)
  by_contra! hn
  have hpos : (1 : ℝ) < remainderPrime η i := by exact_mod_cast hηi.1.one_lt
  have hn' : (remainderPrime η i : ℝ) ≤ remainderPrime η j := by exact_mod_cast hn
  have hm := Real.log_le_log (Real.log_pos hpos)
    (Real.log_le_log (by positivity : (0 : ℝ) < remainderPrime η i) hn')
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [remainderCoord, ite_eq_right hi0, ite_eq_right hj0] at hc
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixFactorization
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact suffix totient factorizations for basic witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma suffixPreimage_pos {x : ℝ} {H i : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) : 0 < suffixPreimage η i := by
  apply Nat.mul_pos hη.1
  apply Finset.prod_pos
  intro r hr
  exact (hη.2.1 r (Finset.mem_Icc.mpr
    ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩)).1.pos

lemma basic_prime_coprime_suffix {x : ℝ} {H i j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hi : i ∈ Finset.Icc 1 (L x H))
    (hij : i ≤ j) (hiL : i < L x H) :
    (remainderPrime η i).Coprime (suffixPreimage η j) := by
  have hp := (hη.2.1 i hi).1
  have him : i < m x := (Finset.mem_Icc.mp hi).2.trans_lt hL
  have hcof : (remainderPrime η i).Coprime η.cofactor := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    have hl := primeFactor_le_largest
      ((Nat.mem_primeFactorsList_iff_dvd hη.1.ne' hp).mpr hdvd)
    have hlast := basic_remainder_prime_strictAnti hη hi
      (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; omega, le_rfl⟩) hiL him
    exact (not_lt_of_ge (hl.trans hη.2.2.2.1)) hlast
  apply hcof.mul_right
  apply Nat.coprime_prod_right_iff.mpr
  intro r hr
  have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
    ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
  have hir : i < r := by have := (Finset.mem_Icc.mp hr).1; omega
  exact (Nat.coprime_primes hp (hη.2.1 r hr').1).mpr
    (ne_of_gt (basic_remainder_prime_strictAnti hη hi hr' hir him))

private lemma totient_prime_product_exact {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (a : ℕ) (hp : ∀ i ∈ I, (p i).Prime)
    (hcop : ∀ i ∈ I, (p i).Coprime a)
    (hpair : Set.InjOn p (↑I : Set ι)) :
    (a*∏ i ∈ I, p i).totient = a.totient*∏ i ∈ I, (p i-1) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hpI : ∀ j ∈ I, (p j).Prime := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hcopI : ∀ j ∈ I, (p j).Coprime a := fun j hj => hcop j (Finset.mem_insert_of_mem hj)
    have hpairI : Set.InjOn p (↑I : Set ι) := fun j hj k hk =>
      hpair (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk)
    have hc : (p i).Coprime (a*∏ j ∈ I, p j) := by
      apply (hcop i (Finset.mem_insert_self _ _)).mul_right
      apply Nat.coprime_prod_right_iff.mpr
      intro j hj
      apply (Nat.coprime_primes (hp i (Finset.mem_insert_self _ _)) (hpI j hj)).mpr
      intro he
      have hij := hpair (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) he
      subst j
      exact hi hj
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    calc
      _ = (p i*(a*∏ j ∈ I, p j)).totient := by congr 1; ring
      _ = (p i-1)*(a*∏ j ∈ I, p j).totient := by
        rw [Nat.totient_mul hc, Nat.totient_prime (hp i (Finset.mem_insert_self _ _))]
      _ = _ := by rw [ih hpI hcopI hpairI]; ring

/-- Cutting a basic witness strictly before its final displayed prime gives an
exact multiplicative totient split. Repetitions inside the final cofactor are retained. -/
theorem basic_suffix_totient_split {x : ℝ} {H i j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hij : i ≤ j) (hjL : j < L x H) :
    (suffixPreimage η i).totient = (suffixPreimage η j).totient *
      ∏ r ∈ Finset.Icc (i+1) j, (remainderPrime η r-1) := by
  have hsub : ∀ r ∈ Finset.Icc (i+1) j, r ∈ Finset.Icc 1 (L x H) := by
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have he : suffixPreimage η i = suffixPreimage η j*
      ∏ r ∈ Finset.Icc (i+1) j, remainderPrime η r := by
    unfold suffixPreimage
    rw [prod_Icc_split_at hij hjL.le]
    ring
  rw [he]
  apply totient_prime_product_exact
  · intro r hr
    exact (hη.2.1 r (hsub r hr)).1
  · intro r hr
    exact basic_prime_coprime_suffix hη hL (hsub r hr)
      (Finset.mem_Icc.mp hr).2 ((Finset.mem_Icc.mp hr).2.trans_lt hjL)
  · intro r hr s hs he
    exact basic_prime_bands_disjoint hη hη (hsub r hr) (hsub s hs)
      ((Finset.mem_Icc.mp (hsub r hr)).2.trans_lt hL)
      ((Finset.mem_Icc.mp (hsub s hs)).2.trans_lt hL) he

lemma suffixPreimage_at_R {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) :
    suffixPreimage η (R x H) = remainderTail x H η := rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionTuples
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tuples, their basic witnesses, and the first differing prime. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma basic_prefix_data_positive {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H ≤ H) (hζ : IsPrefixDatum x H ζ) :
    0 < ζ.d ∧ ∀ i, (ζ.primes i).Prime := by
  obtain ⟨η, hη, hd, hp⟩ := hζ
  constructor
  · rw [← hd]
    exact Nat.totient_pos.mpr (suffixPreimage_pos (i := R x H) hη)
  · intro i
    rw [hp i]
    apply (hη.2.1 _ _).1
    have hi := i.isLt
    apply Finset.mem_Icc.mpr
    unfold R L at *
    omega

lemma basic_tuple_primes {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) :
    ∀ i, (tuplePrimes τ i).Prime := by
  intro i
  refine Fin.cases hτ.1 (fun j => ?_) i
  exact (basic_prefix_data_positive hPH hτ.2.2.1).2 j

lemma basic_tuple_value_pos {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : 0 < tupleValue τ := by
  apply Nat.mul_pos (basic_prefix_data_positive hPH hτ.2.2.1).1
  exact Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (basic_tuple_primes hPH hτ i).one_lt)

/-- The common displayed prefix cancels before the comparison estimate is
applied. The remaining product still contains the true tail totient. -/
lemma tuple_collision_suffix_identity {R : ℕ} {τ σ : TotientTuple R}
    (hp : ∀ i, 2 ≤ tuplePrimes τ i) (hv : tupleValue τ = tupleValue σ)
    (i : Fin (R+1)) (hcommon : ∀ j, j < i → tuplePrimes τ j = tuplePrimes σ j) :
    τ.tail.d*(∏ j ∈ Finset.Ici i, (tuplePrimes τ j-1)) =
      σ.tail.d*(∏ j ∈ Finset.Ici i, (tuplePrimes σ j-1)) := by
  have hsplit (p : Fin (R+1) → ℕ) : (∏ j, (p j-1)) =
      (∏ j ∈ Finset.Iio i, (p j-1))*(∏ j ∈ Finset.Ici i, (p j-1)) := by
    have hpart : Finset.Iio i ∪ Finset.Ici i = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ]
      exact iff_true_intro (lt_or_ge j i)
    have hdis : Disjoint (Finset.Iio i) (Finset.Ici i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_Ici.mp hk)) (Finset.mem_Iio.mp hj)
    rw [← hpart, Finset.prod_union hdis]
  have he : (∏ j ∈ Finset.Iio i, (tuplePrimes τ j-1)) =
      ∏ j ∈ Finset.Iio i, (tuplePrimes σ j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hcommon j (Finset.mem_Iio.mp hj)]
  have hpos : 0 < ∏ j ∈ Finset.Iio i, (tuplePrimes τ j-1) :=
    Finset.prod_pos (fun j _ => by have := hp j; omega)
  unfold tupleValue at hv
  rw [hsplit, hsplit, ← he] at hv
  apply Nat.eq_of_mul_eq_mul_left hpos
  nlinarith [hv]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleCounting
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite set of distinct arithmetic tuples used in the collision count. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma basic_tuple_head_bound {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : τ.head < ⌊t⌋₊+2 := by
  have hpos := basic_prefix_data_positive hPH hτ.2.2.1
  have hd : 0 < τ.tail.d*∏ i, (τ.tail.primes i-1) := by
    apply Nat.mul_pos hpos.1
    exact Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hpos.2 i).one_lt)
  have hv : tupleValue τ = (τ.head-1)*(τ.tail.d*∏ i, (τ.tail.primes i-1)) := by
    unfold tupleValue tuplePrimes
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  have hl : τ.head-1 ≤ tupleValue τ := by rw [hv]; nlinarith
  have hfloor : τ.head-1 ≤ ⌊t⌋₊ := Nat.le_floor ((by exact_mod_cast hl : ((τ.head-1 : ℕ) : ℝ) ≤ tupleValue τ).trans hτ.2.2.2)
  omega

lemma mem_tupleFinset {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) : τ ∈ tupleFinset x H t ↔ IsBasicTuple x H t τ := by
  classical
  constructor
  · exact fun ht => (Finset.mem_filter.mp ht).2
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨?_, ht⟩
    apply Finset.mem_image.mpr
    exact ⟨(τ.head, τ.tail), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (basic_tuple_head_bound hPH ht), mem_prefixDataFinset.mpr ht.2.2.1⟩, rfl⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GoodTuples
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual good tuples: every basic witness must satisfy the four collision conditions. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_goodTupleFinset {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) : τ ∈ goodTupleFinset x H t ↔ IsGoodTuple x H t τ := by
  simp only [goodTupleFinset, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨(mem_tupleFinset hPH).mpr h.1,h⟩⟩

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic size estimates for the complete remainder of a basic witness. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma basic_prime_log_le {x : ℝ} {H r : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hr : r ∈ Finset.Icc 1 (L x H)) :
    Real.log (remainderPrime η r : ℝ) ≤ Real.exp ((11/10 : ℝ)*bandScale x r) := by
  have hp := hη.2.1 r hr
  have hpos : (1 : ℝ) < remainderPrime η r := by exact_mod_cast hp.1.one_lt
  have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
  apply (Real.log_le_iff_le_exp (Real.log_pos hpos)).mp
  simpa only [remainderCoord, ite_eq_right hr0] using hp.2.2

lemma log_suffixPreimage {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    Real.log (suffixPreimage η j : ℝ) = Real.log (η.cofactor : ℝ)+
      ∑ r ∈ Finset.Icc (j+1) (L x H), Real.log (remainderPrime η r : ℝ) := by
  have hcof : (η.cofactor : ℝ) ≠ 0 := by exact_mod_cast hη.1.ne'
  have hp (r : ℕ) (hr : r ∈ Finset.Icc (j+1) (L x H)) :
      (remainderPrime η r : ℝ) ≠ 0 := by
    have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
    exact_mod_cast (hη.2.1 r hr').1.ne_zero
  simp only [suffixPreimage, Nat.cast_mul, Nat.cast_prod]
  rw [Real.log_mul hcof (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp]

/-- All factors after a cutoff are bounded by the first band after it. This
keeps the cofactor separate and permits repetitions of the last prime. -/
theorem basic_suffix_log_bound {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) :
    Real.log (suffixPreimage η j : ℝ) ≤
      (L x H-j : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (j+1))+
        Real.exp (2*bandScale x (L x H)) := by
  rw [log_suffixPreimage hη]
  have hs : (∑ r ∈ Finset.Icc (j+1) (L x H), Real.log (remainderPrime η r : ℝ)) ≤
      (L x H-j : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (j+1)) := by
    calc
      _ ≤ ∑ _r ∈ Finset.Icc (j+1) (L x H), Real.exp ((11/10 : ℝ)*bandScale x (j+1)) := by
        apply Finset.sum_le_sum
        intro r hr
        have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
          ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
        exact (basic_prime_log_le hη hr').trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (bandScale_antitone x (Finset.mem_Icc.mp hr).1)
            (by norm_num)))
      _ = _ := by simp [Nat.card_Icc]
  linarith [hη.2.2.2.2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionSuffixSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform size of the actual suffix following a first differing prime. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collision_coarse_sizes : ∀ᶠ x : ℝ in atTop, ∀ H i : ℕ,
    1 ≤ i → i+2 ≤ L x H → L x H < m x → ∀ η : RemainderDatum (L x H),
    IsBasicRemainder x H η →
    (22/25 : ℝ)*fordBandScale x i ≤ B (remainderPrime η i) ∧
    B (remainderPrime η i) ≤ (28/25 : ℝ)*fordBandScale x i ∧
    Real.log (suffixPreimage η i : ℝ) ≤
      ((m x-i : ℕ)+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro H i hi hiL hL η hη
  have him : i < m x := by omega
  have hb := bandScale_pos him
  have hflo : (99/100 : ℝ)*bandScale x i < fordBandScale x i :=
    (lt_div_iff₀ hb).mp (by linarith [(abs_lt.mp (hx i him)).1])
  have hfhi : fordBandScale x i < (101/100 : ℝ)*bandScale x i :=
    (div_lt_iff₀ hb).mp (by linarith [(abs_lt.mp (hx i him)).2])
  have hp := hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)
  have hu : (9/10 : ℝ)*bandScale x i ≤ B (remainderPrime η i) ∧
      B (remainderPrime η i) ≤ (11/10 : ℝ)*bandScale x i := by
    simpa only [remainderCoord,B,ite_eq_right (by omega : i ≠ 0)] using hp.2
  refine ⟨by nlinarith,by nlinarith,?_⟩
  have hs1 : bandScale x (i+1) ≤ (137/250 : ℝ)*bandScale x i := by
    exact (bandScale_succ_le x i).trans
      (mul_le_mul_of_nonneg_right collision_rho_bounds.2.le hb.le)
  have hs2 : bandScale x (i+2) ≤ (137/250 : ℝ)^2*bandScale x i := by
    have h := (bandScale_succ_le x (i+1)).trans
      (mul_le_mul_of_nonneg_right collision_rho_bounds.2.le (bandScale_nonnegative x (i+1)))
    have h' := mul_le_mul_of_nonneg_left hs1 (by norm_num : (0 : ℝ) ≤ 137/250)
    convert h.trans h' using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hlast := (bandScale_antitone x hiL).trans hs2
  have hnext : (11/10 : ℝ)*bandScale x (i+1) ≤ (7/10 : ℝ)*fordBandScale x i := by
    nlinarith
  have hcof : 2*bandScale x (L x H) ≤ (7/10 : ℝ)*fordBandScale x i := by
    nlinarith
  have hcount : ((L x H-i : ℕ) : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast Nat.sub_le_sub_right hL.le i
  calc
    _ ≤ (L x H-i : ℕ)*Real.exp ((11/10 : ℝ)*bandScale x (i+1))+
        Real.exp (2*bandScale x (L x H)) := basic_suffix_log_bound hη
    _ ≤ (m x-i : ℕ)*Real.exp ((7/10 : ℝ)*fordBandScale x i)+
        Real.exp ((7/10 : ℝ)*fordBandScale x i) :=
      add_le_add (mul_le_mul hcount (Real.exp_le_exp.mpr hnext)
        (Real.exp_pos _).le (Nat.cast_nonneg _)) (Real.exp_le_exp.mpr hcof)
    _ = _ := by ring

lemma collision_tail_ratio_decay : ∀ᶠ b : ℝ in atTop,
    (b+1)*Real.exp ((7/10 : ℝ)*b) ≤ (1/1000 : ℝ)*Real.exp ((22/25 : ℝ)*b) := by
  have ht : Tendsto (fun b : ℝ => (b+1)*Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => b*Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) := by
      simpa only [Real.rpow_one] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (9/50) (by norm_num)
    have h0 : Tendsto (fun b : ℝ => Real.exp (-(9/50 : ℝ)*b)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
    simpa only [add_mul,one_mul,add_zero] using h1.add h0
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/1000))] with b hb
  have hh := mul_le_mul_of_nonneg_right hb.le (Real.exp_pos ((22/25 : ℝ)*b)).le
  have he : ((b+1)*Real.exp (-(9/50 : ℝ)*b))*Real.exp ((22/25 : ℝ)*b) =
      (b+1)*Real.exp ((7/10 : ℝ)*b) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rwa [he] at hh

/-- After any retained positive index, the whole residual preimage, including
its possibly repeated final prime, has logarithm at most one per mille of the
logarithm of the first prime. -/
theorem collision_tail_log_small : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    Real.log (suffixPreimage η i : ℝ) ≤ (1/1000 : ℝ)*Real.log (remainderPrime η i : ℝ) := by
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp collision_tail_ratio_decay
  filter_upwards [ford_band_polynomial_lower 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop b₀),
    eventually_ge_atTop 1] with H hpoly hH hH1
  filter_upwards [hpoly,collision_coarse_sizes] with x hx hcoarse
  intro i hi hiR hiL hL η hη
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hx i him hHi
  have hHiR : (H : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hHi
  have hB : b₀ ≤ fordBandScale x i := hH.trans (hHiR.trans hb)
  obtain ⟨hlo,_,htail⟩ := hcoarse H i hi hiL hL η hη
  have hp : (1 : ℝ) < remainderPrime η i := by
    exact_mod_cast (hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)).1.one_lt
  have hexp : Real.exp ((22/25 : ℝ)*fordBandScale x i) ≤ Real.log (remainderPrime η i : ℝ) := by
    have he := Real.exp_le_exp.mpr hlo
    simpa only [B,Real.exp_log (Real.log_pos hp)] using he
  calc
    _ ≤ ((m x-i : ℕ)+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) := htail
    _ ≤ (fordBandScale x i+1)*Real.exp ((7/10 : ℝ)*fordBandScale x i) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (1/1000 : ℝ)*Real.exp ((22/25 : ℝ)*fordBandScale x i) := hb₀ _ hB
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by norm_num)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalPrimeBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-factor bands derived from normality, including the small-prime case. -/

noncomputable section

namespace TotientAsymptotic

lemma shifted_doubleLog_lower {p : ℕ} (hp : 3 ≤ p) :
    B p-1 ≤ B (p-1 : ℕ) := by
  have hn : 2 ≤ p-1 := by omega
  have hnR : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpn : (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 := by
    have he : p-1+1=p := by omega
    have hs : p ≤ (p-1)^2 := by nlinarith
    exact_mod_cast hs
  have hl := Real.log_le_log hpR hpn
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hh := Real.log_le_log (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (show 1 < p by omega))) hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.log_pos hnR).ne'] at hh
  change Real.log (Real.log (p : ℝ))-1 ≤ Real.log (Real.log ((p-1 : ℕ) : ℝ))
  linarith [Real.log_two_lt_d9]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionDyadicSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic endpoints for actual shifted-prime suffixes. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma dyadic_shift_log_bound {p n : ℕ} {y : ℝ} (hp : p.Prime) (hn : 0 < n)
    (htail : Real.log (n : ℝ) ≤ (1/100 : ℝ)*Real.log p)
    (hpbig : 100*Real.log 2 ≤ Real.log p)
    (hlo : y/2 < ((p-1)*n : ℕ)) (hhi : (((p-1)*n : ℕ) : ℝ) ≤ y) :
    (0 < y) ∧ Real.log y ≤ (51/50 : ℝ)*Real.log p ∧ y^(9/10 : ℝ) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hv0 : (0 : ℝ) < ((p-1)*n : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) hn
  have hy : 0 < y := hv0.trans_le hhi
  have hv : (((p-1)*n : ℕ) : ℝ) ≤ (p : ℝ)*n := by
    exact_mod_cast Nat.mul_le_mul_right n (Nat.sub_le p 1)
  have hlv := Real.log_le_log hv0 hv
  rw [Real.log_mul hp0.ne' hn0.ne'] at hlv
  have hly := Real.log_le_log hy (show y ≤ 2*(((p-1)*n : ℕ) : ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hv0.ne'] at hly
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog : Real.log y ≤ (51/50 : ℝ)*Real.log p := by linarith
  refine ⟨hy,hlog,?_⟩
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hy _) hp0).mp
  rw [Real.log_rpow hy]
  linarith

/-- The first prime in every actual positive-index suffix lies above
`y^0.9` at its dyadic counting endpoint. The endpoint has the same Ford
band scale, uniformly over every retained index. -/
theorem collision_suffix_dyadic_size : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    y/2 < ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) →
    (((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) : ℝ) ≤ y →
    y^(9/10 : ℝ) ≤ remainderPrime η i ∧
    (87/100 : ℝ)*fordBandScale x i ≤ B y ∧ B y ≤ (113/100 : ℝ)*fordBandScale x i := by
  filter_upwards [collision_tail_log_small,ford_band_polynomial_lower 1,
    eventually_ge_atTop 200] with H htail hpoly hH
  filter_upwards [htail,hpoly,collision_coarse_sizes] with x ht hp hc
  intro i hi hiR hiL hL η hη y hlo hhi
  have him : i < m x := by unfold R at hiR; omega
  have hHi : H ≤ m x-i := by unfold R at hiR; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hp i him hHi
  have hb200 : (200 : ℝ) ≤ fordBandScale x i := by
    have hh : 200 ≤ m x-i := hH.trans hHi
    have hhR : (200 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hh
    exact hhR.trans hb
  obtain ⟨hbl,hbu,_⟩ := hc H i hi hiL hL η hη
  have hprime := (hη.2.1 i (Finset.mem_Icc.mpr ⟨hi,by omega⟩)).1
  have hprime1 : (1 : ℝ) < remainderPrime η i := by exact_mod_cast hprime.one_lt
  have hexp : Real.exp ((22/25 : ℝ)*fordBandScale x i) ≤ Real.log (remainderPrime η i : ℝ) := by
    simpa only [B,Real.exp_log (Real.log_pos hprime1)] using Real.exp_le_exp.mpr hbl
  have hpbig : 100*Real.log 2 ≤ Real.log (remainderPrime η i : ℝ) := by
    have he := Real.add_one_le_exp ((22/25 : ℝ)*fordBandScale x i)
    nlinarith [Real.log_two_lt_d9]
  have htp := suffixPreimage_pos hη (i := i)
  have htn := Nat.totient_pos.mpr htp
  have hlogn : Real.log ((suffixPreimage η i).totient : ℝ) ≤
      (1/100 : ℝ)*Real.log (remainderPrime η i : ℝ) := by
    have hbound : Real.log ((suffixPreimage η i).totient : ℝ) ≤
        Real.log (suffixPreimage η i : ℝ) := Real.log_le_log (by exact_mod_cast htn)
          (by exact_mod_cast Nat.totient_le (suffixPreimage η i))
    have hh := ht i hi hiR hiL hL η hη
    have hl := Real.log_pos hprime1
    linarith
  obtain ⟨hy,hlog,hpow⟩ := dyadic_shift_log_bound hprime htn hlogn hpbig hlo hhi
  have hp3 : 3 ≤ remainderPrime η i := by
    by_contra! hn
    have he : remainderPrime η i=2 := by have := hprime.two_le; omega
    rw [he] at hpbig
    norm_num only [Nat.cast_ofNat] at hpbig
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hpminus : (1 : ℝ) < (remainderPrime η i-1 : ℕ) := by exact_mod_cast (show 2 ≤ remainderPrime η i-1 by omega)
  have hshift : ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y := by
    have hh : remainderPrime η i-1 ≤ (remainderPrime η i-1)*(suffixPreimage η i).totient := by
      exact Nat.le_mul_of_pos_right _ htn
    have hhR : ((remainderPrime η i-1 : ℕ) : ℝ) ≤
        ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) := by exact_mod_cast hh
    exact hhR.trans hhi
  have hBy : B (remainderPrime η i-1 : ℕ) ≤ B y :=
    Real.log_le_log (Real.log_pos hpminus) (Real.log_le_log (zero_lt_one.trans hpminus) hshift)
  have hlower := shifted_doubleLog_lower hp3
  have hupper := Real.log_le_log (Real.log_pos (hpminus.trans_le hshift)) hlog
  rw [Real.log_mul (by norm_num : (51/50 : ℝ) ≠ 0) (Real.log_pos hprime1).ne'] at hupper
  have hlogc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51/50)
  refine ⟨hpow,?_,?_⟩
  · linarith
  · change Real.log (Real.log y) ≤ _
    change Real.log (Real.log (remainderPrime η i : ℝ))-1 ≤ _ at hlower
    change _ ≤ Real.log (Real.log (remainderPrime η i : ℝ)) at hbl
    change Real.log (Real.log (remainderPrime η i : ℝ)) ≤ _ at hbu
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LargestPrimeCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform upper counting of the largest prime after a remainder is fixed.
Chebyshev's library theorem suffices for the upper bound; no PNT input is used here. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The largest-prime restriction makes the logarithm of every nonempty
counting interval comparable to `log x`, uniformly in its integer denominator. -/
theorem largest_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D → ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧ ((p-1)*D : ℕ) ≤ x) →
      (Q.card : ℝ) ≤ 10*x/((D : ℝ)*Real.log x) := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ)<1))
  have ht : Tendsto (fun x : ℝ => x^(9/10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ), ht.eventually (eventually_ge_atTop Y₀)] with x hx hxp
  intro D hD Q hQ
  have hD' : (0 : ℝ)<D := by exact_mod_cast hD
  have hx0 : 0<x := zero_lt_one.trans hx
  have hlogx : 0<Real.log x := Real.log_pos hx
  by_cases hne : Q.Nonempty
  · let Y := 1+x/D
    have hpY (p : ℕ) (hp : p ∈ Q) : (p : ℝ) ≤ Y := by
      have hh := hQ p hp
      have hpn := hh.1.one_lt.le
      have hval : ((p : ℝ)-1)*D ≤ x := by
        exact_mod_cast hh.2.2
      change _ ≤ 1+x/D
      have hh' := (le_div_iff₀ hD').mpr hval
      linarith
    obtain ⟨p, hp⟩ := hne
    have hlY : x^(9/10 : ℝ) ≤ Y := (hQ p hp).2.1.trans (hpY p hp)
    have hY0 : 0<Y := by dsimp [Y] <;> positivity
    have hYlarge : Y₀ ≤ Y := hxp.trans hlY
    have hlogY : (9/10 : ℝ)*Real.log x ≤ Real.log Y := by
      have hh := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) hlY
      rw [Real.log_rpow hx0] at hh
      linarith
    have hlogYpos : 0<Real.log Y := lt_of_lt_of_le (by positivity) hlogY
    have hDx : (D : ℝ) ≤ x := by
      have hh := (hQ p hp).2.2
      have hp2 := (hQ p hp).1.two_le
      have hp1 : 1 ≤ p-1 := by omega
      have hnat : D ≤ (p-1)*D := by simpa only [one_mul] using Nat.mul_le_mul_right D hp1
      exact (by exact_mod_cast hnat : (D : ℝ) ≤ ((p-1)*D : ℕ)).trans hh
    have hYupper : Y ≤ 2*x/D := by
      change 1+x/D ≤ _
      have hone : (1 : ℝ) ≤ x/D := (le_div_iff₀ hD').mpr (by simpa using hDx)
      have he : 2*x/D = 2*(x/D) := by ring
      rw [he]
      linarith
    have hsub : Q ⊆ Nat.primesLE ⌊Y⌋₊ := by
      intro q hq
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hpY q hq), (hQ q hq).1⟩
    have hcard : (Q.card : ℝ) ≤ Nat.primeCounting ⌊Y⌋₊ := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting _)
    have hc : Real.log 4+1 ≤ (3 : ℝ) := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
    calc
      _ ≤ (Real.log 4+1)*Y/Real.log Y := hcard.trans (hY₀ Y hYlarge)
      _ ≤ (3*(2*x/D))/((9/10 : ℝ)*Real.log x) := by
        apply div_le_div₀ (by positivity)
          ((mul_le_mul_of_nonneg_right hc hY0.le).trans (mul_le_mul_of_nonneg_left hYupper (by norm_num)))
          (by positivity) hlogY
      _ ≤ 10*x/((D : ℝ)*Real.log x) := by
        field_simp
        nlinarith
  · have hz : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingBlockSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact block values and bounds for both surviving shifted-prime lists. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma witnessBlockValue_positive {x : ℝ} {H i k p : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hi : 1 ≤ i)
    (hik : i ≤ k) (hk : k < L x H) :
    witnessBlockValue p η i k=(remainderPrime η i-1)*(suffixPreimage η i).totient := by
  have hp : (∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1)) =
      ∏ j ∈ Finset.Icc i k, (remainderPrime η j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0)]
  have he : Finset.Icc i k=insert i (Finset.Icc (i+1) k) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [witnessBlockValue,hp,he,Finset.prod_insert (by simp)]
  rw [basic_suffix_totient_split hη hL hik hk]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ChosenCollision
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical basic witnesses for distinct good tuples and their first differing prime. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma chosenRemainder_spec {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hζ : IsPrefixDatum x H ζ) :
    IsBasicRemainder x H (chosenRemainder x H ζ) ∧
      prefixOfRemainder x H (chosenRemainder x H ζ)=ζ := by
  unfold chosenRemainder
  rw [dite_eq_left hζ]
  exact Classical.choose_spec ((isPrefixDatum_iff x H ζ).mp hζ)

lemma chosenRemainder_tuple {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsBasicTuple x H t τ) : witnessTuple τ.head (chosenRemainder x H τ.tail)=τ := by
  have he := (chosenRemainder_spec hτ.2.2.1).2
  cases τ
  simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he

lemma wholeWitnessPrime_tuple {x : ℝ} {H : ℕ} {p : ℕ}
    {η : RemainderDatum (L x H)} (j : Fin (R x H+1)) :
    wholeWitnessPrime p η j.val=tuplePrimes (witnessTuple p η) j := by
  refine Fin.cases ?_ (fun r => ?_) j
  · simp [wholeWitnessPrime,tuplePrimes,witnessTuple]
  · simp [wholeWitnessPrime,tuplePrimes,witnessTuple,prefixOfRemainder]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleSuffix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tuple suffixes, with the common prefix removed exactly once. -/

noncomputable section

namespace TotientAsymptotic

lemma chosen_whole_prime {x t : ℝ} {H j : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsBasicTuple x H t τ) (hj : j ≤ R x H) :
    wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
      tuplePrimes τ ⟨j,by omega⟩ := by
  have he := wholeWitnessPrime_tuple (p := τ.head)
    (η := chosenRemainder x H τ.tail) ⟨j,by omega⟩
  rw [chosenRemainder_tuple hτ] at he
  exact he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixArithmetic
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact values of the suffix data used in the collision quotient. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tupleSuffix_denominator_product {n i : ℕ} (τ : TotientTuple n) (hi : i ≤ n) :
    prefixDenominator (tupleSuffix τ i) =
      τ.tail.d*∏ j ∈ Finset.Ici (⟨i,by omega⟩ : Fin (n+1)), (tuplePrimes τ j-1) := by
  unfold prefixDenominator tupleSuffix
  congr 1
  apply Finset.prod_bij (fun j _ => (⟨i+j.val,by have := j.isLt; omega⟩ : Fin (n+1)))
  · intro j _
    exact Finset.mem_Ici.mpr (by change i ≤ i+j.val; omega)
  · intro j _ k _ he
    apply Fin.ext
    have he' := congrArg Fin.val he
    dsimp only at he'
    omega
  · intro j hj
    have hj' : i ≤ j.val := by
      have hh := Finset.mem_Ici.mp hj
      exact hh
    refine ⟨⟨j.val-i,by have := j.isLt; omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intro j _
    rfl

lemma tupleSuffix_denominator_eq_of_collision {n i : ℕ} {τ σ : TotientTuple n}
    (hi : i ≤ n) (hp : ∀ j, 2 ≤ tuplePrimes τ j)
    (hv : tupleValue τ=tupleValue σ)
    (hcommon : ∀ j : Fin (n+1), j.val < i → tuplePrimes τ j=tuplePrimes σ j) :
    prefixDenominator (tupleSuffix τ i)=prefixDenominator (tupleSuffix σ i) := by
  rw [tupleSuffix_denominator_product τ hi,tupleSuffix_denominator_product σ hi]
  exact tuple_collision_suffix_identity hp hv ⟨i,by omega⟩ hcommon

lemma tupleSuffix_denominator_whole {x t : ℝ} {H i : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (hi : i ≤ R x H) :
    prefixDenominator (tupleSuffix τ i)=τ.tail.d*
      ∏ j ∈ Finset.Icc i (R x H),
        (wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j-1) := by
  unfold prefixDenominator tupleSuffix
  congr 1
  apply Finset.prod_bij (fun j _ => i+j.val)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩
  · intro j _ k _ he
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact ⟨⟨j-i,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
  · intro j _
    rw [chosen_whole_prime hτ (by have := j.isLt; omega)]

lemma tupleSuffix_denominator_positive {x t : ℝ} {H i : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ)
    (hL : L x H < m x) (hR : R x H < L x H) (hi : 1 ≤ i) (hiR : i ≤ R x H) :
    prefixDenominator (tupleSuffix τ i)=
      (remainderPrime (chosenRemainder x H τ.tail) i-1)*
        (suffixPreimage (chosenRemainder x H τ.tail) i).totient := by
  let η := chosenRemainder x H τ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hd : τ.tail.d=(suffixPreimage η (R x H)).totient := by
    have hd' := congrArg PrefixDatum.d (chosenRemainder_spec hτ.2.2.1).2
    change (remainderTail x H (chosenRemainder x H τ.tail)).totient=τ.tail.d at hd'
    rw [← suffixPreimage_at_R] at hd'
    exact hd'.symm
  rw [tupleSuffix_denominator_whole hτ hiR,hd]
  have hp : (∏ j ∈ Finset.Icc i (R x H),
      (wholeWitnessPrime τ.head η j-1)) =
      ∏ j ∈ Finset.Icc i (R x H), (remainderPrime η j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [wholeWitnessPrime,ite_eq_right (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0)]
  rw [hp]
  have hs : Finset.Icc i (R x H)=insert i (Finset.Icc (i+1) (R x H)) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [hs,Finset.prod_insert (by simp),basic_suffix_totient_split hη hL hiR hR]
  ring

lemma tupleSuffix_denominator_block {x t : ℝ} {H i k : ℕ}
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ)
    (hL : L x H < m x) (hR : R x H < L x H)
    (hi : 1 ≤ i) (hiR : i ≤ R x H) (hik : i ≤ k) (hk : k < L x H) :
    prefixDenominator (tupleSuffix τ i)=
      witnessBlockValue τ.head (chosenRemainder x H τ.tail) i k := by
  rw [tupleSuffix_denominator_positive hτ hL hR hi hiR,
    witnessBlockValue_positive (chosenRemainder_spec hτ.2.2.1).1 hL hi hik hk]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalFactorBands
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated largest-factor bands for the actual normal remainder primes. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma basic_remainder_prime_ge_three {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hj : j ∈ Finset.Icc 1 (L x H)) (hjm : j < m x) : 3 ≤ remainderPrime η j := by
  have hp := hη.2.1 j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hpos : 0 < B (remainderPrime η j) := by
    have hh := mul_pos (by norm_num : (0 : ℝ) < 9/10) (bandScale_pos hjm)
    have hlo : (9/10 : ℝ)*bandScale x j ≤ B (remainderPrime η j) := by
      simpa only [remainderCoord,B,ite_eq_right hj0] using hp.2.1
    exact hh.trans_le hlo
  by_contra! hn
  have he : remainderPrime η j=2 := by have := hp.1.two_le; omega
  rw [he] at hpos
  norm_num only [Nat.cast_ofNat] at hpos
  have hlog : Real.log (Real.log (2 : ℝ)) < 0 := Real.log_neg
    (Real.log_pos (by norm_num)) (lt_trans Real.log_two_lt_d9 (by norm_num))
  exact (not_lt_of_ge hpos.le) hlog

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionEndpointDomain
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every retained dyadic endpoint eventually lies in any fixed analytic domain. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem collision_endpoints_eventually {P : ℝ → Prop} (hP : ∀ᶠ y : ℝ in atTop, P y) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 < y → fordBandScale x i/2 ≤ B y → P y := by
  obtain ⟨y₀,hy₀⟩ := eventually_atTop.mp hP
  let z := max 2 y₀
  have hz : 1 < z := lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) (le_max_left _ _)
  obtain ⟨H₀,hH₀⟩ := exists_nat_ge (2*B z)
  filter_upwards [ford_band_polynomial_lower 1,eventually_ge_atTop H₀,eventually_ge_atTop 1]
    with H hpoly hH hH1
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hy hBy
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hlow : (H₀ : ℝ) ≤ fordBandScale x i := by
    have hh : (H₀ : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
    exact hh.trans (by simpa only [pow_one] using hx i him hHi)
  have hBz : B z ≤ B y := by linarith
  have he := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hBz)
  have heq (w : ℝ) (hw : 1<w) : Real.exp (Real.exp (B w))=w := by
    rw [B,Real.exp_log (Real.log_pos hw),Real.exp_log (zero_lt_one.trans hw)]
  rw [heq z hz,heq y hy] at he
  exact hy₀ y ((le_max_right _ _).trans he)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonClassSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite summation over the residual integer, canceled primes, and grid. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma finite_class_card_bound {α β : Type*} [DecidableEq β]
    (Q : Finset α) (T : Finset β) (key : α → β) (w : β → ℝ)
    (hkey : ∀ q ∈ Q, key q ∈ T)
    (hfiber : ∀ b ∈ T, ((Q.filter (fun q => key q=b)).card : ℝ) ≤ w b) :
    (Q.card : ℝ) ≤ ∑ b ∈ T, w b := by
  classical
  have he := Finset.card_eq_sum_card_fiberwise hkey
  rw [he, Nat.cast_sum]
  exact Finset.sum_le_sum hfiber

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixRepresentatives
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selecting one actual witness pair for each distinct suffix pair. -/

noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma finite_image_representatives {α β : Type*} [DecidableEq β] (Q : Finset α) (f : α → β) :
    ∃ S : Finset α, S ⊆ Q ∧ Set.InjOn f (↑S : Set α) ∧ S.image f=Q.image f := by
  classical
  let pick : {b // b ∈ Q.image f} → α := fun b => Classical.choose (Finset.mem_image.mp b.2)
  have hp (b : {b // b ∈ Q.image f}) : pick b ∈ Q ∧ f (pick b)=b.val :=
    Classical.choose_spec (Finset.mem_image.mp b.2)
  let S := (Q.image f).attach.image pick
  refine ⟨S,?_,?_,?_⟩
  · intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    exact (hp b).1
  · intro a ha a' ha' he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp ha'
    have hb : b=b' := Subtype.ext ((hp b).2.symm.trans (he.trans (hp b').2))
    rw [hb]
  · ext b
    constructor
    · intro hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
      rw [(hp b).2]
      exact b.2
    · intro hb
      let b' : {b // b ∈ Q.image f} := ⟨b,hb⟩
      exact Finset.mem_image.mpr ⟨pick b',Finset.mem_image.mpr ⟨b',Finset.mem_attach _ _,rfl⟩,(hp b').2⟩

/-- The full exponential saving counts distinct suffix pairs independently
of how many common prefixes or full witnesses represent each suffix. -/
theorem actual_suffix_block_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    ((Q.image (fun q => pairSuffix q i)).card : ℝ) ≤
      y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_block_count hford hmertens
  refine ⟨y₀,hy₀,?_⟩
  filter_upwards [hcount] with H hH
  filter_upwards [hH] with x hx
  intro i hi hL hR t y hy hBy hlo hup Q hQ
  obtain ⟨S,hSQ,hinj,himage⟩ := finite_image_representatives Q (fun q => pairSuffix q i)
  have he := hx i hi hL hR t y hy hBy hlo hup S (fun q hq => hQ q (hSQ hq)) hinj
  rw [← himage,Finset.card_image_of_injOn hinj]
  exact he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FirstCollision
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual first-difference partition and its suffix quotient. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma firstCollisionPairs_data {x t : ℝ} {H i : ℕ} (hPH : P H ≤ H)
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : q ∈ firstCollisionPairs x H t i) :
    IsGoodTuple x H t q.1 ∧ IsGoodTuple x H t q.2 ∧
    tupleValue q.1=tupleValue q.2 ∧ FirstDifferenceAt i q := by
  obtain ⟨hq,hfirst⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpair,_,hv⟩ := Finset.mem_filter.mp hq
  obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpair
  exact ⟨(mem_goodTupleFinset hPH).mp hl,(mem_goodTupleFinset hPH).mp hr,hv,hfirst⟩

lemma firstCollisionSuffixes_equal_value {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : i ≤ R x H)
    {s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)}
    (hs : s ∈ firstCollisionSuffixes x H t i) :
    prefixDenominator s.1=prefixDenominator s.2 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hl,hr,hv,_,hcommon⟩ := firstCollisionPairs_data hPH hq
  apply tupleSuffix_denominator_eq_of_collision hi
    (fun j => (basic_tuple_primes hPH hl.1 j).two_le) hv
  intro j hj
  rw [← chosen_whole_prime hl.1 (by have := j.isLt; omega),
    ← chosen_whole_prime hr.1 (by have := j.isLt; omega)]
  exact hcommon j.val hj

/-- Every actual positive first-difference pair lies in Ford's counting
block at its suffix's dyadic endpoint. This holds for both chosen witnesses. -/
theorem first_collision_dyadic_blocks : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H →
    ∀ t y : ℝ, ∀ q ∈ firstCollisionPairs x H t i,
    y/2 < (prefixDenominator (tupleSuffix q.1 i) : ℝ) →
    (prefixDenominator (tupleSuffix q.1 i) : ℝ) ≤ y →
    GoodCollisionBlock x t H i y q ∧
    (87/100 : ℝ)*fordBandScale x i ≤ B y ∧ B y ≤ (113/100 : ℝ)*fordBandScale x i := by
  filter_upwards [collision_suffix_dyadic_size,eventually_collision_indices,
    eventually_tail_cut_separated] with H hsize hind hsep
  filter_upwards [hsize,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi hiR hL hR t y q hq hlo hhi
  obtain ⟨hl,hr,hv,hfirst,hcommon⟩ := firstCollisionPairs_data (by omega) hq
  have hiL : i+2 ≤ L x H := by unfold R L at *; omega
  have hk : collisionLastIndex x i < L x H := (hind x hm i hiR).2.2
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have hsame : prefixDenominator (tupleSuffix q.1 i)=prefixDenominator (tupleSuffix q.2 i) :=
    firstCollisionSuffixes_equal_value (by omega) hiR (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hdleft := tupleSuffix_denominator_positive hl.1 hL hR hi hiR
  have hdright := tupleSuffix_denominator_positive hr.1 hL hR hi hiR
  have hls := hx i hi hiR hiL hL _ (chosenRemainder_spec hl.1.2.2.1).1 y
    (by rwa [← hdleft]) (by rwa [← hdleft])
  have hrs := hx i hi hiR hiL hL _ (chosenRemainder_spec hr.1.2.2.1).1 y
    (by rwa [← hdright,← hsame]) (by rwa [← hdright,← hsame])
  refine ⟨⟨hl,hr,hv,hfirst,hcommon,?_,?_,?_,?_⟩,hls.2.1,hls.2.2⟩
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hls.1
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hrs.1
  · rwa [← tupleSuffix_denominator_block hl.1 hL hR hi hiR hik hk]
  · intro hzero
    omega

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualSuffixMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual reciprocal mass of distinct colliding suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma firstCollisionSuffixes_denominator_gt_one {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hL : L x H < m x) (hR : R x H < L x H)
    (hi : 1 ≤ i) (hiR : i ≤ R x H)
    {s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)}
    (hs : s ∈ firstCollisionSuffixes x H t i) : 1 < prefixDenominator s.1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
  have hl := (firstCollisionPairs_data hPH hq).1
  rw [show (pairSuffix q i).1=tupleSuffix q.1 i from rfl,
    tupleSuffix_denominator_positive hl.1 hL hR hi hiR]
  have hη := (chosenRemainder_spec hl.1.2.2.1).1
  have hp := basic_remainder_prime_ge_three hη (Finset.mem_Icc.mpr ⟨hi,hiR.trans hR.le⟩)
    (hiR.trans_lt (hR.trans hL))
  have hd := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := i))
  have he : 2 ≤ (remainderPrime (chosenRemainder x H q.1.tail) i-1)*
      (suffixPreimage (chosenRemainder x H q.1.tail) i).totient := by
    calc
      2 = 2*1 := by omega
      _ ≤ _ := Nat.mul_le_mul (by omega) hd
  omega

/-- All distinct suffix pairs, with no fixed prefix, have exponentially
small reciprocal mass. Constants and the cutoff are uniform in the phase. -/
theorem actual_suffix_mass (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H → ∀ t : ℝ,
    (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹) ≤
      (16/Real.log 2)*((m x-i : ℕ) : ℝ)^4*
        Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_suffix_block_count hford hmertens
  have hevent : ∀ᶠ y : ℝ in atTop, y₀ ≤ y := eventually_ge_atTop y₀
  filter_upwards [hcount,first_collision_dyadic_blocks,
    collision_endpoints_eventually hevent,ford_band_polynomial_lower 1,
    eventually_ge_atTop 100,eventually_tail_cut_separated]
    with H hc hblocks hlarge hpoly hH hsep
  filter_upwards [hc,hblocks,hlarge,hpoly,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hx hb hy hxpoly hm
  intro i hi hiR hL hR t
  let S := firstCollisionSuffixes x H t i
  let h : ℝ := (m x-i : ℕ)
  let σ : ℝ := 1/(8*h^4)
  have hhNat : H ≤ m x-i := by unfold R at hiR; omega
  have hh : (100 : ℝ) ≤ h := by
    dsimp [h]
    exact_mod_cast hH.trans hhNat
  have hσ : 0 < σ := by dsimp [σ] <;> positivity
  have hbi : (100 : ℝ) ≤ fordBandScale x i := by
    have hp := hxpoly i (hiR.trans_lt (hR.trans hL)) hhNat
    have hh' : (100 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hhNat
    exact hh'.trans (by simpa only [pow_one] using hp)
  have hPH : P H ≤ H := by omega
  have hsdata (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      1 ≤ suffixDyadicIndex s ∧
      (2 : ℝ)^(suffixDyadicIndex s)/2 < (prefixDenominator s.1 : ℝ) ∧
      (prefixDenominator s.1 : ℝ) ≤ (2 : ℝ)^(suffixDyadicIndex s) :=
    dyadic_nat_bounds (firstCollisionSuffixes_denominator_gt_one hPH hL hR hi hiR hs)
  have hsband (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      (87/100 : ℝ)*fordBandScale x i ≤ B ((2 : ℝ)^(suffixDyadicIndex s)) := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hs
    have hd := hsdata _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    exact (hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2).2.1
  have hstart (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (hs : s ∈ S) :
      2 ≤ suffixDyadicIndex s ∧ Real.exp (fordBandScale x i/2) ≤
        ((suffixDyadicIndex s-1 : ℕ) : ℝ)*Real.log 2 :=
    dyadic_band_start hbi (hsdata s hs).1 (hsband s hs)
  have hcounts (n : ℕ) : ((S.filter (fun s => suffixDyadicIndex s=n)).card : ℝ) ≤
      1*(2 : ℝ)^n*dyadicSuffixWeight σ n := by
    let Q := (firstCollisionPairs x H t i).filter (fun q => suffixDyadicIndex (pairSuffix q i)=n)
    have himage : S.filter (fun s => suffixDyadicIndex s=n)=Q.image (fun q => pairSuffix q i) := by
      exact Finset.filter_image
    by_cases hne : Q.Nonempty
    · obtain ⟨q,hq⟩ := hne
      obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
      have hs : pairSuffix q i ∈ S := Finset.mem_image.mpr ⟨q,hq,rfl⟩
      have hd := hsdata _ hs
      have hblock := hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2
      have hn1 : 1 ≤ n := by rw [← hn]; exact hd.1
      have hyn : 1 < (2 : ℝ)^n := one_lt_pow₀ (by norm_num) (by omega)
      have hlower : (87/100 : ℝ)*fordBandScale x i ≤ B ((2 : ℝ)^n) := by
        simpa only [hn] using hblock.2.1
      have hupper : B ((2 : ℝ)^n) ≤ 2*fordBandScale x i := by
        have hu : B ((2 : ℝ)^n) ≤ (113/100 : ℝ)*fordBandScale x i := by
          simpa only [hn] using hblock.2.2
        linarith
      have hBy : 0 < B ((2 : ℝ)^n) := by linarith
      have hy₀n : y₀ ≤ (2 : ℝ)^n := hy i hiR _ hyn (by linarith)
      have hQ : ∀ q ∈ Q, GoodCollisionBlock x t H i ((2 : ℝ)^n) q := by
        intro q hq
        obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
        have hd := hsdata _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
        have hh := hb i hi hiR hL hR t _ q hq hd.2.1 hd.2.2
        simpa only [hn] using hh.1
      have he := hx i hiR hL hR t ((2 : ℝ)^n) hy₀n hBy hlower hupper Q hQ
      rw [himage]
      apply he.trans_eq
      dsimp only [dyadicSuffixWeight,σ,h]
      rw [dyadic_endpoint_log,dyadic_endpoint_B]
      have heq : -Real.log ((n : ℝ)*Real.log 2)/(8*((m x-i : ℕ) : ℝ)^4)=
          -(1/(8*((m x-i : ℕ) : ℝ)^4))*Real.log ((n : ℝ)*Real.log 2) := by ring
      rw [heq]
      ring
    · rw [himage,Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
      unfold dyadicSuffixWeight
      positivity
  have he := finite_dyadic_collision_mass S suffixDyadicIndex
    (fun s => (prefixDenominator s.1 : ℝ)) (C := 1) (B := fordBandScale x i/2)
    (by norm_num) hσ hstart (fun s hs => (hsdata s hs).2.1) hcounts
  apply he.trans_eq
  have heq : -σ*(fordBandScale x i/2) = -fordBandScale x i/(16*h^4) := by
    dsimp [σ]
    ring
  rw [heq]
  dsimp [σ,h]
  field_simp
  ring

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
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma tupleInnerPrefix_eq {x t : ℝ} {H n : ℕ} (hPH : P H ≤ H) (hn : n ≤ R x H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (j : Fin n) :
    tupleInnerPrefix τ n j=(chosenRemainder x H τ.tail).primes
      ⟨j.val,by have := j.isLt; unfold R L at *; omega⟩ := by
  have hj : j.val < R x H := lt_of_lt_of_le j.isLt hn
  simp only [tupleInnerPrefix,dite_eq_left hj]
  have hp := congrArg PrefixDatum.primes (chosenRemainder_spec hτ.2.2.1).2
  have he := congrFun hp ⟨j.val,hj⟩
  change remainderPrime (chosenRemainder x H τ.tail) (j.val+1)=τ.tail.primes ⟨j.val,hj⟩ at he
  rw [← he]
  have hjL : 1 ≤ j.val+1 ∧ j.val+1 ≤ L x H := by
    have := j.isLt
    unfold R L at *
    omega
  simp [remainderPrime,hjL]

/-- Every inner prefix of an actual tuple retains all the projected bands
and simplex inequalities; the removed suffix terms were nonnegative. -/
lemma tupleInnerPrefix_geometry {x t : ℝ} {H K : ℕ} (hPH : P H ≤ H)
    (hn : R x K ≤ R x H) (hL : 0 < L x H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) :
    (∀ j, (tupleInnerPrefix τ (R x K) j).Prime) ∧
    primePrefixCoord (tupleInnerPrefix τ (R x K)) ∈ prefixBandRegion x K ∧
    primePrefixCoord (tupleInnerPrefix τ (R x K)) ∈
      enlargedSimplex (R x K) (B x) (xi x 0) (fun j => xi x (j.val+1)) := by
  let η := chosenRemainder x H τ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hnL : R x K ≤ L x H := by unfold R L at *; omega
  have hcoord : primePrefixCoord (tupleInnerPrefix τ (R x K)) =
      fun j => primePrefixCoord η.primes (Fin.castLE hnL j) := by
    funext j
    unfold primePrefixCoord
    rw [tupleInnerPrefix_eq hPH hn hτ]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro j
    simp only [tupleInnerPrefix,dite_eq_left (lt_of_lt_of_le j.isLt hn)]
    exact (basic_prefix_data_positive hPH hτ.2.2.1).2 _
  · intro j
    rw [hcoord]
    have hh := (hη.2.1 (j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩)).2
    change (9/10 : ℝ)*bandScale x (j.val+1) ≤
      remainderCoord x η ((Fin.castLE hnL j).val+1) ∧
      remainderCoord x η ((Fin.castLE hnL j).val+1) ≤ (11/10 : ℝ)*bandScale x (j.val+1) at hh
    rw [remainderCoord_fin] at hh
    exact hh
  · rw [hcoord]
    exact enlargedSimplex_project hnL (basic_remainder_enlargedSimplex hL hη)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixRecovery
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The head, common inner prefix and suffix determine a tuple exactly. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tuple_recovered_from_parts {n i : ℕ} {τ σ : TotientTuple n}
    (hi : 1 ≤ i) (hin : i ≤ n+1) (hh : τ.head=σ.head)
    (hp : tupleInnerPrefix τ (i-1)=tupleInnerPrefix σ (i-1))
    (hs : tupleSuffix τ i=tupleSuffix σ i) : τ=σ := by
  have hd : τ.tail.d=σ.tail.d := congrArg (fun z : PrefixDatum (n+1-i) => z.d) hs
  have he : τ.tail.primes=σ.tail.primes := by
    funext j
    by_cases hj : j.val < i-1
    · have h := congrFun hp ⟨j.val,hj⟩
      simpa only [tupleInnerPrefix,dite_eq_left j.isLt] using h
    · let k : Fin (n+1-i) := ⟨j.val+1-i,by have := j.isLt; omega⟩
      have h := congrFun (congrArg PrefixDatum.primes hs) k
      change tuplePrimes τ ⟨i+k.val,by have := k.isLt; omega⟩=
        tuplePrimes σ ⟨i+k.val,by have := k.isLt; omega⟩ at h
      have hk : i+k.val=j.val+1 := by dsimp [k]; omega
      simp only [hk] at h
      exact h
  cases τ with
  | mk th tt =>
    cases σ with
    | mk sh st =>
      cases tt
      cases st
      simp_all

lemma tupleValue_split_inner_suffix {n i : ℕ} (τ : TotientTuple n)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    tupleValue τ=(τ.head-1)*(∏ j, (tupleInnerPrefix τ (i-1) j-1))*
      prefixDenominator (tupleSuffix τ i) := by
  classical
  let c : Fin (n+1) := ⟨i,by omega⟩
  let z : Fin (n+1) := 0
  have hpart : Finset.Iio c ∪ Finset.Ici c=Finset.univ := by
    ext j
    simp only [Finset.mem_union,Finset.mem_Iio,Finset.mem_Ici,Finset.mem_univ]
    exact iff_true_intro (lt_or_ge j c)
  have hdis : Disjoint (Finset.Iio c) (Finset.Ici c) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact (not_lt_of_ge (Finset.mem_Ici.mp hk)) (Finset.mem_Iio.mp hj)
  have hpref : Finset.Iio c=insert z (Finset.Icc (⟨1,by omega⟩ : Fin (n+1)) ⟨i-1,by omega⟩) := by
    ext j
    simp only [Finset.mem_Iio,Finset.mem_insert,Finset.mem_Icc,Fin.lt_def,Fin.le_def]
    change (j.val < i) ↔ j=z ∨ 1 ≤ j.val ∧ j.val ≤ i-1
    constructor
    · intro hj
      by_cases hz : j.val=0
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr ⟨by omega,by omega⟩
    · rintro (rfl | hj)
      · change 0 < i
        omega
      · omega
  have hprod : (∏ j ∈ Finset.Icc (⟨1,by omega⟩ : Fin (n+1)) ⟨i-1,by omega⟩, (tuplePrimes τ j-1)) =
      ∏ j, (tupleInnerPrefix τ (i-1) j-1) := by
    symm
    apply Finset.prod_bij (fun j _ => (⟨j.val+1,by have := j.isLt; omega⟩ : Fin (n+1)))
    · intro j _
      apply Finset.mem_Icc.mpr
      constructor
      · change 1 ≤ j.val+1
        omega
      · change j.val+1 ≤ i-1
        have := j.isLt
        omega
    · intro j _ k _ he
      apply Fin.ext
      have he' := congrArg (fun z : Fin (n+1) => z.val) he
      dsimp only at he'
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hjlo : 1 ≤ j.val := by
        have hh := hj'.1
        change ((⟨1,by omega⟩ : Fin (n+1)).val) ≤ j.val at hh
        exact hh
      have hjhi : j.val ≤ i-1 := hj'.2
      refine ⟨⟨j.val-1,by omega⟩,Finset.mem_univ _,?_⟩
      apply Fin.ext
      dsimp only
      omega
    · intro j _
      have hj : j.val < n := by have := j.isLt; omega
      simp only [tupleInnerPrefix,dite_eq_left hj]
      rfl
  rw [tupleValue,← hpart,Finset.prod_union hdis,hpref,
    Finset.prod_insert (by simp [z]),hprod,tupleSuffix_denominator_product τ hin]
  dsimp only [z,c]
  simp only [tuplePrimes,Fin.cons_zero]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionPrefixFibers
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring the common prefix does not multiply suffixes by witness choices. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma firstCollision_common_parts {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : 1 ≤ i) (hiR : i ≤ R x H)
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : q ∈ firstCollisionPairs x H t i) :
    q.1.head=q.2.head ∧ tupleInnerPrefix q.1 (i-1)=tupleInnerPrefix q.2 (i-1) := by
  obtain ⟨hl,hr,_,_,hcommon⟩ := firstCollisionPairs_data hPH hq
  refine ⟨?_,?_⟩
  · simpa only [wholeWitnessPrime,ite_true, if_true] using hcommon 0 hi
  · funext j
    have hj : j.val < R x H := by have := j.isLt; omega
    have he := hcommon (j.val+1) (by have := j.isLt; omega)
    rw [chosen_whole_prime hl.1 (by omega),chosen_whole_prime hr.1 (by omega)] at he
    change tuplePrimes q.1 (Fin.succ ⟨j.val,hj⟩)=tuplePrimes q.2 (Fin.succ ⟨j.val,hj⟩) at he
    simpa only [tupleInnerPrefix,dite_eq_left hj,tuplePrimes,Fin.cons_succ] using he

lemma collision_prefix_head_injective {x t : ℝ} {H i : ℕ}
    (hPH : P H ≤ H) (hi : 1 ≤ i) (hiR : i ≤ R x H)
    (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (p : Fin (i-1) → ℕ) :
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => q.1.head)
      (↑((firstCollisionPairs x H t i).filter
        (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)) : Set _) := by
  intro q hq q' hq' he
  obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq',hs',hp'⟩ := Finset.mem_filter.mp hq'
  have hc := firstCollision_common_parts hPH hi hiR hq
  have hc' := firstCollision_common_parts hPH hi hiR hq'
  have hl : q.1=q'.1 := tuple_recovered_from_parts hi (by omega) he (hp.trans hp'.symm)
    (congrArg Prod.fst (hs.trans hs'.symm))
  have hr : q.2=q'.2 := tuple_recovered_from_parts hi (by omega)
    (hc.1.symm.trans (he.trans hc'.1))
    (hc.2.symm.trans ((hp.trans hp'.symm).trans hc'.2))
    (congrArg Prod.snd (hs.trans hs'.symm))
  exact Prod.ext hl hr

/-- For each fixed suffix and common inner prefix, Chebyshev bounds the
number of admissible heads by the reciprocal of their exact denominator. -/
theorem collision_prefix_fiber_bound : ∀ᶠ x : ℝ in atTop,
    ∀ H i : ℕ, P H ≤ H → 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ∀ (s : PrefixDatum (R x H+1-i) × PrefixDatum (R x H+1-i)) (p : Fin (i-1) → ℕ),
    (((firstCollisionPairs x H t i).filter
        (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)).card : ℝ) ≤
      (10*x/Real.log x)*(prefixDenominator s.1 : ℝ)⁻¹*reciprocalShiftWeight p := by
  filter_upwards [largest_prime_count_upper,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H i hPH hi hiR t ht s p
  let Q := (firstCollisionPairs x H t i).filter
    (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p)
  by_cases hne : Q.Nonempty
  · obtain ⟨q,hq⟩ := hne
    obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
    have hl := (firstCollisionPairs_data hPH hq).1
    let D := (∏ j, (p j-1))*prefixDenominator s.1
    have hD : 0 < D := by
      have he := tupleValue_split_inner_suffix q.1 hi hiR
      rw [show tupleSuffix q.1 i=s.1 from congrArg Prod.fst hs,hp] at he
      have hv := basic_tuple_value_pos hPH hl.1
      change 0 < (∏ j, (p j-1))*prefixDenominator s.1
      rw [he,mul_assoc] at hv
      by_contra hnot
      have hz : (∏ j, (p j-1))*prefixDenominator s.1=0 := by omega
      rw [hz,mul_zero] at hv
      omega
    have hQ : ∀ a : ℕ, a ∈ Q.image (fun q => q.1.head) →
        a.Prime ∧ x^(9/10 : ℝ) ≤ a ∧ ((a-1)*D : ℕ) ≤ x := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hq,hs,hp⟩ := Finset.mem_filter.mp hq
      have hl := (firstCollisionPairs_data hPH hq).1
      refine ⟨hl.1.1,hl.1.2.1,?_⟩
      have he := tupleValue_split_inner_suffix q.1 hi hiR
      rw [show tupleSuffix q.1 i=s.1 from congrArg Prod.fst hs,hp] at he
      have hv := hl.1.2.2.2.trans ht
      rw [he] at hv
      simpa only [D,mul_assoc] using hv
    have hb := hx D hD _ hQ
    rw [Finset.card_image_of_injOn (collision_prefix_head_injective hPH hi hiR s p)] at hb
    apply hb.trans_eq
    dsimp [D,reciprocalShiftWeight]
    simp only [Nat.cast_mul,Nat.cast_prod]
    ring
  · have hQ : Q=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (Q.card : ℝ) ≤ _
    rw [hQ,Finset.card_empty,Nat.cast_zero]
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hl : 0 < Real.log x := Real.log_pos hx1
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (reciprocalShiftWeight_nonneg p)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestoreCommonPrefix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring all common prefixes after counting distinct suffix pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma first_collision_prefix_sum : ∀ᶠ x : ℝ in atTop,
    ∀ H i : ℕ, P H ≤ H → 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ((firstCollisionPairs x H t i).card : ℝ) ≤
      (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*
        (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) := by
  filter_upwards [collision_prefix_fiber_bound] with x hx
  intro H i hPH hi hiR t ht
  let Q := firstCollisionPairs x H t i
  let S := firstCollisionSuffixes x H t i
  let P := collisionInnerPrefixes x H t i
  have hb := finite_class_card_bound Q (S ×ˢ P)
    (fun q => (pairSuffix q i,tupleInnerPrefix q.1 (i-1)))
    (fun k => (10*x/Real.log x)*(prefixDenominator k.1.1 : ℝ)⁻¹*reciprocalShiftWeight k.2)
    (by
      intro q hq
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,
        Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩) (by
      rintro ⟨s,p⟩ _
      have he : Q.filter (fun q => (pairSuffix q i,tupleInnerPrefix q.1 (i-1))=(s,p)) =
          Q.filter (fun q => pairSuffix q i=s ∧ tupleInnerPrefix q.1 (i-1)=p) := by
        ext q
        simp only [Finset.mem_filter,Prod.mk.injEq]
      rw [he]
      exact hx H i hPH hi hiR t ht s p)
  apply hb.trans_eq
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [← Finset.mul_sum]

/-- The common-prefix mass is bounded uniformly in the suffix and index. -/
theorem collision_inner_prefix_mass (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t : ℝ,
    (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) ≤ G x (m x) := by
  filter_upwards [projected_mass_le_G hbox hren,eventually_tail_cut_separated]
    with H hmass hsep
  filter_upwards [hmass,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi hiR t
  let K := m x-(i-1)
  have hiM : i ≤ m x := hiR.trans (Nat.sub_le _ _)
  have hd : R x K=i-1 := by dsimp [K,R]; omega
  have hK : H ≤ K := by dsimp [K]; unfold R at hiR; omega
  have hKm : K ≤ m x := Nat.sub_le _ _
  have hlen : R x K ≤ R x H := by rw [hd]; omega
  let Q := (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (R x K))
  have he := hx K hK hKm Q (by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hq' := (firstCollisionPairs_data (by omega) hq).1
    exact tupleInnerPrefix_geometry (by omega) hlen (by unfold L; omega) hq'.1)
  have hsum := congrArg (fun n : ℕ => ∑ p ∈
    (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 n), reciprocalShiftWeight p) hd
  change (∑ p ∈ (firstCollisionPairs x H t i).image (fun q => tupleInnerPrefix q.1 (R x K)),
    reciprocalShiftWeight p) ≤ G x (m x) at he
  rw [hsum] at he
  exact he

/-- Count all original pairs at a positive first-difference index: both
suffix choices and all their common prefixes are now included. -/
theorem actual_positive_collision_count_oai (hford : FordLemma51Input) (hmertens : MertensProductInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → ∀ t ≤ x,
    ((firstCollisionPairs x H t i).card : ℝ) ≤
      (160/Real.log 2)*(x/Real.log x)*G x (m x)*((m x-i : ℕ) : ℝ)^4*
        Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) := by
  filter_upwards [actual_suffix_mass hford hmertens,collision_inner_prefix_mass hbox hren,
    eventually_tail_cut_separated] with H hs hp hsep
  filter_upwards [hs,hp,first_collision_prefix_sum,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hpx hcount hm hx1 hB
  intro i hi hiR t ht
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  have hS := hx i hi hiR hL hR t
  have hP := hpx i hi hiR t
  have hSP : 0 ≤ ∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hA : 0 ≤ 10*x/Real.log x := by positivity
  calc
    _ ≤ (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*
        (∑ p ∈ collisionInnerPrefixes x H t i, reciprocalShiftWeight p) :=
      hcount H i (by omega) hi hiR t ht
    _ ≤ (10*x/Real.log x)*
        (∑ s ∈ firstCollisionSuffixes x H t i, (prefixDenominator s.1 : ℝ)⁻¹)*G x (m x) :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hA hSP)
    _ ≤ (10*x/Real.log x)*
        ((16/Real.log 2)*((m x-i : ℕ) : ℝ)^4*
          Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)))*G x (m x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hA) (G_pos hB _).le
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.actual_positive_collision_count_oai := @OAI.TotientAsymptotic.actual_positive_collision_count_oai
