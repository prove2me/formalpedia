-- Prove2me | solution 1 for OAI.TotientAsymptotic.locally_concentrated_volume_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:36:04.0428+00:00
-- url     : https://prove2.me/submissions/6c4db9ef-2604-447e-b9fa-d56ed017265f

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Analysis.PSeries
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalDifference
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive renewal differences used to construct ordered prime coordinates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_difference_lower {n : ℕ} (hn : 1 ≤ n) :
    a 1*g n ≤ g (n+1)-g n := by
  have hsum : (∑ i ∈ Finset.range n,g i*a (n-i)) ≤
      ∑ i ∈ Finset.range n,g i*a (n+1-i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have he : n+1-i=(n-i)+1 := by omega
    rw [he]
    exact mul_le_mul_of_nonneg_left (a_le_a_succ (by omega)) (g_pos i).le
  rw [← g_convolution (by omega : 0 < n)] at hsum
  have he := g_convolution (by omega : 0 < n+1)
  rw [Finset.sum_range_succ,show n+1-n=1 by omega] at he
  nlinarith only [hsum,he]

theorem renewal_difference_uniform_lower : ∃ c : ℝ,0 < c ∧
    ∀ n : ℕ,1 ≤ n → c*(rho^n)⁻¹ ≤ g (n+1)-g n := by
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  refine ⟨a 1*c,mul_pos (a_pos (j:=1) le_rfl) hc,?_⟩
  intro n hn
  calc
    _ = a 1*(c*(rho^n)⁻¹) := by ring
    _ ≤ a 1*g n := mul_le_mul_of_nonneg_left (hg n) (a_pos (j:=1) le_rfl).le
    _ ≤ _ := renewal_difference_lower hn

lemma renewal_uniform_upper : ∃ C : ℝ,0 < C ∧
    ∀ n : ℕ,g n ≤ C*(rho^n)⁻¹ := by
  obtain ⟨K,hK,hbound⟩ := (normalizedRenewal_properties fordRenewalInput).2
  refine ⟨K+1,by linarith,?_⟩
  intro n
  have hh := (le_abs_self (normalizedRenewal n)).trans
    ((by simpa only [Real.norm_eq_abs] using hbound n : |normalizedRenewal n| ≤ K))
  have hb := mul_le_mul_of_nonneg_right hh (inv_pos.mpr (pow_pos rho_pos n)).le
  have he : g n ≤ K*(rho^n)⁻¹ := by
    simpa only [normalizedRenewal,mul_assoc,mul_inv_cancel₀ (pow_pos rho_pos n).ne',mul_one]
      using hb
  exact he.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_pos.mpr (pow_pos rho_pos n)).le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RenewalBackground
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive ordered translate of the prefix simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_reverse_sum {N i : ℕ} (hi : i < N) :
    (∑ j ∈ Finset.range N,if i < j then a (j-i)*g (N-j) else 0)=
      g (N-i)-a (N-i) := by
  have hrec := g_convolution (by omega : 0 < N-i)
  have hs : (∑ k ∈ Finset.range (N-i),g k*a (N-i-k))=
      a (N-i)+(∑ j ∈ Finset.range N,if i < j then a (j-i)*g (N-j) else 0) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega : 0 < N-i))]
    simp only [g,Nat.sub_zero,one_mul]
    rw [add_comm]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun k _ => N-k)
    · intro k hk
      obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
      have hkN := Finset.mem_range.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
    · intro k hk l hl he
      have hkN := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
      have hlN := Finset.mem_range.mp (Finset.mem_erase.mp hl).2
      omega
    · intro j hj
      obtain ⟨hj,hiJ⟩ := Finset.mem_filter.mp hj
      have hjN := Finset.mem_range.mp hj
      exact ⟨N-j,Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩,
        by omega⟩
    · intro k hk
      have hkN := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
      have he : N-i-k=N-k-i := by omega
      have he' : N-(N-k)=k := by omega
      rw [he,he',mul_comm]
  linarith only [hs,hrec]

lemma renewalBackground_slack (N : ℕ) (t : ℝ) (i : Fin N) :
    prefixLinear N (renewalBackground N t) i=t*a (N-i.val) := by
  rw [prefixLinear_apply]
  have hs : (∑ j : Fin N,if i < j then a (j.val-i.val)*renewalBackground N t j else 0)=
      t*(g (N-i.val)-a (N-i.val)) := by
    rw [←renewal_reverse_sum i.isLt,Finset.mul_sum]
    simp only [renewalBackground,Fin.lt_def]
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      if i.val < j then a (j-i.val)*(t*g (N-j)) else 0)]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [hs]
  unfold renewalBackground
  ring

lemma renewalBackground_top (N : ℕ) (t : ℝ) :
    (∑ i : Fin N,a (i.val+1)*renewalBackground N t i)=
      t*(g (N+1)-a (N+1)) := by
  have hs := renewal_reverse_sum (i:=0) (N:=N+1) (by omega)
  rw [Finset.sum_range_succ'] at hs
  simp only [not_lt_zero,ite_false, if_false,add_zero,Nat.zero_lt_succ,ite_true, if_true,Nat.sub_zero] at hs
  rw [←hs,Finset.mul_sum]
  simp only [renewalBackground]
  rw [Fin.sum_univ_eq_sum_range (fun i => a (i+1)*(t*g (N-i)))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [show N+1-(i+1)=N-i by omega]
  ring

theorem renewalBackground_uniform_gap : ∃ c : ℝ,0 < c ∧
    ∀ (N : ℕ) (t : ℝ),0 ≤ t → ∀ i : Fin (N+1),
      c*t*(rho^(N+2))⁻¹ ≤
        (renewalBackground (N+2) t i.castSucc-
          renewalBackground (N+2) t i.succ)/rho^(i.val+1) := by
  obtain ⟨c,hc,hgap⟩ := renewal_difference_uniform_lower
  refine ⟨c,hc,?_⟩
  intro N t ht i
  have hi : 1 ≤ N+1-i.val := by have := i.isLt; omega
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hgap _ hi) ht) (pow_pos rho_pos (i.val+1)).le
  have he : N+2-i.val=(N+1-i.val)+1 := by have := i.isLt; omega
  have hp : rho^(N+1-i.val)*rho^(i.val+1)=rho^(N+2) := by
    rw [←pow_add,show N+1-i.val+(i.val+1)=N+2 by have := i.isLt; omega]
  refine Eq.trans_le ?_ (hh.trans_eq ?_)
  · rw [←hp]
    field_simp [rho_pos.ne']
  · symm
    simp only [renewalBackground,Fin.val_castSucc,Fin.val_succ,
      show N+2-(i.val+1)=N+1-i.val by omega,he,mul_sub]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedShiftBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical budgets for the ordered renewal translate. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma exists_ordered_shift_size {A c s D : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hs : 0 < s) (hD : 0 < D) :
    ∃ K : ℝ,0 < K ∧ Real.exp (A-s*D*K)/(1-Real.exp (-c)) ≤ 1/2 := by
  let q := 1-Real.exp (-c)
  have hq : 0 < q := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  let K := (A+|Real.log (q/2)|+1)/(s*D)
  have hK : 0 < K := div_pos (by positivity) (mul_pos hs hD)
  refine ⟨K,hK,?_⟩
  have he : A-s*D*K= -|Real.log (q/2)|-1 := by
    dsimp [K]
    field_simp
    ring
  have hlog : A-s*D*K ≤ Real.log (q/2) := by
    rw [he]
    have hh := neg_abs_le (Real.log (q/2))
    linarith only [hh]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < q/2)] at hexp
  apply (div_le_iff₀ hq).mpr
  change Real.exp (A-s*D*K) ≤ (1/2:ℝ)*q
  linarith only [hexp]

lemma renewal_top_cost_nonneg (n : ℕ) : 0 ≤ g (n+1)-a (n+1) := by
  have he := renewal_reverse_sum (N:=n+1) (i:=0) (by omega)
  simp only [Nat.sub_zero] at he
  rw [←he]
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with hj0
  · exact mul_nonneg (a_pos (by omega)).le (g_pos _).le
  · exact le_rfl

lemma renewal_shift_cost {n : ℕ} (hn : 0 < n) {B K : ℝ}
    (hB : 0 < B) (hK : 0 < K) :
    let t := K*B/((n:ℝ)*g (n+1))
    0 < t ∧ 0 ≤ t*(g (n+1)-a (n+1)) ∧
      t*(g (n+1)-a (n+1)) ≤ K*B/n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  dsimp only
  have ht : 0 < K*B/((n:ℝ)*g (n+1)) :=
    div_pos (mul_pos hK hB) (mul_pos hn' (g_pos _))
  refine ⟨ht,mul_nonneg ht.le (renewal_top_cost_nonneg n),?_⟩
  calc
    _ ≤ (K*B/((n:ℝ)*g (n+1)))*g (n+1) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (a_pos (by omega)).le) ht.le
    _ = _ := by field_simp [(g_pos (n+1)).ne',hn'.ne']

lemma renewal_gap_cost_comparison {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hupper : ∀ n : ℕ,g n ≤ C*(rho^n)⁻¹) (n : ℕ) :
    (c*rho/C)*g (n+1) ≤ c*(rho^n)⁻¹ := by
  have hh := mul_le_mul_of_nonneg_left (hupper (n+1))
    (div_nonneg (mul_nonneg hc.le rho_pos.le) hC.le)
  apply hh.trans_eq
  rw [pow_succ]
  field_simp [rho_pos.ne',hC.ne']

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixBudgetLower
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed positive volume survives a bounded loss in the scaled top budget. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefix_budget_power_lower {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E)
    (hEB : 2*E ≤ B) (N : ℕ) :
    Real.exp (-2*(N:ℝ)*E/B)*B^N ≤ (B-E)^N := by
  let q := E/B
  have hq : 0 ≤ q := div_nonneg hE hB.le
  have hq2 : q ≤ 1/2 := by
    apply (div_le_iff₀ hB).mpr
    linarith only [hEB]
  have hp : 0 < 1-q := by linarith only [hq2]
  have hlog : -2*q ≤ Real.log (1-q) := by
    have hh := log_one_add_quadratic_lower (x := -q) (by linarith only [hq2])
    have hs := mul_nonneg hq (show 0 ≤ 1/2-q by linarith only [hq2])
    have he : 1+(-q)=1-q := by ring
    rw [he] at hh
    nlinarith only [hh,hs]
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N))
  simp only [Real.exp_nat_mul,Real.exp_log hp] at he
  have hfac := mul_le_mul_of_nonneg_right he (pow_nonneg hB.le N)
  have hid : B-E=(1-q)*B := by dsimp [q]; field_simp
  have hexp : Real.exp (-2*(N:ℝ)*E/B)=(Real.exp (-2*q))^N := by
    rw [←Real.exp_nat_mul]
    congr 1
    dsimp [q]
    ring
  rw [hid,mul_pow,hexp]
  exact hfac

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGapWeights
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed simplex weights for an adjacent-coordinate gap. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefix_gap_coordinate (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+1)) :
    (u i.castSucc-u i.succ)/rho^(i.val+1)=
      ∑ j,prefixGapWeight N i j*prefixSimplexMap (N+2) u j := by
  have hi := prefixSimplexMap_coordinate (N+2) u i.castSucc
  have hj := prefixSimplexMap_coordinate (N+2) u i.succ
  simp only [prefixGapWeight,sub_mul,Finset.sum_sub_distrib,mul_assoc]
  rw [←Finset.mul_sum,←hi,←hj]
  simp only [Fin.val_castSucc,Fin.val_succ,pow_succ]
  field_simp [rho_pos.ne']

theorem prefix_gap_weight_bounds : ∃ M K : ℝ,1 ≤ M ∧ 0 < K ∧
    ∀ (N : ℕ) (i : Fin (N+1)),
      (∀ j,-M ≤ prefixGapWeight N i j ∧ prefixGapWeight N i j ≤ M) ∧
      (1-rho)*(N+2-i.val:ℕ)-2*K ≤ ∑ j,prefixGapWeight N i j ∧
      (∑ j,(prefixGapWeight N i j)^2) ≤ 4*M*((N+2-i.val:ℕ)+K) := by
  obtain ⟨M,K,hM,hK,hbound⟩ := prefixWeight_bounds
  refine ⟨M,K,hM,hK,?_⟩
  intro N i
  obtain ⟨ha,hsa,hqa⟩ := hbound (N+2) i.castSucc
  obtain ⟨hb,hsb,hqb⟩ := hbound (N+2) i.succ
  have hρ := rho_pos
  have hρ1 := rho_lt_one
  have hmeanA := (abs_le.mp hsa).1
  have hmeanB := (abs_le.mp hsb).2
  have hn : N+2-(i.val+1)=N+2-i.val-1 := by omega
  have hreal : ((N+2-(i.val+1):ℕ):ℝ)=((N+2-i.val:ℕ):ℝ)-1 := by
    rw [hn,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]
  refine ⟨?_,?_,?_⟩
  · intro j
    obtain ⟨ha0,haM⟩ := ha j
    obtain ⟨hb0,hbM⟩ := hb j
    dsimp [prefixGapWeight]
    constructor <;> nlinarith only [ha0,haM,hb0,hbM,hρ,hρ1,hM]
  · simp only [prefixGapWeight,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp only [Fin.val_castSucc,Fin.val_succ] at hmeanA hmeanB
    rw [hreal] at hmeanB
    nlinarith only [hmeanA,hmeanB,hρ,hρ1,hK]
  · have hsq : (∑ j,(prefixGapWeight N i j)^2) ≤
        2*(∑ j,(prefixWeight (N+2) i.castSucc j)^2)+
          2*rho^2*(∑ j,(prefixWeight (N+2) i.succ j)^2) := by
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      dsimp [prefixGapWeight]
      nlinarith only [sq_nonneg (prefixWeight (N+2) i.castSucc j+
        rho*prefixWeight (N+2) i.succ j)]
    simp only [Fin.val_castSucc,Fin.val_succ] at hqa hqb
    rw [hreal] at hqb
    have hqb0 : 0 ≤ ∑ j,(prefixWeight (N+2) i.succ j)^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right
      (show rho^2 ≤ 1 by nlinarith only [hρ,hρ1]) hqb0
    nlinarith only [hsq,hqa,hqb,hh,hM,hK]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixGapVolume
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential control of inversions in ordered prime-coordinate regions. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem prefix_gap_cap_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (i : Fin (N+1)) (B T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      volume.real (standardSimplex (N+2) B ∩
        {v | (∑ j,prefixGapWeight N i j*v j) ≤ -T}) ≤
      Real.exp (A-c*(N+2-i.val:ℕ)-s*(N+2:ℝ)*T/B)*
        volume.real (standardSimplex (N+2) B) := by
  obtain ⟨M,K,hM,hK,hw⟩ := prefix_gap_weight_bounds
  let d := 1-rho
  let s := d/(32*M)
  have hd : 0 < d := sub_pos.mpr rho_lt_one
  have hd1 : d ≤ 1 := by dsimp [d]; linarith only [rho_pos]
  have hs : 0 < s := div_pos hd (by positivity)
  have hsM : s*M=d/32 := by dsimp [s]; field_simp
  have hsM2 : s*M ≤ 1/2 := by rw [hsM]; linarith only [hd1]
  let A := 2*s*K+8*s^2*M*K
  let c := s*d/2
  have hA : 0 < A := by dsimp [A] <;> positivity
  have hc : 0 < c := by dsimp [c] <;> positivity
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N i B T hB _hT hTB
  obtain ⟨hpoint,hmean,hsq⟩ := hw N i
  have hweight (j) : -(1/2:ℝ) ≤ s*prefixGapWeight N i j := by
    have hh := mul_le_mul_of_nonneg_left (hpoint j).1 hs.le
    nlinarith only [hh,hsM2]
  have hbudget : 0 ≤ B+s*(-T) := by linarith only [hTB]
  have hv := volume_simplex_lower_cap_exp (N+2) hB (-T) s
    (prefixGapWeight N i) hs.le hweight hbudget
  apply hv.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.exp_le_exp.mpr
  have hq := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*s^2 by positivity)
  have hcancel : 8*s^2*M=s*d/4 := by
    calc
      _ = 8*s*(s*M) := by ring
      _ = _ := by rw [hsM]; ring
  have hn : 0 ≤ ((N+2-i.val:ℕ):ℝ) := Nat.cast_nonneg _
  dsimp only [A,c]
  change d*((N+2-i.val:ℕ):ℝ)-2*K ≤ _ at hmean
  have hmean' := mul_le_mul_of_nonneg_left hmean hs.le
  simp only [mul_add] at hq
  have hqe : 2*s^2*(4*M*((N+2-i.val:ℕ):ℝ))+2*s^2*(4*M*K)=
      (s*d/4)*((N+2-i.val:ℕ):ℝ)+8*s^2*M*K := by
    calc
      _ = (8*s^2*M)*((N+2-i.val:ℕ):ℝ)+8*s^2*M*K := by ring
      _ = _ := by rw [hcancel]
  rw [hqe] at hq
  have hnon := mul_nonneg (mul_nonneg hs.le hd.le) hn
  have he : ((N+2:ℕ):ℝ)*(s*(-T)/B)= -(s*(N+2:ℝ)*T/B) := by
    push_cast
    ring
  rw [he]
  nlinarith only [hmean',hq,hnon]

lemma prefix_gap_bad_preimage (N : ℕ) (i : Fin (N+1)) (B T : ℝ) :
    prefixRegion (N+2) B 0 0 ∩
      {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T} =
      prefixSimplexMap (N+2) ⁻¹'
        (standardSimplex (N+2) B ∩
          {v | (∑ j,prefixGapWeight N i j*v j) ≤ -T}) := by
  rw [prefixSimplexMap_preimage]
  ext u
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq]
  rw [← prefix_gap_coordinate]
  have hr := pow_pos rho_pos (i.val+1)
  rw [div_le_iff₀ hr]
  have he : -T*rho^(i.val+1)= -rho^(i.val+1)*T := by ring
  rw [he]

theorem prefix_gap_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (i : Fin (N+1)) (B T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      volume.real (prefixRegion (N+2) B 0 0 ∩
        {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T}) ≤
      Real.exp (A-c*(N+2-i.val:ℕ)-s*(N+2:ℝ)*T/B)*
        volume.real (prefixRegion (N+2) B 0 0) := by
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := prefix_gap_cap_volume
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N i B T hB hT hTB
  rw [prefix_gap_bad_preimage]
  apply prefixSimplexMap_transfer
  · apply (measurableSet_standardSimplex _ _).inter
    exact measurableSet_le (by fun_prop) measurable_const
  · exact hbound N i B T hB hT hTB

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TranslatedPrefix
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A renewal translate gives strict positive slack without losing dimension. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma renewal_translate_prefix {N : ℕ} {B t : ℝ} (ht : 0 ≤ t)
    {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0) :
    u+renewalBackground N t ∈ prefixRegion N B 0 0 ∧
      ∀ i,t*a (N-i.val) ≤ prefixLinear N (u+renewalBackground N t) i := by
  have hslack (i : Fin N) : t*a (N-i.val) ≤
      prefixLinear N (u+renewalBackground N t) i := by
    rw [map_add,Pi.add_apply,renewalBackground_slack]
    have hh := hu.1 i
    change 0 ≤ prefixLinear N u i at hh
    linarith only [hh]
  refine ⟨⟨?_,?_⟩,hslack⟩
  · intro i
    exact (mul_nonneg ht (a_pos (by have := i.isLt; omega)).le).trans (hslack i)
  · change (∑ i : Fin N,a (i.val+1)*(u i+renewalBackground N t i)) ≤ B-0
    simp only [mul_add,Finset.sum_add_distrib,renewalBackground_top,sub_zero]
    have hh := hu.2
    simp only [sub_zero] at hh
    linarith only [hh]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TranslatedOrder
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing adjacent inversions in the translated prime-coordinate region. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma finite_gap_exponential_sum {c : ℝ} (hc : 0 < c) (N : ℕ) :
    (∑ i : Fin (N+1),Real.exp (-c*((N+2-i.val:ℕ):ℝ))) ≤
      1/(1-Real.exp (-c)) := by
  classical
  let q := Real.exp (-c)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hinj : Set.InjOn (fun i : Fin (N+1) => N+2-i.val)
      ↑(Finset.univ : Finset (Fin (N+1))) := by
    intro i _ j _ he
    apply Fin.ext
    change N+2-i.val=N+2-j.val at he
    have := i.isLt
    have := j.isLt
    omega
  have he (i : Fin (N+1)) : Real.exp (-c*((N+2-i.val:ℕ):ℝ))=q^(N+2-i.val) := by
    dsimp [q]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  rw [←Finset.sum_image hinj]
  have hs := hasSum_geometric_of_lt_one hq hq1
  simpa only [one_div,q] using
    (hs.summable.sum_le_tsum _ (fun k _ => pow_nonneg hq k)).trans_eq hs.tsum_eq

theorem translated_prefix_inversions : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (B t T : ℝ),0 < B → 0 ≤ T → s*T ≤ B →
      (∀ i : Fin (N+1),rho^(i.val+1)*T ≤
        renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ) →
      volume.real {u : Fin (N+2) → ℝ | u ∈ prefixRegion (N+2) B 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ≤
      (Real.exp (A-s*(N+2:ℝ)*T/B)/(1-Real.exp (-c)))*
        volume.real (prefixRegion (N+2) B 0 0) := by
  classical
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := prefix_gap_volume
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N B t T hB hT hTB hgap
  let S := prefixRegion (N+2) B 0 0
  let E (i : Fin (N+1)) := S ∩
    {u | u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T}
  have hsub : {u : Fin (N+2) → ℝ | u ∈ S ∧
      ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ⊆ ⋃ i,E i := by
    intro u hu
    have hn := hu.2
    rw [Fin.strictAnti_iff_succ_lt] at hn
    push Not at hn
    obtain ⟨i,hi⟩ := hn
    apply Set.mem_iUnion.mpr
    refine ⟨i,hu.1,?_⟩
    have hg := hgap i
    change u i.castSucc-u i.succ ≤ -rho^(i.val+1)*T
    nlinarith only [hi,hg]
  have hfinite : volume (⋃ i,E i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume S ≠ ⊤ from ?_)
      (measure_mono (by intro u hu; obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu; exact hi.1))
    dsimp [S]
    rw [volume_prefixRegion_explicit (N+2) (by omega)]
    exact ENNReal.ofReal_ne_top
  have hmeasure := ENNReal.toReal_mono hfinite (measure_mono hsub)
  apply hmeasure.trans
  apply (measureReal_iUnion_fintype_le E).trans
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound N i B T hB hT hTB)
  apply hsum.trans
  have he (i : Fin (N+1)) :
      Real.exp (A-c*((N+2-i.val:ℕ):ℝ)-s*(N+2:ℝ)*T/B)=
        Real.exp (A-s*(N+2:ℝ)*T/B)*Real.exp (-c*((N+2-i.val:ℕ):ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (finite_gap_exponential_sum hc N)
    (Real.exp_pos (A-s*(N+2:ℝ)*T/B)).le
  simpa only [div_eq_mul_inv,mul_assoc,one_mul,S] using
    mul_le_mul_of_nonneg_right hh (show 0 ≤ volume.real S from ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedTranslateVolume
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive volume of the ordered part of a renewal translate. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefix_budget_volume_lower {N : ℕ} (hN : 0 < N)
    {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (hEB : 2*E ≤ B) :
    Real.exp (-2*(N:ℝ)*E/B)*volume.real (prefixRegion N B 0 0) ≤
      volume.real (prefixRegion N (B-E) 0 0) := by
  have hBE : 0 ≤ B-E := by linarith only [hE,hEB]
  have hd : 0 < ((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) :=
    mul_pos (by exact_mod_cast Nat.factorial_pos N)
      (Finset.prod_pos (fun i _ => g_pos _))
  have hp := prefix_budget_power_lower hB hE hEB N
  simp only [Measure.real,volume_prefixRegion_explicit N hN,Pi.zero_apply,
    mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hB.le,max_eq_left hBE,
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hB.le N) hd.le),
    ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hBE N) hd.le)]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hp hd.le

lemma ordered_translate_half_volume {N : ℕ} (hN : 0 < N) {B t : ℝ}
    (ht : 0 ≤ t)
    (hbad : volume.real {u : Fin N → ℝ |
      u ∈ prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground N t i)} ≤
      volume.real (prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)/2) :
    volume.real (prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0)/2 ≤
      volume.real (orderedSlackRegion N B t) := by
  classical
  let S := prefixRegion N (B-t*(g (N+1)-a (N+1))) 0 0
  let U : Set (Fin N → ℝ) :=
    {u | u ∈ S ∧ StrictAnti (fun i => u i+renewalBackground N t i)}
  let E : Set (Fin N → ℝ) :=
    {u | u ∈ S ∧ ¬StrictAnti (fun i => u i+renewalBackground N t i)}
  have hsplit : S = U ∪ E := by
    ext u
    simp only [U,E,Set.mem_union,Set.mem_ofPred_eq]
    tauto
  have hsum : volume.real S ≤ volume.real U+volume.real E := by
    rw [hsplit]
    exact measureReal_union_le _ _
  have hhalf : volume.real S/2 ≤ volume.real U := by
    change volume.real E ≤ volume.real S/2 at hbad
    linarith only [hsum,hbad]
  have hsub : U ⊆ (fun u : Fin N → ℝ => u+renewalBackground N t) ⁻¹'
      orderedSlackRegion N B t := by
    intro u hu
    have hh := renewal_translate_prefix ht hu.1
    exact ⟨hh.1,hu.2,hh.2⟩
  have hshift := measure_preimage_add_right (volume : Measure (Fin N → ℝ))
    (renewalBackground N t) (orderedSlackRegion N B t)
  have htarget : volume (orderedSlackRegion N B t) ≠ ⊤ :=
    measure_ne_top_of_subset (fun _ hv => hv.1) (prefixRegion_volume_ne_top hN B)
  have hmono := measureReal_mono hsub (by rw [hshift]; exact htarget)
  simp only [Measure.real,hshift] at hmono
  exact hhalf.trans hmono

theorem ordered_translate_volume : ∃ A c s : ℝ,0 < A ∧ 0 < c ∧ 0 < s ∧
    ∀ (N : ℕ) (B t T : ℝ),0 < B → 0 ≤ t →
      0 ≤ t*(g (N+3)-a (N+3)) → 2*t*(g (N+3)-a (N+3)) ≤ B →
      0 ≤ T → s*T ≤ B-t*(g (N+3)-a (N+3)) →
      (∀ i : Fin (N+1),rho^(i.val+1)*T ≤
        renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ) →
      Real.exp (A-s*(N+2:ℝ)*T/(B-t*(g (N+3)-a (N+3))))/
        (1-Real.exp (-c)) ≤ 1/2 →
      Real.exp (-2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B)/2*
        volume.real (prefixRegion (N+2) B 0 0) ≤
      volume.real (orderedSlackRegion (N+2) B t) := by
  obtain ⟨A,c,s,hA,hc,hs,hbound⟩ := translated_prefix_inversions
  refine ⟨A,c,s,hA,hc,hs,?_⟩
  intro N B t T hB ht hE hEB hT hTB hgap hsmall
  have hB' : 0 < B-t*(g (N+3)-a (N+3)) := by
    nlinarith only [hB,hEB,hE]
  have heq : N+2+1=N+3 := by omega
  have hbad := hbound N (B-t*(g (N+3)-a (N+3))) t T hB' hT hTB hgap
  have hbad' : volume.real {u : Fin (N+2) → ℝ |
      u ∈ prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0 ∧
        ¬StrictAnti (fun i => u i+renewalBackground (N+2) t i)} ≤
      volume.real (prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0)/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ volume.real (prefixRegion (N+2) (B-t*(g (N+3)-a (N+3))) 0 0)
        from ENNReal.toReal_nonneg)
    exact hbad.trans (by nlinarith only [hh])
  have hhalf := ordered_translate_half_volume (by omega : 0 < N+2) ht
    (by simpa only [heq] using hbad')
  have hvol := prefix_budget_volume_lower (by omega : 0 < N+2) hB hE
    (by simpa only [mul_assoc] using hEB)
  have hh := div_le_div_of_nonneg_right hvol (by norm_num : (0:ℝ) ≤ 2)
  have harg : -2*((N+2:ℕ):ℝ)*(t*(g (N+3)-a (N+3)))/B=
      -2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B := by push_cast <;> ring
  rw [harg] at hh
  apply le_trans _ (by simpa only [heq] using hhalf)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedPrefixLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform positive fraction of the prefix volume has strict order and slack. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem ordered_prefix_volume_lower : ∃ K δ : ℝ,0 < K ∧ 0 < δ ∧
    ∀ᶠ N : ℕ in atTop, ∀ B : ℝ,0 < B →
      δ*volume.real (prefixRegion (N+2) B 0 0) ≤
        volume.real (orderedSlackRegion (N+2) B
          (K*B/((N+2:ℝ)*g (N+3)))) := by
  obtain ⟨A,c,s,hA,hc,hs,hvol⟩ := ordered_translate_volume
  obtain ⟨c₀,hc₀,hgap⟩ := renewalBackground_uniform_gap
  obtain ⟨C,hC,hupper⟩ := renewal_uniform_upper
  let D := c₀*rho/C
  have hD : 0 < D := div_pos (mul_pos hc₀ rho_pos) hC
  obtain ⟨K,hK,hsmall⟩ := exists_ordered_shift_size hA hc hs hD
  refine ⟨K,Real.exp (-2*K)/2,hK,by positivity,?_⟩
  obtain ⟨L,hL⟩ := exists_nat_gt (max (2*K) (2*s*D*K))
  filter_upwards [eventually_ge_atTop L] with N hN
  intro B hB
  have hn : (0:ℝ) < N+2 := by positivity
  have hLN : (L:ℝ) ≤ N+2 := by exact_mod_cast (show L ≤ N+2 by omega)
  have hKbound : 2*K ≤ N+2 := (le_max_left _ _).trans (hL.le.trans hLN)
  have hsbound : 2*s*D*K ≤ N+2 := (le_max_right _ _).trans (hL.le.trans hLN)
  let t := K*B/((N+2:ℝ)*g (N+3))
  let T := D*K*B/(N+2:ℝ)
  let E := t*(g (N+3)-a (N+3))
  have heq : N+2+1=N+3 := by omega
  obtain ⟨ht,hE,hcost⟩ := renewal_shift_cost (by omega : 0 < N+2) hB hK
  simp only [Nat.cast_add,Nat.cast_ofNat,heq] at ht hE hcost
  change 0 < t at ht
  change 0 ≤ E at hE
  change E ≤ K*B/(N+2:ℝ) at hcost
  have hcosthalf : K*B/(N+2:ℝ) ≤ B/2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hKbound hB.le]
  have hEB : 2*E ≤ B := by linarith only [hcost,hcosthalf]
  have hB' : 0 < B-E := by linarith only [hB,hEB]
  have hT : 0 ≤ T := by dsimp [T] <;> positivity
  have hThalf : s*T ≤ B/2 := by
    dsimp [T]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hn).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hsbound hB.le]
  have hTB : s*T ≤ B-E := by linarith only [hThalf,hEB]
  have hgapT : T ≤ c₀*t*(rho^(N+2))⁻¹ := by
    have hh := renewal_gap_cost_comparison hC hc₀ hupper (N+2)
    rw [heq] at hh
    calc
      T = t*(D*g (N+3)) := by dsimp [T,t]; field_simp [(g_pos (N+3)).ne',hn.ne']
      _ ≤ t*(c₀*(rho^(N+2))⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
      _ = _ := by ring
  have hcoord (i : Fin (N+1)) : rho^(i.val+1)*T ≤
      renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ := by
    have hh := hgapT.trans (hgap N t ht.le i)
    have hh' := (le_div_iff₀ (pow_pos rho_pos (i.val+1))).mp hh
    simpa only [mul_comm] using hh'
  have hscaled : s*D*K ≤ s*(N+2:ℝ)*T/(B-E) := by
    apply (le_div_iff₀ hB').mpr
    have he : s*(N+2:ℝ)*T=s*D*K*B := by dsimp [T]; field_simp
    rw [he]
    nlinarith only [mul_nonneg (show 0 ≤ s*D*K by positivity) hE]
  have hden : 0 < 1-Real.exp (-c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hsmall' : Real.exp (A-s*(N+2:ℝ)*T/(B-E))/(1-Real.exp (-c)) ≤ 1/2 := by
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ hden.le
    exact Real.exp_le_exp.mpr (by linarith only [hscaled])
  have hmain := hvol N B t T hB ht.le hE
    (by simpa only [E,mul_assoc] using hEB) hT hTB hcoord hsmall'
  have hbudget : (N+2:ℝ)*E/B ≤ K := by
    apply (div_le_iff₀ hB).mpr
    have hh := (le_div_iff₀ hn).mp hcost
    nlinarith only [hh]
  have hexp : Real.exp (-2*K) ≤ Real.exp (-2*(N+2:ℝ)*E/B) := by
    apply Real.exp_le_exp.mpr
    have he : -2*(N+2:ℝ)*E/B= -2*((N+2:ℝ)*E/B) := by ring
    rw [he]
    linarith only [hbudget]
  apply le_trans _ hmain
  have hh := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hexp (by norm_num : (0:ℝ) ≤ 2))
    (show 0 ≤ volume.real (prefixRegion (N+2) B 0 0) from ENNReal.toReal_nonneg)
  have harg : -2*(N+2:ℝ)*E/B=
      -2*(N+2:ℝ)*t*(g (N+3)-a (N+3))/B := by dsimp [E] <;> ring
  rw [harg] at hh
  exact hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictContractionCost
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse-cube row contraction has a bounded full Jacobian. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma rowContractionError_nonneg (h : ℕ) : 0 ≤ rowContractionError h := by
  unfold rowContractionError
  positivity

lemma rowContractionError_weighted_summable :
    Summable (fun h : ℕ => (h:ℝ)*rowContractionError h) := by
  have hs : Summable (fun h : ℕ => (1/5:ℝ)*(1/((h+1:ℕ):ℝ)^2)) :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))).mul_left _
  apply Summable.of_nonneg_of_le
    (fun h => mul_nonneg (Nat.cast_nonneg h) (rowContractionError_nonneg h)) _ hs
  intro h
  have hp : (0:ℝ) < h+1 := by positivity
  calc
    _ ≤ (h+1:ℝ)*rowContractionError h :=
      mul_le_mul_of_nonneg_right (by linarith) (rowContractionError_nonneg h)
    _ = _ := by
      unfold rowContractionError
      push_cast
      field_simp [hp.ne']

lemma row_contraction_jacobian {m N : ℕ} (hNm : N ≤ m) :
    (∏ i : Fin N,enlargementScale (fun r => 1+rowContractionError (m-r)) i) ≤
      Real.exp rowContractionCost := by
  apply (enlargement_jacobian_bound
    (fun r => by linarith [rowContractionError_nonneg (m-r)])).trans
  apply Real.exp_le_exp.mpr
  simp only [add_sub_cancel_left]
  have hs : (∑ r ∈ Finset.range N,((N-r:ℕ):ℝ)*rowContractionError (m-r)) ≤
      ∑ r ∈ Finset.range m,((m-r:ℕ):ℝ)*rowContractionError (m-r) := by
    apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNm)
      (fun r _ _ => mul_nonneg (Nat.cast_nonneg _) (rowContractionError_nonneg _)))
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_right _ (rowContractionError_nonneg _)
    exact_mod_cast Nat.sub_le_sub_right hNm r
  apply hs.trans
  simpa only [Nat.sub_zero,Nat.zero_add,rowContractionCost] using
    reverse_perturbation_sum_le (P:=0) (Nat.zero_le m) rowContractionError
      rowContractionError_nonneg rowContractionError_weighted_summable

lemma row_contraction_coordinate {m N : ℕ} (hNm : N ≤ m) (i : Fin N) :
    enlargementScale (fun r => 1+rowContractionError (m-r)) i ≤
      Real.exp rowContractionCost := by
  have hi : i.val < m := i.isLt.trans_le hNm
  simpa only [Nat.sub_zero,Nat.zero_add,rowContractionCost] using
    reverse_enlargement_coordinate (H:=0) (Nat.zero_le m) rowContractionError
      rowContractionError_nonneg rowContractionError_weighted_summable i hi

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictPrefixContraction
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal contraction imposes strict Ford rows while preserving prime order. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixRegion_coordinate_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (i : Fin N) : 0 ≤ u i := by
  rw [prefixLinear_coordinate N u i]
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (g_pos _).le (hu.1 j)
  · exact le_rfl

lemma prefix_contraction {N : ℕ} {B : ℝ} {β κ : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) (hκ : ∀ i,1 ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u) :
    simplexScale κ u ∈ contractedPrefix N B β := by
  have hkpos (i) : 0 < κ i := zero_lt_one.trans_le (hκ i)
  have hbpos (i) : 0 < β i := zero_lt_one.trans_le (hβ i)
  have hu0 := prefixRegion_coordinate_nonneg hu
  have hmono {i j : Fin N} (hij : i < j) : κ i ≤ κ j := by
    have hh := mul_le_mul_of_nonneg_right (hβ i) (hkpos i).le
    have hh' : κ i ≤ β i*κ i := by simpa only [one_mul] using hh
    exact hh'.trans (hstep i j hij)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [simplexScale_apply]
    exact div_nonneg (hu0 i) (hkpos i).le
  · intro i j hij
    simp only [simplexScale_apply]
    exact (div_le_div_of_nonneg_left (hu0 j) (hkpos i) (hmono hij)).trans_lt
      ((div_lt_div_iff_of_pos_right (hkpos i)).mpr (horder hij))
  · intro i
    simp only [simplexScale_apply]
    have hsum : (∑ j : Fin N,if i < j then a (j.val-i.val)*(u j/κ j) else 0) ≤
        (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0)/(β i*κ i) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hij
      · calc
          _ = (a (j.val-i.val)*u j)/κ j := by ring
          _ ≤ _ := div_le_div_of_nonneg_left
            (mul_nonneg (a_pos (by have := hij; simp only [Fin.lt_def] at this; omega)).le
              (hu0 j)) (mul_pos (hbpos i) (hkpos i)) (hstep i j hij)
      · simp
    have hrow := hu.1 i
    rw [prefixLinear_apply] at hrow
    have hrow' : (∑ j : Fin N,if i < j then a (j.val-i.val)*u j else 0) ≤ u i := by
      change 0 ≤ u i-_ at hrow
      linarith only [hrow]
    have hh := hsum.trans (div_le_div_of_nonneg_right hrow'
      (mul_pos (hbpos i) (hkpos i)).le)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · simp only [simplexScale_apply]
    apply le_trans _ (by simpa only [sub_zero] using hu.2)
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (a (i.val+1)*u i)/κ i := by ring
      _ ≤ a (i.val+1)*u i := div_le_self
        (mul_nonneg (a_pos (by omega)).le (hu0 i)) (hκ i)

lemma prefix_contraction_gap {N : ℕ} {B : ℝ} {β κ : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) (hκ : ∀ i,1 ≤ κ i)
    (hstep : ∀ i j,i < j → β i*κ i ≤ κ j)
    {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u)
    {i j : Fin N} (hij : i < j) :
    simplexScale κ u j ≤ simplexScale κ u i/β i := by
  have hk (r) : 0 < κ r := zero_lt_one.trans_le (hκ r)
  have hb : 0 < β i := zero_lt_one.trans_le (hβ i)
  simp only [simplexScale_apply]
  calc
    _ ≤ u i/κ j := div_le_div_of_nonneg_right (horder hij).le (hk j).le
    _ ≤ u i/(β i*κ i) := div_le_div_of_nonneg_left
      (prefixRegion_coordinate_nonneg hu i) (mul_pos hb (hk i)) (hstep i j hij)
    _ = _ := by ring

lemma reciprocal_enlargement_contracts {N : ℕ} {B : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ r,1 ≤ β r) {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) (horder : StrictAnti u) :
    simplexScale (enlargementScale β) u ∈
      contractedPrefix N B (fun i => β (i.val+1)) :=
  prefix_contraction (fun i => hβ (i.val+1))
    (fun i => (hβ 0).trans (enlargementScale_top hβ i))
    (enlargementScale_step hβ) hu horder

lemma reciprocal_enlargement_top {N : ℕ} {B : ℝ} {β : ℕ → ℝ}
    (hβ : ∀ r,1 ≤ β r) {u : Fin N → ℝ} (hu : u ∈ prefixRegion N B 0 0) :
    (∑ i : Fin N,a (i.val+1)*simplexScale (enlargementScale β) u i) ≤ B/β 0 := by
  have hb : 0 < β 0 := zero_lt_one.trans_le (hβ 0)
  simp only [simplexScale_apply]
  calc
    _ ≤ (∑ i : Fin N,a (i.val+1)*u i)/β 0 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = (a (i.val+1)*u i)/enlargementScale β i := by ring
        _ ≤ _ := div_le_div_of_nonneg_left
          (mul_nonneg (a_pos (by omega)).le (prefixRegion_coordinate_nonneg hu i))
          hb (enlargementScale_top hβ i)
    _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [sub_zero] using hu.2) hb.le

lemma contractedPrefix_subset_prefixRegion {N : ℕ} {B : ℝ} {β : Fin N → ℝ}
    (hβ : ∀ i,1 ≤ β i) : contractedPrefix N B β ⊆ prefixRegion N B 0 0 := by
  intro v hv
  refine ⟨?_,by simpa only [sub_zero] using hv.2.2.2⟩
  intro i
  have hh := (hv.2.2.1 i).trans (div_le_self (hv.1 i) (hβ i))
  rw [prefixLinear_apply]
  change 0 ≤ v i-_
  linarith only [hh]

lemma measurableSet_contractedPrefix (N : ℕ) (B : ℝ) (β : Fin N → ℝ) :
    MeasurableSet (contractedPrefix N B β) := by
  have horder : MeasurableSet {v : Fin N → ℝ | StrictAnti v} := by
    change MeasurableSet {v : Fin N → ℝ | ∀ i j,i < j → v j < v i}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hij : i < j
    · simpa [hij] using
        (measurableSet_lt
          (by fun_prop : Measurable (fun v : Fin N → ℝ => v j))
          (by fun_prop : Measurable (fun v : Fin N → ℝ => v i)))
    · simp [hij]
  change MeasurableSet ({v : Fin N → ℝ | ∀ i,0 ≤ v i} ∩
    ({v : Fin N → ℝ | StrictAnti v} ∩
      ({v : Fin N → ℝ | ∀ i,
        (∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) ≤ v i/β i} ∩
        {v : Fin N → ℝ | (∑ i : Fin N,a (i.val+1)*v i) ≤ B})))
  apply MeasurableSet.inter _ (horder.inter (MeasurableSet.inter ?_ ?_))
  · rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · rw [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => ?_)
    have heq : (fun v : Fin N → ℝ =>
        ∑ j : Fin N,if i < j then a (j.val-i.val)*v j else 0) =
        (fun v => v i-prefixLinear N v i) := by
      ext v
      rw [prefixLinear_apply]
      ring
    apply measurableSet_le _ (by fun_prop)
    rw [heq]
    exact (measurable_pi_apply i).sub ((measurable_pi_apply i).comp
      (prefixLinear N).continuous_of_finiteDimensional.measurable)
  · exact measurableSet_le (by fun_prop) measurable_const

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_OrderedPrefixCoordinates
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered positive-volume family retains a geometric lower envelope. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma orderedSlackRegion_coordinate_lower {N : ℕ} {B t : ℝ}
    {u : Fin N → ℝ} (hu : u ∈ orderedSlackRegion N B t) (i : Fin N) :
    t*g (N-i.val) ≤ u i := by
  let v := u-renewalBackground N t
  have hv : v ∈ prefixRegion N (∑ j : Fin N,a (j.val+1)*v j) 0 0 := by
    refine ⟨?_,by simp⟩
    intro j
    change 0 ≤ prefixLinear N (u-renewalBackground N t) j
    rw [map_sub,Pi.sub_apply,renewalBackground_slack]
    exact sub_nonneg.mpr (hu.2.2 j)
  have hh := prefixRegion_coordinate_nonneg hv i
  change 0 ≤ u i-t*g (N-i.val) at hh
  linarith only [hh]

theorem contracted_ordered_coordinate_lower : ∃ c : ℝ,0 < c ∧
    ∀ {m N : ℕ},N ≤ m → ∀ {B t : ℝ},0 ≤ t →
      ∀ {u : Fin N → ℝ},u ∈ orderedSlackRegion N B t → ∀ i : Fin N,
        c*t*(rho^(N-i.val))⁻¹ ≤
          simplexScale (enlargementScale (fun r => 1+rowContractionError (m-r))) u i := by
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  let M := Real.exp rowContractionCost
  have hM : 0 < M := Real.exp_pos _
  refine ⟨c/M,div_pos hc hM,?_⟩
  intro m N hNm B t ht u hu i
  let κ : Fin N → ℝ := enlargementScale (fun r => 1+rowContractionError (m-r))
  have hkpos : 0 < κ i := enlargementScale_pos
    (fun r => by linarith only [rowContractionError_nonneg (m-r)]) i
  have hkM : κ i ≤ M := row_contraction_coordinate hNm i
  have hu0 := prefixRegion_coordinate_nonneg hu.1 i
  have huM := div_le_div_of_nonneg_right (orderedSlackRegion_coordinate_lower hu i) hM.le
  have hrenew := mul_le_mul_of_nonneg_left (hg (N-i.val)) ht
  have hlower := div_le_div_of_nonneg_right hrenew hM.le
  calc
    _ = (t*(c*(rho^(N-i.val))⁻¹))/M := by ring
    _ ≤ (t*g (N-i.val))/M := hlower
    _ ≤ u i/M := huM
    _ ≤ u i/κ i := div_le_div_of_nonneg_left hu0 hkpos hkM
    _ = _ := (simplexScale_apply _ _ _).symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NaturalShiftScale
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shift at a fixed distance below m(x) has the correct geometric scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem natural_shift_scale_lower : ∃ d : ℝ,0 < d ∧
    ∀ᶠ x : ℝ in atTop, ∀ n H : ℕ,0 < n → 1 ≤ H → n+H=m x →
      d*(rho^H)⁻¹ ≤ B x/((n:ℝ)*g (n+1)) := by
  obtain ⟨C,hC,hstep⟩ := uniform_step_bound fordRenewalInput
  refine ⟨rho/C,div_pos rho_pos hC,?_⟩
  filter_upwards [hstep,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro n H hn hH hNm
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hidx : H-1 ≤ m x := by omega
  have he : m x-(H-1)=n+1 := by omega
  have hh := hx (H-1) hidx
  rw [he] at hh
  have hsmall : (n:ℝ)*g (n+1)/B x ≤ C*rho^(H-1) := by
    apply le_trans _ hh
    apply div_le_div_of_nonneg_right _ hB.le
    apply mul_le_mul_of_nonneg_right _ (g_pos _).le
    exact_mod_cast Nat.le_succ n
  have hprod := (div_le_iff₀ hB).mp hsmall
  apply (le_div_iff₀ (mul_pos hn' (g_pos _))).mpr
  calc
    _ ≤ (rho/C*(rho^H)⁻¹)*(C*rho^(H-1)*B x) :=
      mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (div_pos rho_pos hC).le (inv_pos.mpr (pow_pos rho_pos H)).le)
    _ = B x := by
      rw [show rho^H=rho^(H-1)*rho by
        calc rho^H = rho^((H-1)+1) := by congr 1; omega
             _ = _ := pow_succ _ _]
      field_simp [rho_pos.ne',hC.ne']

theorem natural_contracted_coordinate_lower : ∃ d : ℝ,0 < d ∧
    ∀ᶠ x : ℝ in atTop, ∀ n H : ℕ,0 < n → 1 ≤ H → n+H=m x →
      ∀ K : ℝ,0 < K → ∀ u : Fin n → ℝ,
        u ∈ orderedSlackRegion n (B x) (K*B x/((n:ℝ)*g (n+1))) → ∀ i : Fin n,
          d*K*(rho^(m x-i.val))⁻¹ ≤
            simplexScale (enlargementScale
              (fun r => 1+rowContractionError (m x-r))) u i := by
  obtain ⟨d,hd,hscale⟩ := natural_shift_scale_lower
  obtain ⟨c,hc,hcoord⟩ := contracted_ordered_coordinate_lower
  refine ⟨c*d,mul_pos hc hd,?_⟩
  filter_upwards [hscale,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro n H hn hH hNm K hK u hu i
  have ht : 0 ≤ K*B x/((n:ℝ)*g (n+1)) :=
    div_nonneg (mul_pos hK hB).le (mul_nonneg (Nat.cast_nonneg _) (g_pos _).le)
  have hh := hcoord (by omega : n ≤ m x) ht hu i
  have hlo := mul_le_mul_of_nonneg_left (hx n H hn hH hNm) hK.le
  have hlo' : K*d*(rho^H)⁻¹ ≤ K*B x/((n:ℝ)*g (n+1)) := by
    simpa only [mul_assoc,mul_div_assoc] using hlo
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlo' hc.le) (inv_pos.mpr (pow_pos rho_pos (n-i.val))).le
  have hp : rho^H*rho^(n-i.val)=rho^(m x-i.val) := by
    rw [←pow_add]
    congr 1
    have := i.isLt
    omega
  have hid : (c*d)*K*(rho^(m x-i.val))⁻¹=
      (c*(K*d*(rho^H)⁻¹))*(rho^(n-i.val))⁻¹ := by
    rw [←hp,mul_inv_rev]
    ring
  exact hid.trans_le (hmul.trans hh)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ScaleVolumeLower
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower-volume bridge for the concrete diagonal prefix contraction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma simplexScale_volume_lower {N : ℕ} (κ : Fin N → ℝ)
    (hκ : ∀ i,0 < κ i) {S T : Set (Fin N → ℝ)}
    (hT : MeasurableSet T) (hfinite : volume T ≠ ⊤)
    (hmap : Set.MapsTo (simplexScale κ) S T) :
    volume.real S/(∏ i : Fin N,κ i) ≤ volume.real T := by
  have hp : 0 < ∏ i : Fin N,κ i := Finset.prod_pos (fun i _ => hκ i)
  have hdet : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hh := measure_mono (μ:=volume) (show S ⊆ simplexScale κ ⁻¹' T from hmap)
  rw [←Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hT,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet,simplexScale_det,inv_inv,
    abs_of_pos hp,Measure.smul_apply,smul_eq_mul] at hh
  have hr := ENNReal.toReal_mono
    (show ENNReal.ofReal (∏ i : Fin N,κ i)*volume T ≠ ⊤ from
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le] at hr
  apply (div_le_iff₀ hp).mpr
  simpa only [Measure.real,mul_comm] using hr

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_GeometricContractedFamily
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-volume prime-coordinate families with strict rows and geometric minima. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

lemma measurableSet_geometricContractedFamily (m n : ℕ) (B c : ℝ) :
    MeasurableSet (geometricContractedFamily m n B c) := by
  have hcoord : MeasurableSet {v : Fin n → ℝ | ∀ i,c*(rho^(m-i.val))⁻¹ ≤ v i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hgap : MeasurableSet {v : Fin n → ℝ | ∀ i j,i < j →
      v j ≤ v i/(1+rowContractionError (m-(i.val+1)))} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j => ?_))
    by_cases hij : i < j
    · simpa [hij] using
        (measurableSet_le (by fun_prop : Measurable (fun v : Fin n → ℝ => v j))
          (by fun_prop : Measurable
          (fun v : Fin n → ℝ => v i/(1+rowContractionError (m-(i.val+1))))))
    · simp [hij]
  exact (measurableSet_contractedPrefix _ _ _).inter (hcoord.inter hgap)

lemma prefixRegion_real_eq_G {x : ℝ} {n : ℕ} (hB : 0 ≤ B x) (hn : 0 < n) :
    volume.real (prefixRegion n (B x) 0 0)=G x n := by
  have he : volume (prefixRegion n (B x) 0 0)=ENNReal.ofReal (G x n) := by
    rw [volume_prefixRegion_explicit n hn]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hB]
    rw [G,prod_fin_shifted n g]
  rw [Measure.real,he,ENNReal.toReal_ofReal]
  unfold G
  exact div_nonneg (pow_nonneg hB _) (mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => (g_pos i).le)))

theorem geometric_contracted_volume_lower : ∃ c δ : ℝ,0 < c ∧ 0 < δ ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real (geometricContractedFamily (m x) (N+2) (B x) c) := by
  obtain ⟨K,δ,hK,hδ,hprefix⟩ := ordered_prefix_volume_lower
  obtain ⟨d,hd,hcoord⟩ := natural_contracted_coordinate_lower
  let M := Real.exp rowContractionCost
  have hM : 0 < M := Real.exp_pos _
  refine ⟨d*K,δ/M,mul_pos hd hK,div_pos hδ hM,?_⟩
  intro H hH
  obtain ⟨L,hL⟩ := eventually_atTop.mp hprefix
  filter_upwards [hcoord,m_tendsto.eventually (eventually_ge_atTop (L+2+H)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  intro N hN
  have hNL : L ≤ N := by omega
  have hn : N+2 ≤ m x := by omega
  let t := K*B x/((N+2:ℝ)*g (N+3))
  let S := orderedSlackRegion (N+2) (B x) t
  let T := geometricContractedFamily (m x) (N+2) (B x) (d*K)
  let β : ℕ → ℝ := fun r => 1+rowContractionError (m x-r)
  let κ : Fin (N+2) → ℝ := enlargementScale β
  have hβ (r) : 1 ≤ β r := by
    dsimp [β]
    linarith only [rowContractionError_nonneg (m x-r)]
  have hk (i) : 0 < κ i := enlargementScale_pos hβ i
  have hmap : Set.MapsTo (simplexScale κ) S T := by
    intro u hu
    have hv := reciprocal_enlargement_contracts hβ hu.1 hu.2.1
    refine ⟨⟨hv.1,hv.2.1,hv.2.2.1,?_⟩,?_,?_⟩
    · simpa only [β,Nat.sub_zero] using reciprocal_enlargement_top hβ hu.1
    · intro i
      have hh := hx (N+2) H (by omega) hH hN K hK u
        (by simpa only [Nat.cast_add,Nat.cast_ofNat,show N+2+1=N+3 by omega] using hu) i
      simpa only [mul_assoc] using hh
    · intro i j hij
      exact prefix_contraction_gap (fun i => hβ (i.val+1))
        (fun i => (hβ 0).trans (enlargementScale_top hβ i))
        (enlargementScale_step hβ) hu.1 hu.2.1 hij
  have hfinite : volume T ≠ ⊤ := by
    apply measure_ne_top_of_subset
      (fun _ hu => contractedPrefix_subset_prefixRegion (fun i => hβ (i.val+1)) hu.1)
    exact prefixRegion_volume_ne_top (by omega) _
  have hscaled := simplexScale_volume_lower κ hk
    (measurableSet_geometricContractedFamily _ _ _ _) hfinite hmap
  have hp : 0 < ∏ i : Fin (N+2),κ i := Finset.prod_pos (fun i _ => hk i)
  have hjac : (∏ i : Fin (N+2),κ i) ≤ M := row_contraction_jacobian hn
  have hmass : δ*G x (N+2) ≤ volume.real S := by
    have hh := hL N hNL (B x) hB
    rw [prefixRegion_real_eq_G hB.le (by omega)] at hh
    exact hh
  calc
    _ = (δ*G x (N+2))/M := by ring
    _ ≤ volume.real S/M := div_le_div_of_nonneg_right hmass hM.le
    _ ≤ volume.real S/(∏ i : Fin (N+2),κ i) :=
      div_le_div_of_nonneg_left ENNReal.toReal_nonneg hp hjac
    _ ≤ _ := hscaled

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadLimitedFamily
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed upper cutoff for the leading tail coordinate costs vanishing volume. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

lemma renewalSeries_two_thirds_gt_one : 1 < renewalSeries (2/3) := by
  have hs := summable_renewal (r:=2/3) (by norm_num) (by norm_num)
  have hh := hs.sum_le_tsum (Finset.range 3)
    (fun n _ => mul_nonneg (a_pos (by omega)).le (pow_nonneg (by norm_num) _))
  change _ ≤ renewalSeries (2/3) at hh
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  norm_num [Finset.sum_range_succ,a,h4] at hh
  nlinarith [Real.log_two_gt_d9,Real.log_three_gt_d9]

lemma rho_lt_two_thirds : rho < 2/3 := by
  by_contra! hh
  have hm := renewalSeries_strictMonoOn.monotoneOn
    (show (2/3:ℝ) ∈ Set.Ico (0:ℝ) 1 by norm_num)
    (show rho ∈ Set.Ico (0:ℝ) 1 from ⟨rho_pos.le,rho_lt_one⟩) hh
  rw [renewalSeries_rho] at hm
  linarith only [hm,renewalSeries_two_thirds_gt_one]

lemma geometric_family_subset_prefix {m n : ℕ} {B c : ℝ} (hB : 0 ≤ B) :
    geometricContractedFamily m n B c ⊆ prefixRegion n B 0 0 := by
  intro u hu
  have hp := contractedPrefix_subset_prefixRegion
    (fun i => by linarith only [rowContractionError_nonneg (m-(i.val+1))]) hu.1
  refine ⟨hp.1,?_⟩
  apply hp.2.trans
  simp only [sub_zero]
  exact div_le_self hB (by linarith only [rowContractionError_nonneg m])

lemma head_cap_failure_is_coordinate_bad {N m : ℕ} {B c : ℝ} (hB : 0 < B)
    {u : Fin (N+2) → ℝ} (hu : u ∈ geometricContractedFamily m (N+2) B c)
    (hfail : ¬ ∀ i,u i ≤ (3/4:ℝ)*B) :
    u ∈ fordCoordinateBad N B ⟨0,by omega⟩ := by
  obtain ⟨i,hi⟩ := not_forall.mp hfail
  have hi : (3/4:ℝ)*B < u i := lt_of_not_ge hi
  have hhead : u i ≤ u ⟨0,by omega⟩ := hu.1.2.1.antitone (by simp)
  let T := fordSimplexCenter N B ⟨0,by omega⟩
  have hdim : (0:ℝ) < N+2 := by positivity
  have hfactor : 0 < 1-1/(N+2:ℝ) := by
    have hh : (1:ℝ) < N+2 := by have := Nat.cast_nonneg (α:=ℝ) N; linarith
    exact sub_pos.mpr ((div_lt_one hdim).mpr hh)
  have hT : 0 < T := by
    simpa only [T,fordSimplexCenter,Fin.val_mk,Nat.cast_zero,zero_add,pow_one] using
      mul_pos (mul_pos hB rho_pos) hfactor
  have hTB : T ≤ (2/3:ℝ)*B := by
    dsimp [T,fordSimplexCenter]
    simp only [Nat.cast_zero,zero_add,pow_one]
    calc
      _ ≤ B*rho := mul_le_of_le_one_right (mul_nonneg hB.le rho_pos.le)
        (by
          have hdiv : 0 ≤ 1/(N+2:ℝ) := by positivity
          linarith only [hdiv])
      _ ≤ _ := by nlinarith only [rho_lt_two_thirds.le,hB.le]
  have hratio : (41/40:ℝ) < u ⟨0,by omega⟩/T := by
    apply (lt_div_iff₀ hT).mpr
    nlinarith only [hTB,hB,hi,hhead]
  change (1/40:ℝ) < |u ⟨0,by omega⟩/T-1|
  exact lt_of_lt_of_le (by linarith only [hratio]) (le_abs_self _)

theorem head_limited_volume_lower : ∃ c δ : ℝ,0 < c ∧ 0 < δ ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real (headLimitedFamily (m x) (N+2) (B x) c) := by
  obtain ⟨c,δ,hc,hδ,hvol⟩ := geometric_contracted_volume_lower
  obtain ⟨C,k,hC,hk,hcap⟩ := prefix_coordinate_concentration_unconditional
  have ht : Tendsto (fun N : ℕ => C*Real.exp (-k*(N+1:ℝ))) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-k)).le
      (Real.exp_lt_one_iff.mpr (by linarith only [hk]))).const_mul (C*Real.exp (-k))
    convert h using 1
    · ext N
      rw [←Real.exp_nat_mul,mul_assoc,←Real.exp_add]
      congr 2
      ring
    · ring_nf
  obtain ⟨L,hL⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (half_pos hδ)))
  refine ⟨c,δ/2,hc,half_pos hδ,?_⟩
  intro H hH
  filter_upwards [hvol H hH,m_tendsto.eventually (eventually_ge_atTop (L+H+3)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hm hB
  intro N hN
  have hNL : L ≤ N := by omega
  have hNpos : 0 < N := by omega
  let S := geometricContractedFamily (m x) (N+2) (B x) c
  let T := headLimitedFamily (m x) (N+2) (B x) c
  let E := prefixRegion (N+2) (B x) 0 0 ∩ fordCoordinateBad N (B x) ⟨0,by omega⟩
  have hsub : S ⊆ T ∪ E := by
    intro u hu
    by_cases h : ∀ i,u i ≤ (3/4:ℝ)*B x
    · exact Or.inl ⟨hu,h⟩
    · exact Or.inr ⟨geometric_family_subset_prefix hB.le hu,
        head_cap_failure_is_coordinate_bad hB hu h⟩
  have hfinite : volume (T ∪ E) ≠ ⊤ := by
    apply measure_ne_top_of_subset (s:=prefixRegion (N+2) (B x) 0 0)
    · intro u hu
      rcases hu with hu|hu
      · exact geometric_family_subset_prefix hB.le hu.1
      · exact hu.1
    · exact prefixRegion_volume_ne_top (by omega) _
  have hm := (measureReal_mono hsub hfinite).trans (measureReal_union_le T E)
  have he := hcap N (B x) hB ⟨0,by omega⟩ (by omega)
  have hG : volume.real (prefixRegion (N+2) (B x) 0 0)=G x (N+2) := prefixRegion_real_eq_G hB.le (by omega)
  have hbad : volume.real E ≤ (δ/2)*G x (N+2) := by
    have hn : N+2-(0+1)=N+1 := by omega
    simp only [hn,Nat.cast_add,Nat.cast_one] at he
    change volume.real E ≤ C*Real.exp (-k*(N+1:ℝ))*
      volume.real (prefixRegion (N+2) (B x) 0 0) at he
    rw [hG] at he
    exact he.trans (mul_le_mul_of_nonneg_right (hL N hNL).le (G_pos hB _).le)
  have hgood := hx N hN
  change δ*G x (N+2) ≤ volume.real S at hgood
  nlinarith only [hm,hbad,hgood]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentratedPrefix
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simultaneous coordinate upper envelope, with a fixed terminal buffer. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

lemma concentration_index_sum {c : ℝ} (hc : 0 < c) (N L : ℕ) :
    (∑ i ∈ prefixConcentrationIndices N L,
      Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ))) ≤
      Real.exp (-c*(L:ℝ))/(1-Real.exp (-c)) := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
  let K := (prefixConcentrationIndices N L).image (fun i => N+2-(i.val+1)-L)
  have hinj : Set.InjOn (fun i : Fin (N+2) => N+2-(i.val+1)-L)
      (↑(prefixConcentrationIndices N L)) := by
    intro i hi j hj he
    have hi := (Finset.mem_filter.mp hi).2
    have hj := (Finset.mem_filter.mp hj).2
    change N+2-(i.val+1)-L=N+2-(j.val+1)-L at he
    have hiLt := i.isLt
    have hjLt := j.isLt
    apply Fin.ext
    omega
  have he (i : Fin (N+2)) (hi : i ∈ prefixConcentrationIndices N L) :
      Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ)) =
        Real.exp (-c*(L:ℝ))*q^(N+2-(i.val+1)-L) := by
    have hi := (Finset.mem_filter.mp hi).2.2
    have hnat : N+2-(i.val+1)=L+(N+2-(i.val+1)-L) := by omega
    conv_lhs => rw [hnat,Nat.cast_add]
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (-c*(L:ℝ))*∑ j ∈ K,q^j := by
      rw [Finset.mul_sum,Finset.sum_image hinj]
      exact Finset.sum_congr rfl he
    _ ≤ Real.exp (-c*(L:ℝ))*∑' j : ℕ,q^j :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _
          (fun _ _ => pow_nonneg hq0 _)) (Real.exp_pos _).le
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1,div_eq_mul_inv]

lemma prefix_concentration_failure_bound : ∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ N L : ℕ,∀ B : ℝ,0 < B →
      volume.real (prefixConcentrationFailure N L B) ≤
        (C*Real.exp (-c*(L:ℝ))/(1-Real.exp (-c)))*
          volume.real (prefixRegion (N+2) B 0 0) := by
  obtain ⟨C,c,hC,hc,hbound⟩ := prefix_coordinate_concentration_unconditional
  refine ⟨C,c,hC,hc,?_⟩
  intro N L B hB
  apply (measureReal_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ i ∈ prefixConcentrationIndices N L,
        C*Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ))*
          volume.real (prefixRegion (N+2) B 0 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hbound N B hB i (Finset.mem_filter.mp hi).2.1
    _ = C*(∑ i ∈ prefixConcentrationIndices N L,
        Real.exp (-c*((N+2-(i.val+1):ℕ):ℝ)))*
          volume.real (prefixRegion (N+2) B 0 0) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (concentration_index_sum hc N L) hC.le
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_right hh (show 0 ≤ volume.real _ from ENNReal.toReal_nonneg)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LocallyConcentratedFamily
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive-volume candidate families with upper bounds at every local tail scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

lemma coordinate_cap_of_not_bad {N : ℕ} {B : ℝ} (hB : 0 < B)
    {i : Fin (N+2)} (hi : i.val < N) {u : Fin (N+2) → ℝ}
    (hu : u ∉ fordCoordinateBad N B i) :
    u i ≤ localCoordinateCap (N+2) B i := by
  have hn : (0:ℝ)<N+2 := by positivity
  have hidx : (i.val:ℝ)+1 < N+2 := by exact_mod_cast (show i.val+1 < N+2 by omega)
  have hd : 0 < 1-(i.val+1:ℝ)/(N+2) := by
    exact sub_pos.mpr ((div_lt_one hn).mpr hidx)
  have hcenter : 0 < fordSimplexCenter N B i :=
    mul_pos (mul_pos hB (pow_pos rho_pos _)) hd
  have hh : |u i/fordSimplexCenter N B i-1| ≤ 1/40 := le_of_not_gt hu
  have hupper := (abs_le.mp hh).2
  have hule : u i ≤ (41/40:ℝ)*fordSimplexCenter N B i := by
    apply (div_le_iff₀ hcenter).mp
    linarith only [hupper]
  have hcap : (41/40:ℝ)*fordSimplexCenter N B i ≤
      localCoordinateCap (N+2) B i := by
    have he : fordSimplexCenter N B i =
        B*rho^(i.val+1)*((N+2-i.val:ℕ)-1)/(N+2:ℝ) := by
      unfold fordSimplexCenter
      rw [Nat.cast_sub (by omega : i.val ≤ N+2)]
      simp only [Nat.cast_add,Nat.cast_ofNat]
      field_simp
      ring
    rw [he,localCoordinateCap]
    have hb : 0 ≤ B*rho^(i.val+1)/(N+2:ℝ) :=
      div_nonneg (mul_nonneg hB.le (pow_pos rho_pos _).le) hn.le
    have hni : (0:ℝ) ≤ (N+2-i.val:ℕ) := Nat.cast_nonneg _
    calc
      _ = (B*rho^(i.val+1)/(N+2:ℝ))*((41/40:ℝ)*((N+2-i.val:ℕ)-1)) := by ring
      _ ≤ (B*rho^(i.val+1)/(N+2:ℝ))*(2*(N+2-i.val:ℕ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hni]) hb
      _ = _ := by push_cast <;> ring
  exact hule.trans hcap

lemma local_family_failure_subset {m N L : ℕ} {B c : ℝ}
    (hB : 0 < B) (hL : 1 ≤ L) :
    headLimitedFamily m (N+2) B c ⊆
      locallyConcentratedFamily m (N+2) B c L ∪ prefixConcentrationFailure N L B := by
  intro u hu
  by_cases hc : ∀ i : Fin (N+2),i.val+L+2 ≤ N+2 →
      u i ≤ localCoordinateCap (N+2) B i
  · exact Or.inl ⟨hu,hc⟩
  · right
    push Not at hc
    obtain ⟨i,hi,hbad⟩ := hc
    have hiN : i.val < N := by omega
    apply Set.mem_iUnion.mpr
    refine ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiN,by omega⟩,?_⟩⟩
    refine ⟨geometric_family_subset_prefix hB.le hu.1,?_⟩
    by_contra hnot
    exact (not_le.mpr hbad) (coordinate_cap_of_not_bad hB hiN hnot)

theorem locally_concentrated_volume_lower_oai : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real
          (locallyConcentratedFamily (m x) (N+2) (B x) c L) := by
  obtain ⟨c,δ,hc,hδ,hvolume⟩ := head_limited_volume_lower
  obtain ⟨C,k,hC,hk,hfailure⟩ := prefix_concentration_failure_bound
  have hq : Real.exp (-k)<1 := Real.exp_lt_one_iff.mpr (by linarith only [hk])
  have ht : Tendsto (fun L : ℕ => C*Real.exp (-k*(L:ℝ))/(1-Real.exp (-k)))
      atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-k)).le hq).const_mul C
    convert hh.div_const (1-Real.exp (-k)) using 1
    · funext L
      rw [←Real.exp_nat_mul]
      congr 2
      ring_nf
    · simp
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (half_pos hδ)))
  let L := max J 1
  have hL : 1 ≤ L := le_max_right _ _
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  intro H hH
  filter_upwards [hvolume H hH,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hN
  let S := headLimitedFamily (m x) (N+2) (B x) c
  let T := locallyConcentratedFamily (m x) (N+2) (B x) c L
  let E := prefixConcentrationFailure N L (B x)
  have hsub : S ⊆ T ∪ E := local_family_failure_subset hB hL
  have hfinite : volume (T ∪ E) ≠ ⊤ := by
    apply measure_ne_top_of_subset (s:=prefixRegion (N+2) (B x) 0 0)
    · intro u hu
      rcases hu with hu|hu
      · exact geometric_family_subset_prefix hB.le hu.1.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
        obtain ⟨_,hi⟩ := Set.mem_iUnion.mp hi
        exact hi.1
    · exact prefixRegion_volume_ne_top (by omega) _
  have hm := (measureReal_mono hsub hfinite).trans (measureReal_union_le T E)
  have he := hfailure N L (B x) hB
  have hG := prefixRegion_real_eq_G hB.le (by omega : 0 < N+2)
  rw [hG] at he
  have hb : volume.real E ≤ (δ/2)*G x (N+2) :=
    he.trans (mul_le_mul_of_nonneg_right (hJ L (le_max_left _ _)).le (G_pos hB _).le)
  have hs := hx N hN
  change δ*G x (N+2) ≤ volume.real S at hs
  nlinarith only [hm,hb,hs]

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.locally_concentrated_volume_lower_oai := @OAI.TotientAsymptotic.locally_concentrated_volume_lower_oai
