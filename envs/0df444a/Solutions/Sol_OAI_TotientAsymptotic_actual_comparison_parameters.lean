-- Prove2me | solution 1 for OAI.TotientAsymptotic.actual_comparison_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:55.901413+00:00
-- url     : https://prove2.me/submissions/669a1439-02f8-47a6-b84c-b5f0db704c75

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Renewal
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedComparison
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The published comparison input for the conditional collision proof.

Kevin Ford, *The distribution of totients*, Ramanujan J. 2 (1998), 67–151,
revised arXiv:1104.3264v2 (14 July 2013), Lemma 5.1, pp. 21–22.
The published statement permits `k ≥ 1`, including a single surviving
prime. The author-hosted copy also makes this endpoint explicit:
https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf (Lemma 5.1).
We use its specialization with no auxiliary factors (`l = 0`) and with
the entire left shifted product squarefree above the terminal cutoff. The
latter is already part of the application’s good-witness conditions. All its
cutoff, small-remainder, small-cancelled-product and separation hypotheses
are retained here. Its larger smooth-factor exponent is sufficient for the
application; we do not assume the new comparison proposition of the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma squarefreeAbove_of_dvd {m n : ℕ} {Z : ℝ}
    (hmn : m ∣ n) (hn : SquarefreeAbove n Z) : SquarefreeAbove m Z := by
  intro p hp hpZ hpm
  exact hn p hp hpZ (hpm.trans hmn)

lemma shifted_factor_dvd {b : ℕ} (p : Fin b → ℕ) (i : Fin b) :
    p i-1 ∣ shiftedProduct p :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalityAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma omegaIn_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (U T : ℝ) :
    omegaIn (∏ i ∈ s, f i) U T = ∑ i ∈ s, omegaIn (f i) U T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [omegaIn]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      omegaIn_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma omegaIn_eq_zero_of_largest_le {n : ℕ} {U T : ℝ}
    (hn : (largestPrimeFactor n : ℝ) ≤ U) : omegaIn n U T = 0 := by
  unfold omegaIn
  have he : n.primeFactorsList.filter
      (fun p : ℕ => decide (U < (p : ℝ) ∧ (p : ℝ) ≤ T)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro h
    have hle : (p : ℝ) ≤ largestPrimeFactor n := by exact_mod_cast primeFactor_le_largest hp
    linarith [h.1]
  rw [he]
  rfl

lemma normality_interval_bounds {S U T ε : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hSU : S ≤ U) (hUT : U < T)
    (hTp : T ≤ (p-1 : ℕ)) (hε : Real.sqrt (B S * B T) ≤ ε) :
    B T-B U-ε ≤ (omegaIn (p-1) U T : ℝ) ∧
      (omegaIn (p-1) U T : ℝ) ≤ B T-B U+ε := by
  have h := abs_lt.mp (hp.2.2 U T hSU hUT hTp)
  constructor <;> linarith

/-- Equal products force close largest-factor locations. The left side has
`j+1` normal shifts reaching the interval, while only `j` right shifts can
reach it. Smooth residual factors contribute nothing. -/
theorem normality_alignment {k D D' : ℕ} (p q : Fin k → ℕ) (j : Fin k)
    {S U T ε : ℝ} (hD : D ≠ 0) (hD' : D' ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (hprod : D * shiftedProduct p = D' * shiftedProduct q)
    (hDs : (largestPrimeFactor D : ℝ) ≤ U)
    (hD's : (largestPrimeFactor D' : ℝ) ≤ U)
    (hSU : S ≤ U) (hUT : U < T) (hε : Real.sqrt (B S * B T) ≤ ε)
    (hpT : ∀ i ≤ j, T ≤ (p i-1 : ℕ))
    (hqT : ∀ i < j, T ≤ (q i-1 : ℕ))
    (hqsmall : ∀ i, j ≤ i → (largestPrimeFactor (q i-1) : ℝ) ≤ U) :
    B T-B U ≤ (2*(j.val : ℝ)+1)*ε := by
  have hp0 (i : Fin k) : p i-1 ≠ 0 := by have := (hp i).1.two_le; omega
  have hq0 (i : Fin k) : q i-1 ≠ 0 := by have := (hq i).1.two_le; omega
  have hcount : (∑ i : Fin k, omegaIn (p i-1) U T) =
      ∑ i : Fin k, omegaIn (q i-1) U T := by
    have h := congrArg (fun n => omegaIn n U T) hprod
    unfold shiftedProduct at h
    rw [omegaIn_mul hD (Finset.prod_ne_zero_iff.mpr (fun i _ => hp0 i)),
      omegaIn_mul hD' (Finset.prod_ne_zero_iff.mpr (fun i _ => hq0 i)),
      omegaIn_eq_zero_of_largest_le hDs, omegaIn_eq_zero_of_largest_le hD's,
      zero_add, zero_add] at h
    simpa only [shiftedProduct, omegaIn_prod _ _ (fun i _ => hp0 i),
      omegaIn_prod _ _ (fun i _ => hq0 i)] using h
  have hcountR : (∑ i : Fin k, (omegaIn (p i-1) U T : ℝ)) =
      ∑ i : Fin k, (omegaIn (q i-1) U T : ℝ) := by exact_mod_cast hcount
  have hlo : ((j.val+1 : ℕ) : ℝ) * (B T-B U-ε) ≤
      ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) := by
    calc
      _ = ∑ _i ∈ Finset.Iic j, (B T-B U-ε) := by simp [Fin.card_Iic] <;> ring
      _ ≤ ∑ i ∈ Finset.Iic j, (omegaIn (p i-1) U T : ℝ) := by
        exact Finset.sum_le_sum (fun i hi =>
          (normality_interval_bounds (hp i) hSU hUT (hpT i (Finset.mem_Iic.mp hi)) hε).1)
      _ ≤ ∑ i : Fin k, (omegaIn (p i-1) U T : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => Nat.cast_nonneg _)
  have hhi : (∑ i : Fin k, (omegaIn (q i-1) U T : ℝ)) ≤
      (j.val : ℝ) * (B T-B U+ε) := by
    calc
      _ = ∑ i ∈ Finset.Iio j, (omegaIn (q i-1) U T : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hji : j ≤ i := le_of_not_gt (by simpa using hi)
        rw [omegaIn_eq_zero_of_largest_le (hqsmall i hji), Nat.cast_zero]
      _ ≤ ∑ _i ∈ Finset.Iio j, (B T-B U+ε) :=
        Finset.sum_le_sum (fun i hi =>
          (normality_interval_bounds (hq i) hSU hUT (hqT i (Finset.mem_Iio.mp hi)) hε).2)
      _ = _ := by simp [Fin.card_Iio] <;> ring
  rw [hcountR] at hlo
  push_cast at hlo
  nlinarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness of the residual totient in an actual basic collision witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma largestPrimeFactor_le_of_prime_divisors {n z : ℕ} (hz : 1 ≤ z)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → n ≠ 0 → p ≤ z) : largestPrimeFactor n ≤ z := by
  apply max_le hz
  apply Finset.sup_le
  intro p hp
  obtain ⟨hp', hd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact h p hp' hd hn

lemma prime_dvd_le_largest {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hd : p ∣ n) :
    p ≤ largestPrimeFactor n :=
  primeFactor_le_largest ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hd)

/-- Taking a totient cannot introduce a prime larger than every prime of its
argument. This also covers `n = 0` under the existing largest-factor convention. -/
lemma largestPrimeFactor_totient_le (n : ℕ) :
    largestPrimeFactor n.totient ≤ largestPrimeFactor n := by
  by_cases hn : n = 0
  · subst n
    simp [largestPrimeFactor]
  apply largestPrimeFactor_le_of_prime_divisors (le_max_left _ _)
  intro q hq hqφ _
  have hdiv : q ∣ n*∏ p ∈ n.primeFactors, (p-1) := by
    rw [← Nat.totient_mul_prod_primeFactors]
    exact hqφ.trans (dvd_mul_right _ _)
  rcases hq.dvd_mul.mp hdiv with hqn | hqp
  · exact prime_dvd_le_largest hq hn hqn
  · obtain ⟨p, hp, hqp⟩ := hq.prime.dvd_finsetProd_iff (fun p : ℕ => p-1) |>.mp hqp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hpp.one_lt) hqp
    exact hle.trans ((Nat.sub_le _ _).trans
      (prime_dvd_le_largest hpp hn (Nat.mem_primeFactors.mp hp).2.1))

lemma largestPrimeFactor_mul_le {a b z : ℕ}
    (ha : largestPrimeFactor a ≤ z) (hb : largestPrimeFactor b ≤ z) :
    largestPrimeFactor (a*b) ≤ z := by
  apply largestPrimeFactor_le_of_prime_divisors ((le_max_left _ _).trans ha)
  intro p hp hd hn
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · exact (prime_dvd_le_largest hp (left_ne_zero_of_mul hn) hpa).trans ha
  · exact (prime_dvd_le_largest hp (right_ne_zero_of_mul hn) hpb).trans hb

lemma largestPrimeFactor_prod_le {ι : Type*} (I : Finset ι) (f : ι → ℕ) {z : ℕ}
    (hz : 1 ≤ z) (hf : ∀ i ∈ I, largestPrimeFactor (f i) ≤ z) :
    largestPrimeFactor (∏ i ∈ I, f i) ≤ z := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa [largestPrimeFactor] using hz
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi]
    exact largestPrimeFactor_mul_le (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma largestPrimeFactor_prime {p : ℕ} (hp : p.Prime) : largestPrimeFactor p = p := by
  simp [largestPrimeFactor, hp.primeFactors, max_eq_right hp.one_lt.le]

/-- The actual residual integer after a cutoff is smooth below the next
prime. The final cofactor may repeat the last displayed prime. -/
theorem basic_suffix_totient_smooth {x : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hj : j < L x H) :
    largestPrimeFactor (suffixPreimage η j).totient ≤ remainderPrime η (j+1) := by
  apply (largestPrimeFactor_totient_le _).trans
  unfold suffixPreimage
  have hj' : j+1 ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hp := (hη.2.1 (j+1) hj').1
  apply largestPrimeFactor_mul_le
  · apply hη.2.2.2.1.trans
    rcases eq_or_lt_of_le (show j+1 ≤ L x H by omega) with he | he
    · rw [he]
    · exact (basic_remainder_prime_strictAnti hη hj'
        (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) he (he.trans hL)).le
  · apply largestPrimeFactor_prod_le _ _ hp.one_lt.le
    intro r hr
    have hr' : r ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
    rw [largestPrimeFactor_prime (hη.2.1 r hr').1]
    rcases eq_or_lt_of_le (Finset.mem_Icc.mp hr).1 with he | he
    · rw [he]
    · exact (basic_remainder_prime_strictAnti hη hj' hr' he
        ((Finset.mem_Icc.mp hj').2.trans_lt hL)).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionAlgebra
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cancellation and the strict-slack comparison for the surviving prime indices. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Deleting matching primes cancels exactly their shifts, retaining all
multiplicity in the residual integer. -/
theorem cancel_equal_shifts {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p q : ι → ℕ) (D D' : ℕ)
    (hp : ∀ i ∈ I, 2 ≤ p i)
    (hprod : D*(∏ i ∈ I, (p i-1)) = D'*(∏ i ∈ I, (q i-1))) :
    D*(∏ i ∈ I.filter (fun i => p i ≠ q i), (p i-1)) =
      D'*(∏ i ∈ I.filter (fun i => p i ≠ q i), (q i-1)) := by
  classical
  let C := ∏ i ∈ I.filter (fun i => p i = q i), (p i-1)
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i hi
    have := hp i (Finset.mem_filter.mp hi).1
    omega
  have hcq : (∏ i ∈ I.filter (fun i => p i = q i), (q i-1)) = C := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hleft : (∏ i ∈ I, (p i-1)) =
      C*(∏ i ∈ I.filter (fun i => p i ≠ q i), (p i-1)) := by
    exact (Finset.prod_filter_mul_prod_filter_not I (fun i => p i=q i) _).symm
  have hright : (∏ i ∈ I, (q i-1)) =
      C*(∏ i ∈ I.filter (fun i => p i ≠ q i), (q i-1)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not I (fun i => p i=q i) _, hcq]
  rw [hleft, hright] at hprod
  apply Nat.eq_of_mul_eq_mul_left hC
  nlinarith [hprod]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessCollision
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact comparison data extracted from two basic witnesses for colliding tuples. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma wholeWitness_shift_product {x : ℝ} {H k : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) :
    (∏ r ∈ Finset.Icc 0 k, (wholeWitnessPrime p η r-1)) =
      (p-1)*∏ r ∈ Finset.Icc 1 k, (remainderPrime η r-1) := by
  have hsplit : Finset.Icc 0 k = insert 0 (Finset.Icc 1 k) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.prod_insert (by simp)]
  simp only [wholeWitnessPrime, ite_true, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- Every valid cutoff gives the same integer value. No witness representative
is discarded from the tail totient. -/
lemma witness_tuple_value_at_cut {x : ℝ} {H k : ℕ} {p : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) :
    tupleValue (witnessTuple p η) = (suffixPreimage η k).totient *
      ∏ r ∈ Finset.Icc 0 k, (wholeWitnessPrime p η r-1) := by
  have hRsplit := basic_suffix_totient_split hη hL (Nat.zero_le (R x H)) hR
  have hksplit := basic_suffix_totient_split hη hL (Nat.zero_le k) hk
  simp only [Nat.zero_add] at hRsplit hksplit
  have hprod : (∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1)) =
      ∏ r ∈ Finset.Icc 1 (R x H), (remainderPrime η r-1) :=
    prod_fin_shifted (R x H) (fun r => (remainderPrime η r-1))
  unfold tupleValue witnessTuple tuplePrimes prefixOfRemainder
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hprod]
  rw [← suffixPreimage_at_R η, wholeWitness_shift_product]
  calc
    _ = (p-1)*((suffixPreimage η (R x H)).totient*
        ∏ r ∈ Finset.Icc 1 (R x H), (remainderPrime η r-1)) := by ring
    _ = (p-1)*(suffixPreimage η 0).totient := by rw [hRsplit]
    _ = _ := by rw [hksplit]; ring

/-- Cancel all matched primes up to the cutoff, including the common prefix.
The first differing prime survives, and at most `k-i+1` indices survive. -/
theorem witness_collision_cancel {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ)
    (hp : p.Prime) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η) = tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j = wholeWitnessPrime q ξ j) :
    let I := (Finset.Icc 0 k).filter (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j)
    (suffixPreimage η k).totient*(∏ j ∈ I, (wholeWitnessPrime p η j-1)) =
      (suffixPreimage ξ k).totient*(∏ j ∈ I, (wholeWitnessPrime q ξ j-1)) ∧
    i ∈ I ∧ I.card ≤ k-i+1 := by
  classical
  dsimp only
  have hval : (suffixPreimage η k).totient*
      (∏ j ∈ Finset.Icc 0 k, (wholeWitnessPrime p η j-1)) =
      (suffixPreimage ξ k).totient*
      (∏ j ∈ Finset.Icc 0 k, (wholeWitnessPrime q ξ j-1)) := by
    simpa only [witness_tuple_value_at_cut hη hL hR hk,
      witness_tuple_value_at_cut hξ hL hR hk] using hv
  refine ⟨cancel_equal_shifts _ _ _ _ _ ?_ hval, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j=0
    · simp only [wholeWitnessPrime, hj0, ite_true, if_true]
      exact hp.two_le
    · simp only [wholeWitnessPrime, ite_eq_right hj0]
      exact (hη.2.1 j (Finset.mem_Icc.mpr
        ⟨by omega, (Finset.mem_Icc.mp hj).2.trans hk.le⟩)).1.two_le
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hik⟩, hfirst⟩
  · have hsub : (Finset.Icc 0 k).filter
        (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j) ⊆ Finset.Icc i k := by
      intro j hj
      obtain ⟨hj, hne⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hj).2⟩
      by_contra! hh
      exact hne (hcommon j hh)
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    omega

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

lemma next_band_below_ford_cutoff : ∀ᶠ x : ℝ in atTop, ∀ j < m x,
    (11/10 : ℝ)*bandScale x (j+1) < (7/10 : ℝ)*fordBandScale x j := by
  filter_upwards [fordBandScale_uniform_comparison (ε := 1/100) (by norm_num)] with x hx
  intro j hj
  have hp := bandScale_pos hj
  have hd := (lt_div_iff₀ hp).mp (show (99/100 : ℝ) < fordBandScale x j/bandScale x j by
    linarith [(abs_lt.mp (hx j hj)).1])
  have hn := bandScale_succ_le x j
  have hr := collision_rho_bounds.2
  have hρ := mul_lt_mul_of_pos_right hr hp
  nlinarith

theorem basic_residual_ford_smooth : ∀ᶠ x : ℝ in atTop, ∀ H j : ℕ,
    L x H < m x → j < L x H → ∀ η : RemainderDatum (L x H),
    IsBasicRemainder x H η →
    (largestPrimeFactor (suffixPreimage η j).totient : ℝ) <
      Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x j)) := by
  filter_upwards [next_band_below_ford_cutoff] with x hx
  intro H j hL hj η hη
  have hp := hη.2.1 (j+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  have hpos : (1 : ℝ) < remainderPrime η (j+1) := by exact_mod_cast hp.1.one_lt
  have hc : B (remainderPrime η (j+1)) < (7/10 : ℝ)*fordBandScale x j :=
    hp.2.2.trans_lt (hx j (hj.trans hL))
  have hprime : (remainderPrime η (j+1) : ℝ) <
      Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x j)) := by
    apply (Real.log_lt_iff_lt_exp (zero_lt_one.trans hpos)).mp
    exact (Real.log_lt_iff_lt_exp (Real.log_pos hpos)).mp hc
  exact lt_of_le_of_lt (by exact_mod_cast basic_suffix_totient_smooth hη hL hj) hprime

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

lemma cube_root_le_scaled {h : ℕ} {b : ℝ} (hh : 1 ≤ h) (hb : (h : ℝ)^33 ≤ b) :
    b^(1/3 : ℝ) ≤ b/(h : ℝ)^21 := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := lt_of_lt_of_le zero_lt_one h1
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hpow : (h : ℝ)^63 ≤ b^2 := by
    calc
      _ ≤ (h : ℝ)^66 := pow_le_pow_right₀ h1 (by omega)
      _ = ((h : ℝ)^33)^2 := by ring
      _ ≤ b^2 := pow_le_pow_left₀ (by positivity) hb _
  have hcube : b ≤ (b/(h : ℝ)^21)^3 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos (pow_pos h0 _) _)).mpr
    have hp := mul_le_mul_of_nonneg_left hpow hb0.le
    first | (convert hp using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hp.trans (le_of_eq (by ring)))
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  rw [he]
  exact hcube

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

lemma scaled_cube_root_lt {h : ℕ} {b : ℝ} (hh : 10 ≤ h) (hb : (h : ℝ)^33 ≤ b) :
    b^(1/3 : ℝ) < (7/10 : ℝ)*(rho/(2*(h : ℝ)^20)*b) := by
  have h1 : 1 ≤ h := by omega
  have hhR : (10 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := by linarith
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hc : 2 < (7/10 : ℝ)*rho*h := by
    have hp := mul_le_mul_of_nonneg_left hhR
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7/10) rho_pos.le)
    nlinarith [collision_rho_bounds.1]
  apply (cube_root_le_scaled h1 hb).trans_lt
  have hs : 1/(h : ℝ) < (7/10 : ℝ)*rho/2 := by
    apply (div_lt_iff₀ h0).mpr
    linarith
  have hm := mul_lt_mul_of_pos_right hs (div_pos hb0 (pow_pos h0 20))
  convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

/-- The normality scale lies strictly below the smooth-residual cutoff,
uniformly for all retained collision indices. -/
theorem collision_normality_below_cutoff : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i ≤ R x H,
      normalityScale x i < collisionSmoothCutoff x i := by
  filter_upwards [eventually_collision_indices,ford_band_polynomial_lower 33,
    eventually_ge_atTop 10] with H hind hpoly hH
  filter_upwards [hpoly,B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hp hB hm
  intro i hi
  obtain ⟨hHi,hJ,_⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hb := hp i him hHi
  have hr := (ford_collision_layer_ratio hB him hJ).1
  have hb0 := fordBandScale_pos (zero_lt_one.trans hB) him
  have hl : rho/(2*((m x-i : ℕ) : ℝ)^20)*fordBandScale x i ≤
      fordBandScale x (collisionLastIndex x i) := (le_div_iff₀ hb0).mp hr
  apply Real.exp_lt_exp.mpr
  apply Real.exp_lt_exp.mpr
  exact (scaled_cube_root_lt (hH.trans hHi) hb).trans_le
    (mul_le_mul_of_nonneg_left hl (by norm_num))

theorem collision_residual_below_cutoff : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i ≤ R x H, ∀ η : RemainderDatum (L x H),
      IsBasicRemainder x H η →
      (largestPrimeFactor (collisionResidual η i) : ℝ) < collisionSmoothCutoff x i := by
  filter_upwards [eventually_collision_indices,P_tendsto.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 2] with H hind hP hH
  filter_upwards [basic_residual_ford_smooth,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hx hm
  intro i hi η hη
  exact hx H (collisionLastIndex x i) (by unfold L; omega) (hind x hm i hi).2.2 η hη

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGridScale
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially small normalized alignment mesh at each actual collision cut. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cube_root_le_div_pow {h k : ℕ} {b : ℝ} (hh : 1 ≤ h)
    (hb : (h : ℝ)^(3*k) ≤ b) : b^(1/3 : ℝ) ≤ b/(h : ℝ)^(2*k) := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have h0 : (0 : ℝ) < h := zero_lt_one.trans_le h1
  have hb0 : 0 < b := (pow_pos h0 _).trans_le hb
  have hp : (h : ℝ)^(6*k) ≤ b^2 := by
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (h : ℝ)^(3*k)) hb 2
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  have hc : b ≤ (b/(h : ℝ)^(2*k))^3 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((h : ℝ)^(2*k))^3)).mpr
    have hs := mul_le_mul_of_nonneg_left hp hb0.le
    convert hs using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  rwa [he]

lemma collisionMesh_pos {x y : ℝ} {i : ℕ} (hb : 0 < fordBandScale x i) (hy : 0 < B y) :
    0 < collisionMesh x y i := by
  have hs : B (normalityScale x i)=(fordBandScale x i)^(1/3 : ℝ) := by
    simp only [B,normalityScale,Real.log_exp]
  unfold collisionMesh
  rw [hs]
  exact div_pos (Real.sqrt_pos.mpr (mul_pos (Real.rpow_pos_of_pos hb _) hy)) hy

/-- The actual normalized alignment error is smaller than an arbitrary fixed
polynomial mesh; exponent 32 suffices for the retained collision grid. -/
theorem collisionMesh_bound : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 0 < B y → fordBandScale x i/2 ≤ B y →
    collisionMesh x y i ≤ 2/((m x-i : ℕ) : ℝ)^32 := by
  filter_upwards [ford_band_polynomial_lower 96,eventually_ge_atTop 1] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hBy hlo
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hh : 1 ≤ m x-i := hH.trans hHi
  have h0 : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast hh
  have hb := hx i him hHi
  have hb0 : 0 < fordBandScale x i := (pow_pos h0 96).trans_le hb
  have hs : B (normalityScale x i) ≤ fordBandScale x i/((m x-i : ℕ) : ℝ)^64 := by
    simpa only [B,normalityScale,Real.log_exp] using cube_root_le_div_pow (k := 32) hh hb
  have hsq : B (normalityScale x i)*B y ≤
      (2/((m x-i : ℕ) : ℝ)^32*B y)^2 := by
    have hbY : fordBandScale x i ≤ 2*B y := by linarith
    have ht : B (normalityScale x i) ≤ (2*B y)/((m x-i : ℕ) : ℝ)^64 :=
      hs.trans (div_le_div_of_nonneg_right hbY (pow_pos h0 _).le)
    have hp := mul_le_mul_of_nonneg_right ht hBy.le
    have he : (2/((m x-i : ℕ) : ℝ)^32*B y)^2 =
        4*(B y)^2/((m x-i : ℕ) : ℝ)^64 := by ring
    rw [he]
    calc
      _ ≤ (2*B y)/((m x-i : ℕ) : ℝ)^64*B y := hp
      _ = 2*((B y)^2/((m x-i : ℕ) : ℝ)^64) := by ring
      _ ≤ 4*((B y)^2/((m x-i : ℕ) : ℝ)^64) := by
        have hn : 0 ≤ (B y)^2/((m x-i : ℕ) : ℝ)^64 := by positivity
        linarith
      _ = _ := by ring
  apply (div_le_iff₀ hBy).mpr
  exact (Real.sqrt_le_iff).mpr ⟨by positivity,hsq⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonErrorBudget
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit rounding and normality errors fit inside the strict-slack saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collisionMesh_eq_sqrt_ratio {x y : ℝ} {i : ℕ}
    (hS : 0 ≤ B (normalityScale x i)) :
    collisionMesh x y i=Real.sqrt (B (normalityScale x i)/B y) := by
  rw [collisionMesh,Real.sqrt_mul hS,Real.sqrt_div hS,mul_div_assoc,Real.sqrt_div_self]
  rfl

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

/-- The loss of one plus the logarithm of the normality factor is uniformly
absorbed by one percent of the smallest retained collision band. -/
theorem collision_log_loss_small : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 0 < B y → B y ≤ 2*fordBandScale x i →
    1+Real.log (3*B y) ≤ (1/100 : ℝ)*bandScale x (collisionLastIndex x i) := by
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (ford_band_polynomial_lower 2)
  filter_upwards [eventually_collision_indices,eventually_ge_atTop (2*H₀),
    eventually_ge_atTop 100000] with H hind hthreshold hH
  filter_upwards [ford_band_log_upper,hH₀ H₀ le_rfl,
    fordBandScale_uniform_comparison (ε := 1) (by norm_num),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hlog hp hcompare hm
  intro i hi y hBy hByu
  obtain ⟨hHi,hcut,hk⟩ := hind x hm i hi
  have him : i < m x := by unfold R at hi; omega
  have hkm : collisionLastIndex x i < m x := by
    unfold collisionLastIndex
    omega
  have hh : (100000 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
  have hhalf : (m x-i : ℕ) ≤ 2*(m x-collisionLastIndex x i) := by
    unfold collisionLastIndex
    omega
  have hp' : ((m x-collisionLastIndex x i : ℕ) : ℝ)^2 ≤ fordBandScale x (collisionLastIndex x i) := by
    apply hp (collisionLastIndex x i) hkm
    have hcutH : H₀ ≤ m x-collisionLastIndex x i := by omega
    exact hcutH
  have hb := bandScale_pos hkm
  have hfu : fordBandScale x (collisionLastIndex x i) ≤ 2*bandScale x (collisionLastIndex x i) := by
    apply le_of_lt
    apply (div_lt_iff₀ hb).mp
    linarith [(abs_lt.mp (hcompare _ hkm)).2]
  have hlogy : Real.log (3*B y) ≤ 26*(m x-i : ℕ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans (hlog i him)
  have hhalfR : ((m x-i : ℕ) : ℝ) ≤ 2*(m x-collisionLastIndex x i : ℕ) := by exact_mod_cast hhalf
  have hh0 : (0 : ℝ) ≤ (m x-i : ℕ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ hh0 hhalfR 2
  have hgrowth := mul_le_mul_of_nonneg_left hh hh0
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalitySize
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total factor counts and largest-factor locations for normal shifts. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

private lemma interval_count_partition (l : List ℕ) (n : ℕ) (S : ℝ)
    (hl : ∀ p ∈ l, 1 < p ∧ p ≤ n) :
    (l.filter (fun p : ℕ => decide ((1 : ℝ) < p ∧ (p : ℝ) ≤ S))).length +
      (l.filter (fun p : ℕ => decide (S < p ∧ (p : ℝ) ≤ n))).length = l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp.1
    have hn : (p : ℝ) ≤ n := by exact_mod_cast hp.2
    have hh := ih (fun q hq => hl q (by simp [hq]))
    by_cases hS : (p : ℝ) ≤ S
    · rw [List.filter_cons_of_pos (by exact decide_eq_true ⟨h1, hS⟩),
        List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ (S < (p : ℝ) ∧ (p : ℝ) ≤ n) from fun h => (not_lt.mpr hS) h.1)),
        List.length_cons]
      simp only [List.length_cons]
      omega
    · have hS' : S < (p : ℝ) := lt_of_not_ge hS
      rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using
          (show ¬ ((1 : ℝ) < p ∧ (p : ℝ) ≤ S) from fun h => hS h.2)),
        List.filter_cons_of_pos (by exact decide_eq_true ⟨hS', hn⟩),
        List.length_cons]
      simp only [List.length_cons]
      omega

lemma omegaIn_partition (n : ℕ) (S : ℝ) :
    omegaIn n 1 S + omegaIn n S n = n.primeFactorsList.length := by
  apply interval_count_partition
  intro p hp
  exact ⟨(Nat.prime_of_mem_primeFactorsList hp).one_lt, Nat.le_of_mem_primeFactorsList hp⟩

/-- Ford normality controls the full number of prime occurrences of a shift. -/
lemma normality_total_bound {S : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hSn : S < (p-1 : ℕ)) (hBS : 0 ≤ B S) :
    (p-1).primeFactorsList.length ≤ 3*B (p-1 : ℕ) := by
  have hn : (1 : ℝ) < (p-1 : ℕ) := hS.trans hSn
  have hB : B S ≤ B (p-1 : ℕ) := by
    apply Real.log_le_log (Real.log_pos hS)
    exact Real.log_le_log (zero_lt_one.trans hS) hSn.le
  have hBn : 0 ≤ B (p-1 : ℕ) := hBS.trans hB
  have hsqrt : Real.sqrt (B S*B (p-1 : ℕ)) ≤ B (p-1 : ℕ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hBn, by nlinarith⟩
  have hc := hp.2.2 S (p-1 : ℕ) le_rfl hSn le_rfl
  have hh := (abs_lt.mp hc).2
  have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
  push_cast at he
  linarith [hp.2.1]

lemma self_le_largest_pow_length {n : ℕ} (hn : n ≠ 0) :
    n ≤ (largestPrimeFactor n)^n.primeFactorsList.length := by
  calc
    n = n.primeFactorsList.prod := (Nat.prod_primeFactorsList hn).symm
    _ ≤ _ := List.prod_le_pow_card _ _ (fun p hp => primeFactor_le_largest hp)

lemma one_lt_largestPrimeFactor {n : ℕ} (hn : 2 ≤ n) : 1 < largestPrimeFactor n := by
  have h1 : 1 ≤ largestPrimeFactor n := le_max_left _ _
  have hpow := self_le_largest_pow_length (show n ≠ 0 by omega)
  by_contra hh
  have he : largestPrimeFactor n = 1 := by omega
  rw [he, one_pow] at hpow
  omega

/-- A bound for `Ω(n)` puts the largest prime factor within a logarithmic
distance of the double logarithm of `n`. -/
lemma largest_factor_doubleLog_lower {n : ℕ} {K : ℝ} (hn : 2 ≤ n) (hK : 0 < K)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    B n - Real.log K ≤ B (largestPrimeFactor n) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hA : (1 : ℝ) < largestPrimeFactor n := by
    exact_mod_cast one_lt_largestPrimeFactor hn
  have hp : (n : ℝ) ≤ (largestPrimeFactor n : ℝ)^n.primeFactorsList.length := by
    exact_mod_cast self_le_largest_pow_length (show n ≠ 0 by omega)
  have hl := Real.log_le_log (zero_lt_one.trans hnR) hp
  rw [Real.log_pow] at hl
  have hlu : Real.log (n : ℝ) ≤ K*Real.log (largestPrimeFactor n : ℝ) :=
    hl.trans (mul_le_mul_of_nonneg_right hΩ (Real.log_pos hA).le)
  have hdiv : Real.log (n : ℝ)/K ≤ Real.log (largestPrimeFactor n : ℝ) :=
    (div_le_iff₀ hK).mpr (by simpa [mul_comm] using hlu)
  have hh := Real.log_le_log (div_pos (Real.log_pos hnR) hK) hdiv
  simpa only [B, Real.log_div (Real.log_pos hnR).ne' hK.ne'] using hh

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

lemma largestPrimeFactor_le_self {n : ℕ} (hn : 1 ≤ n) : largestPrimeFactor n ≤ n := by
  apply largestPrimeFactor_le_of_prime_divisors hn
  intro p _ hp hn0
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp

lemma normality_total_uniform {S b : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hpb : B (p-1 : ℕ) ≤ b) :
    ((p-1).primeFactorsList.length : ℝ) ≤ 3*b := by
  by_cases hSn : S < (p-1 : ℕ)
  · exact (normality_total_bound hp hS hSn hBS).trans (by linarith)
  · have hpn : 1 ≤ p-1 := by have := hp.1.two_le; omega
    have hs : (largestPrimeFactor (p-1) : ℝ) ≤ S := by
      have hl : (largestPrimeFactor (p-1) : ℝ) ≤ (p-1 : ℕ) := by
        exact_mod_cast largestPrimeFactor_le_self hpn
      exact hl.trans (le_of_not_gt hSn)
    have hz := omegaIn_eq_zero_of_largest_le (T := (p-1 : ℕ)) hs
    have he := congrArg (fun n : ℕ => (n : ℝ)) (omegaIn_partition (p-1) S)
    rw [hz,Nat.add_zero] at he
    linarith [hp.2.1]

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

lemma normal_prime_largest_band {S b lo hi : ℝ} {p : ℕ}
    (hp : IsNormalPrime S p) (hp3 : 3 ≤ p) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSb : B S ≤ b) (hb : 0 < b)
    (hpb : B (p-1 : ℕ) ≤ b) (hlo : lo ≤ B p) (hhi : B p ≤ hi) :
    lo-1-Real.log (3*b) ≤ B (largestPrimeFactor (p-1)) ∧
      B (largestPrimeFactor (p-1)) ≤ hi := by
  have hn : 2 ≤ p-1 := by omega
  constructor
  · have hlow := largest_factor_doubleLog_lower hn (by positivity : 0 < 3*b)
      (normality_total_uniform hp hS hBS hSb hpb)
    linarith [shifted_doubleLog_lower hp3]
  · apply le_trans _ hhi
    have hl : (1 : ℝ) < largestPrimeFactor (p-1) := by
      exact_mod_cast one_lt_largestPrimeFactor hn
    apply Real.log_le_log (Real.log_pos hl)
    apply Real.log_le_log (zero_lt_one.trans hl)
    exact_mod_cast (largestPrimeFactor_le_self (by omega : 1 ≤ p-1)).trans (Nat.sub_le _ _)

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

lemma normal_remainder_largest_band {x S y : ℝ} {H j : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hj : j ∈ Finset.Icc 1 (L x H)) (hjm : j < m x)
    (hp : IsNormalPrime S (remainderPrime η j)) (hS : 1 < S)
    (hBS : 0 ≤ B S) (hSy : S ≤ y) (hBy : 0 < B y)
    (hpy : (remainderPrime η j-1 : ℕ) ≤ y)
    (hloss : 1+Real.log (3*B y) ≤ (1/100 : ℝ)*bandScale x j) :
    (89/100 : ℝ)*bandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (11/10 : ℝ)*bandScale x j := by
  have hp3 := basic_remainder_prime_ge_three hη hj hjm
  have hp1 : (1 : ℝ) < (remainderPrime η j-1 : ℕ) := by exact_mod_cast (show 2 ≤ remainderPrime η j-1 by omega)
  have hSb := Real.log_le_log (Real.log_pos hS) (Real.log_le_log (zero_lt_one.trans hS) hSy)
  have hpb := Real.log_le_log (Real.log_pos hp1) (Real.log_le_log (zero_lt_one.trans hp1) hpy)
  have hh := hη.2.1 j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hu : (9/10 : ℝ)*bandScale x j ≤ B (remainderPrime η j) ∧
      B (remainderPrime η j) ≤ (11/10 : ℝ)*bandScale x j := by
    simpa only [remainderCoord,B,ite_eq_right hj0] using hh.2
  have hn := normal_prime_largest_band hp hp3 hS hBS hSb hBy hpb hu.1 hu.2
  change (9/10 : ℝ)*bandScale x j-1-Real.log (3*B y) ≤
    B (largestPrimeFactor (remainderPrime η j-1)) ∧ _ at hn
  exact ⟨by linarith [hn.1],hn.2⟩

/-- Uniformly over the whole collision block, the normality error is absorbed
by one percent of each actual prime band. -/
theorem collision_normal_factor_bands : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ j ∈ Finset.Icc 1 (collisionLastIndex x i), j ≤ L x H →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    IsNormalPrime (normalityScale x i) (remainderPrime η j) →
    (remainderPrime η j-1 : ℕ) ≤ y →
    (89/100 : ℝ)*bandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (11/10 : ℝ)*bandScale x j := by
  filter_upwards [collision_log_loss_small,eventually_collision_indices] with H hlog hind
  filter_upwards [hlog,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi j hj hjL η hη y hS hBS hSy hBy hByu hnorm hpy
  have hk := (hind x hm i hi).2.2
  have hjm : j < m x := by
    exact ((Finset.mem_Icc.mp hj).2.trans_lt hk).trans_le (Nat.sub_le _ _)
  apply normal_remainder_largest_band hη (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,hjL⟩)
    hjm hnorm hS hBS hSy hBy hpy
  exact (hx i hi y hBy hByu).trans (mul_le_mul_of_nonneg_left
    (bandScale_antitone x (Finset.mem_Icc.mp hj).2) (by norm_num))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingCollision
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical ordered comparison lists obtained from actual colliding witnesses. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma survivingIndex_mem {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ)
    (j : Fin (collisionSurvivors p q η ξ i k).card) :
    survivingIndex p q η ξ i k j ∈ collisionSurvivors p q η ξ i k :=
  (collisionSurvivors p q η ξ i k).orderEmbOfFin_mem rfl j

lemma prod_survivingIndex {M : Type*} [CommMonoid M] {x : ℝ} {H : ℕ} (p q : ℕ)
    (η ξ : RemainderDatum (L x H)) (i k : ℕ) (f : ℕ → M) :
    (∏ j : Fin (collisionSurvivors p q η ξ i k).card, f (survivingIndex p q η ξ i k j)) =
      ∏ r ∈ collisionSurvivors p q η ξ i k, f r := by
  calc
    _ = ∏ r ∈ Finset.univ.image (survivingIndex p q η ξ i k), f r := by
      rw [Finset.prod_image]
      intro a _ b _ hab
      exact (survivingIndex p q η ξ i k).injective hab
    _ = _ := by rw [show Finset.univ.image (survivingIndex p q η ξ i k) =
        collisionSurvivors p q η ξ i k from
          (collisionSurvivors p q η ξ i k).image_orderEmbOfFin_univ rfl]

lemma survivingIndex_first {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hik : i ≤ k)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i) :
    ∃ hb : 0 < (collisionSurvivors p q η ξ i k).card,
      survivingIndex p q η ξ i k ⟨0,hb⟩=i := by
  have hi : i ∈ collisionSurvivors p q η ξ i k :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hik⟩,hfirst⟩
  have hb := Finset.card_pos.mpr ⟨i,hi⟩
  refine ⟨hb,?_⟩
  rw [survivingIndex,Finset.orderEmbOfFin_zero rfl hb]
  apply le_antisymm
  · exact Finset.min'_le _ _ hi
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp
      (Finset.min'_mem _ ⟨i,hi⟩)).1).1

theorem surviving_collision_identity {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ)
    (hp : p.Prime) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) :
    (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left =
      (survivingPair p q η ξ i k).remainder*shiftedProduct (survivingPair p q η ξ i k).right := by
  have hc := (witness_collision_cancel hη hξ hp hL hR hk hik hv hfirst hcommon).1
  have he : (Finset.Icc 0 k).filter
      (fun j => wholeWitnessPrime p η j ≠ wholeWitnessPrime q ξ j) =
      collisionSurvivors p q η ξ i k := by
    ext j
    simp only [collisionSurvivors,Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨hj,hne⟩
      refine ⟨⟨?_,hj.2⟩,hne⟩
      by_contra! hij
      exact hne (hcommon j hij)
    · rintro ⟨hj,hne⟩
      exact ⟨⟨Nat.zero_le _,hj.2⟩,hne⟩
  rw [he] at hc
  simp only [survivingPair,shiftedProduct]
  rw [prod_survivingIndex p q η ξ i k (fun r => wholeWitnessPrime p η r-1),
    prod_survivingIndex p q η ξ i k (fun r => wholeWitnessPrime q ξ r-1)]
  exact hc

theorem surviving_good_conditions {x : ℝ} {H i p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hi : i ≤ R x H)
    (hgη : GoodWitnessConditions p η) (hgξ : GoodWitnessConditions q ξ) :
    ∀ j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      IsNormalPrime (normalityScale x i) ((survivingPair p q η ξ i (collisionLastIndex x i)).left j) ∧
      IsNormalPrime (normalityScale x i) ((survivingPair p q η ξ i (collisionLastIndex x i)).right j) ∧
      (survivingPair p q η ξ i (collisionLastIndex x i)).left j ≠
        (survivingPair p q η ξ i (collisionLastIndex x i)).right j ∧
      SquarefreeAbove ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1)
        (collisionSmoothCutoff x i) ∧
      SquarefreeAbove ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1)
        (collisionSmoothCutoff x i) := by
  intro j
  obtain ⟨hj,hne⟩ := Finset.mem_filter.mp (survivingIndex_mem p q η ξ i (collisionLastIndex x i) j)
  have hηi := hgη i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)
  have hξi := hgξ i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)
  exact ⟨hηi.2.1 _ hj,hξi.2.1 _ hj,hne,
    squarefreeAbove_of_dvd (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime p η r-1) hj) hηi.2.2.1,
    squarefreeAbove_of_dvd (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime q ξ r-1) hj) hξi.2.2.1⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCanceled
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The canceled product and the residual integer satisfy Ford's size bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma canceled_surviving_product {x : ℝ} {H i k p q : ℕ}
    (η ξ : RemainderDatum (L x H)) :
    collisionCanceledProduct p q η ξ i k *
      shiftedProduct (survivingPair p q η ξ i k).left =
        ∏ j ∈ Finset.Icc i k, (wholeWitnessPrime p η j-1) := by
  unfold shiftedProduct
  change collisionCanceledProduct p q η ξ i k *
    (∏ j : Fin (collisionSurvivors p q η ξ i k).card,
      (wholeWitnessPrime p η (survivingIndex p q η ξ i k j)-1)) = _
  rw [prod_survivingIndex p q η ξ i k (fun j => wholeWitnessPrime p η j-1)]
  exact Finset.prod_filter_mul_prod_filter_not (Finset.Icc i k)
    (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) _

lemma collisionCanceledProduct_pos {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hp : p.Prime) (hk : k ≤ L x H) : 0 < collisionCanceledProduct p q η ξ i k := by
  apply Finset.prod_pos
  intro j hj
  obtain ⟨hji,_⟩ := Finset.mem_filter.mp hj
  by_cases hj0 : j=0
  · simp only [wholeWitnessPrime,hj0,ite_true, if_true]
    exact Nat.sub_pos_of_lt hp.one_lt
  · simp only [wholeWitnessPrime,ite_eq_right hj0]
    exact Nat.sub_pos_of_lt (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by omega,(Finset.mem_Icc.mp hji).2.trans hk⟩)).1.one_lt

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonSizes
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer size and large-prime-part bounds for Ford's comparison hypotheses. -/

noncomputable section

namespace TotientAsymptotic

lemma partBelow_mul_partAbove {n : ℕ} (hn : n ≠ 0) (Z : ℝ) :
    partBelow n Z*partAbove n Z=n := by
  have hh := List.prod_map_filter_mul_prod_map_filter_not
    (fun p : ℕ => (p : ℝ) ≤ Z) id n.primeFactorsList
  simpa only [partBelow,partAbove,List.map_id,not_le,Nat.prod_primeFactorsList hn] using hh

lemma partBelow_bound (n : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (partBelow n Z : ℝ) ≤ Z^n.primeFactorsList.length := by
  let l := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) ≤ Z)
  have hb (l : List ℕ) (hl : ∀ p ∈ l, (p : ℝ) ≤ Z) :
      (l.map (fun p : ℕ => (p : ℝ))).prod ≤ Z^l.length := by
    induction l with
    | nil => simp
    | cons p l ih =>
      have hp := hl p (by simp)
      have ht := ih (fun q hq => hl q (by simp [hq]))
      have hn : 0 ≤ (l.map (fun p : ℕ => (p : ℝ))).prod :=
        List.prod_nonneg (by simp)
      simpa only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_comm] using
        mul_le_mul hp ht hn (zero_le_one.trans hZ)
  have hp : ((l.map (fun p : ℕ => (p : ℝ))).prod) ≤ Z^l.length := by
    apply hb
    intro p hp
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hp).2
  have hc : (partBelow n Z : ℝ)=(l.map (fun p : ℕ => (p : ℝ))).prod := by
    exact Nat.cast_list_prod l
  rw [hc]
  exact hp.trans (pow_le_pow_right₀ hZ (List.length_filter_le _ _))

lemma partAbove_log_lower {n : ℕ} {Z K : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) :
    Real.log (n : ℝ)-K*Real.log Z ≤ Real.log (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have hb : 0 < partBelow n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  have hl := Real.log_le_log (by exact_mod_cast hb : (0 : ℝ) < partBelow n Z)
    (partBelow_bound n hZ)
  rw [Real.log_pow] at hl
  have hk := mul_le_mul_of_nonneg_right hΩ (Real.log_nonneg hZ)
  have he' := congrArg (fun z : ℕ => Real.log (z : ℝ)) he
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hb.ne') (by exact_mod_cast ha.ne')] at he'
  linarith

lemma partAbove_gt_sqrt {n : ℕ} {Z K y : ℝ} (hn : 0 < n) (hZ : 1 ≤ Z)
    (hΩ : (n.primeFactorsList.length : ℝ) ≤ K) (hy : 0 < y)
    (hsize : Real.log y/2 < Real.log (n : ℝ)-K*Real.log Z) :
    Real.sqrt y < (partAbove n Z : ℝ) := by
  have he := partBelow_mul_partAbove hn.ne' Z
  have ha : 0 < partAbove n Z := Nat.pos_of_ne_zero (by intro hz; simp [hz] at he; omega)
  apply (Real.log_lt_log_iff (Real.sqrt_pos.mpr hy) (by exact_mod_cast ha)).mp
  rw [Real.log_sqrt hy.le]
  exact hsize.trans_le (partAbove_log_lower hn hZ hΩ)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonLargePart
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The largest-prime restriction supplies Ford's required part above `Y₁`. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma comparison_small_part_cost : ∀ᶠ y : ℝ in atTop,
    (4*B y)*Real.exp ((4/5 : ℝ)*B y) ≤ (1/10 : ℝ)*Real.log y := by
  have ht : Tendsto (fun b : ℝ => 4*b*Real.exp (-(1/5 : ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/5) (by norm_num)).const_mul 4
  filter_upwards [(ht.comp B_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/10)),
    eventually_gt_atTop (1 : ℝ)] with y hy hy1
  have he : Real.exp (B y)=Real.log y := Real.exp_log (Real.log_pos hy1)
  have hh := mul_le_mul_of_nonneg_right hy.le (Real.exp_pos (B y)).le
  change (4*B y*Real.exp (-(1/5 : ℝ)*B y))*Real.exp (B y) ≤
    (1/10 : ℝ)*Real.exp (B y) at hh
  have heq : (4*B y*Real.exp (-(1/5 : ℝ)*B y))*Real.exp (B y) =
      (4*B y)*Real.exp ((4/5 : ℝ)*B y) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rwa [heq,he] at hh

lemma prime_shift_log_lower : ∀ᶠ y : ℝ in atTop, ∀ p : ℕ, p.Prime →
    y^(9/10 : ℝ) ≤ p → (4/5 : ℝ)*Real.log y ≤ Real.log (p-1 : ℕ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (10*Real.log 2))] with y hy hlog
  intro p hp hlo
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp' : (p : ℝ)-1=(p-1 : ℕ) := by rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hhalf : y^(9/10 : ℝ)/2 ≤ (p-1 : ℕ) := by
    rw [← hp']
    linarith
  have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _) (by norm_num)) hhalf
  rw [Real.log_div (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow (zero_lt_one.trans hy)] at hh
  linarith

/-- The large prime part of the first shift exceeds `sqrt y`. The hypotheses
are exactly the size consequences supplied by normality and the ordered grid. -/
theorem comparison_large_prime_part : ∀ᶠ y : ℝ in atTop, ∀ p : ℕ, ∀ Z : ℝ,
    p.Prime → y^(9/10 : ℝ) ≤ p → 1 ≤ Z →
    Z ≤ Real.exp (Real.exp ((4/5 : ℝ)*B y)) →
    ((p-1).primeFactorsList.length : ℝ) ≤ 4*B y →
    Real.sqrt y < (partAbove (p-1) Z : ℝ) := by
  filter_upwards [comparison_small_part_cost,prime_shift_log_lower,
    eventually_gt_atTop (1 : ℝ),B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with y hcost hshift hy hB
  intro p Z hp hlo hZ hZu hΩ
  apply partAbove_gt_sqrt (Nat.sub_pos_of_lt hp.one_lt) hZ hΩ (zero_lt_one.trans hy)
  have hlZ := Real.log_le_log (lt_of_lt_of_le zero_lt_one hZ) hZu
  rw [Real.log_exp] at hlZ
  have hprod := mul_le_mul_of_nonneg_left hlZ (show 0 ≤ 4*B y by positivity)
  have hh := hshift p hp hlo
  linarith [Real.log_pos hy]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble Ford's pointwise comparison hypotheses for actual surviving lists. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma normal_prime_omega_below {S y : ℝ} {p : ℕ} (hp : IsNormalPrime S p)
    (hS : 1 < S) (hBS : 0 ≤ B S) (hSy : S ≤ y) (hpy : (p-1 : ℕ) ≤ y) :
    ((p-1).primeFactorsList.length : ℝ) ≤ 4*B y := by
  have hSb : B S ≤ B y := Real.log_le_log (Real.log_pos hS)
    (Real.log_le_log (zero_lt_one.trans hS) hSy)
  have hBy := hBS.trans hSb
  by_cases hp3 : 3 ≤ p
  · have hp1 : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 2 ≤ p-1 by omega)
    have hpb : B (p-1 : ℕ) ≤ B y := Real.log_le_log (Real.log_pos hp1)
      (Real.log_le_log (zero_lt_one.trans hp1) hpy)
    exact (normality_total_uniform hp hS hBS hSb hpb).trans (by linarith)
  · have he : p=2 := by have := hp.1.two_le; omega
    simp only [he, Nat.reduceSub, Nat.primeFactorsList_one, List.length_nil, Nat.cast_zero]
    positivity

/-- All pointwise hypotheses, including the large-prime-part condition, follow
for the actual canceled lists once their ordered factor intervals are chosen.
The remaining interval construction and summation are separate obligations. -/
theorem surviving_comparison_conditions : ∀ᶠ y : ℝ in atTop,
    ∀ {x : ℝ} {H i p q : ℕ} {η ξ : RemainderDatum (L x H)},
    IsBasicRemainder x H η → IsBasicRemainder x H ξ → p.Prime →
    L x H < m x → R x H < L x H → i ≤ R x H → collisionLastIndex x i < L x H →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    ∀ Y U : ℕ → ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    Y (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card=collisionSmoothCutoff x i →
    (∀ j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      U j ≤ largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1) ∧
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1) : ℝ) ≤ Y j ∧
      U j ≤ largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1) ∧
      (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right j-1) : ℝ) ≤ Y j) →
    ((suffixPreimage η (collisionLastIndex x i)).totient *
      (∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1)) : ℕ) ≤ y →
    (largestPrimeFactor (collisionResidual ξ i) : ℝ) ≤ collisionSmoothCutoff x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → 1 ≤ Y 1 →
    Y 1 ≤ Real.exp (Real.exp ((4/5 : ℝ)*B y)) →
    FordComparisonConditions (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U
      (survivingPair p q η ξ i (collisionLastIndex x i)) := by
  filter_upwards [comparison_large_prime_part] with y hlarge
  intro x H i p q η ξ hη hξ hp hL hR hi hk hv hfirst hcommon hgη hgξ Y U hS hBS hSy hYb hinterval hsize hres hhead hY1 hY1u
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have heq := surviving_collision_identity hη hξ hp hL hR hk hik hv hfirst hcommon
  have hgood := surviving_good_conditions hi hgη hgξ
  have hrpos := collisionCanceledProduct_pos hη hp hk.le (q := q) (ξ := ξ) (i := i)
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := collisionLastIndex x i))
  have hrempos := Nat.totient_pos.mpr (suffixPreimage_pos hξ (i := collisionLastIndex x i))
  have hprodpos : 0 < (collisionResidual η i)*
      shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left := by
    apply Nat.mul_pos hDpos
    apply Finset.prod_pos
    intro j _
    exact Nat.sub_pos_of_lt (hgood j).1.1.one_lt
  have hfactor : collisionCanceledProduct p q η ξ i (collisionLastIndex x i) *
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left) =
      (collisionResidual η i)*∏ j ∈ Finset.Icc i (collisionLastIndex x i), (wholeWitnessPrime p η j-1) := by
    rw [mul_left_comm, canceled_surviving_product]
  have hprodsize : ((collisionResidual η i)*shiftedProduct
      (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) ≤ y := by
    have hh := Nat.le_mul_of_pos_left
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left) hrpos
    rw [hfactor] at hh
    exact (show (((collisionResidual η i)*shiftedProduct
      (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) : ℝ) ≤
      ((collisionResidual η i)*∏ j ∈ Finset.Icc i (collisionLastIndex x i),
        (wholeWitnessPrime p η j-1) : ℕ) by exact_mod_cast hh).trans hsize
  have hshift (j : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      (((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1 : ℕ) : ℝ) ≤ y := by
    exact (show (((survivingPair p q η ξ i (collisionLastIndex x i)).left j-1 : ℕ) : ℝ) ≤
      ((collisionResidual η i)*shiftedProduct (survivingPair p q η ξ i (collisionLastIndex x i)).left : ℕ) by
        exact_mod_cast Nat.le_of_dvd hprodpos
          ((shifted_factor_dvd _ j).trans (dvd_mul_left _ _))).trans hprodsize
  refine ⟨hrempos,?_,heq,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(hgood j).1,(hgood j).2.1,(hgood j).2.2.1,
      (hinterval j).1,(hinterval j).2.1,(hinterval j).2.2.1,(hinterval j).2.2.2,
      hYb.symm ▸ (hgood j).2.2.2.1,hYb.symm ▸ (hgood j).2.2.2.2⟩
  · apply (le_div_iff₀ (by exact_mod_cast hrpos : (0 : ℝ) < collisionCanceledProduct p q η ξ i (collisionLastIndex x i))).mpr
    rw [mul_comm,← Nat.cast_mul,hfactor]
    exact hsize
  · simpa only [hYb,survivingPair,collisionResidual] using hres
  · intro hb
    obtain ⟨hb',hfirstidx⟩ := survivingIndex_first hik hfirst
    have hfirstp : (survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩ =
        wholeWitnessPrime p η i := by
      change wholeWitnessPrime p η (survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩)=_
      rw [hfirstidx]
    apply hlarge _ _ (hgood ⟨0,hb⟩).1.1 (by simpa only [hfirstp] using hhead) hY1 hY1u
    exact normal_prime_omega_below (hgood ⟨0,hb⟩).1 hS hBS hSy (hshift ⟨0,hb⟩)

  · rw [hYb]
    apply squarefreeAbove_of_dvd ?_
      ((hgη i (Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩)).2.2.1)
    refine ⟨collisionCanceledProduct p q η ξ i (collisionLastIndex x i),?_⟩
    rw [mul_comm,canceled_surviving_product]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalHeadBand
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first shifted prime has its largest factor above height 0.9. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma head_logarithmic_loss : ∀ᶠ b : ℝ in atTop,
    2+Real.log (4*b) ≤ (1/10 : ℝ)*b := by
  have ht : Tendsto (fun b : ℝ => (2+Real.log 4)/b+Real.log b/b) atTop (nhds 0) := by
    have h1 : Tendsto (fun b : ℝ => (2+Real.log 4)/b) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [add_zero,id_eq] using h1.add Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/10)),
    eventually_gt_atTop (0 : ℝ)] with b hb hb0
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hb0.ne']
  have hh := (div_le_iff₀ hb0).mp (show (2+Real.log 4+Real.log b)/b ≤ (1/10 : ℝ) by
    simpa only [add_div] using hb.le)
  linarith

/-- This handles the largest-prime coordinate, whose band convention is
`u₀ = B x` rather than `B p`. -/
theorem normal_head_largest_factor : ∀ᶠ x : ℝ in atTop, ∀ S : ℝ, ∀ p : ℕ,
    IsNormalPrime S p → 1 < S → 0 ≤ B S → S ≤ x →
    x^(9/10 : ℝ) ≤ p → (p-1 : ℕ) ≤ x →
    (9/10 : ℝ)*B x ≤ B (largestPrimeFactor (p-1)) := by
  filter_upwards [B_tendsto.eventually head_logarithmic_loss,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually (eventually_gt_atTop (2 : ℝ))]
    with x hloss hB hx hxpow
  intro S p hp hS hBS hSx hpmin hpx
  have hp3 : 3 ≤ p := by
    have hh : (2 : ℝ) < p := hxpow.trans_le hpmin
    exact_mod_cast hh
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hpmin
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hlog
  have hdouble := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 9/10) (Real.log_pos hx)) hlog
  rw [Real.log_mul (by norm_num : (9/10 : ℝ) ≠ 0) (Real.log_pos hx).ne'] at hdouble
  change Real.log (9/10 : ℝ)+B x ≤ Real.log (Real.log (p : ℝ)) at hdouble
  have hl9 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 9/10)
  norm_num only [inv_div,div_self] at hl9
  have hlower := largest_factor_doubleLog_lower (show 2 ≤ p-1 by omega)
    (show 0 < 4*B x by positivity) (normal_prime_omega_below hp hS hBS hSx hpx)
  have hshift := shifted_doubleLog_lower hp3
  change Real.log (Real.log (p : ℝ))-1 ≤ B (p-1 : ℕ) at hshift
  change 2+Real.log (4*B x) ≤ (1/10 : ℝ)*B x at hloss
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionFactorHeights
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative margins between the actual normal largest-factor bands. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma ford_band_step {x : ℝ} {i j : ℕ} (hB : 1 < B x) (hij : i<j) (hjm : j< m x) :
    fordBandScale x j ≤ rho*fordBandScale x i := by
  have him := hij.trans hjm
  have hc : 0 < bandCenterRatio x := by
    rw [← fordBandScale_div_bandScale hB him]
    exact div_pos (fordBandScale_pos (zero_lt_one.trans hB) him) (bandScale_pos him)
  rw [fordBandScale_eq_ratio_mul hB hjm,fordBandScale_eq_ratio_mul hB him]
  have hle := (bandScale_antitone x (show i+1≤j by omega)).trans (bandScale_succ_le x i)
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hle hc.le

lemma ford_band_antitone {x : ℝ} {i j : ℕ} (hB : 1 < B x) (hij : i≤j) (hjm : j< m x) :
    fordBandScale x j ≤ fordBandScale x i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have hp := fordBandScale_pos (zero_lt_one.trans hB) (hlt.trans hjm)
    exact (ford_band_step hB hlt hjm).trans (by nlinarith [rho_lt_one])

/-- Normality changes either endpoint of an actual coarse band by less than
one further percent when expressed in Ford's centers. -/
theorem collision_factor_ford_bands : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ j ∈ Finset.Icc 1 (collisionLastIndex x i), j ≤ L x H →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η → ∀ y : ℝ,
    1 < normalityScale x i → 0 ≤ B (normalityScale x i) → normalityScale x i ≤ y →
    0 < B y → B y ≤ 2*fordBandScale x i →
    IsNormalPrime (normalityScale x i) (remainderPrime η j) → (remainderPrime η j-1 : ℕ) ≤ y →
    (22/25 : ℝ)*fordBandScale x j ≤ B (largestPrimeFactor (remainderPrime η j-1)) ∧
    B (largestPrimeFactor (remainderPrime η j-1)) ≤ (28/25 : ℝ)*fordBandScale x j := by
  filter_upwards [collision_normal_factor_bands,eventually_collision_indices] with H hnormal hind
  filter_upwards [hnormal,fordBandScale_uniform_comparison (ε := 1/100) (by norm_num),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hn hc hm
  intro i hi j hj hjL η hη y hS hBS hSy hBy hByu hp hpy
  have hjm : j< m x := ((Finset.mem_Icc.mp hj).2.trans_lt (hind x hm i hi).2.2).trans_le (Nat.sub_le _ _)
  have hb := bandScale_pos hjm
  have hd := hc j hjm
  have hfl : (99/100 : ℝ)*bandScale x j < fordBandScale x j := by
    apply (lt_div_iff₀ hb).mp
    linarith [(abs_lt.mp hd).1]
  have hfu : fordBandScale x j < (101/100 : ℝ)*bandScale x j := by
    apply (div_lt_iff₀ hb).mp
    linarith [(abs_lt.mp hd).2]
  have hh := hn i hi j hj hjL η hη y hS hBS hSy hBy hByu hp hpy
  constructor <;> nlinarith [hh.1,hh.2]

lemma normal_factor_band_gap {x : ℝ} {j k l : ℕ} {u v : ℝ}
    (hB : 1 < B x) (hjk : j<k) (hkl : k≤l) (hlm : l< m x)
    (hu : (22/25 : ℝ)*fordBandScale x j ≤ u)
    (hv : v ≤ (28/25 : ℝ)*fordBandScale x k) :
    (1/4 : ℝ)*fordBandScale x l ≤ u-v := by
  have hkm := hkl.trans_lt hlm
  have hjm := hjk.trans hkm
  have hs := ford_band_step hB hjk hkm
  have hm := ford_band_antitone hB (hjk.le.trans hkl) hlm
  have hp := fordBandScale_pos (zero_lt_one.trans hB) hjm
  nlinarith [collision_rho_bounds.2]

lemma collision_rounding_margin {h : ℕ} {δ : ℝ} (hh : 4≤h)
    (hδ : δ≤2/(h : ℝ)^32) :
    (2*(h : ℝ)+10)*δ < 1/(100*(h : ℝ)^20) := by
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have h0 : (0 : ℝ)<h := by linarith
  have hp : (1000 : ℝ)<(h : ℝ)^11 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hhR 11
    norm_num at hpow
    linarith
  have hpoly : 400*(h : ℝ)+2000 < (h : ℝ)^12 := by
    have hh1 : 400*(h : ℝ)+2000 ≤ 900*h := by linarith
    have hm := mul_lt_mul_of_pos_right hp h0
    nlinarith
  calc
    _ ≤ (2*(h : ℝ)+10)*(2/(h : ℝ)^32) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    _ < _ := by
      apply (lt_div_iff₀ (by positivity : (0 : ℝ)<100*(h : ℝ)^20)).mpr
      have he : (2*(h : ℝ)+10)*(2/(h : ℝ)^32)*(100*(h : ℝ)^20)=
          (400*(h : ℝ)+2000)/(h : ℝ)^12 := by field_simp <;> ring
      rw [he]
      exact (div_lt_one (by positivity)).mpr hpoly

/-- The smallest factor-band margin dominates the full grid rounding cost. -/
lemma normalized_factor_margin {x y : ℝ} {i : ℕ} {h : ℕ}
    (hh : 4≤h) (hB : 1<B x) (him : i< m x)
    (hcut : 2*collisionCutoff (m x-i)< m x-i) (hhdef : h=m x-i)
    (hBy : 0<B y) (hByu : B y≤2*fordBandScale x i) :
    1/(100*(h : ℝ)^20)<(1/10 : ℝ)*fordBandScale x (collisionLastIndex x i)/B y := by
  have hpos := fordBandScale_pos (zero_lt_one.trans hB) him
  have hl := (le_div_iff₀ hpos).mp (ford_collision_layer_ratio hB him hcut).1
  rw [← hhdef] at hl
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have h0 : (0 : ℝ)<h := by linarith
  have hr : (1/100 : ℝ) < rho/40 := by nlinarith [collision_rho_bounds.1]
  apply (lt_div_iff₀ hBy).mpr
  have hu := mul_le_mul_of_nonneg_left hByu (by positivity : (0 : ℝ)≤1/(100*(h : ℝ)^20))
  have ht : 1/(100*(h : ℝ)^20)*(2*fordBandScale x i) <
      (1/10 : ℝ)*(rho/(2*(h : ℝ)^20)*fordBandScale x i) := by
    have ht := mul_lt_mul_of_pos_right hr (div_pos (mul_pos (by norm_num : (0 : ℝ)<2) hpos) (pow_pos h0 20))
    first | (convert ht using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (ht.trans (le_of_eq (by ring)))
  exact (hu.trans_lt ht).trans_le (mul_le_mul_of_nonneg_left hl (by norm_num))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collision_grid_lower_bounds {δ u v : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    collisionGridLower δ (collisionGridIndex δ u v) ≤ min u v ∧
    min u v < collisionGridLower δ (collisionGridIndex δ u v)+δ := by
  have hmin : 0 ≤ min u v := le_min hu hv
  have hlo := Nat.floor_le (div_nonneg hmin hδ.le)
  have hhi := Nat.lt_floor_add_one (min u v/δ)
  constructor
  · simpa only [collisionGridLower,collisionGridIndex,mul_comm] using (le_div_iff₀ hδ).mp hlo
  · have hh := (div_lt_iff₀ hδ).mp hhi
    rw [add_mul,one_mul] at hh
    simpa only [collisionGridLower,collisionGridIndex,mul_comm] using hh

/-- The paired largest factors fit in one of finitely many grid intervals.
The width retains the full alignment error and one rounding cell. -/
theorem collision_grid_enclosure {δ u v : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hclose : |u-v| ≤ (2*(J : ℝ)+1)*δ) :
    let n := collisionGridIndex δ u v
    collisionGridLower δ n ≤ u ∧ collisionGridLower δ n ≤ v ∧
    u < collisionGridUpper δ J n ∧ v < collisionGridUpper δ J n ∧
    collisionGridUpper δ J n ≤ u+(2*(J : ℝ)+3)*δ := by
  dsimp only
  obtain ⟨hlo,hhi⟩ := collision_grid_lower_bounds hδ hu hv
  have hmax : max u v ≤ min u v+(2*(J : ℝ)+1)*δ := by
    rcases le_total u v with h | h
    · rw [min_eq_left h,max_eq_right h]
      linarith [(abs_le.mp hclose).1]
    · rw [min_eq_right h,max_eq_left h]
      linarith [(abs_le.mp hclose).2]
  have he : collisionGridUpper δ J (collisionGridIndex δ u v) =
      collisionGridLower δ (collisionGridIndex δ u v)+(2*(J : ℝ)+3)*δ := by
    simp only [collisionGridUpper,collisionGridLower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [he]
  exact ⟨hlo.trans (min_le_left _ _),hlo.trans (min_le_right _ _),
    by linarith [le_max_left u v],by linarith [le_max_right u v],
    by linarith [min_le_left u v]⟩

lemma collisionGridIndex_le {δ u v : ℝ} (hδ : 0 < δ) (hu : u ≤ 1) :
    collisionGridIndex δ u v ≤ ⌊1/δ⌋₊ := by
  exact Nat.floor_mono (div_le_div_of_nonneg_right ((min_le_left u v).trans hu) hδ.le)

/-- Disjoint largest-factor bands remain strictly ordered after gridding,
provided their gap exceeds the explicit alignment and rounding costs. -/
lemma collision_grid_separated {δ u v u' v' : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hu' : 0 ≤ u') (hv' : 0 ≤ v')
    (hclose' : |u'-v'| ≤ (2*(J : ℝ)+1)*δ)
    (hgap : max u' v'+(2*(J : ℝ)+4)*δ < min u v) :
    collisionGridUpper δ J (collisionGridIndex δ u' v') <
      collisionGridLower δ (collisionGridIndex δ u v) := by
  have hprev := (collision_grid_lower_bounds hδ hu hv).2
  have hnext := (collision_grid_enclosure hδ hu' hv' hclose').2.2.2.2
  linarith [le_max_left u' v']

lemma collisionGridFamilies_mem {δ : ℝ} {b : ℕ} (hδ : 0 < δ) (u v : Fin b → ℝ)
    (hu : ∀ j, u j ≤ 1) :
    (fun j => collisionGridIndex δ (u j) (v j)) ∈ collisionGridFamilies δ b := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (collisionGridIndex_le hδ (hu j)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's cutoff restrictions in the normalized coordinates of the finite grid. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma comparisonCutoffs_doubleLog {y : ℝ} (hB : B y ≠ 0) (ν : ℕ → ℝ) (j : ℕ) :
    B (comparisonCutoffs y ν j)/B y=ν j := by
  simp only [comparisonCutoffs,B,Real.log_exp]
  exact mul_div_cancel_left₀ _ hB

lemma comparison_upper_cutoff_power : ∀ᶠ y : ℝ in atTop,
    Real.exp (Real.exp ((4/5 : ℝ)*B y)) ≤ y^(1/(10*B y)) := by
  filter_upwards [comparison_small_part_cost,eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with y hcost hy hB
  have he : Real.exp ((4/5 : ℝ)*B y) ≤ Real.log y/(10*B y) := by
    apply (le_div_iff₀ (by positivity : 0 < 10*B y)).mpr
    nlinarith [Real.exp_pos ((4/5 : ℝ)*B y)]
  apply (Real.log_le_log_iff (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hy) _)).mp
  rw [Real.log_exp,Real.log_rpow (zero_lt_one.trans hy)]
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using he

/-- A finite grid with these normalized inequalities satisfies exactly the
published Ford parameter restrictions, including the first-cutoff power. -/
theorem ford_parameters_of_normalized_grid : ∀ᶠ y : ℝ in atTop,
    ∀ b D r : ℕ, ∀ S : ℝ, ∀ ν μ : ℕ → ℝ,
    1 ≤ b → ν 0=1 → Real.exp (Real.exp 1) ≤ S → S ≤ comparisonCutoffs y ν b →
    (∀ j ∈ Finset.range b, ν (j+1) < μ j ∧ μ j < ν j) → ν 1 ≤ 4/5 →
    (∀ j ∈ Finset.Icc 2 b,
      2*Real.sqrt (B S/B y) < ν (j-1)-ν j) →
    1 ≤ D → (D : ℝ) ≤ y^(1/100 : ℝ) →
    (largestPrimeFactor D : ℝ) ≤ comparisonCutoffs y ν b →
    1 ≤ r → (r : ℝ) ≤ y^(1/10 : ℝ) →
    FordComparisonParameters b y S D r (comparisonCutoffs y ν) (comparisonCutoffs y μ) := by
  filter_upwards [comparison_upper_cutoff_power,eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with y hpower hy hB
  intro b D r S ν μ hb hν hS hSb horder hν1 hgap hD hDy hDs hr hry
  refine ⟨hb,?_,hS,hSb,?_,?_,?_,hD,hDy,hDs,hr,hry⟩
  · simp only [comparisonCutoffs,hν,mul_one,B,
      Real.exp_log (Real.log_pos hy),Real.exp_log (zero_lt_one.trans hy)]
  · intro j hj
    exact ⟨Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (horder j hj).1 hB)),
      Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (horder j hj).2 hB))⟩
  · apply le_trans _ hpower
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left hν1 hB.le).trans_eq (mul_comm _ _)
  · intro j hj
    simpa only [comparisonCutoffs_doubleLog hB.ne'] using hgap j hj

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PairedComparisonGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual paired intervals, including the ungridded top and smooth bottom. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- All comparisons are made with the same finite grid label. The endpoint
`ζ` is the smooth residual cutoff and the top endpoint is exactly one. -/
theorem paired_grid_intervals {b : ℕ} {δ ζ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩) ≤ 1)
    (hhead : (4/5 : ℝ)≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩))
    (hfirst : pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) 1 < 4/5)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1<b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+4 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    let n := fun j => collisionGridIndex δ (u j) (v j)
    pairedGridUpper δ ζ n 0=1 ∧ pairedGridUpper δ ζ n b=ζ ∧
    (∀ j : Fin b,
      pairedGridLower δ n j ≤ u j ∧ pairedGridLower δ n j ≤ v j ∧
      u j ≤ pairedGridUpper δ ζ n j ∧ v j ≤ pairedGridUpper δ ζ n j) ∧
    (∀ j ∈ Finset.range b,
      pairedGridUpper δ ζ n (j+1) < pairedGridLower δ n j ∧
      pairedGridLower δ n j < pairedGridUpper δ ζ n j) := by
  dsimp only
  let n := fun j => collisionGridIndex δ (u j) (v j)
  have henc (j : Fin b) := collision_grid_enclosure hδ (hu j) (hv j) (halign j)
  have hlo (j : Fin b) := collision_grid_lower_bounds hδ (hu j) (hv j)
  have hzeroU : u ⟨0,hb⟩ ≤ 1 := (le_max_left _ _).trans htop
  have hzeroV : v ⟨0,hb⟩ ≤ 1 := (le_max_right _ _).trans htop
  refine ⟨by simp [pairedGridUpper],by simp [pairedGridUpper,show b ≠ 0 by omega],?_,?_⟩
  · intro j
    by_cases hj0 : j.val=0
    · have he : j=⟨0,hb⟩ := Fin.ext hj0
      subst j
      simp only [pairedGridLower,pairedGridUpper,ite_true, if_true]
      exact ⟨hhead.trans (min_le_left _ _),hhead.trans (min_le_right _ _),hzeroU,hzeroV⟩
    · simp only [pairedGridLower,pairedGridUpper,hj0,ite_false, if_false,dite_eq_left j.isLt]
      exact ⟨(henc j).1,(henc j).2.1,(henc j).2.2.1.le,(henc j).2.2.2.1.le⟩

  · intro j hj
    have hjb := Finset.mem_range.mp hj
    have hl := hlo ⟨j,hjb⟩
    by_cases hj0 : j=0
    · subst j
      simp only [pairedGridLower,pairedGridUpper,ite_true, if_true]
      exact ⟨hfirst,by norm_num⟩
    simp only [pairedGridLower,hj0,ite_false, if_false,dite_eq_left hjb]
    constructor
    · by_cases hjn : j+1<b
      · have hg := hnext ⟨j,hjb⟩ hjn
        have he : collisionGridUpper δ (j+1) (n ⟨j+1,hjn⟩) <
            collisionGridLower δ (n ⟨j,hjb⟩) := by
          dsimp [n]
          have := collision_grid_separated hδ (hu ⟨j,hjb⟩) (hv ⟨j,hjb⟩)
            (hu ⟨j+1,hjn⟩) (hv ⟨j+1,hjn⟩) (halign ⟨j+1,hjn⟩) hg
          exact this
        simpa only [pairedGridUpper,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false,
          dite_eq_left hjn] using he
      · have hlast : j=b-1 := by omega
        have heq : (⟨b-1,by omega⟩ : Fin b)=⟨j,hjb⟩ := Fin.ext hlast.symm
        have hh : ζ+δ < min (u ⟨j,hjb⟩) (v ⟨j,hjb⟩) := by
          simpa only [heq] using hbottom
        have he : ζ < collisionGridLower δ (n ⟨j,hjb⟩) := by
          dsimp [n]
          linarith [hl.2]
        simpa only [pairedGridUpper,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false,
          dite_eq_right hjn] using he
    · have hh := (henc ⟨j,hjb⟩).1.trans_lt (henc ⟨j,hjb⟩).2.2.1
      simpa only [pairedGridUpper,hj0,ite_false, if_false,dite_eq_left hjb] using hh

lemma paired_grid_gaps {b : ℕ} {δ ζ : ℝ} (hb : 1 ≤ b) (hδ : 0 < δ)
    (u v : Fin b → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (halign : ∀ j, |u j-v j| ≤ (2*(j.val : ℝ)+1)*δ)
    (hnext : ∀ j : Fin b, ∀ hj : j.val+1<b,
      max (u ⟨j.val+1,hj⟩) (v ⟨j.val+1,hj⟩)+(2*(j.val+1 : ℕ)+6 : ℝ)*δ <
        min (u j) (v j))
    (hbottom : ζ+3*δ < min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩)) :
    ∀ j ∈ Finset.Icc 2 b,
      2*δ < pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) (j-1)-
        pairedGridUpper δ ζ (fun j => collisionGridIndex δ (u j) (v j)) j := by
  intro j hj
  have hj2 := (Finset.mem_Icc.mp hj).1
  have hjb := (Finset.mem_Icc.mp hj).2
  have hp : j-1<b := by omega
  have hp0 : j-1 ≠ 0 := by omega
  have heprev := collision_grid_enclosure hδ (hu ⟨j-1,hp⟩) (hv ⟨j-1,hp⟩)
    (halign ⟨j-1,hp⟩)
  simp only [pairedGridUpper,hp0,ite_false, if_false,dite_eq_left hp]
  by_cases hjlt : j<b
  · have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false, if_false,dite_eq_left hjlt]
    have he := (collision_grid_enclosure hδ (hu ⟨j,hjlt⟩) (hv ⟨j,hjlt⟩)
      (halign ⟨j,hjlt⟩)).2.2.2.2
    have hidx : j-1+1=j := by omega
    have hg := hnext ⟨j-1,hp⟩ (by change j-1+1<b; omega)
    simp only [hidx] at hg
    have hmin := min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩)
    have hmax := le_max_left (u ⟨j,hjlt⟩) (v ⟨j,hjlt⟩)
    linarith [heprev.2.2.1]
  · have hjeq : j=b := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [hj0,ite_false, if_false,dite_eq_right hjlt]
    have hg : ζ+3*δ < min (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩) := by
      simpa only [hjeq] using hbottom
    linarith [min_le_left (u ⟨j-1,hp⟩) (v ⟨j-1,hp⟩),heprev.2.2.1]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingGridGeometry
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical grid margins for the ordered surviving Ford bands. -/

noncomputable section

namespace TotientAsymptotic

lemma collision_last_band_le_half {x : ℝ} {i : ℕ} (hB : 1<B x) (hi : i < m x)
    (hh : 2 ≤ m x-i) (hcut : 2*collisionCutoff (m x-i)< m x-i) :
    fordBandScale x (collisionLastIndex x i) ≤ fordBandScale x i/2 := by
  have hb := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hp : (2 : ℝ) ≤ ((m x-i : ℕ) : ℝ)^18 := by
    have h2 : (2 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hh
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) h2 18
    norm_num at hp
    linarith
  have hr := (div_le_iff₀ hb).mp (ford_collision_layer_ratio hB hi hcut).2
  have hfrac : 1/((m x-i : ℕ) : ℝ)^18 ≤ (1/2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  exact hr.trans (by nlinarith)

/-- This statement concerns the actual band heights only; the finite grid
rounding is added afterwards. The first height uses the large head-prime
bound, and every other height uses its own Ford band. -/
theorem ordered_surviving_band_margins {x Y : ℝ} {i k b : ℕ}
    (hb : 0<b) (hB : 1<B x) (hi : i < m x) (hk : k < m x)
    (j : Fin b ↪o ℕ) (hj0 : j ⟨0,hb⟩=i) (hjk : ∀ r, j r≤k)
    (_hY : 0<Y) (hYl : (87/100 : ℝ)*fordBandScale x i≤Y)
    (hlast : fordBandScale x k ≤ fordBandScale x i/2)
    (u v : Fin b → ℝ)
    (hhead : (9/10 : ℝ)*Y≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩))
    (hlo : ∀ r, 0 < r.val → (22/25 : ℝ)*fordBandScale x (j r)≤ min (u r) (v r))
    (hhi : ∀ r, 0 < r.val → max (u r) (v r)≤(28/25 : ℝ)*fordBandScale x (j r)) :
    (∀ r, 0 < r.val → max (u r) (v r)≤(18/25 : ℝ)*Y) ∧
    (∀ r, (4/5 : ℝ)*fordBandScale x k≤ min (u r) (v r)) ∧
    (∀ r s, r < s → (1/10 : ℝ)*fordBandScale x k≤ min (u r) (v r)-max (u s) (v s)) := by
  have hbi := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hbk := fordBandScale_pos (zero_lt_one.trans hB) hk
  have htail (r : Fin b) (hr : 0 < r.val) :
      max (u r) (v r)≤(28/25 : ℝ)*rho*fordBandScale x i := by
    have hir : i<j r := by
      rw [← hj0]
      exact j.strictMono hr
    have hs := ford_band_step hB hir ((hjk r).trans_lt hk)
    exact (hhi r hr).trans (by nlinarith)
  constructor
  · intro r hr
    have hh := htail r hr
    have hρ := mul_lt_mul_of_pos_right collision_rho_bounds.2 hbi
    nlinarith
  constructor
  · intro r
    by_cases hr : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr
      subst r
      nlinarith
    · have hm := ford_band_antitone hB (hjk r) hk
      have hl := hlo r (by omega)
      nlinarith
  · intro r s hrs
    have hs0 : 0 < s.val := by have h0 : (0 : ℕ) ≤ r.val := Nat.zero_le _; exact h0.trans_lt hrs
    by_cases hr : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr
      subst r
      have ht := htail s hs0
      have hρ := mul_lt_mul_of_pos_right collision_rho_bounds.2 hbi
      nlinarith
    · have hg := normal_factor_band_gap hB (j.strictMono hrs) (hjk s) hk
        (hlo r (by omega)) (hhi s hs0)
      linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionNormalityDomain
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normality cutoff lies in the actual dyadic counting domain. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma cube_root_le_half {b : ℝ} (hb : 8 ≤ b) : b^(1/3 : ℝ) ≤ b/2 := by
  have hb0 : 0 < b := by linarith
  have he : (b^(1/3 : ℝ))^3=b := by
    rw [← Real.rpow_mul_natCast hb0.le]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hb0.le _) (by positivity) (by norm_num : 3 ≠ 0)).mp
  rw [he]
  have hs : 8 ≤ b^2 := by nlinarith
  nlinarith

/-- In particular this discharges `S ≥ exp(exp 1)` and `S ≤ y` in the
published comparison lemma at every sufficiently late retained band. -/
theorem collision_normality_domain : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 < y → fordBandScale x i/2 ≤ B y →
    Real.exp (Real.exp 1) ≤ normalityScale x i ∧
    1 ≤ B (normalityScale x i) ∧ normalityScale x i ≤ y := by
  filter_upwards [ford_band_polynomial_lower 1,eventually_ge_atTop 8] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hy hBy
  have him : i < m x := by unfold R at hi; omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hb : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa only [pow_one] using hx i him hHi
  have hb8 : 8 ≤ fordBandScale x i := by
    have hh : (8 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
    exact hh.trans hb
  have hroot : 1 ≤ (fordBandScale x i)^(1/3 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hBscale : B (normalityScale x i)=(fordBandScale x i)^(1/3 : ℝ) := by
    simp only [normalityScale,B,Real.log_exp]
  refine ⟨Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hroot),hBscale ▸ hroot,?_⟩
  have hrootBy := (cube_root_le_half hb8).trans hBy
  have hyexp : Real.exp (Real.exp (B y))=y := by
    rw [B,Real.exp_log (Real.log_pos hy),Real.exp_log (zero_lt_one.trans hy)]
  exact (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hrootBy)).trans_eq hyexp

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingHeights
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual surviving factors, with uniform top and positive-coordinate bounds. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma one_lt_nat_of_doubleLog_pos {n : ℕ} (hn : 0 < B n) : 1<n := by
  by_contra! h
  interval_cases n <;> norm_num [B] at hn

/-- Unlike the positive-coordinate band lemma, this also covers collisions
whose first different prime is the largest prime of the tuple. -/
theorem surviving_factor_heights : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    1<y → 0<B y → fordBandScale x i/2 ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    ∃ hb : 0<(collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((9/10 : ℝ)*B y ≤ B (largestPrimeFactor
        ((survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩-1)) ∧
       (9/10 : ℝ)*B y ≤ B (largestPrimeFactor
        ((survivingPair p q η ξ i (collisionLastIndex x i)).right ⟨0,hb⟩-1))) ∧
      (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
        (0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤ B y) ∧
        (0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤ B y)) ∧
      (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card, 0 < r.val →
        ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
          B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤
          (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) ∧
        ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
          B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
         B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤
          (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r))) := by
  filter_upwards [collision_factor_ford_bands,collision_normality_domain,
    collision_endpoints_eventually normal_head_largest_factor,eventually_collision_indices]
    with H hband hdomain hhead hind
  filter_upwards [hband,hdomain,hhead,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hband hdomain hhead hm hBx
  intro i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  obtain ⟨hb,hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change 0 < (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card at hb
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩=i at hidx0
  have hk := (hind x hm i hi).2.2
  have hgood := surviving_good_conditions hi hgη hgξ
  obtain ⟨hSbig,hBS,hSy⟩ := hdomain i hi y hy hByl
  have hS : 1 < normalityScale x i :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hSbig
  have hBS0 : 0 ≤ B (normalityScale x i) := by linarith
  have hheadfun := hhead i hi y hy hByl
  have hfirstp : (survivingPair p q η ξ i (collisionLastIndex x i)).left ⟨0,hb⟩ = wholeWitnessPrime p η i := by
    simp only [survivingPair,hidx0]
  have hfirstq : (survivingPair p q η ξ i (collisionLastIndex x i)).right ⟨0,hb⟩ = wholeWitnessPrime q ξ i := by
    simp only [survivingPair,hidx0]
  have hl := hheadfun _ _ (hgood ⟨0,hb⟩).1 hS hBS0 hSy
    (by simpa only [hfirstp] using hpmin) (hsize ⟨0,hb⟩).1
  have hr := hheadfun _ _ (hgood ⟨0,hb⟩).2.1 hS hBS0 hSy
    (by simpa only [hfirstq] using hqmin) (hsize ⟨0,hb⟩).2
  have hpositive (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card)
      (hr0 : 0 < r.val) :
      ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
       B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ≤
        (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) ∧
      ((22/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r) ≤
        B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ∧
       B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) ≤
        (28/25 : ℝ)*fordBandScale x (survivingIndex p q η ξ i (collisionLastIndex x i) r)) := by
    have hlt : i < survivingIndex p q η ξ i (collisionLastIndex x i) r := by
      calc
        i = survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb⟩ := hidx0.symm
        _ < _ := (survivingIndex p q η ξ i (collisionLastIndex x i)).strictMono hr0
    have hj := (Finset.mem_Icc.mp (Finset.mem_filter.mp
      (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
    have hj0 : survivingIndex p q η ξ i (collisionLastIndex x i) r ≠ 0 := by omega
    have hbη := hband i hi _ (Finset.mem_Icc.mpr ⟨by omega,hj⟩) (hj.trans hk.le)
      η hη y hS hBS0 hSy hBy hByu
    have hbξ := hband i hi _ (Finset.mem_Icc.mpr ⟨by omega,hj⟩) (hj.trans hk.le)
      ξ hξ y hS hBS0 hSy hBy hByu
    have hg := hgood r
    have hs := hsize r
    simp only [survivingPair,wholeWitnessPrime,ite_eq_right hj0] at hg hs ⊢
    exact ⟨hbη hg.1 hs.1,hbξ hg.2.1 hs.2⟩
  refine ⟨hb,⟨hl,hr⟩,?_,hpositive⟩
  intro r
  have hpos : 0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1)) ∧
      0 < B (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1)) := by
    by_cases hr0 : r.val=0
    · have he : r=⟨0,hb⟩ := Fin.ext hr0
      subst r
      exact ⟨(mul_pos (by norm_num) hBy).trans_le hl,(mul_pos (by norm_num) hBy).trans_le hr⟩
    · have hj := (Finset.mem_Icc.mp (Finset.mem_filter.mp
        (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
      have hjm := (hj.trans_lt hk).trans_le (Nat.sub_le _ _)
      have hbp := fordBandScale_pos (zero_lt_one.trans hBx) hjm
      exact ⟨(mul_pos (by norm_num) hbp).trans_le (hpositive r (by omega)).1.1,
        (mul_pos (by norm_num) hbp).trans_le (hpositive r (by omega)).2.1⟩
  have hupper (n : ℕ) (hn : 0<B n) (hmn : (n : ℝ)≤y) : B n≤B y := by
    have hn1 : (1 : ℝ)<n := by exact_mod_cast one_lt_nat_of_doubleLog_pos hn
    exact Real.log_le_log (Real.log_pos hn1)
      (Real.log_le_log (zero_lt_one.trans hn1) hmn)

  constructor
  · refine ⟨hpos.1,hupper _ hpos.1 ?_⟩
    have hn : 1≤(survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 := by
      have := (hgood r).1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hn).trans (hsize r).1
  · refine ⟨hpos.2,hupper _ hpos.2 ?_⟩
    have hn : 1≤(survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 := by
      have := (hgood r).2.1.1.two_le
      omega
    exact (show (largestPrimeFactor ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1) : ℝ) ≤
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) by
      exact_mod_cast largestPrimeFactor_le_self hn).trans (hsize r).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualSurvivingGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Height geometry derived from the chosen actual good witnesses. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- Both the zero and positive first-difference cases have the same concrete
height geometry at their counting endpoint. -/
theorem actual_surviving_geometry : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    1<y → 0<B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    y^(9/10 : ℝ) ≤ wholeWitnessPrime p η i → y^(9/10 : ℝ) ≤ wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ) ≤ y) →
    0<(collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ∧
      ComparisonHeightBounds (survivingPair p q η ξ i (collisionLastIndex x i))
        (B y) (fordBandScale x (collisionLastIndex x i)) := by
  filter_upwards [surviving_factor_heights,eventually_collision_indices,eventually_ge_atTop 4]
    with H hheights hind hH
  filter_upwards [hheights,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hx hm hBx
  intro i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  have him : i < m x := by unfold R at hi; omega
  have hhalf : fordBandScale x i/2 ≤ B y := by
    have hb := fordBandScale_pos (zero_lt_one.trans hBx) him
    linarith
  obtain ⟨hb,hhead,hheight,hbands⟩ := hx i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hhalf hByu hpmin hqmin hsize
  obtain ⟨hHi,hcut,hkL⟩ := hind x hm i hi
  have hk : collisionLastIndex x i < m x := hkL.trans_le (Nat.sub_le _ _)
  obtain ⟨hb',hidx0⟩ := survivingIndex_first (Nat.le_add_right i _) hfirst
  change survivingIndex p q η ξ i (collisionLastIndex x i) ⟨0,hb'⟩=i at hidx0
  have hidx (r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card) :
      survivingIndex p q η ξ i (collisionLastIndex x i) r ≤ collisionLastIndex x i :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp (survivingIndex_mem p q η ξ i (collisionLastIndex x i) r)).1).2
  have hmin : (9/10 : ℝ)*B y ≤ min
      (leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) ⟨0,hb⟩)
      (rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) ⟨0,hb⟩) := le_min hhead.1 hhead.2
  obtain ⟨htail,hbottom,hsep⟩ := ordered_surviving_band_margins hb hBx him hk
    (survivingIndex p q η ξ i (collisionLastIndex x i)) hidx0 hidx hBy hByl
    (collision_last_band_le_half hBx him (by omega) hcut)
    (leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)))
    (rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i))) hmin
    (fun r hr => le_min (hbands r hr).1.1 (hbands r hr).2.1)
    (fun r hr => max_le (hbands r hr).1.2 (hbands r hr).2.2)
  refine ⟨hb,⟨?_,?_,?_,htail,hbottom,hsep⟩⟩
  · intro r
    exact ⟨(hheight r).1.1,(hheight r).2.1⟩
  · intro r
    exact ⟨(hheight r).1.2,(hheight r).2.2⟩
  · intro hb''
    exact hmin

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonGridFromHeights
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Ford grids from surviving prime heights. -/

noncomputable section

namespace TotientAsymptotic

lemma collisionMesh_le_hundredth {h : ℕ} {δ : ℝ} (hh : 4≤h)
    (hδ : δ≤2/(h : ℝ)^32) : δ≤1/100 := by
  have hhR : (4 : ℝ)≤h := by exact_mod_cast hh
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hhR 32
  have h0 : (0 : ℝ)<(h : ℝ)^32 := by positivity
  apply hδ.trans
  apply (div_le_iff₀ h0).mpr
  norm_num at hp
  linarith

/-- The grid label is chosen from the actual paired largest factors. Every
width and separation restriction is proved here, including the one-prime case. -/
theorem comparison_grid_from_heights {b h : ℕ} {t : ShiftedPair b} {Y Z δ : ℝ}
    (hb : 0<b) (hbh : b≤h) (hh : 4≤h) (hY : 0<Y) (_hZ : 0<Z) (hZY : Z≤Y)
    (hδ : 0<δ) (hδu : δ≤2/(h : ℝ)^32)
    (hmargin : (2*(h : ℝ)+10)*δ < (1/10 : ℝ)*Z/Y)
    (ht : ComparisonHeightBounds t Y Z)
    (halign : ∀ r, |leftFactorHeight t r/Y-rightFactorHeight t r/Y| ≤
      (2*(r.val : ℝ)+1)*δ) :
    let u := fun r => leftFactorHeight t r/Y
    let v := fun r => rightFactorHeight t r/Y
    let n := fun r => collisionGridIndex δ (u r) (v r)
    let ζ := (7/10 : ℝ)*Z/Y
    n ∈ collisionGridFamilies δ b ∧
    pairedGridUpper δ ζ n 0=1 ∧ pairedGridUpper δ ζ n b=ζ ∧
    (∀ r : Fin b, pairedGridLower δ n r≤u r ∧ pairedGridLower δ n r≤v r ∧
      u r≤pairedGridUpper δ ζ n r ∧ v r≤pairedGridUpper δ ζ n r) ∧
    (∀ r ∈ Finset.range b,
      pairedGridUpper δ ζ n (r+1)<pairedGridLower δ n r ∧
      pairedGridLower δ n r<pairedGridUpper δ ζ n r) ∧
    pairedGridUpper δ ζ n 1<4/5 ∧
    (∀ r ∈ Finset.Icc 2 b,
      2*δ<pairedGridUpper δ ζ n (r-1)-pairedGridUpper δ ζ n r) := by
  dsimp only
  let u := fun r => leftFactorHeight t r/Y
  let v := fun r => rightFactorHeight t r/Y
  let n := fun r => collisionGridIndex δ (u r) (v r)
  let ζ := (7/10 : ℝ)*Z/Y
  have hu (r : Fin b) : 0≤u r := div_nonneg (ht.positive r).1.le hY.le
  have hv (r : Fin b) : 0≤v r := div_nonneg (ht.positive r).2.le hY.le
  have hu1 (r : Fin b) : u r≤1 := (div_le_one hY).mpr (ht.top r).1
  have hv1 (r : Fin b) : v r≤1 := (div_le_one hY).mpr (ht.top r).2
  have htop : max (u ⟨0,hb⟩) (v ⟨0,hb⟩)≤1 := max_le (hu1 _) (hv1 _)
  have hhead : (4/5 : ℝ)≤ min (u ⟨0,hb⟩) (v ⟨0,hb⟩) := by
    rw [min_div_div_right hY.le]
    apply (le_div_iff₀ hY).mpr
    have hh := ht.head hb
    linarith
  have hdsmall := collisionMesh_le_hundredth hh hδu
  have hζ : ζ≤7/10 := by
    apply (div_le_iff₀ hY).mpr
    exact mul_le_mul_of_nonneg_left hZY (by norm_num)
  have hfirst : pairedGridUpper δ ζ n 1<4/5 := by
    by_cases hb1 : 1<b
    · simp only [pairedGridUpper,one_ne_zero,ite_false, if_false,dite_eq_left hb1]
      have he := (collision_grid_enclosure hδ (hu ⟨1,hb1⟩) (hv ⟨1,hb1⟩)
        (halign ⟨1,hb1⟩)).2.2.2.2
      have hu1 : u ⟨1,hb1⟩≤18/25 := by
        apply (div_le_iff₀ hY).mpr
        exact (le_max_left _ _).trans (ht.tail _ (by norm_num))
      norm_num only [Nat.cast_one] at he
      linarith
    · simpa only [pairedGridUpper,one_ne_zero,ite_false, if_false,dite_eq_right hb1]
        using hζ.trans_lt (by norm_num : (7/10 : ℝ)<4/5)
  have hsep (r : Fin b) (hr : r.val+1<b) :
      max (u ⟨r.val+1,hr⟩) (v ⟨r.val+1,hr⟩)+(2*(r.val+1 : ℕ)+6 : ℝ)*δ <
        min (u r) (v r) := by
    have hs := div_le_div_of_nonneg_right (ht.separated r ⟨r.val+1,hr⟩ (by exact Nat.lt_succ_self _)) hY.le
    have hcoeff : (2*(r.val+1 : ℕ)+6 : ℝ)*δ≤(2*(h : ℝ)+10)*δ := by
      have hrh : (r.val : ℝ)≤h := by exact_mod_cast r.isLt.le.trans hbh
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have hnorm : (1/10 : ℝ)*Z/Y ≤ min (u r) (v r)-max (u ⟨r.val+1,hr⟩) (v ⟨r.val+1,hr⟩) := by
      simpa only [u,v,min_div_div_right hY.le,max_div_div_right hY.le,sub_div] using hs
    linarith
  have hbottom : ζ+3*δ< min (u ⟨b-1,by omega⟩) (v ⟨b-1,by omega⟩) := by
    have hm := div_le_div_of_nonneg_right (ht.bottom ⟨b-1,by omega⟩) hY.le
    have hcoeff : 3*δ≤(2*(h : ℝ)+10)*δ := by
      have : (0 : ℝ)≤h := Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
    have he : (4/5 : ℝ)*Z/Y=ζ+(1/10 : ℝ)*Z/Y := by dsimp [ζ] <;> ring
    rw [he] at hm
    rw [min_div_div_right hY.le]
    linarith
  have hinter := paired_grid_intervals hb hδ u v hu hv halign htop hhead hfirst
    (by
      intro r hr
      have hs := hsep r hr
      have hh : (2*(r.val+1 : ℕ)+4 : ℝ)*δ≤(2*(r.val+1 : ℕ)+6 : ℝ)*δ := by
        exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
      linarith)
    (by linarith [hbottom])
  refine ⟨collisionGridFamilies_mem hδ u v hu1,hinter.1,hinter.2.1,hinter.2.2.1,hinter.2.2.2,hfirst,?_⟩
  exact paired_grid_gaps hb hδ u v hu hv halign hsep hbottom

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualAlignment
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alignment of the two ordered lists of largest factors after prefix cancellation. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Disjoint decreasing bands turn the factor-count argument into an absolute
bound at every paired index. The residual factors are below the lower edge of the prime-factor bands;
this edge may be strictly above the normality parameter, as in the application. -/
theorem ordered_largest_factor_alignment_smooth_cutoff {k D D' : ℕ} (p q : Fin k → ℕ)
    {S Z ε : ℝ} (hSone : 1 < S) (hSZ : S ≤ Z) (hD : D ≠ 0) (hD' : D' ≠ 0)
    (hp : ∀ i, IsNormalPrime S (p i)) (hq : ∀ i, IsNormalPrime S (q i))
    (heq : D*shiftedProduct p = D'*shiftedProduct q)
    (hDs : (largestPrimeFactor D : ℝ) ≤ Z)
    (hD's : (largestPrimeFactor D' : ℝ) ≤ Z)
    (hS : ∀ i, Z ≤ min (largestPrimeFactor (p i-1) : ℝ)
      (largestPrimeFactor (q i-1) : ℝ))
    (hsep : ∀ i j, i < j →
      max (largestPrimeFactor (p j-1) : ℝ) (largestPrimeFactor (q j-1) : ℝ) ≤
      min (largestPrimeFactor (p i-1) : ℝ) (largestPrimeFactor (q i-1) : ℝ))
    (herr : ∀ i, Real.sqrt (B S * B (max (largestPrimeFactor (p i-1) : ℝ)
      (largestPrimeFactor (q i-1) : ℝ))) ≤ ε) :
    ∀ j, |B (largestPrimeFactor (p j-1))-B (largestPrimeFactor (q j-1))| ≤
      (2*(j.val : ℝ)+1)*ε := by
  have hle (r : Fin k → ℕ) (hr : ∀ i, IsNormalPrime S (r i)) (i : Fin k) :
      (largestPrimeFactor (r i-1) : ℝ) ≤ (r i-1 : ℕ) := by
    have hn : r i-1 ≠ 0 := by have := (hr i).1.two_le; omega
    have : largestPrimeFactor (r i-1) ≤ r i-1 := by
      unfold largestPrimeFactor
      apply max_le (by omega)
      apply Finset.sup_le
      intro a ha
      exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors ha)
    exact_mod_cast this
  have hside (r t : Fin k → ℕ) (hr : ∀ i, IsNormalPrime S (r i))
      (ht : ∀ i, IsNormalPrime S (t i)) (E E' : ℕ) (hE : E ≠ 0) (hE' : E' ≠ 0)
      (he : E*shiftedProduct r = E'*shiftedProduct t)
      (hEs : (largestPrimeFactor E : ℝ) ≤ Z)
      (hE's : (largestPrimeFactor E' : ℝ) ≤ Z)
      (hs : ∀ i, Z ≤ min (largestPrimeFactor (r i-1) : ℝ)
        (largestPrimeFactor (t i-1) : ℝ))
      (hord : ∀ i j, i < j →
        max (largestPrimeFactor (r j-1) : ℝ) (largestPrimeFactor (t j-1) : ℝ) ≤
        min (largestPrimeFactor (r i-1) : ℝ) (largestPrimeFactor (t i-1) : ℝ))
      (heps : ∀ i, Real.sqrt (B S * B (max (largestPrimeFactor (r i-1) : ℝ)
        (largestPrimeFactor (t i-1) : ℝ))) ≤ ε)
      (j : Fin k) (hjt : (largestPrimeFactor (t j-1) : ℝ) < largestPrimeFactor (r j-1)) :
      B (largestPrimeFactor (r j-1))-B (largestPrimeFactor (t j-1)) ≤
        (2*(j.val : ℝ)+1)*ε := by
    apply normality_alignment r t j hE hE' hr ht he
      (hEs.trans ((hs j).trans (min_le_right _ _)))
      (hE's.trans ((hs j).trans (min_le_right _ _)))
      (hSZ.trans ((hs j).trans (min_le_right _ _))) hjt
    · simpa only [max_eq_left hjt.le] using heps j
    · intro i hij
      apply le_trans _ (hle r hr i)
      rcases lt_or_eq_of_le hij with hij | rfl
      · exact (le_max_left _ _).trans ((hord i j hij).trans (min_le_left _ _))
      · rfl
    · intro i hij
      exact (le_max_left _ _).trans ((hord i j hij).trans
        ((min_le_right _ _).trans (hle t ht i)))
    · intro i hji
      rcases lt_or_eq_of_le hji with hji | rfl
      · exact (le_max_right _ _).trans ((hord j i hji).trans (min_le_right _ _))
      · rfl
  have hmono {v w : ℝ} (hv : S ≤ v) (hvw : v ≤ w) : B v ≤ B w :=
    Real.log_le_log (Real.log_pos (hSone.trans_le hv))
      (Real.log_le_log (zero_lt_one.trans (hSone.trans_le hv)) hvw)
  intro j
  have hn : 0 ≤ ε := (Real.sqrt_nonneg _).trans (herr j)
  have hbound : 0 ≤ (2*(j.val : ℝ)+1)*ε := by positivity
  rcases lt_trichotomy (largestPrimeFactor (q j-1)) (largestPrimeFactor (p j-1)) with hj | hj | hj
  · have hjR : (largestPrimeFactor (q j-1) : ℝ) < largestPrimeFactor (p j-1) := by exact_mod_cast hj
    have hb := hmono (hSZ.trans ((hS j).trans (min_le_right _ _))) hjR.le
    rw [abs_of_nonneg (sub_nonneg.mpr hb)]
    exact hside p q hp hq D D' hD hD' heq hDs hD's hS hsep herr j hjR
  · simp only [hj, sub_self, abs_zero]
    exact hbound
  · have hjR : (largestPrimeFactor (p j-1) : ℝ) < largestPrimeFactor (q j-1) := by exact_mod_cast hj
    have hb := hmono (hSZ.trans ((hS j).trans (min_le_left _ _))) hjR.le
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hb)]
    exact hside q p hq hp D' D hD' hD heq.symm hD's hDs
      (by simpa only [min_comm] using hS)
      (by simpa only [min_comm, max_comm] using hsep)
      (by simpa only [max_comm] using herr) j hjR

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingBands
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict ordering of the actual surviving largest factors and their cutoff. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma lt_of_doubleLog_lt {u v : ℝ} (_hu : 1 < u) (hv : 1 < v) (h : B u < B v) : u < v := by
  by_contra! hle
  have hh := Real.log_le_log (Real.log_pos hv) (Real.log_le_log (zero_lt_one.trans hv) hle)
  exact (not_le_of_gt h) hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeightAlignment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alignment of prime heights, including the largest prime. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma height_bounds_factor_order {b : ℕ} {t : ShiftedPair b} {Y Z : ℝ}
    (hZ : 0<Z) (ht : ComparisonHeightBounds t Y Z) :
    (∀ r, Real.exp (Real.exp ((7/10 : ℝ)*Z)) <
      min (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ)) ∧
    (∀ r s, r < s → max (largestPrimeFactor (t.left s-1) : ℝ) (largestPrimeFactor (t.right s-1) : ℝ) <
      min (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ)) := by
  have hposL (r : Fin b) : (1 : ℝ)<largestPrimeFactor (t.left r-1) := by
    exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).1
  have hposR (r : Fin b) : (1 : ℝ)<largestPrimeFactor (t.right r-1) := by
    exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).2
  constructor
  · intro r
    have hc := ht.bottom r
    have hlow : (7/10 : ℝ)*Z < min (leftFactorHeight t r) (rightFactorHeight t r) := by linarith
    have he : B (Real.exp (Real.exp ((7/10 : ℝ)*Z)))=(7/10 : ℝ)*Z := by
      simp only [B,Real.log_exp]
    have h1 : 1<Real.exp (Real.exp ((7/10 : ℝ)*Z)) := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
    exact lt_min (lt_of_doubleLog_lt h1 (hposL r) (by rw [he]; exact hlow.trans_le (min_le_left _ _)))
      (lt_of_doubleLog_lt h1 (hposR r) (by rw [he]; exact hlow.trans_le (min_le_right _ _)))
  · intro r s hrs
    have hc := ht.separated r s hrs
    have hh : max (leftFactorHeight t s) (rightFactorHeight t s) <
        min (leftFactorHeight t r) (rightFactorHeight t r) := by linarith
    have hlL : leftFactorHeight t s < leftFactorHeight t r :=
      (le_max_left _ _).trans_lt (hh.trans_le (min_le_left _ _))
    have hlR : leftFactorHeight t s < rightFactorHeight t r :=
      (le_max_left _ _).trans_lt (hh.trans_le (min_le_right _ _))
    have hrL : rightFactorHeight t s < leftFactorHeight t r :=
      (le_max_right _ _).trans_lt (hh.trans_le (min_le_left _ _))
    have hrR : rightFactorHeight t s < rightFactorHeight t r :=
      (le_max_right _ _).trans_lt (hh.trans_le (min_le_right _ _))
    exact max_lt (lt_min (lt_of_doubleLog_lt (hposL s) (hposL r) hlL)
      (lt_of_doubleLog_lt (hposL s) (hposR r) hlR))
      (lt_min (lt_of_doubleLog_lt (hposR s) (hposL r) hrL)
        (lt_of_doubleLog_lt (hposR s) (hposR r) hrR))

lemma alignment_of_height_bounds {b D : ℕ} {t : ShiftedPair b} {y S Z : ℝ}
    (hS : 1<S) (hBS : 0≤B S) (hSZ : S≤Real.exp (Real.exp ((7/10 : ℝ)*Z)))
    (hZ : 0<Z) (ht : ComparisonHeightBounds t (B y) Z)
    (hD : D≠0) (hD' : t.remainder≠0)
    (hnorm : ∀ r, IsNormalPrime S (t.left r) ∧ IsNormalPrime S (t.right r))
    (heq : D*shiftedProduct t.left=t.remainder*shiftedProduct t.right)
    (hsmooth : (largestPrimeFactor D : ℝ)≤Real.exp (Real.exp ((7/10 : ℝ)*Z)))
    (hsmooth' : (largestPrimeFactor t.remainder : ℝ)≤Real.exp (Real.exp ((7/10 : ℝ)*Z))) :
    ∀ r, |leftFactorHeight t r-rightFactorHeight t r| ≤
      (2*(r.val : ℝ)+1)*Real.sqrt (B S*B y) := by
  have ho := height_bounds_factor_order hZ ht
  apply ordered_largest_factor_alignment_smooth_cutoff t.left t.right hS hSZ hD hD'
    (fun r => (hnorm r).1) (fun r => (hnorm r).2) heq hsmooth hsmooth'
    (fun r => (ho.1 r).le) (fun r s hrs => (ho.2 r s hrs).le)
  intro r
  have hb : B (max (largestPrimeFactor (t.left r-1) : ℝ)
      (largestPrimeFactor (t.right r-1) : ℝ)) ≤ B y := by
    rcases le_total (largestPrimeFactor (t.left r-1) : ℝ) (largestPrimeFactor (t.right r-1) : ℝ) with h | h
    · simpa only [max_eq_right h,rightFactorHeight] using (ht.top r).2
    · simpa only [max_eq_left h,leftFactorHeight] using (ht.top r).1
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hBS)

/-- The concrete good collision lists are aligned also when their first
unequal prime is index zero. No extra comparison input is used. -/
theorem actual_surviving_alignment : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1<y → 0<B y → (87/100 : ℝ)*fordBandScale x i≤B y → B y≤2*fordBandScale x i →
    y^(9/10 : ℝ)≤wholeWitnessPrime p η i → y^(9/10 : ℝ)≤wholeWitnessPrime q ξ i →
    (∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      ((survivingPair p q η ξ i (collisionLastIndex x i)).left r-1 : ℕ)≤y ∧
      ((survivingPair p q η ξ i (collisionLastIndex x i)).right r-1 : ℕ)≤y) →
    ∀ r : Fin (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card,
      |leftFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r-
        rightFactorHeight (survivingPair p q η ξ i (collisionLastIndex x i)) r| ≤
        (2*(r.val : ℝ)+1)*Real.sqrt (B (normalityScale x i)*B y) := by
  filter_upwards [actual_surviving_geometry,collision_normality_domain,
    collision_normality_below_cutoff,collision_residual_below_cutoff,eventually_collision_indices]
    with H hgeom hdom hnorm hres hind
  filter_upwards [hgeom,hdom,hnorm,hres,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hg hd hn hr hm hBx
  intro i p q hi hL hR hp η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hsize
  have him : i < m x := hi.trans_lt (hR.trans hL)
  have hbi := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hhalf : fordBandScale x i/2≤B y := by linarith
  have hk := (hind x hm i hi).2.2
  have hkm := hk.trans hL
  have hbk := fordBandScale_pos (zero_lt_one.trans hBx) hkm
  have hd0 := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := collisionLastIndex x i))
  have hd1 := Nat.totient_pos.mpr (suffixPreimage_pos hξ (i := collisionLastIndex x i))
  obtain ⟨_,ht⟩ := hg i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hsize
  obtain ⟨hSb,hBS,_⟩ := hd i hi y hy hhalf
  apply alignment_of_height_bounds (lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hSb) (by linarith) (hn i hi).le hbk ht hd0.ne' hd1.ne'
    (fun r => ⟨(surviving_good_conditions hi hgη hgξ r).1,
      (surviving_good_conditions hi hgη hgξ r).2.1⟩)
    (surviving_collision_identity hη hξ hp hL hR hk (Nat.le_add_right _ _) heq hfirst hcommon)
    (hr i hi η hη).le (hr i hi ξ hξ).le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingAlignment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality aligns the actual surviving shifted-prime lists. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma normalized_alignment_bound {u v B e : ℝ} {j : ℕ} (hB : 0 < B)
    (h : |u-v| ≤ (2*(j : ℝ)+1)*e) :
    |u/B-v/B| ≤ (2*(j : ℝ)+1)*(e/B) := by
  rw [← sub_div,abs_div,abs_of_pos hB]
  exact (div_le_div_of_nonneg_right h hB.le).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SurvivingBlockSize
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact block values and bounds for both surviving shifted-prime lists. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- A dyadic bound on the full block bounds every surviving shift on either
side, after cancellation and with both residual factors retained. -/
theorem surviving_shift_le_block {x y : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hξ : IsBasicRemainder x H ξ) (hp : p.Prime)
    (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) (hik : i ≤ k)
    (hv : tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ))
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i)
    (hcommon : ∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j)
    (hsize : (witnessBlockValue p η i k : ℝ) ≤ y) :
    ∀ r : Fin (collisionSurvivors p q η ξ i k).card,
      ((survivingPair p q η ξ i k).left r-1 : ℕ) ≤ y ∧
      ((survivingPair p q η ξ i k).right r-1 : ℕ) ≤ y := by
  have heq := surviving_collision_identity hη hξ hp hL hR hk hik hv hfirst hcommon
  have hrpos := collisionCanceledProduct_pos hη hp hk.le (q := q) (ξ := ξ) (i := i)
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := k))
  have hprodpos : 0 < (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left := by
    apply Nat.mul_pos hDpos
    apply Finset.prod_pos
    intro r _
    have hj := (Finset.mem_filter.mp (survivingIndex_mem p q η ξ i k r)).1
    have hjk := (Finset.mem_Icc.mp hj).2
    change 0 < wholeWitnessPrime p η (survivingIndex p q η ξ i k r)-1
    by_cases hz : survivingIndex p q η ξ i k r=0
    · simpa only [wholeWitnessPrime,hz,ite_true, if_true] using Nat.sub_pos_of_lt hp.one_lt
    · simp only [wholeWitnessPrime,ite_eq_right hz]
      exact Nat.sub_pos_of_lt (hη.2.1 _ (Finset.mem_Icc.mpr ⟨by omega,hjk.trans hk.le⟩)).1.one_lt
  have hfactor : collisionCanceledProduct p q η ξ i k*
      ((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left)=
      witnessBlockValue p η i k := by
    rw [mul_left_comm,canceled_surviving_product]
    rfl
  have hnat : (suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left ≤
      witnessBlockValue p η i k := by
    rw [← hfactor]
    exact Nat.le_mul_of_pos_left _ hrpos
  have hle : (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) ≤ y :=
    (show (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) ≤
      witnessBlockValue p η i k by exact_mod_cast hnat).trans hsize
  intro r
  constructor
  · exact (show (((survivingPair p q η ξ i k).left r-1 : ℕ) : ℝ) ≤
      (((suffixPreimage η k).totient*shiftedProduct (survivingPair p q η ξ i k).left : ℕ) : ℝ) by
        exact_mod_cast Nat.le_of_dvd hprodpos ((shifted_factor_dvd _ r).trans (dvd_mul_left _ _))).trans hle
  · rw [heq] at hprodpos hle
    exact (show (((survivingPair p q η ξ i k).right r-1 : ℕ) : ℝ) ≤
      (((survivingPair p q η ξ i k).remainder*shiftedProduct (survivingPair p q η ξ i k).right : ℕ) : ℝ) by
        exact_mod_cast Nat.le_of_dvd hprodpos ((shifted_factor_dvd _ r).trans (dvd_mul_left _ _))).trans hle

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualComparisonCutoffs
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite cutoffs for the actual collision comparison. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma exp_exp_doubleLog {w : ℝ} (hw : 1< w) : Real.exp (Real.exp (B w))=w := by
  rw [B,Real.exp_log (Real.log_pos hw),Real.exp_log (zero_lt_one.trans hw)]

lemma comparisonCutoffs_interval {y w l u : ℝ} (hBy : 0< B y) (hw : 1< w)
    (hl : l≤ B w/B y) (hu : B w/B y≤ u) :
    Real.exp (Real.exp (B y*l))≤ w ∧ w≤ Real.exp (Real.exp (B y*u)) := by
  have hl' := (le_div_iff₀ hBy).mp hl
  have hu' := (div_le_iff₀ hBy).mp hu
  constructor
  · rw [← exp_exp_doubleLog hw]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))
  · rw [← exp_exp_doubleLog hw]
    exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith))

/-- The normalized grid constructed from a collision has all of Ford's
parameter restrictions. The small integer bounds are precisely the previously
proved residual and canceled-product size conclusions. -/
theorem actual_comparison_parameters_oai : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i≤ R x H → L x H< m x → R x H< L x H → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η → IsBasicRemainder x H ξ →
    GoodWitnessConditions p η → GoodWitnessConditions q ξ →
    tupleValue (witnessTuple p η)=tupleValue (witnessTuple q ξ) →
    wholeWitnessPrime p η i≠wholeWitnessPrime q ξ i →
    (∀ j < i, wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) → ∀ y : ℝ,
    1< y → 0< B y → (87/100 : ℝ)*fordBandScale x i≤ B y → B y≤2*fordBandScale x i →
    y^(9/10 : ℝ)≤ wholeWitnessPrime p η i → y^(9/10 : ℝ)≤ wholeWitnessPrime q ξ i →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ)≤ y →
    (collisionResidual η i : ℝ)≤ y^(1/100 : ℝ) →
    (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ)≤ y^(1/10 : ℝ) →
    let t := survivingPair p q η ξ i (collisionLastIndex x i)
    let Z := fordBandScale x (collisionLastIndex x i)
    let δ := collisionMesh x y i
    let U := comparisonCutoffs y (pairLowerCoordinates t y δ)
    let Y := comparisonCutoffs y (pairUpperCoordinates t y Z δ)
    pairGridLabel t y δ∈collisionGridFamilies δ (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card ∧
    FordComparisonParameters (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U ∧
    FordComparisonConditions (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
      y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) Y U t := by
  filter_upwards [actual_surviving_geometry,actual_surviving_alignment,collisionMesh_bound,
    collision_normality_domain,collision_normality_below_cutoff,collision_residual_below_cutoff,eventually_collision_indices,
    collision_endpoints_eventually ford_parameters_of_normalized_grid,
    collision_endpoints_eventually surviving_comparison_conditions,eventually_ge_atTop 4]
    with H hgeom halign hmesh hdomain hScut hres hind hparam hcond hH
  filter_upwards [hgeom,halign,hmesh,hdomain,hScut,hres,hparam,hcond,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hg ha hd hdom hSc hres hp hc hm hBx
  intro i p q hi hL hR hprime η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hsize hDy hry
  dsimp only
  let t := survivingPair p q η ξ i (collisionLastIndex x i)
  let b := (collisionSurvivors p q η ξ i (collisionLastIndex x i)).card
  let Z := fordBandScale x (collisionLastIndex x i)
  let δ := collisionMesh x y i
  have him : i< m x := hi.trans_lt (hR.trans hL)
  have hbi := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hhalf : fordBandScale x i/2≤ B y := by linarith
  obtain ⟨hHi,hcut,hkL⟩ := hind x hm i hi
  have hk : collisionLastIndex x i< m x := hkL.trans hL
  have hZ : 0< Z := fordBandScale_pos (zero_lt_one.trans hBx) hk
  have hh : 4≤ m x-i := hH.trans hHi
  have hshift := surviving_shift_le_block hη hξ hprime hL hR hkL (Nat.le_add_right _ _) heq hfirst hcommon hsize
  obtain ⟨hb,ht⟩ := hg i p q hi η ξ hη hξ hgη hgξ hfirst y hy hBy hByl hByu hpmin hqmin hshift
  have hbcard : b≤ m x-i := by
    have hc := Finset.card_filter_le (Finset.Icc i (collisionLastIndex x i))
      (fun j => wholeWitnessPrime p η j≠wholeWitnessPrime q ξ j)
    change b≤_ at hc
    simp only [Nat.card_Icc] at hc
    unfold collisionLastIndex at hc
    omega
  have hδ : 0<δ := collisionMesh_pos hbi hBy
  have hδu : δ≤2/((m x-i : ℕ) : ℝ)^32 := hd i hi y hBy hhalf
  have hmargin : (2*((m x-i : ℕ) : ℝ)+10)*δ<(1/10 : ℝ)*Z/B y :=
    (collision_rounding_margin hh hδu).trans
      (normalized_factor_margin hh hBx him hcut rfl hBy hByu)
  have hZY : Z≤ B y := by
    have hl := collision_last_band_le_half hBx him (by omega) hcut
    exact hl.trans hhalf
  have hn := comparison_grid_from_heights hb hbcard hh hBy hZ hZY hδ hδu hmargin ht
    (fun r => normalized_alignment_bound hBy
      (ha i p q hi hL hR hprime η ξ hη hξ hgη hgξ heq hfirst hcommon y hy hBy hByl hByu hpmin hqmin hshift r))
  obtain ⟨hnmem,hν0,hνb,hinterval,horder,hν1,hgap⟩ := hn
  have hνb' : pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ) b=(7/10 : ℝ)*Z/B y := hνb
  obtain ⟨hS,hBS,hSy⟩ := hdom i hi y hy hhalf
  have hYb : comparisonCutoffs y (pairUpperCoordinates t y Z δ) b=collisionSmoothCutoff x i := by
    change Real.exp (Real.exp (B y*pairedGridUpper δ ((7/10 : ℝ)*Z/B y) (pairGridLabel t y δ) b))=_
    rw [hνb']
    congr 2
    change B y*((7/10 : ℝ)*Z/B y)=(7/10 : ℝ)*Z
    field_simp
  refine ⟨hnmem,?_,?_⟩
  · apply hp i hi y hy hhalf b (collisionResidual η i)
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i)) (normalityScale x i)
      (pairUpperCoordinates t y Z δ) (pairLowerCoordinates t y δ) hb hν0 hS
    · rw [hYb]
      exact (hSc i hi).le
    · exact horder
    · exact hν1.le
    · intro j hj
      rw [← collisionMesh_eq_sqrt_ratio (by linarith : 0≤ B (normalityScale x i))]
      exact hgap j hj
    · exact Nat.totient_pos.mpr (suffixPreimage_pos hη)
    · exact hDy
    · rw [hYb]
      exact (hres i hi η hη).le
    · exact collisionCanceledProduct_pos hη hprime hkL.le
    · exact hry
  · apply hc i hi y hy hhalf hη hξ hprime hL hR hi hkL heq hfirst hcommon hgη hgξ
      (comparisonCutoffs y (pairUpperCoordinates t y Z δ))
      (comparisonCutoffs y (pairLowerCoordinates t y δ))
      (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hS)
      (by linarith) hSy hYb
    · intro r
      have hl := comparisonCutoffs_interval hBy
        (by exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).1)
        (hinterval r).1 (hinterval r).2.2.1
      have hr := comparisonCutoffs_interval hBy
        (by exact_mod_cast one_lt_nat_of_doubleLog_pos (ht.positive r).2)
        (hinterval r).2.1 (hinterval r).2.2.2
      exact ⟨hl.1,hl.2,hr.1,hr.2⟩
    · exact hsize
    · exact (hres i hi ξ hξ).le
    · exact hpmin
    · exact (Real.one_lt_exp_iff.mpr (Real.exp_pos _)).le
    · apply Real.exp_le_exp.mpr
      apply Real.exp_le_exp.mpr
      have hν1' : pairUpperCoordinates t y Z δ 1 < 4/5 := hν1
      change B y*pairUpperCoordinates t y Z δ 1 ≤ (4/5 : ℝ)*B y
      nlinarith


end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.actual_comparison_parameters_oai := @OAI.TotientAsymptotic.actual_comparison_parameters_oai
