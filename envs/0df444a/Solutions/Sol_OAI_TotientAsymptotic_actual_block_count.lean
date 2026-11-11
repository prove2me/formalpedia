-- Prove2me | solution 1 for OAI.TotientAsymptotic.actual_block_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:53.071367+00:00
-- url     : https://prove2.me/submissions/c88b031d-6e8b-4641-b1f1-6ec474f6c53d

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
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_TotientAsymptotic
import Definitions.Def_OAIQ233A000
import Theorems.Thm_OAI_TotientAsymptotic_actual_collision_exponent
import Theorems.Thm_OAI_TotientAsymptotic_actual_comparison_parameters

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionSlack
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative strict slack in the published comparison exponent. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma comparison_log_power_saving {y E σ : ℝ} (hy : 1 ≤ Real.log y)
    (hE : E ≤ -1-σ) :
    (Real.log y)^E ≤ (Real.log y)⁻¹*Real.exp (-σ*B y) := by
  calc
    _ ≤ (Real.log y)^(-1-σ) := Real.rpow_le_rpow_of_exponent_le hy hE
    _ = (Real.log y)⁻¹*Real.exp (-σ*B y) := by
      rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hy)]
      change Real.exp (B y*(-1-σ)) = _
      rw [mul_sub, mul_neg_one, Real.exp_sub, Real.exp_neg]
      rw [show Real.exp (B y) = Real.log y from
        Real.exp_log (lt_of_lt_of_le zero_lt_one hy)]
      rw [neg_mul, Real.exp_neg]
      simp [div_eq_mul_inv, mul_comm]

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

lemma m_le_log_B : ∀ᶠ x : ℝ in atTop, (m x : ℝ) ≤ Real.log (B x)/lam := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (Real.exp 1 : ℝ)),
    (psi_tendsto.comp B_tendsto).eventually (eventually_ge_atTop (0 : ℝ))] with x hB hpsi
  have hlog : 1 < Real.log (B x) := by rwa [Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hB)]
  have hfloor := Nat.floor_le hpsi
  change (m x : ℝ) ≤ psi (B x) at hfloor
  exact hfloor.trans (by
    unfold psi
    exact div_le_div_of_nonneg_right (sub_le_self _ (Real.log_nonneg hlog.le)) lam_pos.le)

/-- The total logarithmic size of a basic remainder is uniformly smaller
than the largest-prime scale. -/
theorem basic_remainder_log_small (H : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      Real.log (suffixPreimage η 0 : ℝ) ≤ (Real.log x)^(4/5 : ℝ) := by
  let C := Real.exp (2*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹)
  have hsmall : Tendsto (fun b : ℝ => (Real.log b/lam)*Real.exp (-(1/10 : ℝ)*b)+
      C*Real.exp (-(4/5 : ℝ)*b)) atTop (nhds 0) := by
    have he : Tendsto (fun b : ℝ => b*Real.exp (-(1/10 : ℝ)*b)) atTop (nhds 0) := by
      simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/10) (by norm_num : (0 : ℝ)<1/10)
    have he' : Tendsto (fun b : ℝ => Real.log b*Real.exp (-(1/10 : ℝ)*b)) atTop (nhds 0) := by
      apply squeeze_zero'
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
        exact mul_nonneg (Real.log_nonneg hb) (Real.exp_pos _).le
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
        exact mul_le_mul_of_nonneg_right (Real.log_le_self (zero_le_one.trans hb)) (Real.exp_pos _).le
      · exact he
    have hce : Tendsto (fun b : ℝ => Real.exp (-(4/5 : ℝ)*b)) atTop (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      exact tendsto_id.const_mul_atTop_of_neg (by norm_num)
    simpa only [div_mul_eq_mul_div, zero_div, mul_zero, add_zero] using
      (he'.div_const lam).add (hce.const_mul C)
  filter_upwards [m_le_log_B, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℝ), m_tendsto.eventually (eventually_gt_atTop (P H)),
    theta_eventually_mem, (hsmall.comp B_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (9/10 : ℝ)<1))]
    with x hm hB hx hPm htheta hs hB1 hratio
  intro η hη
  have hmpos : 0 < m x := by omega
  have hb0 : bandScale x 0 ≤ (10/9 : ℝ)*B x := by
    have hf := fordBandScale_eq_ratio_mul hB1 hmpos
    have he : fordBandScale x 0 = B x := by simp [fordBandScale]
    rw [he] at hf
    nlinarith [bandScale_nonnegative x 0]
  have hb1 : (11/10 : ℝ)*bandScale x 1 ≤ (7/10 : ℝ)*B x := by
    have hb := bandScale_succ_le x 0
    have hr := collision_rho_bounds.2
    have hp := bandScale_nonnegative x 0
    have : bandScale x 1 ≤ (137/250 : ℝ)*((10/9 : ℝ)*B x) :=
      hb.trans (mul_le_mul hr.le hb0 hp (by norm_num))
    nlinarith
  have hbL : bandScale x (L x H) ≤ (lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ := by
    have he : m x-L x H = P H := by unfold L; omega
    simp only [bandScale, he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (alpha_le _ htheta) (Nat.cast_nonneg _))
      (inv_nonneg.mpr (pow_pos rho_pos _).le)
  have hbound := basic_suffix_log_bound hη (j := 0)
  have hlast : Real.exp (2*bandScale x (L x H)) ≤ C :=
    Real.exp_le_exp.mpr (by nlinarith [hbL])
  have hmL0 : (L x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) (P H)
  have hmL : (L x H : ℝ) ≤ Real.log (B x)/lam := hmL0.trans hm
  have hlog : Real.log (suffixPreimage η 0 : ℝ) ≤
      (Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C := by
    simp only [Nat.sub_zero] at hbound
    exact hbound.trans (add_le_add (mul_le_mul hmL (Real.exp_le_exp.mpr hb1)
      (Real.exp_pos _).le (div_nonneg (Real.log_nonneg hB1.le) lam_pos.le)) hlast)
  have heq : ((Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C)*
      Real.exp (-(4/5 : ℝ)*B x) =
      (Real.log (B x)/lam)*Real.exp (-(1/10 : ℝ)*B x)+C*Real.exp (-(4/5 : ℝ)*B x) := by
    rw [add_mul, mul_assoc, ← Real.exp_add]
    rw [show (7/10 : ℝ)*B x+(-(4/5 : ℝ)*B x) = -(1/10 : ℝ)*B x by ring]
  have hlt : (Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C ≤ Real.exp ((4/5 : ℝ)*B x) := by
    have ht : ((Real.log (B x)/lam)*Real.exp ((7/10 : ℝ)*B x)+C)*Real.exp (-(4/5 : ℝ)*B x) < 1 := by rwa [heq]
    have hh := mul_lt_mul_of_pos_right ht (Real.exp_pos ((4/5 : ℝ)*B x))
    rw [mul_assoc, ← Real.exp_add] at hh
    norm_num at hh
    exact hh.le
  apply hlog.trans (hlt.trans_eq ?_)
  rw [Real.rpow_def_of_pos (Real.log_pos hx)]
  congr 1
  simp only [B]
  ring

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

lemma collisionCanceledProduct_le_suffix {x : ℝ} {H i k p q : ℕ}
    {η ξ : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hk : k ≤ L x H)
    (hfirst : wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i) :
    collisionCanceledProduct p q η ξ i k ≤ suffixPreimage η i := by
  let I := (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j)
  have hsub : I ⊆ Finset.Icc (i+1) (L x H) := by
    intro j hj
    obtain ⟨hj,he⟩ := Finset.mem_filter.mp hj
    have hji := Finset.mem_Icc.mp hj
    have hne : j ≠ i := by intro hh; subst j; exact hfirst he
    exact Finset.mem_Icc.mpr ⟨by omega,hji.2.trans hk⟩
  have hle : collisionCanceledProduct p q η ξ i k ≤ ∏ j ∈ I, remainderPrime η j := by
    apply Finset.prod_le_prod'
    intro j hj
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp (hsub hj)).1; omega
    simpa only [wholeWitnessPrime,ite_eq_right hj0] using Nat.sub_le (remainderPrime η j) 1
  have hrest : (∏ j ∈ I, remainderPrime η j) ≤ ∏ j ∈ Finset.Icc (i+1) (L x H), remainderPrime η j := by
    apply Finset.prod_le_prod_of_subset_of_one_le' hsub
    intro j hj _
    exact (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj).1; omega,(Finset.mem_Icc.mp hj).2⟩)).1.pos
  exact (hle.trans hrest).trans (Nat.le_mul_of_pos_left _ hη.1)

lemma small_suffix_factor_size {p n N : ℕ} {y : ℝ} (hp : 3 ≤ p)
    (hn : 0 < n) (hnN : n ≤ N) (hy : ((p-1 : ℕ) : ℝ) ≤ y)
    (hsmall : Real.log (N : ℝ) ≤ (1/1000 : ℝ)*Real.log p) :
    (n : ℝ) ≤ y^(1/100 : ℝ) := by
  have hp1 : (1 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 2 ≤ p-1 by omega)
  have hy1 : 1 < y := hp1.trans_le hy
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpbound : p ≤ (p-1)^2 := by
    have he : p-1+1=p := by omega
    have hh : 2 ≤ p-1 := by omega
    nlinarith
  have hl := Real.log_le_log hp0 (show (p : ℝ) ≤ ((p-1 : ℕ) : ℝ)^2 by exact_mod_cast hpbound)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hly := Real.log_le_log (zero_lt_one.trans hp1) hy
  have hln := Real.log_le_log (by exact_mod_cast hn : (0 : ℝ) < n)
    (show (n : ℝ) ≤ N by exact_mod_cast hnN)
  apply (Real.log_le_log_iff (by exact_mod_cast hn : (0 : ℝ) < n)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hy1) _)).mp
  rw [Real.log_rpow (zero_lt_one.trans hy1)]
  linarith [Real.log_pos hy1]

/-- Both the fixed residual totient and the product of canceled shifts are
small enough for the original published Ford lemma. No new counting input is
used for these hypotheses. -/
theorem collision_small_factors : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i k p q : ℕ, 1 ≤ i → i ≤ R x H → i+2 ≤ L x H → L x H < m x →
    i ≤ k → k < L x H → ∀ η ξ : RemainderDatum (L x H),
    IsBasicRemainder x H η → 3 ≤ remainderPrime η i →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ,
    ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y →
    ((suffixPreimage η k).totient : ℝ) ≤ y^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ i k : ℝ) ≤ y^(1/100 : ℝ) := by
  filter_upwards [collision_tail_log_small] with H hH
  filter_upwards [hH] with x hx
  intro i k p q hi hiR hiL hL hik hk η ξ hη hp hfirst y hy
  have ht := hx i hi hiR hiL hL η hη
  have hDpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := k))
  have hDdvd : (suffixPreimage η k).totient ∣ (suffixPreimage η i).totient := by
    rw [basic_suffix_totient_split hη hL hik hk]
    exact dvd_mul_right _ _
  have hDle := (Nat.le_of_dvd (Nat.totient_pos.mpr (suffixPreimage_pos hη)) hDdvd).trans
    (Nat.totient_le (suffixPreimage η i))
  refine ⟨small_suffix_factor_size hp hDpos hDle hy ht,?_⟩
  have hrpos : 0 < collisionCanceledProduct p q η ξ i k := by
    apply Finset.prod_pos
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).1
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj').1; omega
    simp only [wholeWitnessPrime,ite_eq_right hj0]
    exact Nat.sub_pos_of_lt (hη.2.1 j (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hj').1; omega,(Finset.mem_Icc.mp hj').2.trans hk.le⟩)).1.one_lt
  exact small_suffix_factor_size hp hrpos (collisionCanceledProduct_le_suffix hη hk.le hfirst) hy ht

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite interval choices for the paired normalized largest factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma collisionGridFamilies_card (δ : ℝ) (b : ℕ) :
    (collisionGridFamilies δ b).card = (⌊1/δ⌋₊+1)^b := by
  simp [collisionGridFamilies]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeWindow
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform largest-prime windows for the actual subpower prefix denominators. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma subpower_log_ratio :
    Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x) atTop (nhds 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/5)).comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [show -(1/5 : ℝ) = 4/5-1 by norm_num, Real.rpow_sub (Real.log_pos hx), Real.rpow_one]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionHeadSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-index collision uses the original endpoint and a subpower tail. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma basic_remainder_subpower (H : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      (suffixPreimage η 0 : ℝ) ≤ x^ε := by
  filter_upwards [basic_remainder_log_small H,
    subpower_log_ratio.eventually (eventually_lt_nhds hε),eventually_gt_atTop (1 : ℝ)] with x hx hs hx1
  intro η hη
  have hlog : (Real.log x)^(4/5 : ℝ) ≤ ε*Real.log x :=
    (div_le_iff₀ (Real.log_pos hx1)).mp hs.le
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx1)]
  apply (Real.log_le_iff_le_exp (by exact_mod_cast suffixPreimage_pos hη (i := 0) :
    (0 : ℝ) < suffixPreimage η 0)).mp
  simpa only [mul_comm] using (hx η hη).trans hlog

/-- At the first differing head prime, both the fixed residual and every
canceled shift already fit under the original endpoint to power `1/100`. -/
theorem collision_head_small_factors (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ k p q : ℕ, L x H < m x → k < L x H → p.Prime → p ≠ q →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η →
    ((suffixPreimage η k).totient : ℝ) ≤ x^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ 0 k : ℝ) ≤ x^(1/100 : ℝ) := by
  filter_upwards [basic_remainder_subpower H (show (0 : ℝ) < 1/100 by norm_num)] with x hx
  intro k p q hL hk hp hpq η ξ hη
  have hbound := hx η hη
  have hdvd : (suffixPreimage η k).totient ∣ (suffixPreimage η 0).totient := by
    rw [basic_suffix_totient_split hη hL (Nat.zero_le k) hk]
    exact dvd_mul_right _ _
  have hDle := (Nat.le_of_dvd (Nat.totient_pos.mpr (suffixPreimage_pos hη)) hdvd).trans
    (Nat.totient_le (suffixPreimage η 0))
  constructor
  · exact (show ((suffixPreimage η k).totient : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hDle).trans hbound
  · have hrle := collisionCanceledProduct_le_suffix hη hk.le
      (show wholeWitnessPrime p η 0 ≠ wholeWitnessPrime q ξ 0 from hpq)
    exact (show (collisionCanceledProduct p q η ξ 0 k : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hrle).trans hbound

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionAllSize
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's small integer conditions at every first difference, including zero. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem collision_small_factors_all : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ, 1 ≤ y →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ) ≤ y → (i=0 → y=x) →
    (collisionResidual η i : ℝ) ≤ y^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ) ≤ y^(1/10 : ℝ) := by
  filter_upwards [collision_small_factors,eventually_collision_indices,eventually_tail_cut_separated]
    with H hsmall hind hsep
  filter_upwards [hsmall,collision_head_small_factors H,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hs hhead hm
  intro i p q hi hL hp η ξ hη hfirst y hy hsize hzero
  have hk := (hind x hm i hi).2.2
  have hsmall' : (collisionResidual η i : ℝ) ≤ y^(1/100 : ℝ) ∧
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ) ≤ y^(1/100 : ℝ) := by
    by_cases hz : i=0
    · have hyx := hzero hz
      subst i
      subst y
      exact hhead _ p q hL hk hp hfirst η ξ hη
    · have hip : 1 ≤ i := by omega
      have hiL : i+2 ≤ L x H := by unfold R L at *; omega
      have hpi := basic_remainder_prime_ge_three hη
        (Finset.mem_Icc.mpr ⟨hip,by omega⟩) (by omega)
      have hv := hsize
      rw [witnessBlockValue_positive (p := p) (k := collisionLastIndex x i) hη hL hip (Nat.le_add_right _ _) hk] at hv
      have hp1 : ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y := by
        have hn := Nat.le_mul_of_pos_right (remainderPrime η i-1)
          (Nat.totient_pos.mpr (suffixPreimage_pos hη (i := i)))
        exact (show ((remainderPrime η i-1 : ℕ) : ℝ) ≤
          ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) by exact_mod_cast hn).trans hv
      exact hs i (collisionLastIndex x i) p q hip hi hiL hL (Nat.le_add_right _ _) hk
        η ξ hη hpi hfirst y hp1
  refine ⟨hsmall'.1,hsmall'.2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)

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

lemma chosenRemainder_good {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsGoodTuple x H t τ) : GoodWitnessConditions τ.head (chosenRemainder x H τ.tail) :=
  hτ.2 _ (chosenRemainder_spec hτ.1.2.2.1).1 (chosenRemainder_spec hτ.1.2.2.1).2

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleRecovery
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The prime-occurrence allocation bound in equations (residual-factorization)
and (tuple-recovery-cost). Repeated prime factors are counted with multiplicity.
-/

open scoped BigOperators

namespace TotientAsymptotic

private lemma prod_update_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι) {p : ℕ} (hp : p ∣ f i) :
    (∏ j, Function.update f i (f i / p) j) = (∏ j, f j) / p := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  simpa [Nat.mul_comm] using (Nat.mul_div_assoc (∏ j ∈ Finset.univ.erase i, f j) hp).symm

private lemma update_div_injOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ι → ℕ)) (i : ι) (p : ℕ)
    (hS : ∀ f ∈ S, p ∣ f i) :
    Set.InjOn (fun (f : ι → ℕ) => Function.update f i (f i / p)) (↑S : Set (ι → ℕ)) := by
  intro f hf f' hf' he
  funext j
  by_cases hji : j = i
  · subst j
    have hh := congrFun he i
    simp only [Function.update_self] at hh
    calc
      f i = (f i / p) * p := (Nat.div_mul_cancel (hS f hf)).symm
      _ = (f' i / p) * p := congrArg (fun t => t*p) hh
      _ = f' i := Nat.div_mul_cancel (hS f' hf')
  · simpa [Function.update_of_ne hji] using congrFun he j

/-- Ordered factorizations into `k` labeled slots are bounded by assigning each
prime occurrence to a slot. The finite set may contain any chosen restrictions. -/
theorem ordered_factorizations_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (hn : 0 < n) (T : Finset (ι → ℕ))
    (hT : ∀ f ∈ T, ∏ i, f i = n) :
    T.card ≤ (Fintype.card ι)^n.primeFactorsList.length := by
  classical
  induction n using Nat.strong_induction_on generalizing T with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      have hf (f : ι → ℕ) (hf : f ∈ T) (i : ι) : f i = 1 := by
        apply Nat.dvd_one.mp
        rw [← hT f hf]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
      have hc : T.card ≤ 1 := Finset.card_le_one.mpr (fun f hff f' hff' =>
        funext (fun i => (hf f hff i).trans (hf f' hff' i).symm))
      simpa using hc
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hquot : 0 < n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
      have hlt : n/p < n := Nat.div_lt_self hn hp.one_lt
      let S : ι → Finset (ι → ℕ) := fun i => T.filter (fun f => p ∣ f i)
      let U : ι → Finset (ι → ℕ) := fun i =>
        (S i).image (fun f => Function.update f i (f i/p))
      have hU (i : ι) : (U i).card ≤ (Fintype.card ι)^(n/p).primeFactorsList.length := by
        apply ih (n/p) hlt hquot (U i)
        intro f hf
        obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
        have hf'' := Finset.mem_filter.mp hf'
        rw [prod_update_div f' i hf''.2, hT f' hf''.1]
      have hS (i : ι) : (S i).card = (U i).card := by
        symm
        apply Finset.card_image_of_injOn
        exact update_div_injOn (S i) i p (fun f hf => (Finset.mem_filter.mp hf).2)
      have hcover : T ⊆ Finset.univ.biUnion S := by
        intro f hf
        have hdiv : p ∣ ∏ i, f i := by rw [hT f hf]; exact hpn
        obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff f).mp hdiv
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hf, hi⟩⟩
      have hlength : n.primeFactorsList.length = 1+(n/p).primeFactorsList.length := by
        have hprod : p*(n/p) = n := Nat.mul_div_cancel' hpn
        have hperm := Nat.perm_primeFactorsList_mul hp.ne_zero hquot.ne'
        rw [hprod, Nat.primeFactorsList_prime hp] at hperm
        simpa [Nat.add_comm] using hperm.length_eq
      calc
        T.card ≤ (Finset.univ.biUnion S).card := Finset.card_le_card hcover
        _ ≤ ∑ i, (S i).card := Finset.card_biUnion_le
        _ = ∑ i, (U i).card := Finset.sum_congr rfl (fun i _ => hS i)
        _ ≤ ∑ _i : ι, (Fintype.card ι)^(n/p).primeFactorsList.length :=
          Finset.sum_le_sum (fun i _ => hU i)
        _ = (Fintype.card ι)^n.primeFactorsList.length := by
          rw [hlength, pow_add]
          simp

lemma prefixDatumEncoding_injOn {n : ℕ} (T : Finset (PrefixDatum n))
    (hT : ∀ t ∈ T, ∀ i, 1 ≤ t.primes i) :
    Set.InjOn prefixDatumEncoding (↑T : Set (PrefixDatum n)) := by
  intro t ht u hu he
  have hd : t.d = u.d := by
    have h := congrFun he 0
    simpa [prefixDatumEncoding] using h
  have hp : t.primes = u.primes := by
    funext i
    have h := congrFun he i.succ
    simp only [prefixDatumEncoding, Fin.cons_succ] at h
    have ht1 := hT t ht i
    have hu1 := hT u hu i
    omega
  cases t
  cases u
  simp_all

/-- Concrete tuple data inside a residual totient are bounded by the ordered
factorization estimate. The tail totient is a separate, final factor. -/
theorem prefixData_card_le {n D : ℕ} (hD : 0 < D) (T : Finset (PrefixDatum n))
    (hp : ∀ t ∈ T, ∀ i, 1 ≤ t.primes i)
    (hprod : ∀ t ∈ T, t.d * (∏ i, (t.primes i-1)) = D) :
    T.card ≤ (n+1)^D.primeFactorsList.length := by
  classical
  let E := T.image prefixDatumEncoding
  have hE : ∀ f ∈ E, ∏ i, f i = D := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    simpa only [prefixDatumEncoding, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      using hprod t ht
  have hcard : E.card = T.card := Finset.card_image_of_injOn (prefixDatumEncoding_injOn T hp)
  have h := ordered_factorizations_card_le D hD E hE
  simpa only [hcard, Fintype.card_fin] using h

end TotientAsymptotic

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting the residual tuple data forgotten by Ford's comparison map. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma recovered_pair_fiber_bound {b n D : ℕ}
    (Q : Finset (RecoveredPair b n)) (t : ShiftedPair b)
    (hD : 0 < D) (ht : 0 < t.remainder)
    (hp : ∀ q ∈ Q, (∀ i, 1 ≤ q.2.1.primes i) ∧ (∀ i, 1 ≤ q.2.2.primes i))
    (hprod : ∀ q ∈ Q,
      q.2.1.d * (∏ i, (q.2.1.primes i-1)) = D ∧
      q.2.2.d * (∏ i, (q.2.2.primes i-1)) = q.1.remainder) :
    (Q.filter (fun q => q.1 = t)).card ≤
      (n+1)^(D.primeFactorsList.length+t.remainder.primeFactorsList.length) := by
  classical
  let F := Q.filter (fun q => q.1 = t)
  let A := F.image (fun q => q.2.1)
  let B := F.image (fun q => q.2.2)
  have ha : A.card ≤ (n+1)^D.primeFactorsList.length := by
    apply prefixData_card_le hD A
    · intro a ha i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hp q (Finset.mem_filter.mp hq).1).1 i
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hprod q (Finset.mem_filter.mp hq).1).1
  have hb : B.card ≤ (n+1)^t.remainder.primeFactorsList.length := by
    apply prefixData_card_le ht B
    · intro a ha i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact (hp q (Finset.mem_filter.mp hq).1).2 i
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      rw [← (Finset.mem_filter.mp hq).2]
      exact (hprod q (Finset.mem_filter.mp hq).1).2
  have hinj : F.card ≤ (A ×ˢ B).card := by
    apply Finset.card_le_card_of_injOn (fun q : RecoveredPair b n => q.2)
    · intro q hq
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    · intro q hq q' hq' he
      apply Prod.ext
      · exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm
      · exact he
  calc
    _ ≤ (A ×ˢ B).card := hinj
    _ = A.card*B.card := Finset.card_product _ _
    _ ≤ (n+1)^D.primeFactorsList.length * (n+1)^t.remainder.primeFactorsList.length :=
      Nat.mul_le_mul ha hb
    _ = _ := (pow_add _ _ _).symm

/-- Ford's comparison counts prime lists and one residual integer. Restoring
both missing prefix tails costs only their prime-occurrence allocations. -/
theorem ford_comparison_with_recovery (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ (b n K : ℕ) (y S : ℝ) (D r : ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters b y S D r Y U →
      ∀ Q : Finset (RecoveredPair b n),
        (∀ q ∈ Q, FordComparisonConditions b y S D r Y U q.1) →
        (∀ q ∈ Q, q.1.remainder.primeFactorsList.length ≤ K) →
        (∀ q ∈ Q, (∀ i, 1 ≤ q.2.1.primes i) ∧ (∀ i, 1 ≤ q.2.2.primes i)) →
        (∀ q ∈ Q, q.2.1.d * (∏ i, (q.2.1.primes i-1)) = D ∧
          q.2.2.d * (∏ i, (q.2.2.primes i-1)) = q.1.remainder) →
        (Q.card : ℝ) ≤ (n+1 : ℝ)^(D.primeFactorsList.length+K) *
          fordComparisonBound C b y S D r Y U := by
  classical
  obtain ⟨C, y₀, hC, hy₀, hford⟩ := hford
  refine ⟨C, y₀, hC, hy₀, ?_⟩
  intro b n K y S D r Y U hy hparam Q hcond hK hp hprod
  let T := Q.image Prod.fst
  have hT : ∀ t ∈ T, FordComparisonConditions b y S D r Y U t := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
    exact hcond q hq
  have hD : 0 < D := hparam.2.2.2.2.2.2.2.1
  have hcard : Q.card ≤ T.card*(n+1)^(D.primeFactorsList.length+K) := by
    rw [Finset.card_eq_sum_card_image Prod.fst Q]
    calc
      _ ≤ ∑ _t ∈ T, (n+1)^(D.primeFactorsList.length+K) := by
        apply Finset.sum_le_sum
        intro t ht
        obtain ⟨q, hq, hqt⟩ := Finset.mem_image.mp ht
        have hr := (hcond q hq).1
        have hk := hK q hq
        rw [hqt] at hr hk
        exact (recovered_pair_fiber_bound Q t hD hr hp hprod).trans
          (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_left hk _))
      _ = _ := by simp [T, Nat.mul_comm]
  have hbound := hford b y S D r Y U hy hparam T hT
  have hreal : (Q.card : ℝ) ≤ (T.card : ℝ)*(n+1 : ℝ)^(D.primeFactorsList.length+K) := by
    exact_mod_cast hcard
  calc
    _ ≤ (T.card : ℝ)*(n+1 : ℝ)^(D.primeFactorsList.length+K) := hreal
    _ ≤ fordComparisonBound C b y S D r Y U * (n+1 : ℝ)^(D.primeFactorsList.length+K) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = _ := mul_comm _ _

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualTupleRecovery
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact tuple data hidden in a comparison residual, on either side of the prefix cut. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma prod_after_cut {M : Type*} [CommMonoid M] {k R : ℕ} (hk : k ≤ R) (f : ℕ → M) :
    (∏ j : Fin (R-k), f (k+j.val+1)) = ∏ r ∈ Finset.Icc (k+1) R, f r := by
  apply Finset.prod_bij (fun j _ => k+j.val+1)
  · intro j _
    exact Finset.mem_Icc.mpr ⟨by omega,by have := j.isLt; omega⟩
  · intro j _ l _ h
    apply Fin.ext
    omega
  · intro r hr
    have hh := Finset.mem_Icc.mp hr
    refine ⟨⟨r-k-1,by omega⟩,Finset.mem_univ _,?_⟩
    simp only
    omega
  · intro j _
    rfl

lemma residualTupleData_denominator {x : ℝ} {H k : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hR : R x H < L x H) :
    prefixDenominator (residualTupleData η k) = (suffixPreimage η k).totient := by
  by_cases hk : k ≤ R x H
  · simp only [prefixDenominator,residualTupleData,ite_eq_left hk]
    rw [prod_after_cut hk (fun r => remainderPrime η r-1),← suffixPreimage_at_R η]
    exact (basic_suffix_totient_split hη hL hk hR).symm
  · have hzero : R x H-k=0 := by omega
    simp only [prefixDenominator,residualTupleData,ite_eq_right hk]
    have he : (∏ j : Fin (R x H-k), (remainderPrime η (k+j.val+1)-1))=1 := by
      rw [hzero]
      simp
    rw [he,mul_one]

lemma residualTupleData_primes {x : ℝ} {H k : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hRL : R x H ≤ L x H) :
    ∀ j, 1 ≤ (residualTupleData η k).primes j := by
  intro j
  have hj := j.isLt
  exact (hη.2.1 (k+j.val+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).1.one_lt.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionClassData
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recovering the fixed-prime data in an actual finite collision class. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma canceledIndices_eq {x : ℝ} {H i k p q : ℕ} {η ξ : RemainderDatum (L x H)} :
    canceledIndices i k (collisionSurvivors p q η ξ i k) =
      (Finset.Icc i k).filter (fun j => wholeWitnessPrime p η j=wholeWitnessPrime q ξ j) := by
  ext j
  simp only [canceledIndices,collisionSurvivors,Finset.mem_sdiff,Finset.mem_filter]
  tauto

lemma canceledPrimesAt_product {x : ℝ} {H i k : ℕ}
    (τ σ : TotientTuple (R x H)) (I : Finset ℕ)
    (hI : collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
      (chosenRemainder x H σ.tail) i k=I) :
    shiftedProduct (canceledPrimesAt x H i k I τ)=
      collisionCanceledProduct τ.head σ.head (chosenRemainder x H τ.tail)
        (chosenRemainder x H σ.tail) i k := by
  unfold shiftedProduct canceledPrimesAt
  have he := Finset.prod_image
    (s := (Finset.univ : Finset (Fin (canceledIndices i k I).card)))
    (g := (canceledIndices i k I).orderEmbOfFin rfl)
    (f := fun j => wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j-1)
    (fun a _ b _ hab => ((canceledIndices i k I).orderEmbOfFin rfl).injective hab)
  rw [← he,(canceledIndices i k I).image_orderEmbOfFin_univ rfl,← hI,canceledIndices_eq]
  rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualFordData
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All Ford hypotheses for a block of actual good tuple pairs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

/-- The finite grid, all published parameter and pointwise restrictions, and
the full strict exponent saving are consequences of the actual good data. -/
theorem actual_ford_data : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    ∀ q : TotientTuple (R x H) × TotientTuple (R x H), GoodCollisionBlock x t H i y q →
    let η := chosenRemainder x H q.1.tail
    let ξ := chosenRemainder x H q.2.tail
    let I := collisionSurvivors q.1.head q.2.head η ξ i (collisionLastIndex x i)
    let T := comparisonPairAt x H (collisionLastIndex x i) I q
    let δ := collisionMesh x y i
    let Z := fordBandScale x (collisionLastIndex x i)
    let Y := comparisonCutoffs y (pairUpperCoordinates T y Z δ)
    let U := comparisonCutoffs y (pairLowerCoordinates T y δ)
    pairGridLabel T y δ ∈ collisionGridFamilies δ I.card ∧
    FordComparisonParameters I.card y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct q.1.head q.2.head η ξ i (collisionLastIndex x i)) Y U ∧
    FordComparisonConditions I.card y (normalityScale x i) (collisionResidual η i)
      (collisionCanceledProduct q.1.head q.2.head η ξ i (collisionLastIndex x i)) Y U T ∧
    (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
      comparisonError I.card y (normalityScale x i) Y U ≤
        -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
  filter_upwards [actual_comparison_parameters,actual_collision_exponent,collision_small_factors_all]
    with H hparam hexp hsmall
  filter_upwards [hparam,hexp,hsmall] with x hp he hs
  intro i hi hL hR t y hy hBy hByl hByu q hq
  let η := chosenRemainder x H q.1.tail
  let ξ := chosenRemainder x H q.2.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hq.left.1.2.2.1).1
  have hξ : IsBasicRemainder x H ξ := (chosenRemainder_spec hq.right.1.2.2.1).1
  have hv : tupleValue (witnessTuple q.1.head η)=tupleValue (witnessTuple q.2.head ξ) := by
    dsimp only [η,ξ]
    rw [chosenRemainder_tuple hq.left.1,chosenRemainder_tuple hq.right.1]
    exact hq.value
  obtain ⟨hD,hr⟩ := hs i q.1.head q.2.head hi hL hq.left.1.1 η ξ hη hq.first y hy.le hq.size hq.zero
  have hparams := hp i q.1.head q.2.head hi hL hR hq.left.1.1 η ξ hη hξ
    (chosenRemainder_good hq.left) (chosenRemainder_good hq.right) hv hq.first hq.common
    y hy hBy hByl hByu hq.minLeft hq.minRight hq.size hD hr
  have hexponent := he i q.1.head q.2.head hi hL hR hq.left.1.1 η ξ hη hξ
    (chosenRemainder_good hq.left) (chosenRemainder_good hq.right) hv hq.first hq.common
    y hy hBy hByl hByu hq.minLeft hq.minRight hq.size hq.zero
  exact ⟨hparams.1,hparams.2.1,hparams.2.2,hexponent⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordCostBudget
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published Ford prefactors and tuple recovery fit inside the saving. -/

noncomputable section

namespace TotientAsymptotic

lemma recovery_log_cost_small {h B : ℝ} (hh : 5 ≤ h) (hB : 0 ≤ B) :
    3*(2*B/h^8)*Real.log (h+1) ≤ B/(16*h^4) := by
  have h0 : 0 < h := by linarith
  have hl : Real.log (h+1) ≤ h := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < h+1)
  have hp : (96 : ℝ) ≤ h^3 := by nlinarith [sq_nonneg (h-5)]
  calc
    _ ≤ 3*(2*B/h^8)*h := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = (6*B)/h^7 := by field_simp <;> ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < h^7) (by positivity : 0 < 16*h^4)).mpr
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ B*h^4 by positivity)
      first | (convert hm using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

lemma smooth_log_cost_small {h B Z : ℝ} {b : ℕ}
    (hh : 2 ≤ h) (hb : (b : ℝ) ≤ h) (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hZu : Z ≤ 2*B/h^18) : (20*(b : ℝ)*Real.log b+2)*Z ≤ B/(16*h^4) := by
  have h0 : 0 < h := by linarith
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hl := Real.log_le_self hb0
  have hcoef : 20*(b : ℝ)*Real.log b+2 ≤ 22*h^2 := by
    have ht := mul_le_mul_of_nonneg_left hl hb0
    have hsq := pow_le_pow_left₀ hb0 hb 2
    nlinarith
  have hp : (704 : ℝ) ≤ h^12 := by
    have hh12 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh 12
    norm_num at hh12
    linarith
  calc
    _ ≤ (22*h^2)*(2*B/h^18) := mul_le_mul hcoef hZu hZ (by positivity)
    _ = 44*B/h^16 := by field_simp <;> ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < h^16) (by positivity : 0 < 16*h^4)).mpr
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ B*h^4 by positivity)
      first | (convert hm using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))

lemma ford_polynomial_prefactor {C B h : ℝ} {b : ℕ}
    (hC : 0 < C) (hB : 0 < B) (hh : 1 ≤ h) (hb : (b : ℝ) ≤ h)
    (hlogB : Real.log B ≤ 26*h) :
    (C*B)^(6*b) ≤ Real.exp (6*(|Real.log C|+26)*h^2) := by
  have hh0 : 0 ≤ h := zero_le_one.trans hh
  have hM : 0 ≤ |Real.log C|+26 := by positivity
  have hl : Real.log (C*B) ≤ (|Real.log C|+26)*h := by
    rw [Real.log_mul hC.ne' hB.ne']
    have hc := le_abs_self (Real.log C)
    have ha := mul_le_mul_of_nonneg_left hh (abs_nonneg (Real.log C))
    nlinarith
  calc
    _ = Real.exp ((6*b : ℕ)*Real.log (C*B)) := by
      rw [Real.exp_nat_mul,Real.exp_log (mul_pos hC hB)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hb0 : (0 : ℝ) ≤ 6*(b : ℝ) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hl hb0
      have h2 := mul_le_mul_of_nonneg_right (show 6*(b : ℝ) ≤ 6*h by linarith)
        (mul_nonneg hM hh0)
      push_cast
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordKernel
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring both residual tuples still leaves an exponential collision saving. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma recovery_prefactor_bound {n b d k : ℕ} {h Y : ℝ}
    (hh : 5 ≤ h) (hY : 0 ≤ Y) (hn : (n : ℝ) ≤ h) (hb : (b : ℝ) ≤ h)
    (hd : (d : ℝ) ≤ 2*Y/h^8) (hk : (k : ℝ) ≤ 2*Y/h^8) :
    (n+1 : ℝ)^(d+k)*(b+1 : ℝ)^d ≤ Real.exp (Y/(16*h^4)) := by
  have hnp : (0 : ℝ) < n+1 := by positivity
  have hbp : (0 : ℝ) < b+1 := by positivity
  have hln := Real.log_le_log hnp (show (n+1 : ℝ) ≤ h+1 by linarith)
  have hlb := Real.log_le_log hbp (show (b+1 : ℝ) ≤ h+1 by linarith)
  have hn0 : 0 ≤ Real.log (n+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hb0 : 0 ≤ Real.log (b+1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) b])
  have hdk : ((d+k : ℕ) : ℝ) ≤ 2*(2*Y/h^8) := by push_cast <;> linarith
  have hleft := mul_le_mul hdk hln hn0 (by positivity : 0 ≤ 2*(2*Y/h^8))
  have hright := mul_le_mul hd hlb hb0 (by positivity : 0 ≤ 2*Y/h^8)
  have hcost : ((d+k : ℕ) : ℝ)*Real.log (n+1 : ℝ)+(d : ℝ)*Real.log (b+1 : ℝ) ≤ Y/(16*h^4) := by
    have hs := recovery_log_cost_small hh hY
    linarith
  have he1 : (n+1 : ℝ)^(d+k) = Real.exp ((d+k : ℕ)*Real.log (n+1 : ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hnp]
  have he2 : (b+1 : ℝ)^d = Real.exp ((d : ℝ)*Real.log (b+1 : ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hbp]
  rw [he1,he2,← Real.exp_add]
  exact Real.exp_le_exp.mpr hcost

lemma smooth_prefactor_bound {b : ℕ} {h Y T : ℝ}
    (hh : 2 ≤ h) (hb : (b : ℝ) ≤ h) (hY : 0 ≤ Y)
    (hT : 1 < T) (hZ : 0 ≤ B T) (hZu : B T ≤ 2*Y/h^18) :
    (Real.log T)^(20*(b : ℝ)*Real.log b+1) ≤ Real.exp (Y/(16*h^4)) := by
  rw [Real.rpow_def_of_pos (Real.log_pos hT)]
  apply Real.exp_le_exp.mpr
  have hc := smooth_log_cost_small hh hb hY hZ hZu
  change Real.log (Real.log T)*(20*(b : ℝ)*Real.log b+1) ≤ _
  change (20*(b : ℝ)*Real.log b+2)*Real.log (Real.log T) ≤ _ at hc
  change 0 ≤ Real.log (Real.log T) at hZ
  nlinarith

/-- A single class of fixed canceled primes, residual integer and grid has
this kernel after paying both missing-tuple and published Ford prefactors. -/
theorem ford_recovered_kernel {b n K D r : ℕ} {C y S h : ℝ} {Y U : ℕ → ℝ}
    (hC : 0 < C) (hy1 : 1 < y) (hy : 1 ≤ Real.log y) (hBy : 0 < B y)
    (hh : 5 ≤ h) (hn : (n : ℝ) ≤ h) (hb : (b : ℝ) ≤ h)
    (hlogB : Real.log (B y) ≤ 26*h)
    (hD : (D.primeFactorsList.length : ℝ) ≤ 2*B y/h^8)
    (hK : (K : ℝ) ≤ 2*B y/h^8)
    (hT : 1 < Y b) (hZ : 0 ≤ B (Y b)) (hZu : B (Y b) ≤ 2*B y/h^18)
    (hDr : 0 < D*r)
    (hE : -2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+comparisonError b y S Y U ≤
      -1-1/(2*h^4)) :
    (n+1 : ℝ)^(D.primeFactorsList.length+K)*fordComparisonBound C b y S D r Y U ≤
      y/(D*r)/Real.log y*Real.exp (6*(|Real.log C|+26)*h^2-B y/(4*h^4)) := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have hp := ford_polynomial_prefactor hC hBy (by linarith) hb hlogB
  have hr := recovery_prefactor_bound hh hBy.le hn hb hD hK
  have hs := smooth_prefactor_bound (by linarith) hb hBy.le hT hZ hZu
  have hs0 := Real.rpow_nonneg (Real.log_nonneg hT.le) (20*(b : ℝ)*Real.log b+1)
  have he := comparison_log_power_saving hy hE
  have hdr : (0 : ℝ) < (D*r : ℕ) := by exact_mod_cast hDr
  have hscale : 0 ≤ y/(D*r) := div_nonneg hy0.le (by simpa using hdr.le)
  have hlog0 : 0 < Real.log y := zero_lt_one.trans_le hy
  calc
    _ = (y/(D*r))*((C*B y)^(6*b))*
        ((n+1 : ℝ)^(D.primeFactorsList.length+K)*(b+1 : ℝ)^D.primeFactorsList.length)*
        (Real.log (Y b))^(20*(b : ℝ)*Real.log b+1)*
        (Real.log y)^(-2+(∑ j ∈ Finset.Icc 1 (b-1), a j*(B (Y j)/B y))+comparisonError b y S Y U) := by
      unfold fordComparisonBound
      ring
    _ ≤ (y/(D*r))*Real.exp (6*(|Real.log C|+26)*h^2)*
        Real.exp (B y/(16*h^4))*Real.exp (B y/(16*h^4))*
        ((Real.log y)⁻¹*Real.exp (-(1/(2*h^4))*B y)) := by
      gcongr
    _ = y/(D*r)/Real.log y*Real.exp (6*(|Real.log C|+26)*h^2-3*B y/(8*h^4)) := by
      rw [show 6*(|Real.log C|+26)*h^2-3*B y/(8*h^4) =
        ((6*(|Real.log C|+26)*h^2+B y/(16*h^4))+B y/(16*h^4))+
          (-(1/(2*h^4))*B y) by ring,
        Real.exp_add,Real.exp_add,Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hfrac : B y/(4*h^4) ≤ 3*B y/(8*h^4) := by
        field_simp
        nlinarith
      linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionKernelDomain
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform numerical data for applying the recovered Ford kernel. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma good_residual_omega_floor {x t y : ℝ} {H i : ℕ}
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hi : i ≤ R x H) (hq : GoodCollisionBlock x t H i y q) :
    (collisionResidual (chosenRemainder x H q.1.tail) i).primeFactorsList.length ≤
      ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ ∧
    (collisionResidual (chosenRemainder x H q.2.tail) i).primeFactorsList.length ≤
      ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ := by
  have hm := Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩
  constructor
  · exact Nat.le_floor ((chosenRemainder_good hq.left i hm).2.2.2)
  · exact Nat.le_floor ((chosenRemainder_good hq.right i hm).2.2.2)

lemma normalized_grid_bottom {b : ℕ} {y Z δ : ℝ} (v : Fin b → ℕ)
    (hb : 0 < b) (hy : B y ≠ 0) :
    B (comparisonCutoffs y (pairedGridUpper δ ((7/10 : ℝ)*Z/B y) v) b)=(7/10 : ℝ)*Z := by
  rw [B,comparisonCutoffs,Real.log_exp,Real.log_exp]
  simp only [pairedGridUpper,ite_eq_right (Nat.ne_of_gt hb),lt_self_iff_false,dite_false]
  field_simp

lemma comparison_cutoff_one_lt (y : ℝ) (v : ℕ → ℝ) (b : ℕ) :
    1 < comparisonCutoffs y v b := Real.one_lt_exp_iff.mpr (Real.exp_pos _)

/-- All scalar hypotheses of the single-class kernel follow uniformly from
the Ford bands. The only tuple-dependent bound is its number of survivors. -/
theorem collision_kernel_domain : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ y : ℝ,
    1 < y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    5 ≤ ((m x-i : ℕ) : ℝ) ∧ 1 ≤ Real.log y ∧
    ((R x H-collisionLastIndex x i : ℕ) : ℝ) ≤ ((m x-i : ℕ) : ℝ) ∧
    Real.log (B y) ≤ 26*((m x-i : ℕ) : ℝ) ∧
    (⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ : ℝ) ≤
      2*B y/((m x-i : ℕ) : ℝ)^8 ∧
    0 < fordBandScale x (collisionLastIndex x i) ∧
    (7/10 : ℝ)*fordBandScale x (collisionLastIndex x i) ≤
      2*B y/((m x-i : ℕ) : ℝ)^18 ∧
    collisionCutoff (m x-i)+1 ≤ m x-i := by
  filter_upwards [eventually_collision_indices,ford_band_polynomial_lower 1,
    eventually_ge_atTop 5] with H hind hpoly hH
  filter_upwards [hpoly,ford_band_log_upper,
    m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (1 : ℝ))] with x hp hl hm hBx
  intro i hi hL hR y hy hBy hlo hup
  have him : i < m x := hi.trans_lt (hR.trans hL)
  obtain ⟨hHi,hcut,hk⟩ := hind x hm i hi
  have hh : (5 : ℝ) ≤ (m x-i : ℕ) := by exact_mod_cast hH.trans hHi
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := by linarith
  have hbi : 0 < fordBandScale x i := fordBandScale_pos (zero_lt_one.trans hBx) him
  have hbige : ((m x-i : ℕ) : ℝ) ≤ fordBandScale x i := by simpa using hp i him hHi
  have hBy1 : 1 ≤ B y := by
    have hh5 : (5 : ℝ) ≤ fordBandScale x i := hh.trans hbige
    linarith
  have hlogy : 1 ≤ Real.log y := by
    have he := Real.exp_le_exp.mpr hBy1
    rw [B,Real.exp_log (Real.log_pos hy)] at he
    have he1 := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hn : R x H-collisionLastIndex x i ≤ m x-i := by
    have hkge : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
    omega
  have hlog := (Real.log_le_log hBy (show B y ≤ 6*fordBandScale x i by linarith)).trans (hl i him)
  have hf := Nat.floor_le (div_nonneg hbi.le (pow_nonneg hh0.le 8))
  have hratio := (ford_collision_layer_ratio hBx him hcut).2
  have hZ : 0 < fordBandScale x (collisionLastIndex x i) :=
    fordBandScale_pos (zero_lt_one.trans hBx) (hk.trans hL)
  have hzu : fordBandScale x (collisionLastIndex x i) ≤
      fordBandScale x i/((m x-i : ℕ) : ℝ)^18 := by
    have ht := (div_le_iff₀ hbi).mp hratio
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using ht
  refine ⟨hh,hlogy,by exact_mod_cast hn,hlog,?_,hZ,?_,by omega⟩
  · apply hf.trans
    apply div_le_div_of_nonneg_right _ (pow_nonneg hh0.le _)
    linarith
  · have hdiv := div_le_div_of_nonneg_right
      (show (7/10 : ℝ)*fordBandScale x i ≤ 2*B y by linarith)
      (pow_nonneg hh0.le 18)
    have hz := mul_le_mul_of_nonneg_left hzu (by norm_num : (0 : ℝ) ≤ 7/10)
    exact hz.trans (by simpa only [mul_div_assoc] using hdiv)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleSuffix
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

/-- Comparison primes and residual tuples recover only the suffix being
counted; the earlier common prefix is irrelevant to this reconstruction. -/
theorem tupleSuffix_recovered {x t : ℝ} {H i k : ℕ}
    {τ σ : TotientTuple (R x H)} (hτ : IsBasicTuple x H t τ) (hσ : IsBasicTuple x H t σ)
    (hL : L x H < m x) (hkL : k < L x H) (hiR : i ≤ R x H)
    (hknown : ∀ r ∈ Finset.Icc i k,
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) r =
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) r)
    (hdata : residualTupleData (chosenRemainder x H τ.tail) k =
      residualTupleData (chosenRemainder x H σ.tail) k) :
    tupleSuffix τ i=tupleSuffix σ i := by
  let η := chosenRemainder x H τ.tail
  let ξ := chosenRemainder x H σ.tail
  have hη : IsBasicRemainder x H η := (chosenRemainder_spec hτ.2.2.1).1
  have hξ : IsBasicRemainder x H ξ := (chosenRemainder_spec hσ.2.2.1).1
  have hps := congrArg PrefixDatum.primes hdata
  have hds := congrArg PrefixDatum.d hdata
  have hp : (tupleSuffix τ i).primes=(tupleSuffix σ i).primes := by
    funext j
    have hj : i+j.val ≤ R x H := by have := j.isLt; omega
    change tuplePrimes τ ⟨i+j.val,by omega⟩=tuplePrimes σ ⟨i+j.val,by omega⟩
    rw [← chosen_whole_prime hτ hj,← chosen_whole_prime hσ hj]
    by_cases hr : i+j.val ≤ k
    · exact hknown _ (Finset.mem_Icc.mpr ⟨by omega,hr⟩)
    · let l : Fin (R x H-k) := ⟨i+j.val-k-1,by omega⟩
      have he := congrFun hps l
      change remainderPrime η (k+l.val+1)=remainderPrime ξ (k+l.val+1) at he
      have hidx : k+l.val+1=i+j.val := by dsimp [l]; omega
      rw [hidx] at he
      simpa only [wholeWitnessPrime,ite_eq_right (by omega : i+j.val ≠ 0)] using he
  have ht : (tupleSuffix τ i).d=(tupleSuffix σ i).d := by
    have htailτ : (remainderTail x H η).totient=τ.tail.d :=
      congrArg PrefixDatum.d (chosenRemainder_spec hτ.2.2.1).2
    have htailσ : (remainderTail x H ξ).totient=σ.tail.d :=
      congrArg PrefixDatum.d (chosenRemainder_spec hσ.2.2.1).2
    change τ.tail.d=σ.tail.d
    rw [← htailτ,← htailσ]
    by_cases hk : k ≤ R x H
    · simpa only [residualTupleData,ite_eq_left hk] using hds
    · have hd : (suffixPreimage η k).totient=(suffixPreimage ξ k).totient := by
        simpa only [residualTupleData,ite_eq_right hk] using hds
      rw [← suffixPreimage_at_R η,← suffixPreimage_at_R ξ,
        basic_suffix_totient_split hη hL (by omega : R x H ≤ k) hkL,
        basic_suffix_totient_split hξ hL (by omega : R x H ≤ k) hkL,hd]
      congr 1
      apply Finset.prod_congr rfl
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have he := hknown r (Finset.mem_Icc.mpr ⟨by omega,hr'.2⟩)
      have hprime : remainderPrime η r=remainderPrime ξ r := by
        simpa only [wholeWitnessPrime,ite_eq_right (by omega : r ≠ 0)] using he
      exact congrArg (fun n : ℕ => n-1) hprime
  exact congrArg₂ PrefixDatum.mk hp ht

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixComparison
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The comparison count for distinct suffixes after removing a varying prefix. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

/-- Comparison data need determine only the suffix, because representatives
of distinct suffix pairs are selected before applying this estimate. -/
theorem comparisonEncoding_injOn_of_suffix {x t : ℝ} {H i k : ℕ}
    (I : Finset ℕ) (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)))
    (hL : L x H < m x) (hk : k < L x H) (hi : i ≤ R x H)
    (hQ : ∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2)
    (hdet : Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _))
    (fixed : ℕ → ℕ × ℕ)
    (hfixed : ∀ q ∈ Q, ∀ r ∈ Finset.Icc i k, r ∉ I →
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r=(fixed r).1 ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r=(fixed r).2) :
    Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) := by
  intro q hq q' hq' he
  have hwhole (r) (hr : r ∈ Finset.Icc i k) :
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) r=
        wholeWitnessPrime q'.1.head (chosenRemainder x H q'.1.tail) r ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) r=
        wholeWitnessPrime q'.2.head (chosenRemainder x H q'.2.tail) r := by
    by_cases hrI : r ∈ I
    · have him : r ∈ Finset.univ.image (I.orderEmbOfFin rfl) := by
        rw [I.image_orderEmbOfFin_univ rfl]
        exact hrI
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp him
      exact ⟨congrArg (fun z : RecoveredPair I.card (R x H-k) => z.1.left j) he,
        congrArg (fun z : RecoveredPair I.card (R x H-k) => z.1.right j) he⟩
    · exact ⟨(hfixed q hq r hr hrI).1.trans (hfixed q' hq' r hr hrI).1.symm,
        (hfixed q hq r hr hrI).2.trans (hfixed q' hq' r hr hrI).2.symm⟩
  apply hdet hq hq'
  apply Prod.ext
  · exact tupleSuffix_recovered (hQ q hq).1 (hQ q' hq').1 hL hk hi
      (fun r hr => (hwhole r hr).1)
      (congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.1) he)
  · exact tupleSuffix_recovered (hQ q hq).2 (hQ q' hq').2 hL hk hi
      (fun r hr => (hwhole r hr).2)
      (congrArg (fun z : RecoveredPair I.card (R x H-k) => z.2.2) he)

lemma fixed_canceled_coordinates {x : ℝ} {H i k : ℕ}
    (I : Finset ℕ) (q : TotientTuple (R x H) × TotientTuple (R x H))
    (v : Fin (canceledIndices i k I).card → ℕ)
    (hI : collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i k=I)
    (hv : canceledPrimesAt x H i k I q.1=v) :
    ∀ j ∈ Finset.Icc i k, j ∉ I →
      let a := if h : j ∈ canceledIndices i k I then
        v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,h⟩) else 1
      wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=a ∧
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j=a := by
  intro j hj hjI
  have hmem : j ∈ canceledIndices i k I := Finset.mem_sdiff.mpr ⟨hj,hjI⟩
  have hleft : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j =
      v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,hmem⟩) := by
    rw [← hv]
    simp [canceledPrimesAt,Finset.orderEmbOfFin]
  have hsame : wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=
      wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j := by
    rw [← hI,canceledIndices_eq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  simpa only [dite_eq_left hmem] using And.intro hleft (hsame.symm.trans hleft)

/-- The raw published bound is unchanged when the finite actual family is
known injective in its recovered comparison data. -/
theorem actual_comparison_injective (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ {x t : ℝ} {H k K D r : ℕ} (I : Finset ℕ) (y S : ℝ) (Y U : ℕ → ℝ),
      y₀ ≤ y → FordComparisonParameters I.card y S D r Y U →
      L x H < m x → R x H < L x H →
      ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
      (∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2) →
      Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) →
      (∀ q ∈ Q, (suffixPreimage (chosenRemainder x H q.1.tail) k).totient=D) →
      (∀ q ∈ Q, (comparisonPairAt x H k I q).remainder.primeFactorsList.length ≤ K) →
      (∀ q ∈ Q, FordComparisonConditions I.card y S D r Y U (comparisonPairAt x H k I q)) →
      (Q.card : ℝ) ≤ (((R x H-k : ℕ) : ℝ)+1)^(D.primeFactorsList.length+K)*
        fordComparisonBound C I.card y S D r Y U := by
  obtain ⟨C,y₀,hC,hy₀,hbound⟩ := ford_comparison_with_recovery hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  intro x t H k K D r I y S Y U hy hparam hL hR Q hQ hinj hD hK hcond
  have hcard : (Q.image (comparisonEncoding x H k I)).card=Q.card := Finset.card_image_of_injOn hinj
  have hb := hbound I.card (R x H-k) K y S D r Y U hy hparam
    (Q.image (comparisonEncoding x H k I))
    (by intro z hz; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz; exact hcond q hq)
    (by intro z hz; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz; exact hK q hq)
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨residualTupleData_primes (chosenRemainder_spec (hQ q hq).1.2.2.1).1 hR.le,
        residualTupleData_primes (chosenRemainder_spec (hQ q hq).2.2.2.1).1 hR.le⟩)
    (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(residualTupleData_denominator (chosenRemainder_spec (hQ q hq).1.2.2.1).1 hL hR).trans (hD q hq),
        residualTupleData_denominator (chosenRemainder_spec (hQ q hq).2.2.2.1).1 hL hR⟩)
  simpa only [hcard] using hb

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixClassKernel
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bound for one fixed class of actual tuple pairs, including both tails. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Fix the surviving indices, canceled primes, grid and residual integer.
The common prefix may vary when the comparison encoding remains injective. The published Ford estimate then bounds actual pairs,
with both residual tuple factorizations included in the saving. -/
theorem actual_comparison_class_kernel_injective (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ {x t y S h : ℝ} {H k K D r : ℕ} (I : Finset ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → 1 ≤ Real.log y → 0 < B y → 5 ≤ h →
      ((R x H-k : ℕ) : ℝ) ≤ h → (I.card : ℝ) ≤ h →
      Real.log (B y) ≤ 26*h →
      (D.primeFactorsList.length : ℝ) ≤ 2*B y/h^8 → (K : ℝ) ≤ 2*B y/h^8 →
      1 < Y I.card → 0 ≤ B (Y I.card) → B (Y I.card) ≤ 2*B y/h^18 →
      FordComparisonParameters I.card y S D r Y U →
      (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
        comparisonError I.card y S Y U ≤ -1-1/(2*h^4)) →
      L x H < m x → R x H < L x H → k < L x H →
      ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
      (∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2) →
      Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) →
      (∀ q ∈ Q, (suffixPreimage (chosenRemainder x H q.1.tail) k).totient=D) →
      (∀ q ∈ Q, (comparisonPairAt x H k I q).remainder.primeFactorsList.length ≤ K) →
      (∀ q ∈ Q, FordComparisonConditions I.card y S D r Y U (comparisonPairAt x H k I q)) →
      (Q.card : ℝ) ≤ y/(D*r)/Real.log y*
        Real.exp (6*(|Real.log C|+26)*h^2-B y/(4*h^4)) := by
  obtain ⟨C,y₀,hC,hy₀,hbound⟩ := actual_comparison_injective hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  intro x t y S h H k K D r I Y U hy hlog hBy hh hn hb hlogB hD hK hT hZ hZu
    hparam hE hL hR _hk Q hQ hinj hres hrem hcond
  have hDr : 0 < D*r := Nat.mul_pos hparam.2.2.2.2.2.2.2.1
    hparam.2.2.2.2.2.2.2.2.2.2.1
  exact (hbound I y S Y U hy hparam hL hR Q hQ hinj hres hrem hcond).trans
    (ford_recovered_kernel hC (hy₀.trans_le hy) hlog hBy hh hn hb hlogB hD hK hT hZ hZu hDr hE)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualFixedClass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the recovered Ford kernel to a fixed actual collision class. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_fixed_class_bound (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y →
    B y ≤ 2*fordBandScale x i →
    ∀ (I : Finset ℕ) (D : ℕ) (v : Fin (canceledIndices i (collisionLastIndex x i) I).card → ℕ)
      (grid : Fin I.card → ℕ)
      (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    (∀ q ∈ Q, collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=I) →
    (∀ q ∈ Q, collisionResidual (chosenRemainder x H q.1.tail) i=D) →
    (∀ q ∈ Q, canceledPrimesAt x H i (collisionLastIndex x i) I q.1=v) →
    (∀ q ∈ Q, pairGridLabel (comparisonPairAt x H (collisionLastIndex x i) I q)
      y (collisionMesh x y i)=grid) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/(D*shiftedProduct v)/Real.log y*
      Real.exp (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨C,y₀,hC,hy₀,hclass⟩ := actual_comparison_class_kernel_injective hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  filter_upwards [actual_ford_data,collision_kernel_domain,eventually_collision_indices]
    with H hdata hdomain hind
  filter_upwards [hdata,hdomain,m_tendsto.eventually (eventually_ge_atTop H)] with x hd hdom hm
  intro i hi hL hR t y hy hBy hlo hup I D v grid Q hQ hI hD hv hg hdet
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hh,hlog,hn,hlogB,hK,hZ,hZu,hcut⟩ := hdom i hi hL hR y hy1 hBy hlo hup
  rcases Q.eq_empty_or_nonempty with hqe | ⟨q₀,hq₀⟩
  · rw [hqe]
    simp only [Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (div_nonneg (div_nonneg (zero_lt_one.trans hy1).le (by positivity))
      (by linarith)) (Real.exp_pos _).le
  let k := collisionLastIndex x i
  let δ := collisionMesh x y i
  let Z := fordBandScale x k
  let Y := comparisonCutoffs y (pairedGridUpper δ ((7/10 : ℝ)*Z/B y) grid)
  let U := comparisonCutoffs y (pairedGridLower δ grid)
  have hdataq (q) (hq : q ∈ Q) :
      FordComparisonParameters I.card y (normalityScale x i) D (shiftedProduct v) Y U ∧
      FordComparisonConditions I.card y (normalityScale x i) D (shiftedProduct v) Y U
        (comparisonPairAt x H k I q) ∧
      (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
        comparisonError I.card y (normalityScale x i) Y U ≤ -1-1/(2*((m x-i : ℕ) : ℝ)^4)) := by
    have hdq := hd i hi hL hR t y hy1 hBy hlo hup q (hQ q hq)
    dsimp only at hdq
    rw [hI q hq] at hdq
    have hr : collisionCanceledProduct q.1.head q.2.head (chosenRemainder x H q.1.tail)
        (chosenRemainder x H q.2.tail) i k=shiftedProduct v := by
      rw [← canceledPrimesAt_product q.1 q.2 I (hI q hq),hv q hq]
    change collisionCanceledProduct q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=shiftedProduct v at hr
    simp only [pairUpperCoordinates,pairLowerCoordinates,hg q hq,hD q hq,hr] at hdq
    exact hdq.2
  obtain ⟨hp,hc,he⟩ := hdataq q₀ hq₀
  have hb : 0 < I.card := hp.1
  have hbc : I.card ≤ m x-i := by
    have hsub : I ⊆ Finset.Icc i k := by
      rw [← hI q₀ hq₀]
      exact Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcalc : k+1-i=collisionCutoff (m x-i)+1 := by dsimp [k,collisionLastIndex]; omega
    rw [hcalc] at hcard
    exact hcard.trans hcut
  have hY : B (Y I.card)=(7/10 : ℝ)*Z := normalized_grid_bottom grid hb hBy.ne'
  have hDf := (good_residual_omega_floor hi (hQ q₀ hq₀)).1
  rw [hD q₀ hq₀] at hDf
  have hDreal : (D.primeFactorsList.length : ℝ) ≤ 2*B y/((m x-i : ℕ) : ℝ)^8 :=
    (show (D.primeFactorsList.length : ℝ) ≤ ⌊fordBandScale x i/((m x-i : ℕ) : ℝ)^8⌋₊ by exact_mod_cast hDf).trans hK
  have hinj : Set.InjOn (comparisonEncoding x H k I) (↑Q : Set _) := by
    apply comparisonEncoding_injOn_of_suffix I Q hL (hind x hm i hi).2.2 hi
      (fun q hq => ⟨(hQ q hq).left.1,(hQ q hq).right.1⟩) hdet
      (fun j => let a := (if h : j ∈ canceledIndices i k I then v (((canceledIndices i k I).orderIsoOfFin rfl).symm ⟨j,h⟩) else 1); (a,a))
    intro q hq j hj hjI
    exact fixed_canceled_coordinates I q v (hI q hq) (hv q hq) j hj hjI
  apply hclass I Y U hy hlog hBy hh hn (by exact_mod_cast hbc) hlogB hDreal hK
    (comparison_cutoff_one_lt _ _ _) (by rw [hY]; positivity) (by rw [hY]; exact hZu)
    hp he hL hR (hind x hm i hi).2.2 Q (fun q hq => ⟨(hQ q hq).left.1,(hQ q hq).right.1⟩) hinj
  · exact hD
  · intro q hq
    exact (good_residual_omega_floor hi (hQ q hq)).2
  · exact fun q hq => (hdataq q hq).2.1

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionChoiceBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime and smoothness bounds for all the choices in the class partition. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma wholeWitnessPrime_prime {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p j : ℕ} (hp : p.Prime) (hj : j ≤ L x H) :
    (wholeWitnessPrime p η j).Prime := by
  by_cases hz : j=0
  · simpa [wholeWitnessPrime,hz] using hp
  · simpa only [wholeWitnessPrime,ite_eq_right hz] using
      (hη.2.1 j (Finset.mem_Icc.mpr ⟨by omega,hj⟩)).1

lemma witnessBlockValue_pos {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p i k : ℕ} (hp : p.Prime) (hk : k ≤ L x H) :
    0 < witnessBlockValue p η i k := by
  apply Nat.mul_pos (Nat.totient_pos.mpr (suffixPreimage_pos hη))
  apply Finset.prod_pos
  intro j hj
  exact Nat.sub_pos_of_lt (wholeWitnessPrime_prime hη hp ((Finset.mem_Icc.mp hj).2.trans hk)).one_lt

lemma whole_shift_le_block {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {p i k j : ℕ} (hp : p.Prime) (hk : k ≤ L x H)
    (hj : j ∈ Finset.Icc i k) :
    wholeWitnessPrime p η j-1 ≤ witnessBlockValue p η i k := by
  apply Nat.le_of_dvd (witnessBlockValue_pos hη hp hk)
  change wholeWitnessPrime p η j-1 ∣
    (suffixPreimage η k).totient*∏ r ∈ Finset.Icc i k, (wholeWitnessPrime p η r-1)
  exact (Finset.dvd_prod_of_mem (fun r => wholeWitnessPrime p η r-1) hj).trans (dvd_mul_left _ _)

lemma canceledPrimesAt_prime_bound {x t y : ℝ} {H i : ℕ}
    {q : TotientTuple (R x H) × TotientTuple (R x H)}
    (hq : GoodCollisionBlock x t H i y q) (I : Finset ℕ)
    (hk : collisionLastIndex x i ≤ L x H) :
    ∀ j, (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j).Prime ∧
      (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j : ℝ) ≤ y+1 := by
  intro j
  have hj := (canceledIndices i (collisionLastIndex x i) I).orderEmbOfFin_mem rfl j
  have hj' := (Finset.mem_sdiff.mp hj).1
  have hη := (chosenRemainder_spec hq.left.1.2.2.1).1
  have hprime := wholeWitnessPrime_prime hη hq.left.1.1 ((Finset.mem_Icc.mp hj').2.trans hk)
  refine ⟨hprime,?_⟩
  have hle := whole_shift_le_block hη hq.left.1.1 hk hj'
  have hler : ((canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ) : ℝ) ≤ y :=
    (show ((canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ) : ℝ) ≤
      witnessBlockValue q.1.head (chosenRemainder x H q.1.tail) i (collisionLastIndex x i) by exact_mod_cast hle).trans hq.size
  have he : (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j : ℝ)=
      (canceledPrimesAt x H i (collisionLastIndex x i) I q.1 j-1 : ℕ)+1 := by
    exact_mod_cast (Nat.sub_add_cancel hprime.one_lt.le).symm
  linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CanceledPrimeMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal cost of fixing the canceled primes, from Mertens' input. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_shift_inv_le_log_factor {p : ℕ} (hp : p.Prime) :
    ((p-1 : ℕ) : ℝ)⁻¹ ≤ 2*Real.log ((p : ℝ)/(p-1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hm : (0 : ℝ) < p-1 := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp0 hm)
  have he : 1-((p : ℝ)/(p-1))⁻¹=(p : ℝ)⁻¹ := by field_simp <;> ring
  rw [he] at hl
  have hs : (p-1 : ℝ)⁻¹ ≤ 2*(p : ℝ)⁻¹ := by
    have hh : 1/((p : ℝ)-1) ≤ 2/(p : ℝ) := (div_le_div_iff₀ hm hp0).mpr (by linarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  rw [Nat.cast_sub hp.one_lt.le,Nat.cast_one]
  linarith

lemma primeEulerProduct_pos (N : ℕ) : 0 < primeEulerProduct N := by
  apply Finset.prod_pos
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact div_pos (by linarith) (by linarith)

lemma canceled_prime_mass_le_log_product (N : ℕ) :
    (∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      2*Real.log (primeEulerProduct N) := by
  calc
    _ ≤ ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, 2*Real.log ((p : ℝ)/(p-1)) :=
      Finset.sum_le_sum (fun p hp => prime_shift_inv_le_log_factor (Finset.mem_filter.mp hp).2)
    _ = 2*Real.log (primeEulerProduct N) := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply Real.log_prod
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
      exact (div_pos (by linarith : (0 : ℝ) < p) (by linarith : (0 : ℝ) < p-1)).ne'

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SmoothResidualMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler product bounds the entire smooth residual-integer sum. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_reciprocal_norm_lt_one {p : ℕ} (hp : p.Prime) : ‖reciprocalNatHom p‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [reciprocalNatHom,MonoidHom.coe_mk,OneHom.coe_mk,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)] using (inv_lt_one₀ (zero_lt_one.trans hpR)).mpr hpR

lemma reciprocal_prime_factor (p : ℕ) (hp : p.Prime) :
    (1-reciprocalNatHom p)⁻¹=(p : ℝ)/(p-1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change (1-(p : ℝ)⁻¹)⁻¹=(p : ℝ)/(p-1)
  field_simp

/-- Only positivity and smoothness are used; the residuals may repeat prime
factors and the upper cutoff on their size is arbitrary. -/
theorem smooth_residual_reciprocal_mass (N : ℕ) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q, 0 < n ∧ largestPrimeFactor n ≤ N) :
    (∑ n ∈ Q, (n : ℝ)⁻¹) ≤ primeEulerProduct N := by
  classical
  let S := Finset.Icc 2 N
  have hm (n : ℕ) (hn : n ∈ Q) : n ∈ Nat.factoredNumbers S := by
    refine ⟨(hQ n hn).1.ne',?_⟩
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactorsList hp).two_le,
      (primeFactor_le_largest hp).trans (hQ n hn).2⟩
  let e : {n // n ∈ Q} → Nat.factoredNumbers S := fun n => ⟨n.1,hm n.1 n.2⟩
  let T : Finset (Nat.factoredNumbers S) := Q.attach.image e
  have he : Function.Injective e := by
    intro n m h
    apply Subtype.ext
    exact congrArg (fun z : Nat.factoredNumbers S => z.val) h
  have hsum : (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ T, reciprocalNatHom n := by
    dsimp only [T]
    rw [Finset.sum_image (fun n _ m _ h => he h)]
    change (∑ n ∈ Q, (n : ℝ)⁻¹) = ∑ n ∈ Q.attach, (n.val : ℝ)⁻¹
    exact (Finset.sum_attach Q (fun n : ℕ => (n : ℝ)⁻¹)).symm
  have hseries := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun {_} hp => prime_reciprocal_norm_lt_one hp) S
  calc
    _ = ∑ n ∈ T, reciprocalNatHom n := hsum
    _ ≤ ∑' n : Nat.factoredNumbers S, reciprocalNatHom n := by
      apply hseries.1.of_norm.sum_le_tsum
      intro n _
      change 0 ≤ (n.val : ℝ)⁻¹
      positivity
    _ = ∏ p ∈ S with p.Prime, (1-reciprocalNatHom p)⁻¹ := hseries.2.tsum_eq
    _ = primeEulerProduct N := by
      apply Finset.prod_congr rfl
      intro p hp
      exact reciprocal_prime_factor p (Finset.mem_filter.mp hp).2

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ComparisonClassSum
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma canceled_tuple_mass (c : ℕ) (P : Finset ℕ) :
    (∑ p ∈ Fintype.piFinset (fun _ : Fin c => P),
      ∏ j : Fin c, (((p j-1 : ℕ) : ℝ)⁻¹)) =
      (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹))^c := by
  have he := Finset.prod_univ_sum (fun _ : Fin c => P)
    (fun (_ : Fin c) (p : ℕ) => (((p-1 : ℕ) : ℝ)⁻¹))
  simpa using he.symm

/-- The actual finite class partition has no independence requirement: its
image is only enlarged to the product of the available choices. -/
theorem comparison_class_sum {α γ : Type*} [DecidableEq γ]
    (Q : Finset α) (D P : Finset ℕ) (G : Finset γ) (c : ℕ)
    (d : α → ℕ) (p : α → Fin c → ℕ) (g : α → γ) (A : ℝ)
    (hD : ∀ q ∈ Q, d q ∈ D)
    (hP : ∀ q ∈ Q, ∀ j, p q j ∈ P)
    (hG : ∀ q ∈ Q, g q ∈ G)
    (hclass : ∀ a ∈ D, ∀ v ∈ Fintype.piFinset (fun _ : Fin c => P), ∀ z ∈ G,
      ((Q.filter (fun q => (d q,p q,g q)=(a,v,z))).card : ℝ) ≤
        A*(a : ℝ)⁻¹*∏ j : Fin c, (((v j-1 : ℕ) : ℝ)⁻¹)) :
    (Q.card : ℝ) ≤ A*(G.card : ℝ)*(∑ a ∈ D, (a : ℝ)⁻¹)*
      (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹))^c := by
  classical
  let T := D ×ˢ ((Fintype.piFinset (fun _ : Fin c => P)) ×ˢ G)
  have hkey : ∀ q ∈ Q, (d q,p q,g q) ∈ T := by
    intro q hq
    exact Finset.mem_product.mpr ⟨hD q hq,Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr (hP q hq),hG q hq⟩⟩
  have hc := finite_class_card_bound Q T (fun q => (d q,p q,g q))
    (fun z => A*(z.1 : ℝ)⁻¹*∏ j : Fin c, (((z.2.1 j-1 : ℕ) : ℝ)⁻¹)) hkey (by
      intro z hz
      obtain ⟨hd,hpg⟩ := Finset.mem_product.mp hz
      obtain ⟨hp,hg⟩ := Finset.mem_product.mp hpg
      exact hclass z.1 hd z.2.1 hp z.2.2 hg)
  apply hc.trans_eq
  dsimp only [T]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product,Finset.sum_const, nsmul_eq_mul]
  rw [← canceled_tuple_mass c P]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [← Finset.mul_sum D (fun x => (x : ℝ)⁻¹) A]
  ring

/-- Enlarge residuals to all smooth integers only after applying the class
estimate. Mertens bounds both the smooth sum and each canceled prime sum. -/
theorem comparison_class_sum_mertens (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α γ : Type*} [DecidableEq γ]
      (Q : Finset α) (D : Finset ℕ) (G : Finset γ) (c Nz Np : ℕ)
      (d : α → ℕ) (p : α → Fin c → ℕ) (g : α → γ) (A : ℝ),
      2 ≤ Nz → 2 ≤ Np → 0 ≤ A →
      (∀ a ∈ D, 0 < a ∧ largestPrimeFactor a ≤ Nz) →
      (∀ q ∈ Q, d q ∈ D) →
      (∀ q ∈ Q, ∀ j, (p q j).Prime ∧ p q j ≤ Np) →
      (∀ q ∈ Q, g q ∈ G) →
      (∀ a ∈ D, ∀ v ∈ Fintype.piFinset (fun _ : Fin c => (Finset.Icc 2 Np).filter Nat.Prime),
        ∀ z ∈ G, ((Q.filter (fun q => (d q,p q,g q)=(a,v,z))).card : ℝ) ≤
          A*(a : ℝ)⁻¹*∏ j : Fin c, (((v j-1 : ℕ) : ℝ)⁻¹)) →
      (Q.card : ℝ) ≤ A*(G.card : ℝ)*(C*Real.log Nz)*
        (2*(Real.log C+B Np))^c := by
  obtain ⟨C,hC,hprod⟩ := hmertens
  refine ⟨C,hC,?_⟩
  intro α γ _ Q D G c Nz Np d p g A hNz hNp hA hsmooth hd hp hg hc
  let P := (Finset.Icc 2 Np).filter Nat.Prime
  have hp' : ∀ q ∈ Q, ∀ j, p q j ∈ P := by
    intro q hq j
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hp q hq j).1.two_le,
      (hp q hq j).2⟩,(hp q hq j).1⟩
  have hdm := (smooth_residual_reciprocal_mass Nz D hsmooth).trans (hprod Nz hNz)
  have hlN : 0 < Real.log (Np : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Np by omega))
  have hpm : (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹)) ≤ 2*(Real.log C+B Np) := by
    have hl := Real.log_le_log (primeEulerProduct_pos Np) (hprod Np hNp)
    rw [Real.log_mul hC.ne' hlN.ne'] at hl
    exact (canceled_prime_mass_le_log_product Np).trans (by
      change _ ≤ 2*(Real.log C+Real.log (Real.log (Np : ℝ)))
      linarith)
  apply (comparison_class_sum Q D P G c d p g A hd hp' hg hc).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hdm (by positivity)
  · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hpm c
  · positivity
  · positivity

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualClassSum
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing all grids, canceled primes, and residuals for fixed survivors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_survivor_class_sum (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ C M y₀ : ℝ, 0 < C ∧ 0 < M ∧ 1 < y₀ ∧
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ (I : Finset ℕ) (Nz Np : ℕ),
    2 ≤ Nz → 2 ≤ Np → collisionSmoothCutoff x i ≤ Nz → y+1 ≤ Np →
    ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    (∀ q ∈ Q, collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i (collisionLastIndex x i)=I) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/Real.log y*
      Real.exp (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4))*
      ((collisionGridFamilies (collisionMesh x y i) I.card).card : ℝ)*(M*Real.log Nz)*
      (2*(Real.log M+B Np))^(canceledIndices i (collisionLastIndex x i) I).card := by
  obtain ⟨C,y₀,hC,hy₀,hfixed⟩ := actual_fixed_class_bound hford
  obtain ⟨M,hM,hsum⟩ := comparison_class_sum_mertens hmertens
  refine ⟨C,M,y₀,hC,hM,hy₀,?_⟩
  filter_upwards [hfixed,actual_ford_data,collision_residual_below_cutoff,eventually_collision_indices]
    with H hfixed hdata hres hind
  filter_upwards [hfixed,hdata,hres,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hf hd hr hm
  intro i hi hL hR t y hy hBy hlo hup I Nz Np hNz hNp hzN hyN Q hQ hI hdet
  let k := collisionLastIndex x i
  let c := (canceledIndices i k I).card
  let d := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    collisionResidual (chosenRemainder x H q.1.tail) i
  let p := fun q : TotientTuple (R x H) × TotientTuple (R x H) => canceledPrimesAt x H i k I q.1
  let g := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    pairGridLabel (comparisonPairAt x H k I q) y (collisionMesh x y i)
  let G := collisionGridFamilies (collisionMesh x y i) I.card
  let A := y/Real.log y*Real.exp
    (6*(|Real.log C|+26)*((m x-i : ℕ) : ℝ)^2-B y/(4*((m x-i : ℕ) : ℝ)^4))
  have hy1 : 1 < y := hy₀.trans_le hy
  apply hsum Q (Q.image d) G c Nz Np d p g A hNz hNp
    (mul_nonneg (div_nonneg (zero_lt_one.trans hy1).le (Real.log_pos hy1).le) (Real.exp_pos _).le)
  · intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    have hη := (chosenRemainder_spec (hQ q hq).left.1.2.2.1).1
    refine ⟨Nat.totient_pos.mpr (suffixPreimage_pos hη),?_⟩
    have hsm := (hr i hi _ hη).le.trans hzN
    exact_mod_cast hsm
  · exact fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩
  · intro q hq j
    have hp := canceledPrimesAt_prime_bound (hQ q hq) I (hind x hm i hi).2.2.le j
    exact ⟨hp.1,by exact_mod_cast hp.2.trans hyN⟩
  · intro q hq
    have hh := hd i hi hL hR t y hy1 hBy hlo hup q (hQ q hq)
    dsimp only at hh
    rw [hI q hq] at hh
    exact hh.1
  · intro a _ v _ z _
    let F := Q.filter (fun q => (d q,p q,g q)=(a,v,z))
    have hmem (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).1
    have heq (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).2
    have hc := hf i hi hL hR t y hy hBy hlo hup I a v z F
      (fun q hq => hQ q (hmem q hq)) (fun q hq => hI q (hmem q hq))
      (fun q hq => congrArg Prod.fst (heq q hq))
      (fun q hq => congrArg (fun w => w.2.1) (heq q hq))
      (fun q hq => congrArg (fun w => w.2.2) (heq q hq))
      (fun q hq q' hq' he => hdet (hmem q hq) (hmem q' hq') he)
    apply hc.trans_eq
    dsimp only [A]
    rw [shiftedProduct,Nat.cast_prod]
    simp only [div_eq_mul_inv,mul_inv_rev]
    rw [Finset.prod_inv_distrib]
    ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionChoiceCost
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The remaining finite choices fit inside the recovered collision saving. -/

noncomputable section

namespace TotientAsymptotic

lemma canceled_mass_power_bound {M Y h : ℝ} {c : ℕ}
    (hY : 1 ≤ Y) (hh : 1 ≤ h) (hc : (c : ℝ) ≤ h)
    (hlog : Real.log Y ≤ 26*h) :
    (2*(|Real.log M|+3*Y))^c ≤ Real.exp ((2*|Real.log M|+32)*h^2) := by
  let K := 2*|Real.log M|+6
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hbase : 2*(|Real.log M|+3*Y) ≤ K*Y := by
    have hm := mul_le_mul_of_nonneg_left hY (abs_nonneg (Real.log M))
    dsimp [K]
    nlinarith
  have hlogK : Real.log K ≤ K := Real.log_le_self hK.le
  have he : (K*Y)^c=Real.exp ((c : ℝ)*(Real.log K+Real.log Y)) := by
    rw [← Real.log_mul hK.ne' hY0.ne',Real.exp_nat_mul,Real.exp_log (mul_pos hK hY0)]
  apply (pow_le_pow_left₀ (by positivity) hbase c).trans
  rw [he]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left (add_le_add hlogK hlog) (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  have hm' := mul_le_mul_of_nonneg_right hc (show 0 ≤ K+26*h by positivity)
  have hk := mul_le_mul_of_nonneg_left hh (show 0 ≤ K*h by positivity)
  dsimp [K] at *
  nlinarith

lemma smooth_choice_cost {M z : ℝ} (hM : 0 < M) (hz : 1 < z) (hlz : 1 ≤ Real.log z) :
    M*Real.log (⌈z⌉₊ : ℝ) ≤ Real.exp (|Real.log M|+1+B z) := by
  have hceil0 : (0 : ℝ) < ⌈z⌉₊ := lt_of_lt_of_le (zero_lt_one.trans hz) (Nat.le_ceil z)
  have hceil : (⌈z⌉₊ : ℝ) ≤ 2*z := by have := Nat.ceil_lt_add_one (zero_lt_one.trans hz).le; linarith
  have hlog := Real.log_le_log hceil0 hceil
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (zero_lt_one.trans hz).ne'] at hlog
  have hlog2 : Real.log (⌈z⌉₊ : ℝ) ≤ 2*Real.log z := by linarith [Real.log_two_lt_d9]
  have hm : M ≤ Real.exp |Real.log M| := by
    conv_lhs => rw [← Real.exp_log hM]
    exact Real.exp_le_exp.mpr (le_abs_self _)
  calc
    _ ≤ Real.exp (|Real.log M|)*(2*Real.log z) :=
      mul_le_mul hm hlog2 (Real.log_nonneg (hz.trans_le (Nat.le_ceil z)).le) (Real.exp_pos _).le
    _ = Real.exp (|Real.log M|+Real.log 2+B z) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 2),
        B,Real.exp_log (Real.log_pos hz)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.log_two_lt_d9])

lemma residual_choice_exponent {Y h Z : ℝ} (hY : 0 ≤ Y) (hh : 2 ≤ h)
    (hZ : Z ≤ 2*Y/h^18) : Z ≤ Y/(16*h^4) := by
  have hh0 : 0 < h := by linarith
  have hp : (32 : ℝ) ≤ h^14 := by
    have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh 14
    norm_num at ht
    linarith
  have hdiv : 2/h^14 ≤ (1/16 : ℝ) := by
    apply (div_le_iff₀ (pow_pos hh0 _)).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_right hdiv (div_nonneg hY (pow_nonneg hh0.le 4))
  apply hZ.trans
  convert hmul using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

lemma subset_choice_cost {J : ℕ} {h : ℝ} (hh : 1 ≤ h) (hJ : (J : ℝ) ≤ h) :
    (2 : ℝ)^J ≤ Real.exp (h^2) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2),← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hj : (J : ℝ)*Real.log 2 ≤ J := by
    have := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ h by linarith)
  nlinarith

lemma rounded_prime_endpoint_height {y : ℝ} (hy : 1 < y)
    (hlog : 1 ≤ Real.log y) (hB : 1 ≤ B y) :
    2 ≤ ⌈y+1⌉₊ ∧ B (⌈y+1⌉₊ : ℝ) ≤ 3*B y := by
  have hnlo : y+1 ≤ (⌈y+1⌉₊ : ℝ) := Nat.le_ceil _
  have hnhi : (⌈y+1⌉₊ : ℝ) ≤ 3*y := by
    have ht := (Nat.ceil_lt_add_one (show 0 ≤ y+1 by linarith)).le
    linarith
  have hn1 : (1 : ℝ) < ⌈y+1⌉₊ := by linarith
  have hp := Real.log_le_log (zero_lt_one.trans hn1) hnhi
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (zero_lt_one.trans hy).ne'] at hp
  have hl3 : Real.log (3 : ℝ) ≤ 2 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog' : Real.log (⌈y+1⌉₊ : ℝ) ≤ 3*Real.log y := by linarith
  have hB' := Real.log_le_log (Real.log_pos hn1) hlog'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by linarith : Real.log y ≠ 0)] at hB'
  have hn2 : 2 ≤ ⌈y+1⌉₊ := by
    have ht : 1 < ⌈y+1⌉₊ := by exact_mod_cast hn1
    omega
  refine ⟨hn2,?_⟩
  change Real.log (Real.log (⌈y+1⌉₊ : ℝ)) ≤ 3*B y
  change 1 ≤ Real.log (Real.log y) at hB
  change Real.log (Real.log (⌈y+1⌉₊ : ℝ)) ≤ Real.log 3+Real.log (Real.log y) at hB'
  change _ ≤ 3*Real.log (Real.log y)
  linarith

lemma canceled_rounded_mass_power {M y : ℝ} {c : ℕ} (hy : 1 < y)
    (hlog : 1 ≤ Real.log y) (hB : 1 ≤ B y) :
    (2*(Real.log M+B (⌈y+1⌉₊ : ℝ)))^c ≤ (2*(|Real.log M|+3*B y))^c := by
  have hheight := (rounded_prime_endpoint_height hy hlog hB).2
  have hyle : y ≤ (⌈y+1⌉₊ : ℝ) := by have ht := Nat.le_ceil (y+1); linarith
  have hlogmono := Real.log_le_log (zero_lt_one.trans hy) hyle
  have hBmono := Real.log_le_log (Real.log_pos hy) hlogmono
  have hnonneg : 0 ≤ B (⌈y+1⌉₊ : ℝ) := (zero_le_one.trans hB).trans hBmono
  calc
    _ ≤ |(2*(Real.log M+B (⌈y+1⌉₊ : ℝ)))^c| := le_abs_self _
    _ = |2*(Real.log M+B (⌈y+1⌉₊ : ℝ))|^c := abs_pow _ _
    _ ≤ _ := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have ha := abs_add_le (Real.log M) (B (⌈y+1⌉₊ : ℝ))
      rw [abs_of_nonneg hnonneg] at ha
      nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionChoiceAbsorption
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorbing the complete class-choice costs in the strict exponent saving. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma smooth_choice_cost_scaled {M z Y h : ℝ} (hM : 0 < M) (hz : 1 < z)
    (hlz : 1 ≤ Real.log z) (hh : 2 ≤ h) (hY : 0 ≤ Y) (hZ : B z ≤ 2*Y/h^18) :
    M*Real.log (⌈z⌉₊ : ℝ) ≤
      Real.exp ((|Real.log M|+1)*h^2+Y/(16*h^4)) := by
  apply (smooth_choice_cost hM hz hlz).trans
  apply Real.exp_le_exp.mpr
  have hh1 : 1 ≤ h^2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ |Real.log M|+1 by positivity)
  have hb := residual_choice_exponent hY hh hZ
  nlinarith

lemma collision_all_choice_cost {A M y Y z h G : ℝ} {c J : ℕ}
    (hy : 0 ≤ y/Real.log y) (hM : 0 < M) (hY : 1 ≤ Y) (hh : 2 ≤ h)
    (hlogY : Real.log Y ≤ 26*h) (hz : 1 < z) (hlz : 1 ≤ Real.log z)
    (hZ : B z ≤ 2*Y/h^18) (hG : 0 ≤ G) (hGu : G ≤ Real.exp (26*h^2))
    (hc : (c : ℝ) ≤ h) (hJ : (J : ℝ) ≤ h) :
    (2 : ℝ)^J*(y/Real.log y*Real.exp (A*h^2-Y/(4*h^4))*G*
      (M*Real.log (⌈z⌉₊ : ℝ))*(2*(|Real.log M|+3*Y))^c) ≤
      y/Real.log y*Real.exp ((A+3*|Real.log M|+60)*h^2-3*Y/(16*h^4)) := by
  have hs := smooth_choice_cost_scaled hM hz hlz hh (zero_le_one.trans hY) hZ
  have hp := canceled_mass_power_bound (M := M) hY (by linarith) hc hlogY
  have hj := subset_choice_cost (by linarith) hJ
  have hzs : 0 ≤ M*Real.log (⌈z⌉₊ : ℝ) := by
    apply mul_nonneg hM.le
    apply Real.log_nonneg
    exact hz.le.trans (Nat.le_ceil z)
  have hprod := mul_le_mul hj
    (mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hGu (mul_nonneg hy (Real.exp_pos (A*h^2-Y/(4*h^4))).le))
        hs hzs (by positivity))
      hp (by positivity) (by positivity))
    (by positivity) (Real.exp_pos _).le
  apply hprod.trans_eq
  rw [show (A+3*|Real.log M|+60)*h^2-3*Y/(16*h^4) =
    h^2+(((A*h^2-Y/(4*h^4))+26*h^2)+
      ((|Real.log M|+1)*h^2+Y/(16*h^4)))+(2*|Real.log M|+32)*h^2 by ring]
  simp only [Real.exp_add]
  ring

/-- Any fixed quadratic logarithmic cost is eventually smaller than the
remaining fraction of the strict slack, uniformly for all retained bands. -/
theorem ford_band_absorbs_square (K : ℝ) : ∀ᶠ H : ℕ in atTop,
    ∀ᶠ x : ℝ in atTop, ∀ i : ℕ, i ≤ R x H → ∀ Y : ℝ,
    (87/100 : ℝ)*fordBandScale x i ≤ Y →
    K*((m x-i : ℕ) : ℝ)^2 ≤ Y/(16*((m x-i : ℕ) : ℝ)^4) := by
  filter_upwards [ford_band_polynomial_lower 8,
    eventually_ge_atTop (⌈max 1 (32*|K|)⌉₊)] with H hpoly hH
  filter_upwards [hpoly,m_tendsto.eventually (eventually_ge_atTop H)] with x hp hm
  intro i hi Y hY
  have him : i < m x := by
    have hh : 1 ≤ H := by
      have ht := (le_max_left 1 (32*|K|)).trans (Nat.le_ceil _)
      have hH' : (⌈max 1 (32*|K|)⌉₊ : ℝ) ≤ H := by exact_mod_cast hH
      exact_mod_cast ht.trans hH'
    unfold R at hi
    omega
  have hHi : H ≤ m x-i := by unfold R at hi; omega
  have hthreshold : max 1 (32*|K|) ≤ ((m x-i : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hH.trans hHi)
  have hh1 := (le_max_left 1 (32*|K|)).trans hthreshold
  have hhK := (le_max_right 1 (32*|K|)).trans hthreshold
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := zero_lt_one.trans_le hh1
  have hs : 32*K ≤ ((m x-i : ℕ) : ℝ)^2 := by
    have hab := le_abs_self K
    nlinarith
  have hb := hp i him hHi
  have hhalf : ((m x-i : ℕ) : ℝ)^8/2 ≤ Y := by nlinarith [pow_nonneg hh0.le 8]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16*((m x-i : ℕ) : ℝ)^4)).mpr
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ ((m x-i : ℕ) : ℝ)^2*(16*((m x-i : ℕ) : ℝ)^4)/32 by positivity)
  have he : K*((m x-i : ℕ) : ℝ)^2*(16*((m x-i : ℕ) : ℝ)^4) ≤
      ((m x-i : ℕ) : ℝ)^8/2 := by nlinarith only [hm]
  exact he.trans hhalf

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionGridCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete family of alignment grids has only exponential-square cost. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collisionMesh_inverse_bound {x y : ℝ} {i : ℕ}
    (hS : 1 ≤ B (normalityScale x i)) (hy : 1 ≤ B y) :
    1/collisionMesh x y i ≤ B y := by
  have hmul : 1 ≤ B (normalityScale x i)*B y := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (B (normalityScale x i)*B y) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmul
  rw [collisionMesh,one_div_div]
  exact div_le_self (zero_le_one.trans hy) hsqrt

lemma alignment_grid_card_bound {x y : ℝ} {i b h : ℕ}
    (hS : 1 ≤ B (normalityScale x i)) (hy : 1 ≤ B y)
    (hbh : b ≤ h) (hlog : Real.log (2*B y) ≤ 26*h) :
    ((collisionGridFamilies (collisionMesh x y i) b).card : ℝ) ≤
      Real.exp (26*(h : ℝ)^2) := by
  rw [collisionGridFamilies_card,Nat.cast_pow]
  have hbase : ((⌊1/collisionMesh x y i⌋₊+1 : ℕ) : ℝ) ≤ 2*B y := by
    have hδ : 0 < collisionMesh x y i := by
      unfold collisionMesh
      exact div_pos (Real.sqrt_pos.mpr (by nlinarith)) (zero_lt_one.trans_le hy)
    have hf := Nat.floor_le (show 0 ≤ 1/collisionMesh x y i by positivity)
    have hb := collisionMesh_inverse_bound hS hy
    push_cast
    linarith
  have hp : 0 < 2*B y := by linarith
  calc
    _ ≤ (2*B y)^b := pow_le_pow_left₀ (by positivity) hbase b
    _ = Real.exp ((b : ℝ)*Real.log (2*B y)) := by rw [Real.exp_nat_mul,Real.exp_log hp]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hbR : (b : ℝ) ≤ h := by exact_mod_cast hbh
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      have hm := mul_le_mul hlog hbR (Nat.cast_nonneg b) (by positivity : (0 : ℝ) ≤ 26*h)
      nlinarith

/-- The source's grid-choice cost is bounded uniformly in the phase by
`exp (26 h²)` for all retained positive or zero collision indices. -/
theorem collision_grid_card_uniform : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i ≤ R x H, ∀ y : ℝ, 1 ≤ B (normalityScale x i) → 1 ≤ B y →
    B y ≤ 2*fordBandScale x i → ∀ b ≤ m x-i,
    ((collisionGridFamilies (collisionMesh x y i) b).card : ℝ) ≤
      Real.exp (26*((m x-i : ℕ) : ℝ)^2) := by
  filter_upwards [eventually_ge_atTop 1] with H hH
  filter_upwards [ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi y hS hy hBy b hb
  have him : i < m x := by unfold R at hi; omega
  apply alignment_grid_card_bound hS hy hb
  have hp : 0 < 2*B y := by linarith
  have hb0 : 0 < fordBandScale x i := by linarith
  exact (Real.log_le_log hp (show 2*B y ≤ 6*fordBandScale x i by linarith)).trans (hx i him)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualBlockCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete comparison summation for distinct actual suffix representatives. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem actual_block_count_oai (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∃ y₀ : ℝ, 1 < y₀ ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, i ≤ R x H → L x H < m x → R x H < L x H → ∀ t y : ℝ,
    y₀ ≤ y → 0 < B y → (87/100 : ℝ)*fordBandScale x i ≤ B y → B y ≤ 2*fordBandScale x i →
    ∀ (Q : Finset (TotientTuple (R x H) × TotientTuple (R x H))),
    (∀ q ∈ Q, GoodCollisionBlock x t H i y q) →
    Set.InjOn (fun q : TotientTuple (R x H) × TotientTuple (R x H) => pairSuffix q i) (↑Q : Set _) →
    (Q.card : ℝ) ≤ y/Real.log y*Real.exp (-B y/(8*((m x-i : ℕ) : ℝ)^4)) := by
  obtain ⟨C,M,y₀,hC,hM,hy₀,hsum⟩ := actual_survivor_class_sum hford hmertens
  let A := 6*(|Real.log C|+26)
  let K := A+3*|Real.log M|+61
  refine ⟨y₀,hy₀,?_⟩
  filter_upwards [hsum,collision_kernel_domain,collision_normality_domain,collision_grid_card_uniform,
    ford_band_absorbs_square K] with H hsum hkern hnormal hgrid habs
  filter_upwards [hsum,hkern,hnormal,hgrid,habs] with x hs hk hn hg ha
  intro i hi hL hR t y hy hBy hlo hup Q hQ hdet
  have hy1 : 1 < y := hy₀.trans_le hy
  obtain ⟨hh,hlog,_,hlogB,_,hZ,hZu,hcut⟩ := hk i hi hL hR y hy1 hBy hlo hup
  have hhalf : fordBandScale x i/2 ≤ B y := by
    have hbi : 0 < fordBandScale x i := by
      have hratio := hup
      linarith
    linarith
  obtain ⟨hS,hBS,hSy⟩ := hn i hi y hy1 hhalf
  have hS1 : 1 < normalityScale x i :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hBy1 : 1 ≤ B y := hBS.trans
    (Real.log_le_log (Real.log_pos hS1) (Real.log_le_log (zero_lt_one.trans hS1) hSy))
  let z := collisionSmoothCutoff x i
  let k := collisionLastIndex x i
  let J := collisionCutoff (m x-i)+1
  let h := ((m x-i : ℕ) : ℝ)
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (Real.exp_pos _)
  have hlz : 1 ≤ Real.log z := by
    change 1 ≤ Real.log (Real.exp (Real.exp ((7/10 : ℝ)*fordBandScale x k)))
    rw [Real.log_exp]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hBz : B z=(7/10 : ℝ)*fordBandScale x k := by
    simp only [z,k,collisionSmoothCutoff,B,Real.log_exp]
  have hZupper : B z ≤ 2*B y/h^18 := by rw [hBz]; exact hZu
  have hNz : 2 ≤ ⌈z⌉₊ := by
    have hz' : 1 < (⌈z⌉₊ : ℝ) := hz.trans_le (Nat.le_ceil z)
    have hz'' : 1 < ⌈z⌉₊ := by exact_mod_cast hz'
    omega
  have hNp := (rounded_prime_endpoint_height hy1 hlog hBy1).1
  let S := (Finset.Icc i k).powerset
  let key := fun q : TotientTuple (R x H) × TotientTuple (R x H) =>
    collisionSurvivors q.1.head q.2.head (chosenRemainder x H q.1.tail)
      (chosenRemainder x H q.2.tail) i k
  let T := y/Real.log y*Real.exp ((A+3*|Real.log M|+60)*h^2-3*B y/(16*h^4))
  have hylog : 0 ≤ y/Real.log y := div_nonneg (zero_lt_one.trans hy1).le (Real.log_pos hy1).le
  have hJ : (J : ℝ) ≤ h := by dsimp only [J,h]; exact_mod_cast hcut
  have hcount : (Q.card : ℝ) ≤ ∑ _I ∈ S, T := by
    apply finite_class_card_bound Q S key (fun _ => T)
    · intro q _
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · intro I hIS
      have hIsub := Finset.mem_powerset.mp hIS
      have hlen : (Finset.Icc i k).card=J := by
        rw [Nat.card_Icc]
        dsimp [J,k,collisionLastIndex]
        omega
      have hIcard : I.card ≤ m x-i := by
        have ht := Finset.card_le_card hIsub
        rw [hlen] at ht
        exact ht.trans hcut
      have hccard : ((canceledIndices i k I).card : ℝ) ≤ h := by
        have ht : (canceledIndices i k I).card ≤ (Finset.Icc i k).card := Finset.card_le_card (show canceledIndices i k I ⊆ Finset.Icc i k from Finset.sdiff_subset)
        rw [hlen] at ht
        dsimp only [h]
        exact_mod_cast ht.trans hcut
      let F := Q.filter (fun q => key q=I)
      have hF (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).1
      have hFkey (q) (hq : q ∈ F) := (Finset.mem_filter.mp hq).2
      have hbound := hs i hi hL hR t y hy hBy hlo hup I ⌈z⌉₊ ⌈y+1⌉₊ hNz hNp
        (Nat.le_ceil _) (Nat.le_ceil _) F (fun q hq => hQ q (hF q hq))
        (fun q hq => hFkey q hq) (fun q hq q' hq' he => hdet (hF q hq) (hF q' hq') he)
      have hGbound := hg i hi y hBS hBy1 hup I.card hIcard
      have hcost := collision_all_choice_cost (A := A) (J := 0) hylog hM hBy1
        (by linarith) hlogB hz hlz hZupper
        (by positivity : (0 : ℝ) ≤ (collisionGridFamilies (collisionMesh x y i) I.card).card)
        hGbound hccard (by simpa only [Nat.cast_zero] using (Nat.cast_nonneg (α := ℝ) (m x-i)))
      apply hbound.trans
      apply le_trans _ (by simpa only [pow_zero,one_mul] using hcost)
      apply mul_le_mul_of_nonneg_left (canceled_rounded_mass_power hy1 hlog hBy1)
      exact mul_nonneg (mul_nonneg (mul_nonneg hylog (Real.exp_pos _).le) (by positivity))
        (mul_nonneg hM.le (Real.log_nonneg (hz.le.trans (Nat.le_ceil z))))
  have hT : 0 ≤ T := mul_nonneg hylog (Real.exp_pos _).le
  have hS : S.card=2^J := by
    rw [Finset.card_powerset,Nat.card_Icc]
    congr 1
    dsimp [J,k,collisionLastIndex]
    omega
  calc
    (Q.card : ℝ) ≤ ∑ _I ∈ S, T := hcount
    _ = (2 : ℝ)^J*T := by simp only [Finset.sum_const,nsmul_eq_mul,hS,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ Real.exp (h^2)*T := mul_le_mul_of_nonneg_right (subset_choice_cost (by linarith) hJ) hT
    _ = y/Real.log y*Real.exp (K*h^2-3*B y/(16*h^4)) := by
      dsimp only [T,K]
      rw [show (A+3*|Real.log M|+61)*h^2-3*B y/(16*h^4) =
        h^2+((A+3*|Real.log M|+60)*h^2-3*B y/(16*h^4)) by ring,Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hylog
      apply Real.exp_le_exp.mpr
      have hab := ha i hi (B y) hlo
      change K*h^2 ≤ B y/(16*h^4) at hab
      calc
        K*h^2-3*B y/(16*h^4) ≤ B y/(16*h^4)-3*B y/(16*h^4) := sub_le_sub_right hab _
        _ = -B y/(8*h^4) := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.actual_block_count_oai := @OAI.TotientAsymptotic.actual_block_count_oai
