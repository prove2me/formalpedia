-- Prove2me | solution 1 for OAI.TotientAsymptotic.head_square_tuple_discard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:35:20.682732+00:00
-- url     : https://prove2.me/submissions/0689b123-102d-4ef2-8f74-f6de3baeb1d2

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
import Mathlib.Analysis.PSeries
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeGrid
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal prime mass of finite disjoint unions of unit boxes. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma reciprocalShiftWeight_nonneg {N : ℕ} (p : Fin N → ℕ) :
    0 ≤ reciprocalShiftWeight p := by unfold reciprocalShiftWeight; positivity

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal totient majorants, including repeated primes in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma totient_prime_product_lower {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (a : ℕ) (hp : ∀ i ∈ I, (p i).Prime) :
    a.totient*(∏ i ∈ I, (p i-1)) ≤ (a*∏ i ∈ I, p i).totient := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hrec := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
    have hprime := hp i (Finset.mem_insert_self _ _)
    calc
      _ = (a.totient*(∏ j ∈ I, (p j-1)))*(p i-1) := by ring
      _ ≤ (a*∏ j ∈ I, p j).totient*(p i-1) := Nat.mul_le_mul_right _ hrec
      _ = (a*∏ j ∈ I, p j).totient*(p i).totient := by rw [Nat.totient_prime hprime]
      _ ≤ ((a*∏ j ∈ I, p j)*p i).totient := Nat.totient_super_multiplicative _ _
      _ = _ := by congr 1; ring

/-- No coprimality or distinctness assumption is needed for this majorant. -/
theorem reciprocal_totient_prime_product {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (a : ℕ) (ha : 0 < a) (hp : ∀ i ∈ I, (p i).Prime) :
    ((a*∏ i ∈ I, p i).totient : ℝ)⁻¹ ≤
      (a.totient : ℝ)⁻¹ * ∏ i ∈ I, (p i-1 : ℝ)⁻¹ := by
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hprod : 0 < (∏ i ∈ I, (p i-1 : ℝ)) := by
    apply Finset.prod_pos
    intro i hi
    have := (hp i hi).two_le
    have : (2 : ℝ) ≤ p i := by exact_mod_cast this
    linarith
  have hnat := totient_prime_product_lower I p a hp
  have hR : (a.totient : ℝ)*(∏ i ∈ I, (p i-1 : ℝ)) ≤
      (a*∏ i ∈ I, p i).totient := by
    have he : (∏ i ∈ I, (p i-1 : ℝ)) = ((∏ i ∈ I, (p i-1)) : ℕ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.cast_sub (hp i hi).one_lt.le, Nat.cast_one]
    rw [he]
    exact_mod_cast hnat
  calc
    _ ≤ ((a.totient : ℝ)*(∏ i ∈ I, (p i-1 : ℝ)))⁻¹ :=
      inv_anti₀ (mul_pos hφ hprod) hR
    _ = _ := by rw [mul_inv, Finset.prod_inv_distrib]

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

lemma prefix_reciprocal_majorant {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hPH : P H ≤ H) :
    1 / (((remainderTail x H η).totient : ℝ)*
      ∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ)) ≤ remainderReciprocalWeight η := by
  have hRL : R x H ≤ L x H := by unfold R L; omega
  have htail := reciprocal_totient_prime_product (Finset.Icc (R x H+1) (L x H))
    (remainderPrime η) η.cofactor hη.1 (fun r hr =>
      (hη.2.1 r (Finset.mem_Icc.mpr
        ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩)).1)
  have hp : ∀ r ∈ Finset.Icc 1 (L x H), 1 ≤ remainderPrime η r :=
    fun r hr => (hη.2.1 r hr).1.one_lt.le
  have hprod : (∏ i : Fin (L x H), (η.primes i-1 : ℕ)) =
      (∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ))*
        ∏ r ∈ Finset.Icc (R x H+1) (L x H), (remainderPrime η r-1 : ℕ) := by
    have he : (∏ i : Fin (L x H), (η.primes i-1 : ℕ)) =
        ∏ i : Fin (L x H), (remainderPrime η (i.val+1)-1 : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [remainderPrime, i.isLt]
    rw [he, prod_fin_shifted (L x H) (fun r => (remainderPrime η r-1 : ℕ)),
      prod_Icc_split_at (Nat.zero_le _) hRL,
      prod_fin_shifted (R x H) (fun r => (remainderPrime η r-1 : ℕ))]
  have hcast (r : ℕ) (hr : r ∈ Finset.Icc (R x H+1) (L x H)) :
      ((remainderPrime η r-1 : ℕ) : ℝ) = (remainderPrime η r : ℝ)-1 := by
    rw [Nat.cast_sub (hp r (Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩)), Nat.cast_one]
  have he : (∏ r ∈ Finset.Icc (R x H+1) (L x H), (remainderPrime η r-1 : ℝ)⁻¹) =
      ∏ r ∈ Finset.Icc (R x H+1) (L x H), ((remainderPrime η r-1 : ℕ) : ℝ)⁻¹ := by
    apply Finset.prod_congr rfl
    intro r hr
    rw [hcast r hr]
  rw [he, Finset.prod_inv_distrib, ← Nat.cast_prod] at htail
  change ((remainderTail x H η).totient : ℝ)⁻¹ ≤ _ at htail
  have hh := mul_le_mul_of_nonneg_right htail
    (show 0 ≤ (((∏ i : Fin (R x H), (remainderPrime η (i.val+1)-1 : ℕ)) : ℕ) : ℝ)⁻¹ by positivity)
  unfold remainderReciprocalWeight reciprocalShiftWeight
  rw [hprod, Nat.cast_mul, mul_inv]
  simpa only [one_div, mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SuffixFactorization
attribute [-instance] _root_.instMeasurableSpace
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleMassBound
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tuple counts controlled by arithmetic mass. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma tupleValue_eq_head {R : ℕ} (p : ℕ) (ζ : PrefixDatum R) :
    tupleValue (TotientTuple.mk p ζ) = (p-1)*(ζ.d*∏ i, (ζ.primes i-1)) := by
  unfold tupleValue tuplePrimes
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma basic_prefix_denominator_pos {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H ≤ H) (hζ : IsPrefixDatum x H ζ) :
    0 < ζ.d*∏ i, (ζ.primes i-1) := by
  have hp := basic_prefix_data_positive hPH hζ
  exact Nat.mul_pos hp.1 (Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hp.2 i).one_lt))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllCollisionCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation over all first-difference indices in the actual collision set. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma G_eventually_one_le (hren : FordRenewalInput) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ G x (m x) := by
  obtain ⟨D,hD,hproj⟩ := uniform_projected_volume_bound hren
  have he := (summable_projectedEnvelope hD).tendsto_atTop_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hproj,m_tendsto.eventually he,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx he hB
  have hg := (div_le_iff₀ (G_pos hB (m x))).mp (hx (m x) le_rfl)
  have hg0 : G x 0=1 := by simp [G]
  rw [Nat.sub_self,hg0] at hg
  exact hg.trans (mul_le_of_le_one_left (G_pos hB _).le he.le)

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullWitnessWeight
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct weighted count including the head prime, used only for the
zero-index squarefree exclusion. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fullWitnessWeight_eq {x : ℝ} {H : ℕ} (q : RemainderDatum (L x H) × ℕ) :
    (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q) =
      ((q.2-1 : ℕ) : ℝ)⁻¹*remainderReciprocalWeight q.1 := by
  simp only [reciprocalShiftWeight,fullWitnessPrimes,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
    remainderReciprocalWeight,Nat.cast_mul,mul_inv]
  ring

lemma full_witness_count_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) (ht : t ≤ x)
    (S : Finset (RemainderDatum (L x H) × ℕ))
    (hS : ∀ q ∈ S, IsBasicRemainder x H q.1 ∧ IsBasicTuple x H t (witnessTuple q.2 q.1)) :
    (S.card : ℝ) ≤ x*∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q) := by
  classical
  rw [Finset.mul_sum]
  calc
    _ = ∑ _q ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hη,hτ⟩ := hS q hq
      let D := (prefixOfRemainder x H q.1).d*∏ i, ((prefixOfRemainder x H q.1).primes i-1)
      have hpre := (isPrefixDatum_iff x H (prefixOfRemainder x H q.1)).mpr ⟨q.1,hη,rfl⟩
      have hD : 0 < D := basic_prefix_denominator_pos hPH hpre
      have hp : 0 < q.2-1 := Nat.sub_pos_of_lt hτ.1.one_lt
      have hv : (((q.2-1)*D : ℕ) : ℝ) ≤ x := by
        have hh := hτ.2.2.2.trans ht
        simpa only [witnessTuple,tupleValue_eq_head,D] using hh
      have hvpos : (0 : ℝ) < ((q.2-1)*D : ℕ) := by exact_mod_cast Nat.mul_pos hp hD
      have hx : 0 ≤ x := hvpos.le.trans hv
      have hu : 1 ≤ x/(((q.2-1)*D : ℕ) : ℝ) := (one_le_div hvpos).mpr hv
      have hw : 1/(D : ℝ) ≤ remainderReciprocalWeight q.1 := by
        simpa only [D,prefixOfRemainder,Nat.cast_mul,Nat.cast_prod] using prefix_reciprocal_majorant hη hPH
      rw [fullWitnessWeight_eq]
      apply hu.trans
      have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ ((q.2-1 : ℕ) : ℝ)⁻¹ by positivity)
      have hh' := mul_le_mul_of_nonneg_left hh hx
      simpa only [Nat.cast_mul,div_eq_mul_inv,mul_inv,one_mul,mul_assoc] using hh'

lemma full_witness_weight_le {x : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (S : Finset (RemainderDatum (L x H) × ℕ))
    (hS : ∀ q ∈ S, IsBasicRemainder x H q.1) :
    (∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q)) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ S.image fullWitnessPrimes, reciprocalShiftWeight p := by
  classical
  let F := fun q : RemainderDatum (L x H) × ℕ => (q.1.cofactor,fullWitnessPrimes q)
  have hF : Function.Injective F := by
    rintro ⟨η,p⟩ ⟨ξ,q⟩ he
    have hc := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    have hpq := congrFun hv 0
    have het : η.primes=ξ.primes := by
      funext i
      exact congrFun hv i.succ
    simp only [F,fullWitnessPrimes,Fin.cons_zero] at hc hpq
    have heq : η=ξ := by cases η; cases ξ; simp_all
    exact Prod.ext heq hpq
  have he : (∑ q ∈ S, (q.1.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (fullWitnessPrimes q)) =
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image (fun q _ r _ h => hF h)]
  rw [he]
  have hsub : S.image F ⊆ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image fullWitnessPrimes := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (witness_cofactor_bound hs
      (extractTail_isWitness (hS q hq) hPH hHm)),Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image fullWitnessPrimes,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareGeometry
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma head_prime_discard_bound {x : ℝ} (hx : 2 ≤ x) (hB : 5 ≤ B x)
    {p : ℕ} (hp : p.Prime) (hpX : ((p-1 : ℕ) : ℝ) ≤ x) :
    p ∈ Nat.primesLE (discardPrimeBound (B x)) := by
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpx : (p : ℝ) ≤ x+1 := by
    have hcast : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by rw [Nat.cast_sub hp.one_lt.le]; norm_num
    rw [hcast] at hpX
    linarith
  have hpx2 : (p : ℝ) ≤ x^2 := hpx.trans (by nlinarith)
  have hlogp := Real.log_le_log (zero_lt_one.trans hp1) hpx2
  rw [Real.log_pow] at hlogp
  norm_num only [Nat.cast_ofNat] at hlogp
  have hBp : B p ≤ B x+1 := by
    have hh := Real.log_le_log (Real.log_pos hp1) hlogp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogx.ne'] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    change Real.log (Real.log (p : ℝ)) ≤ Real.log (Real.log x)+1
    linarith
  have hcoord : B p ≤ (6/5 : ℝ)*B x := hBp.trans (by linarith)
  have hpbound : (p : ℝ) ≤ Real.exp (Real.exp ((6/5 : ℝ)*B x)) :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans hp1)).mp
      ((Real.log_le_iff_le_exp (Real.log_pos hp1)).mp hcoord)
  exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpbound.trans (discardPrimeBound_bounds (by linarith : 2 ≤ B x)).2.2.2,hp⟩

lemma wholeWitnessPrime_full {x : ℝ} {H j : ℕ} (q : RemainderDatum (L x H) × ℕ)
    (hj : j ≤ L x H) :
    wholeWitnessPrime q.2 q.1 j=fullWitnessPrimes q ⟨j,by omega⟩ := by
  cases j with
  | zero => simp [wholeWitnessPrime,fullWitnessPrimes]
  | succ j =>
    have hj' : 1 ≤ j+1 ∧ j+1 ≤ L x H := by omega
    simp only [wholeWitnessPrime,Nat.add_one_ne_zero,ite_false, if_false,remainderPrime,dite_eq_left hj',
      Nat.add_sub_cancel,fullWitnessPrimes]
    exact (Fin.cons_succ (α := fun _ : Fin (L x H+1) => ℕ)
      q.2 q.1.primes (⟨j,by omega⟩ : Fin (L x H))).symm


lemma full_witness_prime_bound : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
    ∀ t : ℝ, t ≤ x → ∀ q : RemainderDatum (L x H) × ℕ,
      IsBasicRemainder x H q.1 → IsBasicTuple x H t (witnessTuple q.2 q.1) →
      ∀ j, fullWitnessPrimes q j ∈ Nat.primesLE (discardPrimeBound (B x)) := by
  filter_upwards [basic_suffix_discard_bound,eventually_ge_atTop (2 : ℝ),
    B_tendsto.eventually (eventually_ge_atTop (5 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop 1)] with x hbound hx hB hm
  intro H hPH t ht q hη hτ j
  by_cases hj : j.val=0
  · have hj0 : j=0 := Fin.ext hj
    rw [hj0]
    change q.2 ∈ Nat.primesLE (discardPrimeBound (B x))
    have hpre := (isPrefixDatum_iff x H (prefixOfRemainder x H q.1)).mpr ⟨q.1,hη,rfl⟩
    have hD := basic_prefix_denominator_pos hPH hpre
    have hval := hτ.2.2.2.trans ht
    rw [witnessTuple,tupleValue_eq_head] at hval
    have hle : ((q.2-1 : ℕ) : ℝ) ≤ x := by
      have hnat : q.2-1 ≤ (q.2-1)*((prefixOfRemainder x H q.1).d*
          ∏ i, ((prefixOfRemainder x H q.1).primes i-1)) :=
        Nat.le_mul_of_pos_right _ hD
      exact (Nat.cast_le.mpr hnat).trans hval
    exact head_prime_discard_bound hx hB hτ.1 hle
  · have hjL : j.val ≤ L x H := by have := j.isLt; omega
    rw [← wholeWitnessPrime_full q hjL,wholeWitnessPrime,ite_eq_right hj]
    have hb0 : fordBandScale x 0=B x := by simp [fordBandScale]
    rw [← hb0]
    exact hbound H 0 j.val (by omega) (Nat.zero_le _) hjL hm (by rw [hb0]; linarith) q.1 hη

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftDivisorMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary reciprocal mass of divisible prime shifts and square tails. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma shifted_divisor_mass (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ p ∈ shiftDivisiblePrimes N d, ((p-1 : ℕ) : ℝ)⁻¹) ≤
      (1+Real.log N)/(d : ℝ) := by
  let Q := shiftDivisiblePrimes N d
  let f : ℕ → ℕ := fun p => (p-1)/d
  have hp (p : ℕ) (h : p ∈ Q) : p.Prime ∧ p ≤ N ∧ d ∣ p-1 := by
    obtain ⟨hN,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨hN,hp⟩ := Nat.mem_primesLE.mp hN
    exact ⟨hp,hN,hd⟩
  have he (p : ℕ) (h : p ∈ Q) : d*f p=p-1 := Nat.mul_div_cancel' (hp p h).2.2
  have hi : Set.InjOn f (↑Q : Set ℕ) := by
    intro p hP q hQ h
    have h1 := he p hP
    have h2 := he q hQ
    have hp2 := (hp p hP).1.two_le
    have hq2 := (hp q hQ).1.two_le
    change f p=f q at h
    rw [h] at h1
    omega
  have hsub : Q.image f ⊆ Finset.Icc 1 N := by
    intro k hk
    obtain ⟨p,hpQ,rfl⟩ := Finset.mem_image.mp hk
    have h := hp p hpQ
    refine Finset.mem_Icc.mpr ⟨?_,(Nat.div_le_self _ _).trans ((Nat.sub_le p 1).trans h.2.1)⟩
    have hh := he p hpQ
    have h2 := h.1.two_le
    by_contra hn
    have hz : f p=0 := by omega
    rw [hz,mul_zero] at hh
    omega
  calc
    _ = (d : ℝ)⁻¹*∑ k ∈ Q.image f, (k : ℝ)⁻¹ := by
      rw [Finset.sum_image hi,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpQ
      have hh : (d : ℝ)*(f p : ℝ)=((p-1 : ℕ) : ℝ) := by exact_mod_cast he p hpQ
      rw [← hh,mul_inv]
    _ ≤ (d : ℝ)⁻¹*∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
    _ = (d : ℝ)⁻¹*(harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    _ ≤ _ := by
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity : 0 ≤ (d : ℝ)⁻¹)

lemma inverse_square_tail (Q : Finset ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, z < (q : ℝ)) :
    (∑ q ∈ Q, ((q : ℝ)^2)⁻¹) ≤ 2/z := by
  let k := ⌊z⌋₊
  let N := Q.sup id+1
  have hsub : Q ⊆ Finset.Ioo k N := by
    intro q hq
    refine Finset.mem_Ioo.mpr ⟨?_,?_⟩
    · have hh : (k : ℝ) ≤ z := Nat.floor_le (by linarith)
      have hqz := hQ q hq
      exact_mod_cast (show (k : ℝ) < q by linarith)
    · have hh : q ≤ Q.sup id := Finset.le_sup (f := id) hq
      dsimp [N]
      omega
  have hk : z < (k : ℝ)+1 := Nat.lt_floor_add_one z
  have hk0 : 0 < (k : ℝ)+1 := by positivity
  calc
    _ ≤ ∑ q ∈ Finset.Ioo k N, ((q : ℝ)^2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ 2/((k : ℝ)+1) := sum_Ioo_inv_sq_le k N
    _ ≤ 2/z := div_le_div_of_nonneg_left (by norm_num) (by linarith) hk.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TwoExceptionalPrimeLayer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two distinct restricted coordinates in the short suffix. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prime_mass_two_exceptions {N n : ℕ} (hn : n ≤ N) (Q : Finset (Fin N → ℕ))
    (j k : Fin (N-n)) (hjk : j ≠ k) (U V W : Finset ℕ)
    (hU : ∀ p ∈ Q, ∀ l, primeFinal p n l ∈ U)
    (hV : ∀ p ∈ Q, primeFinal p n j ∈ V)
    (hW : ∀ p ∈ Q, primeFinal p n k ∈ W) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (∑ p ∈ Q.image (fun p => primeInitial p n hn), reciprocalShiftWeight p)*
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
  classical
  let F := fun l : Fin (N-n) => ∑ q ∈ (if l=j then V else if l=k then W else U), ((q-1 : ℕ) : ℝ)⁻¹
  have hh := prime_mass_split hn Q (fun l => if l=j then V else if l=k then W else U) (by
    intro p hp l
    split_ifs with hj hk
    · subst l; exact hV p hp
    · subst l; exact hW p hp
    · exact hU p hp l)
  have hjmem : j ∈ (Finset.univ : Finset (Fin (N-n))) := Finset.mem_univ j
  have hkmem : k ∈ (Finset.univ : Finset (Fin (N-n))).erase j := by simp [Ne.symm hjk]
  have he : (∏ l, F l) =
      (∑ q ∈ V, ((q-1 : ℕ) : ℝ)⁻¹)*(∑ q ∈ W, ((q-1 : ℕ) : ℝ)⁻¹)*
      (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
    rw [← Finset.mul_prod_erase _ _ hjmem,← Finset.mul_prod_erase _ _ hkmem]
    have hr : (∏ l ∈ ((Finset.univ : Finset (Fin (N-n))).erase j).erase k, F l) =
        (∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹)^(N-n-2) := by
      calc
        _ = ∏ _l ∈ ((Finset.univ : Finset (Fin (N-n))).erase j).erase k,
            ∑ q ∈ U, ((q-1 : ℕ) : ℝ)⁻¹ := by
          apply Finset.prod_congr rfl
          intro l hl
          have hlk := (Finset.mem_erase.mp hl).1
          have hlj := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
          simp only [F,ite_eq_right hlj,ite_eq_right hlk]
        _ = _ := by simp [Finset.card_erase_of_mem hkmem,Nat.sub_sub]
    rw [hr]
    simp only [F,ite_true, if_true,ite_eq_right (Ne.symm hjk)]
    ring
  change _ ≤ _*(∏ l, F l) at hh
  rw [he] at hh
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeSquareMass
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma empty_prime_initial_mass {N : ℕ} (Q : Finset (Fin N → ℕ)) :
    (∑ p ∈ Q.image (fun p => primeInitial p 0 (Nat.zero_le N)), reciprocalShiftWeight p) ≤ 1 := by
  classical
  have hc : (Q.image (fun p => primeInitial p 0 (Nat.zero_le N))).card ≤ 1 :=
    Finset.card_le_one.mpr (fun p _ q _ => Subsingleton.elim _ _)
  have hcR : ((Q.image (fun p => primeInitial p 0 (Nat.zero_le N))).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [reciprocalShiftWeight,Fin.prod_univ_zero,Nat.cast_one,inv_one,
    Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one,Nat.cast_le,Nat.cast_one] using
    hcR

lemma prime_square_mass {d h N q : ℕ} (hN : 1 ≤ N) (hq : q.Prime) (hd : d ≤ h)
    (Q : Finset (Fin d → ℕ)) (j k : Fin d) {E : ℝ} (hE : 1 ≤ E)
    (hU : ∀ p ∈ Q, ∀ l, p l ∈ Nat.primesLE N)
    (hdiv : ∀ p ∈ Q, if j=k then q^2 ∣ p j-1 else q ∣ p j-1 ∧ q ∣ p k-1)
    (hmass : (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ E) :
    (∑ p ∈ Q, reciprocalShiftWeight p) ≤
      (1+Real.log N)^2*E^h*((q : ℝ)^2)⁻¹ := by
  classical
  let A := 1+Real.log N
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 1 ≤ A := by dsimp [A] <;> linarith [Real.log_nonneg hNR]
  have hpre := empty_prime_initial_mass Q
  have hpow (e : ℕ) (he : e ≤ h) :
      (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹)^e ≤ E^h :=
    (pow_le_pow_left₀ (by positivity) hmass e).trans (pow_le_pow_right₀ hE he)
  have hfinal (p : Fin d → ℕ) (l : Fin d) : primeFinal p 0 l=p l := by
    unfold primeFinal
    congr 1
    apply Fin.ext
    simp
  by_cases hjk : j=k
  · have hV : ∀ p ∈ Q, primeFinal p 0 j ∈ shiftDivisiblePrimes N (q^2) := by
      intro p hp
      rw [hfinal]
      apply Finset.mem_filter.mpr
      exact ⟨hU p hp j,by simpa only [ite_eq_left hjk] using hdiv p hp⟩
    have hu : ∀ p ∈ Q, ∀ l, primeFinal p 0 l ∈ Nat.primesLE N := by
      intro p hp l
      simpa only [hfinal] using hU p hp l
    have hh := prime_mass_one_exception (Nat.zero_le d) Q j _ _ hu hV
    have hv0 := shifted_divisor_mass N (pow_pos hq.pos 2)
    have hv : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A^2/((q : ℝ)^2) := by
      have hh : (∑ p ∈ shiftDivisiblePrimes N (q^2), ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/((q : ℝ)^2) := by
        simpa only [A,Nat.cast_pow] using hv0
      exact hh.trans (div_le_div_of_nonneg_right (by nlinarith : A ≤ A^2) (by positivity))
    have hm := mul_le_mul (mul_le_mul hpre hv (by positivity) (by norm_num))
      (hpow (d-0-1) (by omega)) (by positivity) (by positivity)
    exact hh.trans (by simpa only [one_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hm)
  · have hV : ∀ p ∈ Q, primeFinal p 0 j ∈ shiftDivisiblePrimes N q := by
      intro p hp
      rw [hfinal]
      exact Finset.mem_filter.mpr ⟨hU p hp j,(by simpa only [ite_eq_right hjk] using hdiv p hp : q ∣ p j-1 ∧ q ∣ p k-1).1⟩
    have hW : ∀ p ∈ Q, primeFinal p 0 k ∈ shiftDivisiblePrimes N q := by
      intro p hp
      rw [hfinal]
      exact Finset.mem_filter.mpr ⟨hU p hp k,(by simpa only [ite_eq_right hjk] using hdiv p hp : q ∣ p j-1 ∧ q ∣ p k-1).2⟩
    have hu : ∀ p ∈ Q, ∀ l, primeFinal p 0 l ∈ Nat.primesLE N := by
      intro p hp l
      simpa only [hfinal] using hU p hp l
    have hh := prime_mass_two_exceptions (Nat.zero_le d) Q j k hjk _ _ _ hu hV hW
    have hv : (∑ p ∈ shiftDivisiblePrimes N q, ((p-1 : ℕ) : ℝ)⁻¹) ≤ A/(q : ℝ) := shifted_divisor_mass N hq.pos
    have hm := mul_le_mul (mul_le_mul (mul_le_mul hpre hv (by positivity) (by norm_num)) hv
      (by positivity) (by positivity)) (hpow (d-0-2) (by omega)) (by positivity) (by positivity)
    apply hh.trans
    convert hm using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [A] <;> ring)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareCase
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma headSquareCase_basic {x t : ℝ} {H q j k : ℕ}
    {w : RemainderDatum (L x H) × ℕ} (hw : w ∈ headSquareCase x H t q j k) :
    IsBasicRemainder x H w.1 ∧ IsBasicTuple x H t (witnessTuple w.2 w.1) := by
  have hh := Finset.mem_filter.mp (Finset.mem_filter.mp hw).1
  exact ⟨mem_basicRemainderFinset.mp (Finset.mem_product.mp hh.1).1,hh.2⟩

lemma head_square_case_count (hmertens : MertensProductInput) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ t ≤ x, ∀ j k q : ℕ, j ≤ L x H → k ≤ L x H → q.Prime →
      ((headSquareCase x H t q j k).card : ℝ) ≤
      x*(∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ((1+Real.log (discardPrimeBound (B x) : ℝ))^2*
          (D*(2*B x+2))^(m x))*((q : ℝ)^2)⁻¹ := by
  obtain ⟨D,hD,hall⟩ := prime_reciprocal_mass_bound hmertens
  refine ⟨D+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)] with H hH hP
  filter_upwards [full_witness_prime_bound,theta_eventually_mem,
    m_tendsto.eventually (eventually_ge_atTop H),B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hbound hs hHm hB hx
  intro t ht j k q hj hk hq
  let S := headSquareCase x H t q j k
  let Q := S.image fullWitnessPrimes
  let N := discardPrimeBound (B x)
  let E := (D+1)*(2*B x+2)
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hPH := P_lt_self hH
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have hE : 1 ≤ E := by dsimp [E] <;> nlinarith
  have hN := discardPrimeBound_bounds hB
  have hmass : (∑ p ∈ Nat.primesLE N, ((p-1 : ℕ) : ℝ)⁻¹) ≤ E := by
    have hh := (hall N (by dsimp [N]; omega) hN.2.1).trans
      (mul_le_mul_of_nonneg_left (show 1+B (N : ℝ) ≤ 2*B x+2 by linarith [hN.2.2.1]) hD.le)
    exact hh.trans (by dsimp [E] <;> nlinarith)
  have hS : ∀ w ∈ S, IsBasicRemainder x H w.1 ∧ IsBasicTuple x H t (witnessTuple w.2 w.1) :=
    fun _ hw => headSquareCase_basic hw
  have hU : ∀ p ∈ Q, ∀ l, p l ∈ Nat.primesLE N := by
    intro p hp l
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    exact hbound H hPH.le t ht w (hS w hw).1 (hS w hw).2 l
  let j' : Fin (L x H+1) := ⟨j,by omega⟩
  let k' : Fin (L x H+1) := ⟨k,by omega⟩
  have hdiv : ∀ p ∈ Q, if j'=k' then q^2 ∣ p j'-1 else q ∣ p j'-1 ∧ q ∣ p k'-1 := by
    intro p hp
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hp
    have hh := (Finset.mem_filter.mp hw).2
    have hej : fullWitnessPrimes w j'=wholeWitnessPrime w.2 w.1 j := (wholeWitnessPrime_full w hj).symm
    have hek : fullWitnessPrimes w k'=wholeWitnessPrime w.2 w.1 k := (wholeWitnessPrime_full w hk).symm
    simpa only [j',k',Fin.mk.injEq,hej,hek] using hh
  have hdim : L x H+1 ≤ m x := by unfold L; omega
  have hpm := prime_square_mass (N := N) (by dsimp [N]; omega) hq hdim Q j' k' hE hU hdiv hmass
  have hc := full_witness_count_le hPH.le ht S hS
  have hw := full_witness_weight_le hPH hHm hs S (fun w hw => (hS w hw).1)
  calc
    _ ≤ x*(W*∑ p ∈ Q, reciprocalShiftWeight p) := hc.trans (mul_le_mul_of_nonneg_left hw hx.le)
    _ ≤ x*(W*((1+Real.log (N : ℝ))^2*E^(m x)*((q : ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpm hW) hx.le
    _ = _ := by dsimp [W,N,E] <;> ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareDivisor
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square in a finite product comes from one factor or two distinct factors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prime_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ ∏ j ∈ I, f j) : ∃ j ∈ I, q ∣ f j := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hq.not_dvd_one hd
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    rcases hq.dvd_mul.mp hd with h | h
    · exact ⟨a,Finset.mem_insert_self _ _,h⟩
    · obtain ⟨j,hj,hdj⟩ := ih h
      exact ⟨j,Finset.mem_insert_of_mem hj,hdj⟩

lemma square_dvd_product {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    {q : ℕ} (hq : q.Prime) (hd : q^2 ∣ ∏ j ∈ I, f j) :
    (∃ j ∈ I, q^2 ∣ f j) ∨
    (∃ j ∈ I, ∃ k ∈ I, j ≠ k ∧ q ∣ f j ∧ q ∣ f k) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have hh : q ∣ 1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans (by simpa using hd)
    exact (hq.not_dvd_one hh).elim
  | @insert a I ha ih =>
    rw [Finset.prod_insert ha] at hd
    by_cases h1 : q^2 ∣ f a
    · exact Or.inl ⟨a,Finset.mem_insert_self _ _,h1⟩
    by_cases h2 : q^2 ∣ ∏ j ∈ I, f j
    · rcases ih h2 with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
      · exact Or.inl ⟨j,Finset.mem_insert_of_mem hj,hj2⟩
      · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,k,Finset.mem_insert_of_mem hk,hjk,hqj,hqk⟩
    · have haq : q ∣ f a := by
        by_contra hn
        exact h2 (hq.prime.pow_dvd_of_dvd_mul_left 2 hn hd)
      have hIq : q ∣ ∏ j ∈ I, f j := by
        by_contra hn
        exact h1 (hq.prime.pow_dvd_of_dvd_mul_right 2 hn hd)
      obtain ⟨k,hk,hqk⟩ := prime_dvd_product I f hq hIq
      exact Or.inr ⟨a,Finset.mem_insert_self _ _,k,Finset.mem_insert_of_mem hk,
        (fun he => ha (he ▸ hk)),haq,hqk⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareCaseSum
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma finite_square_case_sum {β : Type*} (Q I : Finset ℕ)
    (S : ℕ → ℕ → ℕ → Finset β) (f : β → ℝ) (hf : ∀ y, 0 ≤ f y)
    {C A E h z : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hI : (I.card : ℝ) ≤ h) (hz : 1 ≤ z) (hQ : ∀ q ∈ Q, z < (q : ℝ))
    (hS : ∀ q ∈ Q, ∀ j ∈ I, ∀ k ∈ I,
      (∑ y ∈ S q j k, f y) ≤ C*A*E*((q : ℝ)^2)⁻¹) :
    (∑ y ∈ Q.biUnion (fun q => I.biUnion (fun j => I.biUnion (S q j))), f y) ≤
      C*(h^2*A*E)*(2/z) := by
  classical
  have hi0 : 0 ≤ h := (Nat.cast_nonneg I.card).trans hI
  have hqsum := inverse_square_tail Q hz hQ
  have hcases (q : ℕ) (hq : q ∈ Q) :
      (∑ y ∈ I.biUnion (fun j => I.biUnion (S q j)), f y) ≤
      C*(h^2*A*E)*((q : ℝ)^2)⁻¹ := by
    calc
      _ ≤ ∑ j ∈ I, ∑ k ∈ I, ∑ y ∈ S q j k, f y := by
        apply (nonnegative_sum_biUnion_le _ _ _ hf).trans
        exact Finset.sum_le_sum (fun j _ => nonnegative_sum_biUnion_le _ _ _ hf)
      _ ≤ ∑ _j ∈ I, ∑ _k ∈ I, C*A*E*((q : ℝ)^2)⁻¹ :=
        Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun k hk => hS q hq j hj k hk))
      _ = C*((I.card : ℝ)^2*A*E)*((q : ℝ)^2)⁻¹ := by simp <;> ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ q ∈ Q, ∑ y ∈ I.biUnion (fun j => I.biUnion (S q j)), f y :=
      nonnegative_sum_biUnion_le _ _ _ hf
    _ ≤ ∑ q ∈ Q, C*(h^2*A*E)*((q : ℝ)^2)⁻¹ := Finset.sum_le_sum hcases
    _ = C*(h^2*A*E)*(∑ q ∈ Q, ((q : ℝ)^2)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hqsum (by positivity)

lemma discard_square_log_mass {b : ℝ} (hb : 2 ≤ b) :
    2*(1+Real.log (discardPrimeBound b : ℝ))^2 ≤ (8*Real.exp 2)*Real.exp (4*b) := by
  have hn := discardPrimeBound_bounds hb
  have hn1 : (1 : ℝ) < discardPrimeBound b := by exact_mod_cast (show 1 < discardPrimeBound b by omega)
  have hl : Real.log (discardPrimeBound b : ℝ) ≤ Real.exp (2*b+1) := by
    simpa only [B,Real.exp_log (Real.log_pos hn1)] using Real.exp_le_exp.mpr hn.2.2.1
  have he1 : 1 ≤ Real.exp (2*b+1) := Real.one_le_exp (by linarith)
  have hA : 0 ≤ 1+Real.log (discardPrimeBound b : ℝ) := by
    linarith [Real.log_nonneg hn1.le]
  have hAb : 1+Real.log (discardPrimeBound b : ℝ) ≤ 2*Real.exp (2*b+1) := by linarith
  have hs := pow_le_pow_left₀ hA hAb 2
  have he : (Real.exp (2*b+1))^2=Real.exp (4*b+2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [mul_pow,he,Real.exp_add] at hs
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareDiscardDecay
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree cutoff absorbs all short-suffix entropy. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma square_cutoff_large {h : ℕ} {b u : ℝ} (hh : (100 : ℝ) ≤ h)
    (hb : (h : ℝ)^44 ≤ b) (hu : b/(8*(h : ℝ)^20) ≤ u) :
    b*(h : ℝ)^2 ≤ Real.exp u := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hb0 : 0 < b := (pow_pos hh0 44).trans_le hb
  have hu0 : 0 ≤ u := (by positivity : 0 ≤ b/(8*(h : ℝ)^20)).trans hu
  have h128 : (128 : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hp : 128*(h : ℝ)^42 ≤ (h : ℝ)^44 := by
    have ht := mul_le_mul_of_nonneg_right h128 (show 0 ≤ (h : ℝ)^42 by positivity)
    convert ht using 1 <;> first | rfl | ring
  have hnum : 128*b*(h : ℝ)^42 ≤ b^2 := by
    have ht := mul_le_mul_of_nonneg_left (hp.trans hb) hb0.le
    nlinarith
  have hs : b*(h : ℝ)^2 ≤ (b/(8*(h : ℝ)^20))^2/2 := by
    rw [div_pow,div_div]
    apply (le_div_iff₀ (by positivity : 0 < (8*(h : ℝ)^20)^2*2)).mpr
    convert hnum using 1 <;> first | rfl | ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ b/(8*(h : ℝ)^20)) hu 2
  have he := Real.quadratic_le_exp_of_nonneg hu0
  linarith

lemma square_head_discard_geometric {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∀ᶠ h : ℕ in atTop, ∀ b u : ℝ,
      (h : ℝ)^44 ≤ b → Real.log (6*b) ≤ 26*h → b/(8*(h : ℝ)^20) ≤ u →
      (h : ℝ)^2*(C*Real.exp (6*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) ≤ rho^h := by
  let A := |Real.log C|+|Real.log D|+lam+30
  have hA : 30 ≤ A := by dsimp [A] <;> linarith [abs_nonneg (Real.log C),abs_nonneg (Real.log D),lam_pos]
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2*A+100))] with h hh
  intro b u hb hlog hu
  have hh100 : (100 : ℝ) ≤ h := by linarith
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hhp : (h : ℝ) ≤ (h : ℝ)^44 := by simpa using pow_le_pow_right₀ hh1 (show 1 ≤ 44 by omega)
  have hhb : (h : ℝ) ≤ b := hhp.trans hb
  have hb0 : 0 < b := hh0.trans_le hhb
  have hb1 : 1 ≤ b := hh1.trans hhb
  have he := square_cutoff_large hh100 hb hu
  have hbase : 0 < 2*b+2 := by linarith
  have hlogbase : Real.log (2*b+2) ≤ 26*h :=
    (Real.log_le_log hbase (by linarith : 2*b+2 ≤ 6*b)).trans hlog
  have hlogh : Real.log (h : ℝ) ≤ h := by linarith [Real.log_le_sub_one_of_pos hh0]
  have hnt : (h : ℝ)*(Real.log D+Real.log (2*b+2)) ≤
      (h : ℝ)*(|Real.log D|+26*h) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_abs_self _) hlogbase) hh0.le
  have hh2 : (h : ℝ) ≤ (h : ℝ)^2 := by nlinarith
  have hsmall : |Real.log C|+(2+|Real.log D|+lam)*(h : ℝ)+26*(h : ℝ)^2 ≤ A*(h : ℝ)^2 := by
    have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (h : ℝ)^2 by nlinarith)
      (abs_nonneg (Real.log C))
    have hd := mul_le_mul_of_nonneg_left hh2
      (show 0 ≤ 2+|Real.log D|+lam by linarith [abs_nonneg (Real.log D),lam_pos])
    dsimp [A]
    nlinarith
  have hhalf1 : 6*b ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg hb0.le (show 0 ≤ (h : ℝ)^2-12 by nlinarith)]
  have hhalf2 : A*(h : ℝ)^2 ≤ b*(h : ℝ)^2/2 := by
    nlinarith [mul_nonneg (show 0 ≤ b-2*A by linarith) (show 0 ≤ (h : ℝ)^2 by positivity)]
  have hexponent : 2*Real.log (h : ℝ)+Real.log C+6*b+
      (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u ≤ -lam*h := by
    nlinarith [le_abs_self (Real.log C)]
  have heq : (h : ℝ)^2*(C*Real.exp (6*b))*(D*(2*b+2))^h/Real.exp (Real.exp u) =
      Real.exp (2*Real.log (h : ℝ)+Real.log C+6*b+
        (h : ℝ)*(Real.log D+Real.log (2*b+2))-Real.exp u) := by
    have htwo : Real.exp (2*Real.log (h : ℝ))=(h : ℝ)^2 := by
      simpa only [Nat.cast_ofNat,Real.exp_log hh0] using Real.exp_nat_mul (Real.log (h : ℝ)) 2
    rw [Real.exp_sub,Real.exp_add,Real.exp_add,Real.exp_add,htwo,Real.exp_nat_mul,
      Real.exp_add,Real.exp_log hC,Real.exp_log hD,Real.exp_log hbase]
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SquareLayerSum
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum square divisors and both coordinate choices in each positive-index layer. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma collision_cutoff_exponent_lower {x : ℝ} {i : ℕ} (hB : 1 < B x)
    (hi : i < m x) (hJ : 2*collisionCutoff (m x-i) < m x-i) :
    fordBandScale x i/(8*((m x-i : ℕ) : ℝ)^20) ≤
      (7/10 : ℝ)*fordBandScale x (collisionLastIndex x i) := by
  have hb := fordBandScale_pos (zero_lt_one.trans hB) hi
  have hh0 : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have hd := (le_div_iff₀ hb).mp (ford_collision_layer_ratio hB hi hJ).1
  have hc : (1/8 : ℝ) ≤ (7/20)*rho := by linarith [collision_rho_bounds.1]
  have hm := mul_le_mul_of_nonneg_right hc (div_nonneg hb.le (pow_pos hh0 20).le)
  have hmul := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 7/10)
  calc
    _ ≤ (7/10 : ℝ)*(rho/(2*((m x-i : ℕ) : ℝ)^20)*fordBandScale x i) := by
      first | (convert hm using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))
    _ ≤ _ := hmul

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareSum
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma discard_square_log_with_head {x : ℝ} (hx : 1 < x) (hB : 2 ≤ B x) :
    2*(1+Real.log (discardPrimeBound (B x) : ℝ))^2*Real.log x ≤
      (8*Real.exp 2)*Real.exp (6*B x) := by
  have ha := mul_le_mul_of_nonneg_right (discard_square_log_mass hB) (Real.log_pos hx).le
  have he : Real.log x=Real.exp (B x) := (Real.exp_log (Real.log_pos hx)).symm
  rw [he] at ha ⊢
  apply ha.trans
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)

lemma head_square_family_count (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      ((headSquareFamily x H t).card : ℝ) ≤
      (x/Real.log x)*(∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*rho^(m x) := by
  obtain ⟨D,hD,hcase⟩ := head_square_case_count hmertens
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (square_head_discard_geometric
    (C := 8*Real.exp 2) (D := D) (by positivity) (lt_of_lt_of_le zero_lt_one hD))
  filter_upwards [hcase,ford_band_polynomial_lower 44,eventually_collision_indices,eventually_ge_atTop H₀,
    eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hc hpoly hind hH0 hH hP
  filter_upwards [hc,hpoly,ford_band_log_upper,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),eventually_gt_atTop (1 : ℝ)]
    with x hcases hp hlog hHm hB hx
  intro t ht
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  let A := 1+Real.log (discardPrimeBound (B x) : ℝ)
  let E := D*(2*B x+2)
  let I := Finset.Icc 0 (L x H)
  let Q := squareLayerPrimes x 0
  let z := collisionSmoothCutoff x 0
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hA : 0 ≤ A := by
    have hN : (1 : ℝ) ≤ discardPrimeBound (B x) := by exact_mod_cast (show 1 ≤ discardPrimeBound (B x) by have := (discardPrimeBound_bounds hB).1; omega)
    dsimp [A]
    linarith [Real.log_nonneg hN]
  have hI : (I.card : ℝ) ≤ m x := by
    have hcn : I.card ≤ m x := by dsimp [I]; simp only [Nat.card_Icc]; unfold L; omega
    exact_mod_cast hcn
  have hz1 : 1 ≤ z := by dsimp [z,collisionSmoothCutoff]; exact Real.one_le_exp (Real.exp_pos _).le
  have hs := finite_square_case_sum Q I (headSquareCase x H t) (fun _ => (1 : ℝ))
    (fun _ => by norm_num) (mul_nonneg (zero_lt_one.trans hx).le hW) (sq_nonneg A)
    (pow_nonneg hE (m x)) hI hz1 (fun q hq => (Finset.mem_filter.mp hq).2) (by
      intro q hq j hj k hk
      have hqp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
      simpa only [W,A,E,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,mul_one,mul_assoc]
        using hcases t ht j k q (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hk).2 hqp)
  have hs' : ((headSquareFamily x H t).card : ℝ) ≤ x*W*((m x : ℝ)^2*A^2*E^(m x))*(2/z) := by
    simpa only [headSquareFamily,Q,I,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,mul_one] using hs
  have hm0 : 0 < m x := by omega
  have hb44 : (m x : ℝ)^44 ≤ B x := by simpa [fordBandScale] using hp 0 hm0 hHm
  have hlog0 : Real.log (6*B x) ≤ 26*m x := by simpa [fordBandScale] using hlog 0 hm0
  have hcut : B x/(8*(m x : ℝ)^20) ≤ (7/10)*fordBandScale x (collisionLastIndex x 0) := by
    simpa [fordBandScale] using collision_cutoff_exponent_lower (by linarith : 1 < B x) hm0 (hind x hHm 0 (Nat.zero_le _)).2.1
  have hsmall := hH₀ (m x) (hH0.trans hHm) (B x) ((7/10)*fordBandScale x (collisionLastIndex x 0)) hb44 hlog0 hcut
  have hlogx := Real.log_pos hx
  have hcoef : 0 ≤ (x/Real.log x)*W := mul_nonneg (div_nonneg (zero_lt_one.trans hx).le hlogx.le) hW
  calc
    _ ≤ x*W*((m x : ℝ)^2*A^2*E^(m x))*(2/z) := hs'
    _ = ((x/Real.log x)*W)*((m x : ℝ)^2*(2*A^2*Real.log x)*E^(m x)/z) := by field_simp
    _ ≤ ((x/Real.log x)*W)*((m x : ℝ)^2*((8*Real.exp 2)*Real.exp (6*B x))*E^(m x)/z) := by
      have ht := mul_le_mul_of_nonneg_left (discard_square_log_with_head hx hB)
        (show 0 ≤ (m x : ℝ)^2 by positivity)
      have ht' := mul_le_mul_of_nonneg_right ht (pow_nonneg hE (m x))
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right ht' (by dsimp [z,collisionSmoothCutoff] <;> positivity)) hcoef
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall hcoef

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_HeadSquareDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma headSquareFailure_card_le : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t ≤ x, (headSquareFailureTuples x H t).card ≤ (headSquareFamily x H t).card := by
  filter_upwards [eventually_collision_indices,eventually_ge_atTop 2] with H hind hH
  filter_upwards [full_witness_prime_bound,m_tendsto.eventually (eventually_ge_atTop H)] with x hb hm
  intro t ht
  have hPH := (P_lt_self hH).le
  have hcut := (hind x hm 0 (Nat.zero_le _)).2.2
  have hsub : headSquareFailureTuples x H t ⊆
      (headSquareFamily x H t).image (fun w => witnessTuple w.2 w.1) := by
    intro τ hτ
    obtain ⟨hτ,η,hη,he,hfail⟩ := Finset.mem_filter.mp hτ
    have hτb := (mem_tupleFinset hPH).mp hτ
    have hw : witnessTuple τ.head η=τ := by
      cases τ
      simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
    have hwb : IsBasicTuple x H t (witnessTuple τ.head η) := hw.symm ▸ hτb
    let w : RemainderDatum (L x H) × ℕ := (η,τ.head)
    have hbasic : w ∈ witnessFamily t (basicRemainderFinset x H) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨mem_basicRemainderFinset.mpr hη,Finset.mem_range.mpr (basic_tuple_head_bound hPH hτb)⟩,hwb⟩
    obtain ⟨q,hq,hqz,hqd⟩ : ∃ q : ℕ, q.Prime ∧ collisionSmoothCutoff x 0 < q ∧
        q^2 ∣ ∏ j ∈ Finset.Icc 0 (collisionLastIndex x 0), (wholeWitnessPrime τ.head η j-1) := by
      simpa only [SquarefreeAbove,not_forall,_root_.not_imp,not_not,exists_prop] using hfail
    have hprime (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0)) :
        wholeWitnessPrime τ.head η j ∈ Nat.primesLE (discardPrimeBound (B x)) := by
      have hjL := (Finset.mem_Icc.mp hj).2.trans hcut.le
      rw [wholeWitnessPrime_full w hjL]
      exact hb H hPH t ht w hη hwb _
    have hqN (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0))
        (hd : q ∣ wholeWitnessPrime τ.head η j-1) : q ∈ squareLayerPrimes x 0 := by
      have hp := Nat.mem_primesLE.mp (hprime j hj)
      have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.2.one_lt) hd
      refine Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_,hq⟩,hqz⟩
      have hh := hle.trans ((Nat.sub_le _ _).trans hp.1)
      simpa [fordBandScale] using hh
    have hjL (j : ℕ) (hj : j ∈ Finset.Icc 0 (collisionLastIndex x 0)) :
        j ∈ Finset.Icc 0 (L x H) :=
      Finset.mem_Icc.mpr ⟨Nat.zero_le _,(Finset.mem_Icc.mp hj).2.trans hcut.le⟩
    have hmem : w ∈ headSquareFamily x H t := by
      let : DecidableEq (RemainderDatum (L x H) × ℕ) := Classical.decEq _
      rcases square_dvd_product _ _ hq hqd with ⟨j,hj,hj2⟩ | ⟨j,hj,k,hk,hjk,hqj,hqk⟩
      · have hqj : q ∣ wholeWitnessPrime τ.head η j-1 := (dvd_pow_self q (by norm_num : 2 ≠ 0)).trans hj2
        refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr
          ⟨j,hjL j hj,Finset.mem_biUnion.mpr ⟨j,hjL j hj,?_⟩⟩⟩
        exact Finset.mem_filter.mpr ⟨hbasic,by simpa only [w,ite_true, if_true] using hj2⟩
      · refine Finset.mem_biUnion.mpr ⟨q,hqN j hj hqj,Finset.mem_biUnion.mpr
          ⟨j,hjL j hj,Finset.mem_biUnion.mpr ⟨k,hjL k hk,?_⟩⟩⟩
        exact Finset.mem_filter.mpr ⟨hbasic,by simpa only [w,ite_eq_right hjk] using And.intro hqj hqk⟩
    exact Finset.mem_image.mpr ⟨w,hmem,hw⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem head_square_tuple_discard_oai (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((headSquareFailureTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨E,hE,hcof⟩ := tail_cofactor_sum hmertens
  let ε := fun H => E*Real.exp ((4*(lam/rho))*cofactorScale H)*polynomialGeometricTail 0 rho H
  refine ⟨ε,?_,?_⟩
  · have hh := (cofactor_polynomialGeometricTail_tendsto (4*(lam/rho)) 0 rho_pos.le rho_lt_one).const_mul E
    simpa only [ε,mul_assoc,mul_zero] using hh
  filter_upwards [headSquareFailure_card_le,head_square_family_count hmertens] with H hcard hcount
  filter_upwards [hcard,hcount,G_eventually_one_le hren,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ)] with x hc hn hG hHm hx
  intro t ht
  let W := ∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹
  have hw : W ≤ E*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [W,cofactorScale,mul_assoc] using hcof H
  have hr : rho^(m x) ≤ polynomialGeometricTail 0 rho H := by
    apply le_trans _ (reverse_geometric_sum hHm)
    simpa only [Nat.sub_zero] using
      (Finset.single_le_sum (f := fun i => rho^(m x-i))
        (fun _ _ => (pow_pos rho_pos _).le)
        (Finset.mem_Icc.mpr ⟨le_rfl,Nat.zero_le (m x-H)⟩))
  have hscale : 0 ≤ x/Real.log x := div_nonneg (zero_lt_one.trans hx).le (Real.log_pos hx).le
  have hsmall : W*rho^(m x) ≤ ε H := by
    apply mul_le_mul hw hr
    · exact (pow_pos rho_pos _).le
    · positivity
  have heps : 0 ≤ ε H := mul_nonneg (by positivity) (polynomialGeometricTail_nonneg 0 rho_pos.le H)
  calc
    _ ≤ ((headSquareFamily x H t).card : ℝ) := Nat.cast_le.mpr (hc t ht)
    _ ≤ (x/Real.log x)*(W*rho^(m x)) := by simpa only [W,mul_assoc] using hn t ht
    _ ≤ (x/Real.log x)*ε H := mul_le_mul_of_nonneg_left hsmall hscale
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG (mul_nonneg hscale heps)
      simpa only [mul_one,one_mul,mul_assoc,mul_comm,mul_left_comm] using hh

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.head_square_tuple_discard_oai := @OAI.TotientAsymptotic.head_square_tuple_discard_oai
