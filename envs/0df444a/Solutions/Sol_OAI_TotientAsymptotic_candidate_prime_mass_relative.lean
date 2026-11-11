-- Prove2me | solution 1 for OAI.TotientAsymptotic.candidate_prime_mass_relative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:31:58.401729+00:00
-- url     : https://prove2.me/submissions/0a826eb8-b32d-42eb-a82a-201908c8b998

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
import Mathlib.MeasureTheory.Constructions.Pi
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



lemma isTotient_pos {d : ℕ} (hd : IsTotient d) : 0 < d := by
  obtain ⟨n, hn, rfl⟩ := hd
  exact Nat.totient_pos.mpr hn

lemma ell_spec {d : ℕ} (hd : IsTotient d) : 0 < ell d ∧ (ell d).totient = d := by
  classical
  simpa only [ell, dite_eq_left hd] using Nat.find_spec hd

lemma ell_le {d n : ℕ} (hn : 0 < n) (hφ : n.totient = d) : ell d ≤ n := by
  classical
  have hd : IsTotient d := ⟨n, hn, hφ⟩
  simpa only [ell, dite_eq_left hd] using Nat.find_min' hd ⟨hn, hφ⟩

lemma le_ell {d : ℕ} (hd : IsTotient d) : d ≤ ell d := by
  calc d = (ell d).totient := (ell_spec hd).2.symm
       _ ≤ ell d := Nat.totient_le _

lemma one_le_ell_ratio {d : ℕ} (hd : IsTotient d) : 1 ≤ (ell d : ℝ) / d := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (isTotient_pos hd)
  rw [le_div_iff₀ hdpos, one_mul]
  exact_mod_cast le_ell hd

end TotientAsymptotic

end

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBounds
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite tail bounds and nonnegative coefficients from exponential random variables. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic



lemma witness_w_bound {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) :
    w η ≤ tailCofactorBound H * (tailPrimeBound H)^(H-P H) := by
  have hp : ∏ h ∈ Finset.Ico (P H) H, tailPrime η h ≤
      (tailPrimeBound H)^(H-P H) := by
    calc
      _ ≤ ∏ _h ∈ Finset.Ico (P H) H, tailPrimeBound H := by
        apply Finset.prod_le_prod'
        intro h hh
        have hhH := (Finset.mem_Ico.mp hh).2
        simpa [tailPrime, hhH] using (witness_prime_bound hs hη ⟨h, hhH⟩).2
      _ = _ := by simp
  exact Nat.mul_le_mul (witness_cofactor_bound hs hη).2 hp

lemma witness_totient_bound {H : ℕ} {s : ℝ} {d : ℕ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (η : TailDatum H) (hη : η ∈ witnesses H s d) :
    d ≤ tailCofactorBound H * (tailPrimeBound H)^(H-P H) := by
  rw [← hη.2]
  exact (Nat.totient_le _).trans (witness_w_bound hs hη.1)


open MeasureTheory ProbabilityTheory
open scoped Classical

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

lemma extractTail_value {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H))
    (hPH : P H ≤ H) (hHm : H ≤ m x) :
    w (extractTail x H η) = remainderTail x H η := by
  unfold w remainderTail
  change η.cofactor* _ = η.cofactor* _
  congr 1
  apply Finset.prod_bij (fun h _ => m x-h)
  · intro h hh
    have := Finset.mem_Ico.mp hh
    apply Finset.mem_Icc.mpr
    unfold R L
    omega
  · intro h hh k hk heq
    have := Finset.mem_Ico.mp hh
    have := Finset.mem_Ico.mp hk
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hr : m x-i ∈ Finset.Ico (P H) H := by
      apply Finset.mem_Ico.mpr
      unfold R L at *
      omega
    refine ⟨m x-i, hr, ?_⟩
    unfold L at hi'
    omega
  · intro h hh
    exact extractTail_prime η hh

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassTailSupport
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed finite tail support and exact grouping of the actual prefix mass. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma witness_w_pos {H : ℕ} {s : ℝ} {η : TailDatum H} (hη : IsWitness H s η) :
    0 < w η := by
  apply Nat.mul_pos hη.2.1
  apply Finset.prod_pos
  intro h hh
  exact (hη.2.2.1 h hh).1.pos

lemma prefix_tail_support {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (hζ : IsPrefixDatum x H ζ) :
    IsTotient ζ.d ∧ ζ.d ∈ Finset.Icc 1 (tailValueBound H) := by
  obtain ⟨η, hη, hd, _⟩ := hζ
  let η' := extractTail x H η
  have hw : IsWitness H (theta x) η' := extractTail_isWitness hη hPH hHm
  have hwd : (w η').totient = ζ.d := by
    rw [extractTail_value η hPH.le hHm]
    exact hd
  have hdt : IsTotient ζ.d := ⟨w η', witness_w_pos hw, hwd⟩
  refine ⟨hdt, Finset.mem_Icc.mpr ⟨isTotient_pos hdt, ?_⟩⟩
  exact witness_totient_bound hs η' ⟨hw, hwd⟩

lemma mass_eq_sum_prefixData (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    M x H f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)) := by
  unfold M
  rw [finsum_eq_sum_of_support_subset _ (s := prefixDataFinset x H)]
  · apply Finset.sum_congr rfl
    intro ζ hζ
    rw [ite_eq_left (mem_prefixDataFinset.mp hζ)]
  · intro ζ hζ
    by_contra hnot
    have h := mt mem_prefixDataFinset.mpr hnot
    simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hζ

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixSize
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prefix denominators and the size bound needed for largest-prime summation. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma prefixDenominator_of_witness {x : ℝ} {H : ℕ}
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H) :
    prefixDenominator (prefixOfRemainder x H η) = (suffixPreimage η 0).totient := by
  rw [basic_suffix_totient_split hη hL (Nat.zero_le (R x H)) hR]
  simp only [prefixDenominator, prefixOfRemainder, ← suffixPreimage_at_R]
  simpa only [Nat.zero_add] using congrArg
    (fun n : ℕ => (suffixPreimage η (R x H)).totient*n)
    (prod_fin_shifted (R x H) (fun r => remainderPrime η r-1))

lemma basic_prefix_denominator_log_small {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      Real.log (prefixDenominator ζ : ℝ) ≤ (Real.log x)^(4/5 : ℝ) := by
  filter_upwards [basic_remainder_log_small H, m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro ζ hζ
  obtain ⟨η, hη, rfl⟩ := (isPrefixDatum_iff x H ζ).mp hζ
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  rw [prefixDenominator_of_witness hη hL hR]
  have hpos := Nat.totient_pos.mpr (suffixPreimage_pos hη (i := 0))
  have hpR : (0 : ℝ) < (suffixPreimage η 0).totient := by exact_mod_cast hpos
  exact (Real.log_le_log hpR (by exact_mod_cast Nat.totient_le (suffixPreimage η 0))).trans (hx η hη)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PublishedPrimeCount
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The classical prime number theorem, in precisely the epsilon form used here.
Hadamard and de la Vallée Poussin (1896); for a numbered, accessible statement
see Terence Tao, *254A, Notes 2: Complex-analytic multiplicative number theory*
(9 December 2014), Exercise 40, following Corollary 39:
https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/
Only pi(y) ~ y/log(y) is retained from the stronger published estimate.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- A deterministic change of the logarithm and the endpoint in a prime
count. Its hypotheses are later verified uniformly over all prefix data. -/
lemma prime_count_change_scale {x y z δ : ℝ}
    (hL : 0 < Real.log x) (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/4)
    (hlog : (1-δ)*Real.log x ≤ Real.log y ∧ Real.log y ≤ (1+δ)*Real.log x)
    (hy : z ≤ y ∧ y ≤ (1+δ)*z)
    (hp : |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y| ≤ δ*(y/Real.log y)) :
    |(Nat.primeCounting ⌊y⌋₊ : ℝ)-z/Real.log x| ≤ 6*δ*(z/Real.log x) := by
  have hly : 0 < Real.log y := lt_of_lt_of_le (mul_pos (by linarith) hL) hlog.1
  have hden : 0 < Real.log y*Real.log x := mul_pos hly hL
  have hratio : |y/Real.log y-z/Real.log x| ≤ 3*δ*(z/Real.log x) := by
    apply (abs_le).mpr
    constructor
    · have hh : -(3*δ*z*Real.log y) ≤ y*Real.log x-z*Real.log y := by
        have h1 := mul_le_mul_of_nonneg_right hy.1 hL.le
        have h2 := mul_le_mul_of_nonneg_left hlog.2 hz
        have h3 := mul_le_mul_of_nonneg_left hlog.1 (mul_nonneg hδ hz)
        nlinarith
      convert (div_le_div_of_nonneg_right hh hden.le) using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    · have hh : y*Real.log x-z*Real.log y ≤ 3*δ*z*Real.log y := by
        have h1 := mul_le_mul_of_nonneg_right hy.2 hL.le
        have h2 := mul_le_mul_of_nonneg_left hlog.1 hz
        have h3 := mul_le_mul_of_nonneg_left hlog.1 (mul_nonneg hδ hz)
        nlinarith [mul_nonneg (show 0 ≤ δ*(1-4*δ) by nlinarith) (mul_nonneg hz hL.le)]
      convert (div_le_div_of_nonneg_right hh hden.le) using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hsize : y/Real.log y ≤ 2*(z/Real.log x) := by
    apply (div_le_iff₀ hly).mpr
    have h1 := mul_le_mul_of_nonneg_right hy.2 hL.le
    have h2 := mul_le_mul_of_nonneg_left hlog.1 hz
    have hh : y*Real.log x ≤ 2*z*Real.log y := by
      nlinarith [mul_nonneg hz hL.le]
    have ht := (le_div_iff₀ hL).mpr hh
    convert ht using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  calc
    _ ≤ |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y|+|y/Real.log y-z/Real.log x| := abs_sub_le _ _ _
    _ ≤ δ*(y/Real.log y)+3*δ*(z/Real.log x) := add_le_add hp hratio
    _ ≤ 6*δ*(z/Real.log x) := by
      have hh := mul_le_mul_of_nonneg_left hsize hδ
      nlinarith [mul_nonneg hδ (div_nonneg hz hL.le)]

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

lemma small_denominator_window {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t → t ≤ x →
      let z := t/D
      let y := 1+z
      x^(1/2 : ℝ) ≤ z ∧ z ≤ y ∧ y ≤ (1+δ)*z ∧
      (1-δ)*Real.log x ≤ Real.log y ∧ Real.log y ≤ (1+δ)*Real.log x := by
  have hc : Tendsto (fun x : ℝ => -Real.log a/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh : Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x +
      -Real.log a/Real.log x) atTop (nhds 0) := by
    simpa only [add_zero] using subpower_log_ratio.add hc
  have hroot : Tendsto (fun x : ℝ => x^(1/2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hh.eventually (eventually_lt_nhds hδ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2/δ)),
    hroot.eventually (eventually_ge_atTop (1/δ))] with x hx hsmall hlog2 hlarge
  intro D t hD hlogD ht htx
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have ht0 : 0 < t := (mul_pos ha hx0).trans_le ht
  have hz0 : 0 < t/D := div_pos ht0 hD0
  have hlo : (1-δ)*Real.log x ≤ Real.log (t/D) := by
    have hb := (div_lt_iff₀ hL).mp (show ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x < δ by
      have e : ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x =
          (Real.log x)^(4/5 : ℝ)/Real.log x + -Real.log a/Real.log x := by ring
      rw [e]; exact hsmall)
    have hlt := Real.log_le_log (mul_pos ha hx0) ht
    rw [Real.log_mul ha.ne' hx0.ne'] at hlt
    rw [Real.log_div ht0.ne' hD0.ne']
    linarith
  have hz : x^(1/2 : ℝ) ≤ t/D := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log (t/D)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_log hz0
  refine ⟨hz, by linarith, ?_, ?_, ?_⟩
  · have hh : 1 ≤ δ*(t/D) := by
      calc
        1 = δ*(1/δ) := by field_simp
        _ ≤ δ*(t/D) := mul_le_mul_of_nonneg_left (hlarge.trans hz) hδ.le
    linarith
  · exact hlo.trans (Real.log_le_log hz0 (by linarith))
  · have hzle : t/D ≤ x := (div_le_iff₀ hD0).mpr (by nlinarith)
    have hyle : 1+t/D ≤ 2*x := by linarith
    have hb := Real.log_le_log (by positivity : (0 : ℝ)<1+t/D) hyle
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hx0.ne'] at hb
    have h2 : Real.log 2 ≤ δ*Real.log x := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog2
    linarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShiftedPrimeCount
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact largest-prime fibers and the negligible lower cutoff. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_shiftedPrimeSet {x t : ℝ} {D p : ℕ} (ht : 0 ≤ t) (hD : 0 < D) :
    p ∈ shiftedPrimeSet x t D ↔
      p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧ ((p-1 : ℕ)*D : ℕ) ≤ t := by
  have hD0 : (0 : ℝ)<D := by exact_mod_cast hD
  have hy : 0 ≤ 1+t/D := by positivity
  simp only [shiftedPrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpy,hp⟩,hlo⟩
    refine ⟨hp,hlo,?_⟩
    have hh : (p : ℝ) ≤ 1+t/D := (by exact_mod_cast hpy : (p : ℝ)≤⌊1+t/D⌋₊).trans (Nat.floor_le hy)
    have hp1 : 1 ≤ p := hp.one_lt.le
    push_cast
    rw [Nat.cast_sub hp1]
    have := (le_div_iff₀ hD0).mp (show (p : ℝ)-1 ≤ t/D by linarith)
    simpa only [Nat.cast_one] using this
  · rintro ⟨hp,hlo,hv⟩
    have hv' : ((p : ℝ)-1)*D ≤ t := by simpa only [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one] using hv
    have hh : (p : ℝ) ≤ 1+t/D := by
      have := (le_div_iff₀ hD0).mpr hv'
      linarith
    exact ⟨⟨Nat.le_floor hh,hp⟩,hlo⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LowerPrimeCutoff
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The lower bound on the largest prime has negligible cost in every actual fiber. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma headCutoffLoss_tendsto : Tendsto headCutoffLoss atTop (nhds 0) := by
  have hb : Tendsto (fun x : ℝ => 2*(Real.log x*Real.exp (-(1/20 : ℝ)*Real.log x))) atTop (nhds 0) := by
    simpa only [Real.rpow_one, mul_zero, Function.comp_def] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/20) (by norm_num)).comp
        Real.tendsto_log_atTop).const_mul 2
  apply squeeze_zero' (g := fun x : ℝ => 2*(Real.log x*Real.exp (-(1/20 : ℝ)*Real.log x)))
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.log_pos hx).le) (zero_lt_one.trans hx).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      subpower_log_ratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/20))] with x hx hs
    have hx0 := zero_lt_one.trans hx
    have hL := Real.log_pos hx
    have hsmall : (Real.log x)^(4/5 : ℝ) ≤ (1/20 : ℝ)*Real.log x :=
      ((div_lt_iff₀ hL).mp hs).le
    have hxpow : 1 ≤ x^(9/10 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    have he : (x^(9/10 : ℝ)+1)*Real.exp ((Real.log x)^(4/5 : ℝ)) ≤
        2*Real.exp ((19/20 : ℝ)*Real.log x) := by
      calc
        _ ≤ (2*x^(9/10 : ℝ))*Real.exp ((1/20 : ℝ)*Real.log x) :=
          mul_le_mul (by linarith) (Real.exp_le_exp.mpr hsmall) (Real.exp_pos _).le (by positivity)
        _ = _ := by
          rw [Real.rpow_def_of_pos hx0, mul_assoc, ← Real.exp_add]
          congr 2
          ring
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hL.le) hx0.le).trans_eq
    calc
      _ = (2*Real.log x)*(Real.exp ((19/20 : ℝ)*Real.log x)*Real.exp (-Real.log x)) := by
        rw [div_eq_mul_inv, show x⁻¹ = Real.exp (-Real.log x) by rw [Real.exp_neg, Real.exp_log hx0]]
        ring
      _ = _ := by
        rw [← Real.exp_add]
        rw [show (19/20 : ℝ)*Real.log x+-Real.log x = -(1/20 : ℝ)*Real.log x by ring]
        ring
  · exact hb

lemma lower_prime_cutoff_negligible {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t →
      x^(9/10 : ℝ)+1 ≤ ε*(t/(D*Real.log x)) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    headCutoffLoss_tendsto.eventually (eventually_lt_nhds (mul_pos hε ha))] with x hx hsmall
  intro D t hD hlogD ht
  have hx0 := zero_lt_one.trans hx
  have hL := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have he : D ≤ Real.exp ((Real.log x)^(4/5 : ℝ)) := (Real.log_le_iff_le_exp hD0).mp hlogD
  have hc : 0 ≤ x^(9/10 : ℝ)+1 := by positivity
  have hmain : (x^(9/10 : ℝ)+1)*(D*Real.log x) ≤ ε*t := by
    calc
      _ ≤ (x^(9/10 : ℝ)+1)*(Real.exp ((Real.log x)^(4/5 : ℝ))*Real.log x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hL.le) hc
      _ = headCutoffLoss x*x := by unfold headCutoffLoss; field_simp
      _ ≤ (ε*a)*x := mul_le_mul_of_nonneg_right hsmall.le hx0.le
      _ ≤ ε*t := by nlinarith
  have hdiv := (le_div_iff₀ (mul_pos hD0 hL)).mpr hmain
  convert hdiv using 1 <;> first | rfl | ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixReciprocals
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

lemma prefixReciprocalError_tendsto : Tendsto prefixReciprocalError atTop (nhds 0) :=
  polynomialGeometricTail_tendsto 0 _

lemma prefix_prime_reciprocal : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    ∀ i : Fin (R x H), (1 : ℝ)/remainderPrime η (i.val+1) ≤
      Real.exp (-1)^(m x-(i.val+1)) := by
  have ht : Tendsto (fun h : ℝ => h*Real.exp (-(1/2 : ℝ)*h)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      1 (1/2) (by norm_num : (0 : ℝ)<1/2)
  obtain ⟨h₀,hh₀⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))
  filter_upwards [eventually_ge_atTop (Nat.ceil h₀),eventually_ge_atTop 2] with H hH hH2
  intro x hs hm η hη i
  have hi : i.val+1 ≤ R x H := by have := i.isLt; omega
  have hPH := (P_lt_self hH2).le
  have hiL : i.val+1 ≤ L x H := by unfold R L at *; omega
  have hh : H ≤ m x-(i.val+1) := by unfold R at hi; omega
  let h := m x-(i.val+1)
  have hhr : h₀ ≤ (h : ℝ) := (Nat.le_ceil h₀).trans (by exact_mod_cast hH.trans hh)
  have he := hh₀ h hhr
  have he' : (h : ℝ) ≤ Real.exp ((1/2 : ℝ)*h) := by
    have he' := mul_lt_mul_of_pos_right he (Real.exp_pos ((1/2 : ℝ)*h))
    rw [mul_assoc,← Real.exp_add] at he'
    simpa using he'.le
  have hband : lam*h ≤ bandScale x (i.val+1) := by
    have ha := alpha_ge_lam hs
    have hp : 1 ≤ (rho^h)⁻¹ := (one_le_inv₀ (pow_pos rho_pos h)).mpr
      (pow_le_one₀ rho_pos.le rho_lt_one.le)
    change _ ≤ alpha (theta x)*h*(rho^h)⁻¹
    exact (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg h)).trans
      (le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg h)) hp)
  have hp := hη.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega,hiL⟩)
  have hp0 : (0 : ℝ) < remainderPrime η (i.val+1) := by exact_mod_cast hp.1.pos
  have hp1 : (1 : ℝ) < remainderPrime η (i.val+1) := by exact_mod_cast hp.1.one_lt
  have hl : (1/2 : ℝ)*h ≤ Real.log (Real.log (remainderPrime η (i.val+1) : ℝ)) := by
    have hlow := hp.2.1
    simp only [remainderCoord,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false, if_false] at hlow
    have hlambda := collision_lambda_bounds.1
    nlinarith [Nat.cast_nonneg (α := ℝ) h]
  have hlog : (h : ℝ) ≤ Real.log (remainderPrime η (i.val+1) : ℝ) :=
    he'.trans ((Real.le_log_iff_exp_le (Real.log_pos hp1)).mp hl)
  have hprime : Real.exp h ≤ (remainderPrime η (i.val+1) : ℝ) :=
    (Real.le_log_iff_exp_le hp0).mp hlog
  calc
    (1 : ℝ)/remainderPrime η (i.val+1) ≤ 1/Real.exp h := one_div_le_one_div_of_le (Real.exp_pos _) hprime
    _ = Real.exp (-1)^h := by rw [one_div,← Real.exp_neg,← Real.exp_nat_mul]; congr 1; ring

lemma prefix_reciprocal_sum : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, 0 ≤ theta x → H ≤ m x →
    ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      (∑ i, (1 : ℝ)/ζ.primes i) ≤ prefixReciprocalError H := by
  filter_upwards [prefix_prime_reciprocal] with H hH
  intro x hs hm ζ hζ
  obtain ⟨η,hη,hd,hp⟩ := hζ
  have hsummable : Summable (fun n : ℕ => Real.exp (-1)^(H+n)) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)).comp_injective (fun _ _ h => by omega)
  have he : (∑ i : Fin (R x H), Real.exp (-1)^(m x-(i.val+1))) =
      ∑ n ∈ Finset.range (R x H), Real.exp (-1)^(H+n) := by
    apply Finset.sum_bij (fun i _ => m x-(i.val+1)-H)
    · intro i _
      have := i.isLt
      apply Finset.mem_range.mpr
      unfold R at *
      omega
    · intro i _ j _ hij
      apply Fin.ext
      have := i.isLt
      have := j.isLt
      unfold R at *
      omega
    · intro n hn
      have hn' := Finset.mem_range.mp hn
      refine ⟨⟨m x-H-1-n,by unfold R at *; omega⟩,Finset.mem_univ _,?_⟩
      change m x-(m x-H-1-n+1)-H=n
      unfold R at hn'
      omega
    · intro i _
      congr 1
      have := i.isLt
      unfold R at *
      omega
  calc
    (∑ i, (1 : ℝ)/ζ.primes i) ≤ ∑ i : Fin (R x H), Real.exp (-1)^(m x-(i.val+1)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [hp]
      exact hH x hs hm η hη i
    _ = _ := he
    _ ≤ ∑' n : ℕ, Real.exp (-1)^(H+n) := hsummable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = prefixReciprocalError H := by simp [prefixReciprocalError,polynomialGeometricTail]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightPerturbation
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma one_sub_prod_le_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i ∧ a i ≤ 1) :
    1-∏ i ∈ S, a i ≤ ∑ i ∈ S, (1-a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hp0 : 0 ≤ ∏ j ∈ S, a j := Finset.prod_nonneg (fun j hj => (hS j hj).1)
    have hp1 : ∏ j ∈ S, a j ≤ 1 :=
      Finset.prod_le_one (fun j hj => (hS j hj).1) (fun j hj => (hS j hj).2)
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    have hh := ih hS
    nlinarith [mul_nonneg (sub_nonneg.mpr hai.2) (sub_nonneg.mpr hp1)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedPrimeWindow
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime counts at both moving endpoints of the least-preimage interval. -/

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem linear_prime_window (hpnt : PrimeNumberTheoremInput)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D y : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) →
      a*x/D ≤ y → y ≤ b*x/D →
      |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log x| ≤ ε*x/(D*Real.log x) := by
  let δ := min (1/4 : ℝ) (ε/(6*b))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδq : δ ≤ 1/4 := min_le_left _ _
  have hδb : 6*δ*b ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 6*b by positivity)).mp (min_le_right (1/4 : ℝ) (ε/(6*b)))
    nlinarith
  have hlow : Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x+
      (-Real.log a)/Real.log x) atTop (nhds 0) := by
    simpa using subpower_log_ratio.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hupp : Tendsto (fun x : ℝ => Real.log b/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (hpnt δ hδ)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hlow.eventually (eventually_lt_nhds hδ),hupp.eventually (eventually_lt_nhds hδ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).eventually (eventually_ge_atTop Y)]
    with x hx hlo hup hYx
  intro D y hD hlogD hylo hyhi
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hy0 : 0 < y := (div_pos (mul_pos ha hx0) hD0).trans_le hylo
  have hloglo : (1-δ)*Real.log x ≤ Real.log y := by
    have hh := (div_lt_iff₀ hL).mp (show ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x < δ by
      have e : ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x =
          (Real.log x)^(4/5 : ℝ)/Real.log x + -Real.log a/Real.log x := by ring
      rw [e]; exact hlo)
    have ht := Real.log_le_log (div_pos (mul_pos ha hx0) hD0) hylo
    rw [Real.log_div (mul_pos ha hx0).ne' hD0.ne',Real.log_mul ha.ne' hx0.ne'] at ht
    linarith
  have hloghi : Real.log y ≤ (1+δ)*Real.log x := by
    have hxy : y ≤ b*x := hyhi.trans (div_le_self (mul_nonneg hb.le hx0.le) hD)
    have ht := Real.log_le_log hy0 hxy
    rw [Real.log_mul hb.ne' hx0.ne'] at ht
    have hh := (div_lt_iff₀ hL).mp hup
    linarith
  have hroot : x^(1/2 : ℝ) ≤ y := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr (by nlinarith)
      _ = y := Real.exp_log hy0
  have hp := hY y (hYx.trans hroot)
  have he := prime_count_change_scale hL hy0.le hδ.le hδq ⟨hloglo,hloghi⟩
    ⟨le_rfl,le_mul_of_one_le_left hy0.le (by linarith : 1 ≤ 1+δ)⟩ hp
  apply he.trans
  calc
    6*δ*(y/Real.log x) ≤ 6*δ*((b*x/D)/Real.log x) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hyhi hL.le) (by positivity)
    _ = (6*δ*b)*x/(D*Real.log x) := by ring
    _ ≤ ε*x/(D*Real.log x) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδb hx0.le) (mul_nonneg hD0.le hL.le)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedFiber
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

lemma tupleLeastCandidate_eq_head {r p : ℕ} (ζ : PrefixDatum r) :
    tupleLeastCandidate (TotientTuple.mk p ζ)=p*prefixCandidateFactor ζ := by
  simp only [tupleLeastCandidate,tuplePrimeProduct,tuplePrimes,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,prefixCandidateFactor]
  ring

lemma candidate_fiber_card {x : ℝ} {H k : ℕ} (hPH : P H ≤ H) (hx : 0 ≤ x)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    ((candidateTuples x H k).filter (fun τ => τ.tail=ζ)).card=(candidatePrimeSet x H k ζ).card := by
  apply Finset.card_bij (fun τ _ => τ.head)
  · intro τ hτ
    obtain ⟨hτ,htail⟩ := Finset.mem_filter.mp hτ
    obtain ⟨hb,hw⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hb
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_shiftedPrimeSet hx (basic_prefix_denominator_pos hPH hζ)).mpr
      refine ⟨hb.1,hb.2.1,?_⟩
      have hv := hb.2.2.2
      change ((tupleValue (TotientTuple.mk τ.head τ.tail) : ℕ) : ℝ) ≤ x at hv
      rw [tupleValue_eq_head,htail] at hv
      exact hv
    · have he : τ=TotientTuple.mk τ.head ζ := by cases τ; simp_all
      rw [he] at hw
      simpa only [candidateInWindow,tupleLeastCandidate_eq_head] using hw
  · intro τ hτ σ hσ he
    have ht := (Finset.mem_filter.mp hτ).2
    have hs := (Finset.mem_filter.mp hσ).2
    cases τ
    cases σ
    simp_all
  · intro p hp
    obtain ⟨hp,hw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hlo,hval⟩ := (mem_shiftedPrimeSet hx (basic_prefix_denominator_pos hPH hζ)).mp hp
    refine ⟨⟨p,ζ⟩,Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_tupleFinset hPH).mpr
      refine ⟨hp,hlo,hζ,?_⟩
      simpa only [tupleValue_eq_head,prefixDenominator] using hval
    · simpa only [candidateInWindow,tupleLeastCandidate_eq_head] using hw

lemma candidate_count_eq_prime_fibers {x : ℝ} {H k : ℕ} (hPH : P H ≤ H) (hx : 0 ≤ x) :
    ((candidateTuples x H k).card : ℝ)=
      ∑ ζ ∈ prefixDataFinset x H, ((candidatePrimeSet x H k ζ).card : ℝ) := by
  have hmap : ∀ τ ∈ candidateTuples x H k, τ.tail ∈ prefixDataFinset x H := by
    intro τ hτ
    exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp (Finset.mem_filter.mp hτ).1).2.2.1
  have he := Finset.sum_card_fiberwise_eq_card_filter (candidateTuples x H k) (prefixDataFinset x H) TotientTuple.tail
  rw [Finset.filter_eq_self.mpr hmap] at he
  rw [← he,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ζ hζ
  rw [candidate_fiber_card hPH hx (mem_prefixDataFinset.mp hζ)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixWeight
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

lemma prefixQ_bounds {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    0 < prefixQ ζ ∧ prefixQ ζ ≤ 1 ∧
      1-prefixQ ζ ≤ ∑ i, (1 : ℝ)/ζ.primes i := by
  have hp := (basic_prefix_data_positive hPH hζ).2
  have hi (i : Fin (R x H)) : 0 < 1-(1 : ℝ)/ζ.primes i ∧ 1-(1 : ℝ)/ζ.primes i ≤ 1 := by
    have hpi : (1 : ℝ) < ζ.primes i := by exact_mod_cast (hp i).one_lt
    constructor
    · exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans hpi)).mpr hpi)
    · have : 0 ≤ (1 : ℝ)/ζ.primes i := by positivity
      linarith
  refine ⟨Finset.prod_pos (fun i _ => (hi i).1),Finset.prod_le_one (fun i _ => (hi i).1.le) (fun i _ => (hi i).2),?_⟩
  have hh := one_sub_prod_le_sum Finset.univ (fun i => 1-(1 : ℝ)/ζ.primes i)
    (fun i _ => ⟨(hi i).1.le,(hi i).2⟩)
  simpa only [prefixQ,sub_sub_cancel] using hh

lemma prefix_candidate_ratio {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ =
      ((ell ζ.d : ℝ)/ζ.d)/prefixQ ζ := by
  have hp := (basic_prefix_data_positive hPH hζ).2
  have hq : prefixQ ζ=(∏ i, (ζ.primes i-1 : ℕ) : ℕ)/(∏ i, ζ.primes i : ℕ) := by
    simp only [prefixQ,Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hpi : (0 : ℝ) < ζ.primes i := by exact_mod_cast (hp i).pos
    rw [Nat.cast_sub (hp i).one_lt.le,Nat.cast_one]
    field_simp
  have hpp : (0 : ℝ) < (∏ i, ζ.primes i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (hp i).pos)
  have hsp : (0 : ℝ) < (∏ i, (ζ.primes i-1) : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (hp i).one_lt)
  have hd : (0 : ℝ) < ζ.d := by exact_mod_cast (basic_prefix_data_positive hPH hζ).1
  rw [hq,prefixCandidateFactor,prefixDenominator]
  push_cast
  field_simp

lemma prefix_ell_bound {x : ℝ} {H : ℕ} (hPH : P H < H) (hm : H ≤ m x)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) {ζ : PrefixDatum (R x H)}
    (hζ : IsPrefixDatum x H ζ) : ell ζ.d ≤ tailValueBound H := by
  obtain ⟨η,hη,hd,_⟩ := hζ
  have hw := extractTail_isWitness hη hPH hm
  have hwd : (w (extractTail x H η)).totient=ζ.d := by
    rw [extractTail_value η hPH.le hm]
    exact hd
  exact (ell_le (witness_w_pos hw) hwd).trans (witness_w_bound hs hw)

lemma prefix_candidate_ratio_bounds : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, theta x ∈ Set.Ico (0 : ℝ) 1 → H ≤ m x →
    ∀ ζ : PrefixDatum (R x H), IsPrefixDatum x H ζ →
      1 ≤ (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ ∧
      (prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ ≤ 2*tailValueBound H := by
  filter_upwards [prefix_reciprocal_sum,eventually_ge_atTop 2,
    prefixReciprocalError_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/2))]
    with H hsum hH herr
  intro x hs hm ζ hζ
  have hPH := P_lt_self hH
  have hq := prefixQ_bounds hPH.le hζ
  have hqh : (1/2 : ℝ) ≤ prefixQ ζ := by
    have hh := hq.2.2.trans (hsum x hs.1 hm ζ hζ)
    linarith
  have hd := (prefix_tail_support hPH hm hs hζ).1
  have hr := one_le_ell_ratio hd
  have hd1 : (1 : ℝ) ≤ ζ.d := by exact_mod_cast isTotient_pos hd
  have hel : (ell ζ.d : ℝ) ≤ tailValueBound H := by exact_mod_cast prefix_ell_bound hPH hm hs hζ
  have hrbound : (ell ζ.d : ℝ)/ζ.d ≤ tailValueBound H :=
    (div_le_self (Nat.cast_nonneg _) hd1).trans hel
  rw [prefix_candidate_ratio hPH.le hζ]
  constructor
  · exact (one_le_div hq.1).mpr (hq.2.1.trans hr)
  · apply (div_le_iff₀ hq.1).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (tailValueBound H)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrimeInterval
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

lemma primeInterval_card {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) :
    ((primeInterval l u).card : ℝ) =
      (Nat.primeCounting ⌊u⌋₊ : ℝ)-Nat.primeCounting ⌊min l u⌋₊ := by
  have he : (Nat.primesLE ⌊u⌋₊).filter (fun p : ℕ => ¬l < p)=Nat.primesLE ⌊min l u⌋₊ := by
    ext p
    simp only [Finset.mem_filter,Nat.mem_primesLE,not_lt,
      Nat.le_floor_iff hu,Nat.le_floor_iff (le_min hl hu),le_min_iff]
    tauto
  have hc := Finset.card_filter_add_card_filter_not (s := Nat.primesLE ⌊u⌋₊) (fun p : ℕ => l < p)
  rw [he,Nat.primesLE_card_eq_primeCounting] at hc
  have hc' := congrArg (fun n : ℕ => (n : ℝ)) hc
  simp only [Nat.cast_add,Nat.primesLE_card_eq_primeCounting] at hc'
  change ((primeInterval l u).card : ℝ)+_=_ at hc'
  linarith

/-- Counts may vanish: the positive part is encoded by min(l,u), so no
relative estimate for a short or empty prime interval is assumed. -/
lemma prime_interval_uniform (hpnt : PrimeNumberTheoremInput)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D l u : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) →
      a*x/D ≤ l → a*x/D ≤ u → u ≤ b*x/D →
      |((primeInterval l u).card : ℝ)-(u-min l u)/Real.log x| ≤
        ε*x/(D*Real.log x) := by
  filter_upwards [linear_prime_window hpnt ha hb (show 0 < ε/2 by positivity),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro D l u hD hlog hl hu huo
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hl0 : 0 ≤ l := ((div_pos (mul_pos ha hx0) hD0).trans_le hl).le
  have hu0 : 0 ≤ u := ((div_pos (mul_pos ha hx0) hD0).trans_le hu).le
  have h₁ := hx D u hD hlog hu huo
  have h₂ := hx D (min l u) hD hlog (le_min hl hu) ((min_le_right _ _).trans huo)
  rw [primeInterval_card hl0 hu0]
  calc
    _ = |((Nat.primeCounting ⌊u⌋₊ : ℝ)-u/Real.log x)-
        ((Nat.primeCounting ⌊min l u⌋₊ : ℝ)-min l u/Real.log x)| := by congr 1; ring
    _ ≤ |(Nat.primeCounting ⌊u⌋₊ : ℝ)-u/Real.log x|+
        |(Nat.primeCounting ⌊min l u⌋₊ : ℝ)-min l u/Real.log x| := abs_sub _ _
    _ ≤ _ := (add_le_add h₁ h₂).trans_eq (by ring)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedIntervalGeometry
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TotientAsymptotic

lemma intervalLength_lipschitz {l u v : ℝ} (huv : v ≤ u) (hvu : u ≤ v+1) :
    |(u-min l u)-(v-min l v)| ≤ 1 := by
  by_cases hlv : l ≤ v
  · rw [min_eq_left hlv,min_eq_left (hlv.trans huv)]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hvl := (not_le.mp hlv).le
    rw [min_eq_right hvl]
    by_cases hlu : l ≤ u
    · rw [min_eq_left hlu,abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right (not_le.mp hlu).le]
      norm_num

lemma shifted_interval_length {T U r : ℝ} (hT : 0 < T) (hU : 0 ≤ U)
    (_hr : 0 < r) (he : U=T/r) (k : ℕ) :
    |(min (T+1) ((k+1 : ℝ)*U)-min ((k : ℝ)*U) (min (T+1) ((k+1 : ℝ)*U)))-
      T*fk k r| ≤ 1 := by
  have hlc : (k : ℝ)*U ≤ (k+1 : ℝ)*U := by nlinarith
  have hm : min ((k : ℝ)*U) (min T ((k+1 : ℝ)*U)) = min T ((k : ℝ)*U) := by
    rw [← min_assoc,min_comm ((k : ℝ)*U) T,min_assoc,min_eq_left hlc]
  have hf : T*fk k r=min T ((k+1 : ℝ)*U)-min T ((k : ℝ)*U) := by
    rw [fk,mul_sub,mul_min_of_nonneg _ _ hT.le,mul_min_of_nonneg _ _ hT.le]
    rw [mul_one]
    rw [he]
    congr 2 <;> ring
  have hlow : min T ((k+1 : ℝ)*U) ≤ min (T+1) ((k+1 : ℝ)*U) :=
    min_le_min_right _ (by linarith)
  have hhigh : min (T+1) ((k+1 : ℝ)*U) ≤ min T ((k+1 : ℝ)*U)+1 := by
    by_cases hc : T ≤ (k+1 : ℝ)*U
    · rw [min_eq_left hc]
      exact min_le_left _ _
    · rw [min_eq_right (not_le.mp hc).le]
      exact (min_le_right _ _).trans (by linarith)
  rw [hf,← hm]
  exact intervalLength_lipschitz hlow hhigh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedPrimeSet
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

lemma mem_primeInterval {l u : ℝ} (hu : 0 ≤ u) (p : ℕ) :
    p ∈ primeInterval l u ↔ p.Prime ∧ l < p ∧ (p : ℝ) ≤ u := by
  simp only [primeInterval,Finset.mem_filter,Nat.mem_primesLE,Nat.le_floor_iff hu]
  tauto

lemma intervalHeads_eq_cutoff {x : ℝ} {k D A : ℕ}
    (hx : 0 ≤ x) (hD : 0 < D) (hA : 0 < A) :
    intervalHeads x k D A =
      (primeInterval ((k : ℝ)*x/A) (min (1+x/D) ((k+1 : ℝ)*x/A))).filter
        (fun p : ℕ => x^(9/10 : ℝ) ≤ p) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hu : 0 ≤ min (1+x/D) ((k+1 : ℝ)*x/A) := le_min (by positivity) (by positivity)
  ext p
  rw [intervalHeads,Finset.mem_filter,Finset.mem_filter,mem_shiftedPrimeSet hx hD,mem_primeInterval hu]
  by_cases hp : p.Prime
  · simp only [hp,true_and]
    have hv : (((p-1)*D : ℕ) : ℝ) ≤ x ↔ (p : ℝ) ≤ 1+x/D := by
      rw [Nat.cast_mul,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
      rw [← le_div_iff₀ hD0]
      constructor <;> intro h <;> linarith
    simp only [Nat.cast_mul] at hv
    simp only [hv,Nat.cast_mul,le_min_iff,div_lt_iff₀ hA0,le_div_iff₀ hA0]
    tauto
  · simp [hp]

lemma finite_prime_cutoff_error {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    |((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)-S.card| ≤ x^(9/10 : ℝ)+1 := by
  let E := S.filter (fun p : ℕ => ¬x^(9/10 : ℝ) ≤ p)
  have he : E.card ≤ ⌊x^(9/10 : ℝ)⌋₊+1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊x^(9/10 : ℝ)⌋₊+1)) ?_).trans_eq (Finset.card_range _)
    intro p hp
    have ht := lt_of_not_ge (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ht.le))
  have hs := Finset.card_filter_add_card_filter_not (s := S) (fun p : ℕ => x^(9/10 : ℝ) ≤ p)
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  rw [Nat.cast_add] at hsR
  change ((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)+(E.card : ℝ)=S.card at hsR
  rw [show ((S.filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)).card : ℝ)-S.card=-(E.card : ℝ) by linarith,
    abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
  have heR : (E.card : ℝ) ≤ (⌊x^(9/10 : ℝ)⌋₊ : ℝ)+1 := by exact_mod_cast he
  exact heR.trans (by linarith [Nat.floor_le (Real.rpow_nonneg hx (9/10 : ℝ))])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedPrimeCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma weighted_endpoint_bounds {x D A C : ℝ} {k : ℕ}
    (hx : 0 < x) (hD : 0 < D) (hDA : D ≤ A) (hC : 1 ≤ C) (hAC : A ≤ C*D)
    (hT : 1 ≤ x/D) (hk : 1 ≤ k) :
    (1/C)*x/D ≤ (k : ℝ)*x/A ∧
    (1/C)*x/D ≤ min (1+x/D) ((k+1 : ℝ)*x/A) ∧
    min (1+x/D) ((k+1 : ℝ)*x/A) ≤ 2*x/D := by
  have hA : 0 < A := hD.trans_le hDA
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hb : (1/C)*x/D ≤ x/A := by
    have hh := div_le_div_of_nonneg_left hx.le hA hAC
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1/C)*x/D ≤ x/D := by
    have hi : 1/C ≤ (1 : ℝ) := (div_le_one hC0).mpr hC
    calc
      (1/C)*x/D = (1/C)*(x/D) := by ring
      _ ≤ 1*(x/D) := mul_le_mul_of_nonneg_right hi (div_pos hx hD).le
      _ = x/D := one_mul _
  refine ⟨hb.trans ?_,le_min (hp.trans (by linarith)) (hb.trans ?_),?_⟩
  · exact div_le_div_of_nonneg_right (by nlinarith) hA.le
  · exact div_le_div_of_nonneg_right (by nlinarith) hA.le
  · apply (min_le_left _ _).trans
    rw [show 2*x/D=2*(x/D) by ring]
    linarith

/-- Ordinary PNT at two long-scale endpoints suffices, uniformly for all
allowed integers A,D. The estimate remains additive for empty intervals. -/
theorem weighted_prime_count (hpnt : PrimeNumberTheoremInput)
    {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ k D A : ℕ, 1 ≤ k → 0 < D → D ≤ A →
      (A : ℝ) ≤ C*D → Real.log (D : ℝ) ≤ (Real.log x)^(4/5 : ℝ) →
      |((intervalHeads x k D A).card : ℝ)-
        (x/(D*Real.log x))*fk k ((A : ℝ)/D)| ≤ ε*(x/(D*Real.log x)) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  filter_upwards [prime_interval_uniform hpnt (a := 1/C) (by positivity)
      (b := 2) (by norm_num) (show 0 < ε/3 by positivity),
    lower_prime_cutoff_negligible (a := 1) (by norm_num) (show 0 < ε/3 by positivity),
    small_denominator_window (a := 1) (by norm_num) (δ := 1/4) (by norm_num) le_rfl,
    eventually_gt_atTop (Real.exp 1)] with x hint hcut hwindow hx
  intro k D A hk hD hDA hAC hlogD
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hx1 : 1 < x := he1.trans hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx.le
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hDA' : (D : ℝ) ≤ A := by exact_mod_cast hDA
  have hA0 : (0 : ℝ) < A := hD0.trans_le hDA'
  let l : ℝ := (k : ℝ)*x/A
  let u : ℝ := min (1+x/D) ((k+1 : ℝ)*x/A)
  have hT : 1 ≤ x/D := (Real.one_le_rpow hx1.le (by norm_num : (0 : ℝ)≤1/2)).trans
    (hwindow D x hD1 hlogD (by simp) le_rfl).1
  have hb := weighted_endpoint_bounds hx0 hD0 hDA' hC hAC hT hk
  have hi := hint D l u hD1 hlogD hb.1 hb.2.1 hb.2.2
  have hc := (finite_prime_cutoff_error hx0.le (primeInterval l u))
  rw [← intervalHeads_eq_cutoff hx0.le hD (hD.trans_le hDA)] at hc
  have hc' := hcut D x hD1 hlogD (by simp)
  have hg := shifted_interval_length (div_pos hx0 hD0) (div_pos hx0 hA0).le
    (div_pos hA0 hD0) (show x/(A : ℝ)=(x/D)/((A : ℝ)/D) by field_simp) k
  have hg' : |(u-min l u)-(x/D)*fk k ((A : ℝ)/D)| ≤ 1 := by
    simpa only [l,u,add_comm,mul_div_assoc] using hg
  have he : |(u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)| ≤ 1/Real.log x := by
    rw [show (u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)=
      ((u-min l u)-(x/D)*fk k ((A : ℝ)/D))/Real.log x by ring,abs_div,abs_of_pos hL]
    exact div_le_div_of_nonneg_right hg' hL.le
  have hsmall : 1/Real.log x ≤ (ε/3)*(x/(D*Real.log x)) := by
    exact ((div_le_one hL).mpr hL1).trans ((by linarith [Real.rpow_nonneg hx0.le (9/10 : ℝ)] : (1 : ℝ) ≤ x^(9/10 : ℝ)+1).trans hc')
  calc
    _ ≤ |((intervalHeads x k D A).card : ℝ)-(primeInterval l u).card|+
        |((primeInterval l u).card : ℝ)-(x/(D*Real.log x))*fk k ((A : ℝ)/D)| := abs_sub_le _ _ _
    _ ≤ (ε/3)*(x/(D*Real.log x))+
        (|(primeInterval l u).card-(u-min l u)/Real.log x|+
          |(u-min l u)/Real.log x-(x/(D*Real.log x))*fk k ((A : ℝ)/D)|) :=
      add_le_add (hc.trans hc') (abs_sub_le _ _ _)
    _ ≤ (ε/3)*(x/(D*Real.log x))+
        ((ε/3)*(x/(D*Real.log x))+(ε/3)*(x/(D*Real.log x))) := by
      apply add_le_add_right
      apply add_le_add _ (he.trans hsmall)
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = ε*(x/(D*Real.log x)) := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

lemma mass_eq_prefix_denominators (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    M x H f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)/(prefixDenominator ζ : ℝ) := by
  rw [mass_eq_sum_prefixData]
  simp only [prefixDenominator,Nat.cast_mul,Nat.cast_prod]

/-- Summation of the actual least-preimage prime intervals, before replacing
its prefix ratio by the tail ratio. -/
theorem candidate_prime_mass_relative_oai (hpnt : PrimeNumberTheoremInput) :
    ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ k : ℕ, 1 ≤ k →
      |((candidateTuples x H k).card : ℝ)-(x/Real.log x)*candidateMass x H k| ≤
        ε*(x/Real.log x)*M x H (fun _ => 1) := by
  filter_upwards [prefix_candidate_ratio_bounds,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hratio hH hP
  intro ε hε
  let C : ℝ := max 1 (2*tailValueBound H)
  filter_upwards [weighted_prime_count hpnt (C := C) (le_max_left _ _) hε,
    basic_prefix_denominator_log_small (P_lt_self hH) hP,
    theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1 : ℝ)] with x hcount hlog hs hm hx
  intro k hk
  rw [candidate_count_eq_prime_fibers (P_lt_self hH).le (zero_lt_one.trans hx).le,
    candidateMass,mass_eq_prefix_denominators,Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  have hd := basic_prefix_denominator_pos (P_lt_self hH).le hz
  have hdR : (0 : ℝ) < prefixDenominator ζ := by exact_mod_cast hd
  obtain ⟨hlo,hhi⟩ := hratio x hs hm ζ hz
  have hDA : prefixDenominator ζ ≤ prefixCandidateFactor ζ := by
    exact_mod_cast (one_le_div hdR).mp hlo
  have hAC : (prefixCandidateFactor ζ : ℝ) ≤ C*prefixDenominator ζ :=
    (div_le_iff₀ hdR).mp (hhi.trans (le_max_right _ _))
  have hc := hcount k (prefixDenominator ζ) (prefixCandidateFactor ζ) hk hd hDA hAC (hlog ζ hz)
  change |((candidatePrimeSet x H k ζ).card : ℝ)-_| ≤ _
  change |((intervalHeads x k (prefixDenominator ζ) (prefixCandidateFactor ζ)).card : ℝ)-_| ≤ _
  have heq : (x/Real.log x)*(fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ)/
      (prefixDenominator ζ : ℝ))=
      (x/(prefixDenominator ζ*Real.log x))*fk k ((prefixCandidateFactor ζ : ℝ)/prefixDenominator ζ) := by ring
  rw [heq]
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.candidate_prime_mass_relative_oai := @OAI.TotientAsymptotic.candidate_prime_mass_relative_oai
