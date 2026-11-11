-- Prove2me | solution 1 for OAI.TotientAsymptotic.bounded_ratio_tuple_weight
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:32:31.136196+00:00
-- url     : https://prove2.me/submissions/2d15af1e-1a18-4daa-831c-b704ecf12102

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

lemma outside_preimageExceptions_iff {x : ℝ} {Q : ℕ → Prop} {v : ℕ}
    (hv : v ∈ Finset.Icc 1 ⌊x⌋₊) :
    v ∉ preimageExceptionValues x Q ↔
      ∀ n : ℕ, 0 < n → n.totient = v → Q n := by
  classical
  constructor
  · intro h n hn hφ
    by_contra hnQ
    exact h (Finset.mem_filter.mpr ⟨hv, n, hn, hφ, hnQ⟩)
  · intro h hmem
    obtain ⟨_, n, hn, hφ, hnQ⟩ := Finset.mem_filter.mp hmem
    exact hnQ (h n hn hφ)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Companion
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero alternative for weighted totient counts when no arithmetic seed exists. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fk_nonneg (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ fk k r := by
  unfold fk
  apply sub_nonneg.mpr
  exact min_le_min_left 1 (div_le_div_of_nonneg_right (by norm_num) hr)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Arithmetic
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Arithmetic facts for the weighted companion theorem.  The inverse-fiber
transport is the elementary consequence used after Ford's propagation
construction (The distribution of totients, 2013 revision, Section 5,
equations (5.10)--(5.19), and Section 7.3).
-/

noncomputable section
open scoped BigOperators Topology

namespace TotientAsymptotic

lemma fk_eq_one_sub {k : ℕ} {r : ℝ} (hr : 0 < r)
    (hk : (k : ℝ) ≤ r) (hk1 : r ≤ k+1) : fk k r = 1 - k/r := by
  unfold fk
  rw [min_eq_left ((le_div_iff₀ hr).mpr (by simpa using hk1)),
    min_eq_right ((div_le_one hr).mpr hk)]

lemma fk_eq_inv {k : ℕ} {r : ℝ} (hr : 0 < r) (hk1 : (k+1 : ℝ) ≤ r) :
    fk k r = 1/r := by
  have hk : (k : ℝ) ≤ r := by linarith
  unfold fk
  rw [min_eq_right ((div_le_one hr).mpr hk1),
    min_eq_right ((div_le_one hr).mpr hk)]
  rw [← sub_div]
  congr 1
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ResidualFactorCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-factor counts in actual residual totients, including a repeated
last prime in the cofactor. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma omega_count_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa only [List.length_append] using (Nat.perm_primeFactorsList_mul ha hb).length_eq

lemma omega_count_prod {ι : Type*} (I : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ I, f i ≠ 0) :
    (∏ i ∈ I, f i).primeFactorsList.length=∑ i ∈ I, (f i).primeFactorsList.length := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,omega_count_mul
      (hf i (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PreimageOmega
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

/-- Apart from the possible prime 2, every distinct prime contributes at
least one factor to the corresponding shifted-prime product. -/
lemma prime_shift_factor_count {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    1 ≤ (p-1).primeFactorsList.length := by
  by_contra! h
  have hnil : (p-1).primeFactorsList=[] := List.length_eq_zero_iff.mp (by omega)
  have he := Nat.prod_primeFactorsList (by have := hp.two_le; omega : p-1 ≠ 0)
  rw [hnil,List.prod_nil] at he
  have := hp.two_le
  omega

lemma preimage_factor_count {n : ℕ} (hn : 0 < n) :
    n.primeFactorsList.length ≤ n.totient.primeFactorsList.length+1 := by
  have hpn (p : ℕ) (hp : p ∈ n.primeFactors) : p ≠ 0 :=
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsn (p : ℕ) (hp : p ∈ n.primeFactors) : p-1 ≠ 0 := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have he := congrArg (fun t : ℕ => t.primeFactorsList.length) (Nat.totient_mul_prod_primeFactors n)
  rw [omega_count_mul (Nat.totient_pos.mpr hn).ne' (Finset.prod_ne_zero_iff.mpr hpn),
    omega_count_mul hn.ne' (Finset.prod_ne_zero_iff.mpr hsn),
    omega_count_prod _ _ hpn,omega_count_prod _ _ hsn] at he
  have hpcount : (∑ p ∈ n.primeFactors, p.primeFactorsList.length)=n.primeFactors.card := by
    calc
      _ = ∑ _p ∈ n.primeFactors, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [Nat.primeFactorsList_prime (Nat.prime_of_mem_primeFactors hp)]
      _ = _ := by simp
  rw [hpcount] at he
  have hs : n.primeFactors.card ≤ 1+∑ p ∈ n.primeFactors, (p-1).primeFactorsList.length := by
    have hcard : n.primeFactors.card ≤ (n.primeFactors.erase 2).card+1 := by
      by_cases hm : 2 ∈ n.primeFactors
      · have := Finset.card_pos.mpr ⟨2,hm⟩
        rw [Finset.card_erase_of_mem hm]
        omega
      · simp [hm]
    have hsum : (n.primeFactors.erase 2).card ≤ ∑ p ∈ n.primeFactors.erase 2, (p-1).primeFactorsList.length := by
      calc
        _ = ∑ _p ∈ n.primeFactors.erase 2, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun p hp => prime_shift_factor_count
          (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) (Finset.mem_erase.mp hp).1)
    have hsub := Finset.sum_le_sum_of_subset (Finset.erase_subset (a := 2) (s := n.primeFactors))
      (f := fun p => (p-1).primeFactorsList.length)
    omega
  omega

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorShellDecay
attribute [-instance] _root_.instMeasurableSpace
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

lemma fordCofactor_pos (n k : ℕ) : 0 < fordCofactor n k := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop hp))).pos

lemma ford_prefix_product {n k : ℕ} (hk : k ≤ n.primeFactorsList.length) :
    (n.primeFactorsList.reverse.take k).prod = ∏ i ∈ Finset.range k, fordPrime n i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.prod_take_succ _ _ (by simpa using hk),ih (by omega),Finset.prod_range_succ,
      fordPrime_eq_get (by omega)]

lemma ford_factorization {n k : ℕ} (hn : 0 < n) (hk : k ≤ n.primeFactorsList.length) :
    n=fordCofactor n k*∏ i ∈ Finset.range k, fordPrime n i := by
  rw [← ford_prefix_product hk,fordCofactor,mul_comm,List.prod_take_mul_prod_drop,
    List.prod_reverse,Nat.prod_primeFactorsList hn.ne']

lemma fordCofactor_largest {n j : ℕ} (hj : j < n.primeFactorsList.length) :
    largestPrimeFactor (fordCofactor n (j+1)) ≤ fordPrime n j := by
  let l := n.primeFactorsList.reverse.drop (j+1)
  have hp (i : Fin l.length) : (l[i.val]).Prime :=
    Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp (List.mem_of_mem_drop (List.getElem_mem _)))
  have he : fordCofactor n (j+1) = ∏ i : Fin l.length, l[i.val] :=
    (Fin.prod_univ_getElem l).symm
  rw [he]
  apply largestPrimeFactor_prod_le _ _ (fordPrime_prime hj).one_lt.le
  intro i _
  rw [largestPrimeFactor_prime (hp i)]
  have hi := i.isLt
  have hi' : j+1+i.val < n.primeFactorsList.length := by
    dsimp [l] at hi
    simp only [List.length_drop,List.length_reverse] at hi
    omega
  have hget : l[i.val]=fordPrime n (j+1+i.val) := by
    rw [fordPrime_eq_get hi']
    exact List.getElem_drop
  rw [hget]
  exact fordPrime_antitone hj hi' (by omega)

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteMap
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The finite-map counting lemma in `collisions.tex`, Lemma `finite-map`.
The collision count records ordered distinct pairs of good tuples with the
same image.  Both the exceptional values and all tuples above them are bounded.
-/

open scoped BigOperators

namespace TotientAsymptotic.FiniteMap

variable {α β : Type*} [DecidableEq β]

lemma collisionCount_eq_ordered_pairs [DecidableEq α]
    (G : Finset α) (W : Finset β) (F : α → β)
    (hmap : ∀ t ∈ G, F t ∈ W) :
    collisionCount G W F = (G.offDiag.filter (fun p => F p.1 = F p.2)).card := by
  have hdisjoint : (W : Set β).PairwiseDisjoint (fun w => (fiber G F w).offDiag) := by
    intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp).1).2
    have hq' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hq).1).2
    exact huv (hp'.symm.trans hq')
  have hunion : W.biUnion (fun w => (fiber G F w).offDiag) =
      G.offDiag.filter (fun p => F p.1 = F p.2) := by
    ext p
    constructor
    · intro hp
      obtain ⟨w, _, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨ha, hfa⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hfb⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hfa.trans hfb.symm⟩
    · intro hp
      obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      apply Finset.mem_biUnion.mpr
      refine ⟨F p.1, hmap _ ha, Finset.mem_offDiag.mpr ⟨?_, ?_, hne⟩⟩
      · exact Finset.mem_filter.mpr ⟨ha, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hb, heq.symm⟩
  rw [← hunion, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.offDiag_card, Nat.mul_sub_one]

private lemma twice_le_two_add_pairs (r : ℕ) : 2*r ≤ 2 + r*(r-1) := by
  cases r with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ n => simp only [Nat.add_sub_cancel] <;> nlinarith

private lemma two_le_pairs {r : ℕ} (hr : 2 ≤ r) : 2 ≤ r*(r-1) := by
  have hsub : 1 ≤ r-1 := by omega
  nlinarith

lemma good_preimage_bound (G : Finset α) (W B : Finset β) (F : α → β)
    (hB : B ⊆ W) :
    2 * (G.filter (fun t => F t ∈ B)).card ≤ 2*B.card + collisionCount G W F := by
  have hsum : ∑ w ∈ B, (fiber G F w).card * ((fiber G F w).card - 1) ≤
      collisionCount G W F :=
    Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => Nat.zero_le _)
  calc
    2 * (G.filter (fun t => F t ∈ B)).card = ∑ w ∈ B, 2*(fiber G F w).card := by
      rw [← Finset.sum_card_fiberwise_eq_card_filter G B F, Finset.mul_sum]
      rfl
    _ ≤ ∑ w ∈ B, (2 + (fiber G F w).card * ((fiber G F w).card - 1)) :=
      Finset.sum_le_sum (fun _ _ => twice_le_two_add_pairs _)
    _ = 2*B.card + ∑ w ∈ B, (fiber G F w).card * ((fiber G F w).card - 1) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ 2*B.card + collisionCount G W F := Nat.add_le_add_left hsum _

lemma multiple_values_bound (G : Finset α) (W : Finset β) (F : α → β) :
    2*(multipleValues G W F).card ≤ collisionCount G W F := by
  calc
    2*(multipleValues G W F).card = ∑ _w ∈ multipleValues G W F, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ multipleValues G W F,
        (fiber G F w).card * ((fiber G F w).card - 1) := by
      apply Finset.sum_le_sum
      intro w hw
      exact two_le_pairs (Finset.mem_filter.mp hw).2
    _ ≤ collisionCount G W F :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

lemma bad_values_subset (G D : Finset α) (W E : Finset β) (F : α → β)
    (hE : E ⊆ W) (hD : ∀ t ∈ D, F t ∈ W) : badValues G D W E F ⊆ W := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_union.mp hw with hw | hw
    · exact hE hw
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      exact hD t ht
  · exact (Finset.mem_filter.mp hw).1

lemma bad_values_bound (G D : Finset α) (W E : Finset β) (F : α → β) :
    2*(badValues G D W E F).card ≤
      2*E.card + 2*D.card + collisionCount G W F := by
  have h₁ := Finset.card_union_le (E ∪ D.image F) (multipleValues G W F)
  have h₂ := Finset.card_union_le E (D.image F)
  have h₃ := Finset.card_image_le (s := D) (f := F)
  have h₄ := multiple_values_bound G W F
  change 2*((E ∪ D.image F) ∪ multipleValues G W F).card ≤ _
  omega

/-- The manuscript's finite-map lemma, with all half-collision bounds expressed
over the reals and the bijection expressed as `Set.BijOn`. -/
theorem counting [DecidableEq α] (T G D : Finset α) (W E : Finset β) (F : α → β)
    (hpartition : T = G ∪ D) (hdisjoint : Disjoint G D)
    (hmap : ∀ t ∈ T, F t ∈ W) (hE : E ⊆ W)
    (hcoverage : W \ E ⊆ T.image F) :
    (-(E.card : ℝ) ≤ (T.card : ℝ) - W.card) ∧
    ((T.card : ℝ) - W.card ≤ D.card + (collisionCount G W F : ℝ)/2) ∧
    ((badValues G D W E F).card : ℝ) ≤
      E.card + D.card + (collisionCount G W F : ℝ)/2 ∧
    ((badPreimages T G D W E F).card : ℝ) ≤
      E.card + 2*D.card + collisionCount G W F ∧
    Set.BijOn F (↑(T \ badPreimages T G D W E F))
      (↑(W \ badValues G D W E F)) := by
  have hGT : G ⊆ T := by rw [hpartition]; exact Finset.subset_union_left
  have hDT : D ⊆ T := by rw [hpartition]; exact Finset.subset_union_right
  have hGmap : ∀ t ∈ G, F t ∈ W := fun t ht => hmap t (hGT ht)
  have hDmap : ∀ t ∈ D, F t ∈ W := fun t ht => hmap t (hDT ht)
  have hbadsub := bad_values_subset G D W E F hE hDmap
  have hcardT : T.card = G.card + D.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hgood : 2*G.card ≤ 2*W.card + collisionCount G W F := by
    have h := good_preimage_bound G W W F (fun _ hw => hw)
    have hfilter : G.filter (fun t => F t ∈ W) = G :=
      Finset.filter_eq_self.mpr hGmap
    rwa [hfilter] at h
  have hlower : W.card ≤ T.card + E.card := by
    have h₁ := Finset.card_le_card hcoverage
    have h₂ := Finset.card_image_le (s := T) (f := F)
    have h₃ := Finset.card_sdiff_add_card_eq_card hE
    omega
  have hbad := bad_values_bound G D W E F
  have hpre : (badPreimages T G D W E F).card ≤
      E.card + 2*D.card + collisionCount G W F := by
    have hgpre := good_preimage_bound G W (badValues G D W E F) F hbadsub
    have hsplit : badPreimages T G D W E F =
        G.filter (fun t => F t ∈ badValues G D W E F) ∪
          D.filter (fun t => F t ∈ badValues G D W E F) := by
      simp only [badPreimages, hpartition, Finset.filter_union]
    have h₁ := Finset.card_union_le
      (G.filter (fun t => F t ∈ badValues G D W E F))
      (D.filter (fun t => F t ∈ badValues G D W E F))
    have h₂ := Finset.card_filter_le D (fun t => F t ∈ badValues G D W E F)
    rw [hsplit]
    omega
  have hbij : Set.BijOn F (↑(T \ badPreimages T G D W E F))
      (↑(W \ badValues G D W E F)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨ht, hnot⟩ := Finset.mem_sdiff.mp ht
      exact Finset.mem_sdiff.mpr ⟨hmap t ht, fun h =>
        hnot (Finset.mem_filter.mpr ⟨ht, h⟩)⟩
    · intro a ha b hb hab
      obtain ⟨ha, haout⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hb, hbout⟩ := Finset.mem_sdiff.mp hb
      have haout' : F a ∉ badValues G D W E F := fun h =>
        haout (Finset.mem_filter.mpr ⟨ha, h⟩)
      have hbout' : F b ∉ badValues G D W E F := fun h =>
        hbout (Finset.mem_filter.mpr ⟨hb, h⟩)
      have hag : a ∈ G := by
        rw [hpartition] at ha
        rcases Finset.mem_union.mp ha with h | h
        · exact h
        · exact False.elim (haout' (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, h, rfl⟩))))
      have hbg : b ∈ G := by
        rw [hpartition] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact h
        · exact False.elim (hbout' (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, h, rfl⟩))))
      have hr : (fiber G F (F a)).card ≤ 1 := by
        by_contra h
        have hm : F a ∈ multipleValues G W F :=
          Finset.mem_filter.mpr ⟨hmap a (hGT hag), by omega⟩
        exact haout' (Finset.mem_union_right _ hm)
      exact Finset.card_le_one.mp hr a (Finset.mem_filter.mpr ⟨hag, rfl⟩)
        b (Finset.mem_filter.mpr ⟨hbg, hab.symm⟩)
    · intro w hw
      obtain ⟨hw, hwout⟩ := Finset.mem_sdiff.mp hw
      have hwe : w ∉ E := fun h => hwout
        (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      obtain ⟨t, ht, htw⟩ := Finset.mem_image.mp
        (hcoverage (Finset.mem_sdiff.mpr ⟨hw, hwe⟩))
      refine ⟨t, Finset.mem_sdiff.mpr ⟨ht, ?_⟩, htw⟩
      intro h
      exact hwout (htw ▸ (Finset.mem_filter.mp h).2)
  refine ⟨?_, ?_, ?_, ?_, hbij⟩
  · have h : (W.card : ℝ) ≤ T.card + E.card := by exact_mod_cast hlower
    linarith
  · have h : 2*(G.card : ℝ) ≤ 2*W.card + collisionCount G W F := by
      exact_mod_cast hgood
    have hT : (T.card : ℝ) = G.card + D.card := by exact_mod_cast hcardT
    linarith
  · have h : 2*((badValues G D W E F).card : ℝ) ≤
        2*E.card + 2*D.card + collisionCount G W F := by exact_mod_cast hbad
    linarith
  · exact_mod_cast hpre

end TotientAsymptotic.FiniteMap

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleTotients
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual arithmetic realization of tuples and the finite-map comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma basic_head_coprime (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ p : ℕ, p.Prime → x^(9/10 : ℝ) ≤ p →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      p.Coprime (suffixPreimage η 0) := by
  filter_upwards [basic_remainder_subpower H (show (0 : ℝ)<1/10 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro p hp hpl η hη
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hle := Nat.le_of_dvd (suffixPreimage_pos hη (i := 0)) hd
  have hsmall := (hx η hη).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num : (1/10 : ℝ)<9/10))
  exact (not_lt_of_ge (show (p : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hle))
    (hsmall.trans_le hpl)

lemma wholePreimage_totient {x : ℝ} {H p : ℕ}
    {η : RemainderDatum (L x H)} (hp : p.Prime) (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H)
    (hcop : p.Coprime (suffixPreimage η 0)) :
    (wholePreimage p η).totient = tupleValue (witnessTuple p η) := by
  rw [wholePreimage, Nat.totient_mul hcop, Nat.totient_prime hp,
    witness_tuple_value_at_cut hη hL hR (Nat.zero_lt_of_lt hR)]
  simp only [Finset.Icc_self, Finset.prod_singleton, wholeWitnessPrime, ite_true, if_true]
  ring

lemma basic_tuple_isTotient : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t : ℝ, ∀ τ : TotientTuple (R x H), IsBasicTuple x H t τ → IsTotient (tupleValue τ) := by
  filter_upwards [eventually_tail_cut_separated] with H hH
  obtain ⟨hPH,hP⟩ := hH
  filter_upwards [basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro t τ hτ
  obtain ⟨η,hη,he⟩ := (isPrefixDatum_iff x H τ.tail).mp hτ.2.2.1
  have hw : witnessTuple τ.head η=τ := by
    cases τ
    simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  refine ⟨wholePreimage τ.head η,Nat.mul_pos hτ.1.pos (suffixPreimage_pos hη),?_⟩
  rw [wholePreimage_totient hτ.1 hη hL hR (hx τ.head hτ.1 hτ.2.1 η hη),hw]

lemma basic_tuple_mem_values {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) (hval : IsTotient (tupleValue τ)) :
    tupleValue τ ∈ totientValues t := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨basic_tuple_value_pos hPH hτ,Nat.le_floor hτ.2.2.2⟩,hval⟩

lemma good_collision_count_eq {x t : ℝ} {H : ℕ}
    (hmap : ∀ τ ∈ goodTupleFinset x H t, tupleValue τ ∈ totientValues t) :
    FiniteMap.collisionCount (goodTupleFinset x H t) (totientValues t) tupleValue =
      (goodCollisionPairs x H t).card := by
  classical
  rw [FiniteMap.collisionCount_eq_ordered_pairs _ _ _ hmap]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_offDiag,goodCollisionPairs,Finset.mem_product]
  tauto

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StructuredRemainder
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact passage from Ford's canonical preimage coordinates to basic witnesses. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma fordRemainder_prime {x : ℝ} {H n i : ℕ} (hi : i ∈ Finset.Icc 1 (L x H)) :
    remainderPrime (fordRemainder x H n) i=fordPrime n i := by
  rw [remainderPrime,dite_eq_left (Finset.mem_Icc.mp hi)]
  change fordPrime n (i-1+1)=fordPrime n i
  congr 1
  have := (Finset.mem_Icc.mp hi).1
  omega

lemma fordRemainder_coord {x : ℝ} {H n i : ℕ} (hi : i ≤ L x H) :
    remainderCoord x (fordRemainder x H n) i=rawSimplexCoordinate x n i := by
  by_cases h0 : i=0
  · simp [remainderCoord,rawSimplexCoordinate,h0]
  · simp only [remainderCoord,rawSimplexCoordinate,ite_eq_right h0,primeDoubleLog]
    rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨by omega,hi⟩)]

lemma fordRemainder_basic {x : ℝ} {H n : ℕ} (hL : 0 < L x H)
    (hstruct : extractedStructureCondition x (P H) n)
    (hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H))) :
    IsBasicRemainder x H (fordRemainder x H n) := by
  have hlast : 0 < primeDoubleLog n (L x H) := lt_trans (by norm_num) hstruct.2.1
  have hindex := fordPrime_index_of_doubleLog_pos hlast
  refine ⟨fordCofactor_pos _ _,?_,?_,?_,hsize⟩
  · intro i hi
    rw [fordRemainder_prime hi,fordRemainder_coord (Finset.mem_Icc.mp hi).2]
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
    rw [rawSimplexCoordinate,ite_eq_right hi0]
    exact ⟨fordPrime_prime (by have := (Finset.mem_Icc.mp hi).2; omega),hstruct.1 i hi⟩
  · intro i hi
    have hiL := (Finset.mem_Icc.mp hi).2
    rw [fordRemainder_coord hiL]
    by_cases he : i=L x H
    · subst i
      rw [ite_eq_left rfl]
      have hempty : Finset.Icc (L x H+1) (L x H)=∅ := by simp
      rw [hempty,Finset.sum_empty,one_mul]
      simpa only [rawSimplexCoordinate,ite_eq_right (Nat.ne_of_gt hL)] using hlast.le
    · rw [ite_eq_right he]
      convert hstruct.2.2 i (Finset.mem_Ico.mpr ⟨Nat.zero_le _,by unfold L at *; omega⟩) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro r hr
      rw [fordRemainder_coord (Finset.mem_Icc.mp hr).2]
  · rw [fordRemainder_prime (Finset.mem_Icc.mpr ⟨hL,le_rfl⟩)]
    exact fordCofactor_largest hindex

lemma fordRemainder_factorization {x : ℝ} {H n : ℕ} (hn : 0 < n)
    (hindex : L x H < n.primeFactorsList.length) :
    wholePreimage (fordPrime n 0) (fordRemainder x H n)=n := by
  have he := ford_factorization hn (show L x H+1 ≤ n.primeFactorsList.length by omega)
  have hI : Finset.range (L x H+1)=insert 0 (Finset.Icc 1 (L x H)) := by
    ext i
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hI,Finset.prod_insert (by simp)] at he
  rw [wholePreimage,suffixPreimage]
  have hp : (∏ i ∈ Finset.Icc (0+1) (L x H), remainderPrime (fordRemainder x H n) i)=
      ∏ i ∈ Finset.Icc 1 (L x H), fordPrime n i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact fordRemainder_prime hi
  rw [hp]
  change fordPrime n 0 * (fordCofactor n (L x H+1) * _) = n
  calc
    _ = fordCofactor n (L x H+1)*(fordPrime n 0*∏ i ∈ Finset.Icc 1 (L x H),fordPrime n i) := by ring
    _ = n := he.symm

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordHead
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

lemma first_band_small : ∀ᶠ x : ℝ in atTop,
    (11/10 : ℝ)*bandScale x 1 ≤ (7/10 : ℝ)*B x := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0),
    bandCenterRatio_tendsto.eventually (eventually_gt_nhds (by norm_num : (9/10 : ℝ)<1))]
    with x hB hm hr
  have he := fordBandScale_eq_ratio_mul (i := 0) hB hm
  have he0 : fordBandScale x 0=B x := by simp [fordBandScale]
  rw [he0] at he
  have hb0 : bandScale x 0 ≤ (10/9 : ℝ)*B x := by nlinarith [bandScale_nonnegative x 0]
  have hb := bandScale_succ_le x 0
  have hρ := collision_rho_bounds.2
  have hp := bandScale_nonnegative x 0
  have hh : bandScale x 1 ≤ (137/250 : ℝ)*((10/9 : ℝ)*B x) :=
    hb.trans (mul_le_mul hρ.le hb0 hp (by norm_num))
  nlinarith

lemma ford_rest_le_power {n : ℕ} (hlen : 1 < n.primeFactorsList.length) :
    fordCofactor n 1 ≤ (fordPrime n 1)^n.primeFactorsList.length := by
  let l := n.primeFactorsList.reverse.drop 1
  have hh : l.prod ≤ (fordPrime n 1)^l.length := by
    apply List.prod_le_pow_card
    intro q hq
    obtain ⟨j,hj,he⟩ := List.mem_drop_iff_getElem.mp hq
    have hj' : 1+j < n.primeFactorsList.length := by simpa only [List.length_reverse,Nat.add_comm] using hj
    rw [← he,← fordPrime_eq_get hj']
    exact fordPrime_antitone hlen hj' (by omega)
  exact hh.trans (Nat.pow_le_pow_right (fordPrime_prime hlen).pos (by
    dsimp [l]
    simp))

lemma ford_log_factorization {n : ℕ} (hn : 0 < n) (hlen : 1 < n.primeFactorsList.length) :
    Real.log n ≤ Real.log (fordPrime n 0)+
      n.primeFactorsList.length*Real.log (fordPrime n 1) := by
  have hp0 := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  have htail := fordCofactor_pos n 1
  have he : n=fordPrime n 0*fordCofactor n 1 := by
    simpa only [Finset.range_one,Finset.prod_singleton,mul_comm] using
      ford_factorization hn (show 1≤n.primeFactorsList.length by omega)
  have hlog := Real.log_le_log (show (0 : ℝ)<fordCofactor n 1 by exact_mod_cast htail)
    (show (fordCofactor n 1 : ℝ) ≤ (fordPrime n 1 : ℝ)^n.primeFactorsList.length by exact_mod_cast ford_rest_le_power hlen)
  rw [Real.log_pow] at hlog
  have heR : Real.log n=Real.log (fordPrime n 0)+Real.log (fordCofactor n 1) := by
    conv_lhs => rw [he]
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp0.ne_zero) (by exact_mod_cast htail.ne')]
  linarith

lemma head_remainder_log_error : ∀ᶠ b : ℝ in atTop,
    21*b*Real.exp ((7/10 : ℝ)*b) ≤ (1/20 : ℝ)*Real.exp b := by
  have ht : Tendsto (fun b : ℝ => 21*b*Real.exp (-(3/10 : ℝ)*b)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_assoc,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (3/10) (by norm_num : (0 : ℝ)<3/10)).const_mul 21
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/20))] with b hb
  have hh := mul_le_mul_of_nonneg_right hb.le (Real.exp_pos b).le
  rw [mul_assoc,← Real.exp_add] at hh
  simpa only [show -(3/10 : ℝ)*b+b=(7/10 : ℝ)*b by ring] using hh

/-- All preimages outside the small-value and high-Omega sets have a head
prime in the required range. The constants leave room for the coarse bands. -/
theorem extracted_head_large : ∀ᶠ x : ℝ in atTop, ∀ H n : ℕ,
    0 < L x H → 0 < n → extractedStructureCondition x (P H) n →
    x^(19/20 : ℝ) ≤ n.totient → (n.totient.primeFactorsList.length : ℝ) ≤ 20*B x →
    x^(9/10 : ℝ) ≤ fordPrime n 0 := by
  filter_upwards [first_band_small,B_tendsto.eventually head_remainder_log_error,
    B_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),eventually_gt_atTop (1 : ℝ)]
    with x hb he hB hx
  intro H n hL hn hs hval hΩ
  have hlast := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hlen : 1<n.primeFactorsList.length := lt_of_le_of_lt hL hlast
  have hprime := fordPrime_prime hlen
  have hp0 := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  have hpn : (0 : ℝ)<fordPrime n 1 := by exact_mod_cast hprime.pos
  have hlogpn : 0 < Real.log (fordPrime n 1 : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hb1 : primeDoubleLog n 1 ≤ (7/10 : ℝ)*B x :=
    ((hs.1 1 (Finset.mem_Icc.mpr ⟨le_rfl,hL⟩)).2).trans hb
  have hp1 : Real.log (fordPrime n 1 : ℝ) ≤ Real.exp ((7/10 : ℝ)*B x) :=
    (Real.log_le_iff_le_exp hlogpn).mp hb1
  have hΩn : (n.primeFactorsList.length : ℝ) ≤ 21*B x := by
    have hh : (n.primeFactorsList.length : ℝ) ≤ n.totient.primeFactorsList.length+1 :=
      by exact_mod_cast preimage_factor_count hn
    linarith
  have hbound := ford_log_factorization hn hlen
  have hrest := mul_le_mul hΩn hp1 hlogpn.le (by positivity : (0 : ℝ) ≤ 21*B x)
  have hexp : Real.exp (B x)=Real.log x := Real.exp_log (Real.log_pos hx)
  rw [hexp] at he
  have hvn : x^(19/20 : ℝ) ≤ (n : ℝ) := hval.trans (by exact_mod_cast Nat.totient_le n)
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hvlog := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _) hvn
  rw [Real.log_rpow (zero_lt_one.trans hx)] at hvlog
  have hh : (9/10 : ℝ)*Real.log x ≤ Real.log (fordPrime n 0) := by linarith
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]
  apply (Real.le_log_iff_exp_le (by exact_mod_cast hp0.pos)).mp
  simpa only [mul_comm] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CanonicalCoverage
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

/-- The exact coverage statement once the three explicit exceptional
conditions (structure, largest prime, cofactor) have been excluded. -/
lemma canonical_tuple_coverage {x t : ℝ} {H n : ℕ} (hPH : P H < H) (hP : 1 ≤ P H)
    (hm : H ≤ m x) (hn : 0<n)
    (hstruct : extractedStructureCondition x (P H) n)
    (hhead : x^(9/10 : ℝ) ≤ fordPrime n 0)
    (hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)))
    (hval : (n.totient : ℝ) ≤ t)
    (hcop : (fordPrime n 0).Coprime (suffixPreimage (fordRemainder x H n) 0)) :
    n.totient ∈ (tupleFinset x H t).image tupleValue := by
  have hL : 0<L x H := by unfold L; omega
  have hLm : L x H< m x := by unfold L; omega
  have hRL : R x H<L x H := by unfold R L; omega
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hstruct.2.1)
  have hp := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  let η := fordRemainder x H n
  let p := fordPrime n 0
  have hη : IsBasicRemainder x H η := fordRemainder_basic hL hstruct hsize
  have he : tupleValue (witnessTuple p η)=n.totient := by
    rw [← wholePreimage_totient hp hη hLm hRL hcop,fordRemainder_factorization hn hindex]
  have ht : IsBasicTuple x H t (witnessTuple p η) :=
    ⟨hp,hhead,(isPrefixDatum_iff x H _).mpr ⟨η,hη,rfl⟩,he.symm ▸ hval⟩
  exact Finset.mem_image.mpr ⟨witnessTuple p η,(mem_tupleFinset hPH.le).mpr ht,he⟩

/-- The coprimality premise is automatically available uniformly for actual
basic remainders once the head lower bound and cofactor cutoff hold. -/
theorem canonical_tuple_coverage_eventually {H : ℕ} (hPH : P H < H) (hP : 1≤P H) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ, 0<n →
      extractedStructureCondition x (P H) n → x^(9/10 : ℝ) ≤ fordPrime n 0 →
      Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) →
      (n.totient : ℝ) ≤ t → n.totient ∈ (tupleFinset x H t).image tupleValue := by
  filter_upwards [basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)] with x hc hm
  intro t n hn hs hp ha hv
  have hL : 0<L x H := by unfold L; omega
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hprime := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  exact canonical_tuple_coverage hPH hP hm hn hs hp ha hv
    (hc _ hprime hp _ (fordRemainder_basic hL hs ha))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BasicCoverage
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

lemma uncovered_values_subset {H : ℕ} (hPH : P H<H) (hP : 1≤P H) :
    ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      uncoveredValues x H t ⊆
        (preimageExceptionValues x (extractedStructureCondition x (P H)) ∪ smallValues x) ∪
          (largeOmegaValues x ∪ cofactorExceptionValues x H) := by
  filter_upwards [canonical_tuple_coverage_eventually hPH hP,extracted_head_large,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hcover hhead hm
  intro t ht v hv
  obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hvt,hvφ⟩ := Finset.mem_filter.mp hv
  have hvpos := (Finset.mem_Icc.mp hvt).1
  have ht0 : 0≤t := by
    by_contra h
    have hz := Nat.floor_of_nonpos (lt_of_not_ge h).le
    have hh := (Finset.mem_Icc.mp hvt).2
    rw [hz] at hh
    omega
  have hvtR : (v : ℝ)≤t := (Nat.le_floor_iff ht0).mp (Finset.mem_Icc.mp hvt).2
  have hvx : v ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr
    ⟨hvpos,(Finset.mem_Icc.mp hvt).2.trans (Nat.floor_mono ht)⟩
  by_cases he : v ∈ preimageExceptionValues x (extractedStructureCondition x (P H))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  by_cases hsmall : v ∈ smallValues x
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hsmall)
  by_cases hω : v ∈ largeOmegaValues x
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hω)
  have hn := ell_spec hvφ
  have hs := (outside_preimageExceptions_iff hvx).mp he (ell v) hn.1 hn.2
  have hlow : x^(19/20 : ℝ) ≤ (v : ℝ) := by
    apply le_of_not_gt
    intro h
    exact hsmall (Finset.mem_Icc.mpr ⟨hvpos,Nat.le_floor h.le⟩)
  have hΩ : (v.primeFactorsList.length : ℝ) ≤ 20*B x := by
    apply le_of_not_gt
    intro h
    exact hω (Finset.mem_filter.mpr ⟨hvx,h⟩)
  have hL : 0<L x H := by unfold L; omega
  have hp := hhead H (ell v) hL hn.1 hs (hn.2.symm ▸ hlow) (hn.2.symm ▸ hΩ)
  by_cases ha : Real.exp (2*bandScale x (L x H))<Real.log (fordCofactor (ell v) (L x H+1))
  · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hvx,hvφ⟩,ell v,hn.1,hn.2,hs,hp,ha⟩))
  · exfalso
    apply hout
    rw [← hn.2]
    exact hcover t (ell v) hn.1 hs hp (le_of_not_gt ha)
      (hn.2.symm ▸ hvtR)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AllPreimageCoverage
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform arithmetic extraction for every preimage outside explicit exceptional values. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

lemma all_preimages_basic {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ v ∈ totientValues x, v ∉ basicExceptionValues x H →
    ∀ n : ℕ, 0 < n → n.totient = v →
      IsBasicTuple x H x (witnessTuple (fordPrime n 0) (fordRemainder x H n)) ∧
      wholePreimage (fordPrime n 0) (fordRemainder x H n) = n := by
  filter_upwards [basic_head_coprime H,extracted_head_large,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_ge_atTop (0 : ℝ)] with x hcop hhead hm hx0
  intro v hv hout n hn hnv
  have houts : v ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) ∧
      v ∉ smallValues x ∧ v ∉ largeOmegaValues x ∧ v ∉ cofactorExceptionValues x H := by
    simpa only [basicExceptionValues,Finset.mem_union,not_or,and_assoc] using hout
  obtain ⟨hvr,hvφ⟩ := Finset.mem_filter.mp hv
  have hs := (outside_preimageExceptions_iff hvr).mp houts.1 n hn hnv
  have hvpos := (Finset.mem_Icc.mp hvr).1
  have hlow : x^(19/20 : ℝ) ≤ (v : ℝ) := by
    apply le_of_not_gt
    intro h
    exact houts.2.1 (Finset.mem_Icc.mpr ⟨hvpos,Nat.le_floor h.le⟩)
  have hΩ : (v.primeFactorsList.length : ℝ) ≤ 20*B x := by
    apply le_of_not_gt
    intro h
    exact houts.2.2.1 (Finset.mem_filter.mpr ⟨hvr,h⟩)
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H < m x := by unfold L; omega
  have hRL : R x H < L x H := by unfold R L; omega
  have hp := hhead H n hL hn hs (hnv.symm ▸ hlow) (hnv.symm ▸ hΩ)
  have hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
    apply le_of_not_gt
    intro h
    exact houts.2.2.2 (Finset.mem_filter.mpr ⟨hv,n,hn,hnv,hs,hp,h⟩)
  have hη := fordRemainder_basic hL hs hsize
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hprime := fordPrime_prime (show 0 < n.primeFactorsList.length by omega)
  have hfact := fordRemainder_factorization hn hindex
  refine ⟨⟨hprime,hp,(isPrefixDatum_iff x H _).mpr ⟨_,hη,rfl⟩,?_⟩,hfact⟩
  rw [← wholePreimage_totient hprime hη hLm hRL (hcop _ hprime hp _ hη),hfact,hnv]
  exact (Nat.le_floor_iff hx0).mp (Finset.mem_Icc.mp hvr).2

/-- Every preimage of an ordinary value induces a tuple with that exact value. -/
lemma all_preimages_tuple_value {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ v ∈ totientValues x, v ∉ basicExceptionValues x H →
    ∀ n : ℕ, 0 < n → n.totient = v →
      witnessTuple (fordPrime n 0) (fordRemainder x H n) ∈ tupleFinset x H x ∧
      tupleValue (witnessTuple (fordPrime n 0) (fordRemainder x H n)) = v := by
  filter_upwards [all_preimages_basic hPH hP,basic_head_coprime H,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hb hc hm
  intro v hv he n hn hnv
  obtain ⟨ht,hfact⟩ := hb v hv he n hn hnv
  have hη : IsBasicRemainder x H (fordRemainder x H n) := by
    have hout : v ∉ cofactorExceptionValues x H := by
      intro h
      exact he (Finset.mem_union_right _ (Finset.mem_union_right _ h))
    have hvr := (Finset.mem_filter.mp hv).1
    have hstout : v ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) := by
      intro h
      exact he (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hs := (outside_preimageExceptions_iff hvr).mp hstout n hn hnv
    have hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
      apply le_of_not_gt
      intro h
      exact hout (Finset.mem_filter.mpr ⟨hv,n,hn,hnv,hs,ht.2.1,h⟩)
    exact fordRemainder_basic (by unfold L; omega) hs hsize
  refine ⟨(mem_tupleFinset hPH.le).mpr ht,?_⟩
  rw [← wholePreimage_totient (p := fordPrime n 0) ht.1 hη (by unfold L; omega)
    (by unfold R L; omega) (hc _ ht.1 ht.2.1 _ hη),hfact,hnv]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBelowPrefix
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

lemma tail_log_comparison : ∀ᶠ b : ℝ in atTop,
    4*b*Real.exp ((7/10 : ℝ)*b) < Real.exp ((9/10 : ℝ)*b) := by
  have ht : Tendsto (fun b : ℝ => 4*(b*Real.exp (-(1/5 : ℝ)*b))) atTop (nhds 0) := by
    simpa only [Real.rpow_one,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/5) (by norm_num : (0 : ℝ)<1/5)).const_mul 4
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with b hb
  have h := mul_lt_mul_of_pos_right hb (Real.exp_pos ((9/10 : ℝ)*b))
  rw [mul_assoc,mul_assoc,← Real.exp_add] at h
  rw [show -(1/5 : ℝ)*b+9/10*b=(7/10 : ℝ)*b by ring,one_mul] at h
  simpa only [mul_assoc] using h

/-- The exact arithmetic tail lies below every retained prefix prime. This is
uniform in the phase; the cofactor cut grows much slower than the prefix cut. -/
theorem basic_tail_lt_last_prefix : ∀ᶠ H : ℕ in atTop,
    ∀ x : ℝ, theta x ∈ Set.Ico (0 : ℝ) 1 → H < m x →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      remainderTail x H η < remainderPrime η (R x H) := by
  obtain ⟨b₀,hb₀⟩ := eventually_atTop.mp tail_log_comparison
  filter_upwards [eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1),
    cofactor_envelope_le_self (2*(lam/rho)),
    (tendsto_natCast_atTop_atTop.const_mul_atTop lam_pos).eventually (eventually_ge_atTop b₀)]
    with H hH hP hcof hlarge
  intro x hs hm η hη
  have hPH := P_lt_self hH
  have hR : 0 < R x H := by unfold R; omega
  have hRL : R x H < L x H := by unfold R L; omega
  have hRmem : R x H ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr ⟨hR,hRL.le⟩
  have hRH : m x-R x H=H := by unfold R; omega
  have hLP : m x-L x H=P H := by unfold L; omega
  let b := bandScale x (R x H)
  have hb0 : 0 ≤ b := bandScale_nonnegative _ _
  have hα : lam ≤ alpha (theta x) := by
    unfold alpha
    exact le_mul_of_one_le_right lam_pos.le (Real.one_le_exp (mul_nonneg lam_pos.le hs.1))
  have hpow : (1 : ℝ) ≤ (rho^H)⁻¹ := one_le_inv₀ (pow_pos rho_pos H) |>.mpr
    (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hbH : lam*H ≤ b := by
    change _ ≤ alpha (theta x)*(m x-R x H : ℕ)*(rho^(m x-R x H))⁻¹
    rw [hRH]
    exact (mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg H)).trans
      (le_mul_of_one_le_right (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _)) hpow)
  have hHb : (H : ℝ) ≤ 2*b := by
    have hl := collision_lambda_bounds.1
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hsuc : (11/10 : ℝ)*bandScale x (R x H+1) ≤ (7/10 : ℝ)*b := by
    have hh := bandScale_succ_le x (R x H)
    have hr := collision_rho_bounds.2
    change bandScale x (R x H+1) ≤ rho*b at hh
    nlinarith
  have hlast : Real.exp (2*bandScale x (L x H)) ≤ H := by
    apply (Real.exp_le_exp.mpr ?_).trans hcof
    rw [bandScale,hLP]
    unfold cofactorScale
    have hi := (inv_pos.mpr (pow_pos rho_pos (P H))).le
    have ha := alpha_le _ hs
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg (P H))) hi]
  have hlen : L x H-R x H ≤ H := by unfold L R; omega
  have hlenR : (L x H-R x H : ℕ) ≤ (H : ℝ) := by exact_mod_cast hlen
  have he : (1 : ℝ) ≤ Real.exp ((7/10 : ℝ)*b) := Real.one_le_exp (by positivity)
  have hlog := basic_suffix_log_bound (j := R x H) hη
  have hu : Real.log (remainderTail x H η : ℝ) < Real.exp ((9/10 : ℝ)*b) := by
    change Real.log (suffixPreimage η (R x H) : ℝ) < _
    calc
      _ ≤ (H : ℝ)*Real.exp ((7/10 : ℝ)*b)+H := hlog.trans
        (add_le_add (mul_le_mul hlenR (Real.exp_le_exp.mpr hsuc) (Real.exp_pos _).le (Nat.cast_nonneg _)) hlast)
      _ ≤ 4*b*Real.exp ((7/10 : ℝ)*b) := by nlinarith
      _ < _ := hb₀ b (hlarge.trans hbH)
  have hp := hη.2.1 _ hRmem
  have hpR : (1 : ℝ) < remainderPrime η (R x H) := by exact_mod_cast hp.1.one_lt
  have hlower : Real.exp ((9/10 : ℝ)*b) ≤ Real.log (remainderPrime η (R x H) : ℝ) := by
    apply (Real.le_log_iff_exp_le (Real.log_pos hpR)).mp
    simpa only [remainderCoord,ite_eq_right (ne_of_gt hR)] using hp.2.1
  have hpos : (0 : ℝ) < remainderTail x H η := by
    exact_mod_cast suffixPreimage_pos (i := R x H) hη
  exact_mod_cast (Real.log_lt_log_iff hpos (zero_lt_one.trans hpR)).mp (hu.trans_le hlower)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixPreimage
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact prime-prefix factorization and minimization over a common inverse fiber. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma wholePreimage_prefix_split {x : ℝ} {H : ℕ} (p : ℕ)
    (η : RemainderDatum (L x H)) (hRL : R x H ≤ L x H) :
    wholePreimage p η = tuplePrimeProduct (witnessTuple p η)*remainderTail x H η := by
  unfold tuplePrimeProduct tuplePrimes witnessTuple
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,prefixOfRemainder]
  rw [prod_fin_shifted]
  unfold wholePreimage suffixPreimage remainderTail
  rw [prod_Icc_split_at (Nat.zero_le (R x H)) hRL]
  simp only [Nat.zero_add]
  ring

lemma tuplePrimeProduct_pos {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : 0 < tuplePrimeProduct τ := by
  exact Finset.prod_pos (fun i _ => (basic_tuple_primes hPH hτ i).pos)

/-- If every inverse image has a fixed multiplicative prefix, minimizing the
remaining inverse image minimizes the whole fiber. -/
lemma ell_of_common_prefix {v d b : ℕ} (hv : IsTotient v) (hd : IsTotient d)
    (hb : 0 < b) (hreal : (b*ell d).totient=v)
    (hcommon : ∀ n : ℕ, 0 < n → n.totient=v →
      ∃ w : ℕ, 0 < w ∧ w.totient=d ∧ n=b*w) :
    ell v=b*ell d := by
  apply le_antisymm (ell_le (Nat.mul_pos hb (ell_spec hd).1) hreal)
  obtain ⟨w,hw,hwd,he⟩ := hcommon (ell v) (ell_spec hv).1 (ell_spec hv).2
  rw [he]
  exact Nat.mul_le_mul_left b (ell_le hw hwd)

lemma coprime_of_prime_gt {p w : ℕ} (hp : p.Prime) (hw : 0 < w) (hwp : w < p) :
    p.Coprime w := by
  apply hp.coprime_iff_not_dvd.mpr
  intro h
  exact (not_le_of_gt hwp) (Nat.le_of_dvd hw h)

/-- Replacing the tail of a represented value by its least preimage preserves
that value once the tail is smaller than every prefix prime. -/
lemma tuple_candidate_realizes {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ)
    {w : ℕ} (hw : 0 < w) (hwd : w.totient=τ.tail.d)
    (hsmall : ∀ i, w < tuplePrimes τ i)
    (hreal : (tuplePrimeProduct τ*w).totient=tupleValue τ) :
    (tupleLeastCandidate τ).totient=tupleValue τ := by
  have hd : IsTotient τ.tail.d := ⟨w,hw,hwd⟩
  have he := ell_le hw hwd
  have hc : (tuplePrimeProduct τ).Coprime w := Nat.coprime_prod_left_iff.mpr
    (fun i _ => coprime_of_prime_gt (basic_tuple_primes hPH hτ i) hw (hsmall i))
  have hce : (tuplePrimeProduct τ).Coprime (ell τ.tail.d) := Nat.coprime_prod_left_iff.mpr
    (fun i _ => coprime_of_prime_gt (basic_tuple_primes hPH hτ i) (ell_spec hd).1
      (he.trans_lt (hsmall i)))
  unfold tupleLeastCandidate
  rw [Nat.totient_mul hce,(ell_spec hd).2]
  rwa [Nat.totient_mul hc,hwd] at hreal

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleCandidate
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

lemma remainderTail_dvd_suffix {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H))
    (hRL : R x H ≤ L x H) : remainderTail x H η ∣ suffixPreimage η 0 := by
  have he : suffixPreimage η 0 = remainderTail x H η *
      ∏ i ∈ Finset.Icc 1 (R x H), remainderPrime η i := by
    unfold suffixPreimage remainderTail
    rw [prod_Icc_split_at (Nat.zero_le (R x H)) hRL]
    simp only [Nat.zero_add]
    ring
  rw [he]
  exact dvd_mul_right _ _

lemma basic_tail_lt_all_tuple_primes : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ p : ℕ, p.Prime → x^(9/10 : ℝ) ≤ p →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
    ∀ i, remainderTail x H η < tuplePrimes (witnessTuple p η) i := by
  filter_upwards [basic_tail_lt_last_prefix,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hlast hH hP
  filter_upwards [theta_eventually_mem,m_tendsto.eventually (eventually_gt_atTop H),
    basic_remainder_subpower H (show (0 : ℝ)<1/10 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hs hm hsub hx1
  intro p hp hpl η hη i
  have hPH := P_lt_self hH
  have hRL : R x H < L x H := by unfold R L; omega
  have hLm : L x H < m x := by unfold L; omega
  have hRpos : 0 < R x H := by unfold R; omega
  refine Fin.cases ?_ (fun j => ?_) i
  · change remainderTail x H η < p
    have hwle : remainderTail x H η ≤ suffixPreimage η 0 :=
      Nat.le_of_dvd (suffixPreimage_pos hη) (remainderTail_dvd_suffix η hRL.le)
    have hsmall := (show (remainderTail x H η : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hwle).trans (hsub η hη)
    exact_mod_cast hsmall.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hx1
      (show (1/10 : ℝ)<9/10 by norm_num)).trans_le hpl)
  · change remainderTail x H η < remainderPrime η (j.val+1)
    have hj : j.val+1 ≤ R x H := by have := j.isLt; omega
    have hl := hlast x hs hm η hη
    rcases lt_or_eq_of_le hj with hj | hj
    · exact hl.trans (basic_remainder_prime_strictAnti hη
        (Finset.mem_Icc.mpr ⟨by omega,hj.le.trans hRL.le⟩)
        (Finset.mem_Icc.mpr ⟨hRpos,hRL.le⟩) hj (hj.trans hRL |>.trans hLm))
    · simpa only [hj] using hl

/-- Every basic tuple has the candidate obtained by replacing its arithmetic
tail by the least inverse image of the same tail totient. -/
theorem basic_tuple_candidate_realizes : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t : ℝ, ∀ τ : TotientTuple (R x H), IsBasicTuple x H t τ →
      (tupleLeastCandidate τ).totient=tupleValue τ := by
  filter_upwards [basic_tail_lt_all_tuple_primes,eventually_tail_cut_separated]
    with H hsmall hH
  obtain ⟨hP,hcuts⟩ := hH
  have hPH : P H < H := by omega
  filter_upwards [hsmall,basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hsmall hc hm
  intro t τ hτ
  obtain ⟨η,hη,he⟩ := (isPrefixDatum_iff x H τ.tail).mp hτ.2.2.1
  have hτe : witnessTuple τ.head η=τ := by
    cases τ
    simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
  have hRL : R x H < L x H := by unfold R L; omega
  apply tuple_candidate_realizes (w := remainderTail x H η) hPH.le hτ (suffixPreimage_pos (i := R x H) hη)
  · exact congrArg PrefixDatum.d he
  · intro i
    rw [← hτe]
    exact hsmall _ hτ.1 hτ.2.1 η hη i
  · rw [← hτe,← wholePreimage_prefix_split _ _ hRL.le]
    exact wholePreimage_totient hτ.1 hη (by unfold L; omega) hRL
      (hc _ hτ.1 hτ.2.1 η hη)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UniquePrefix
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

lemma unique_prefix_finite_comparison : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ((nonuniqueValues x H).card : ℝ) ≤ (basicExceptionValues x H).card+
      (badTupleFinset x H x).card+((goodCollisionPairs x H x).card : ℝ)/2 ∧
    ((discardedTuples x H).card : ℝ) ≤ (basicExceptionValues x H).card+
      2*(badTupleFinset x H x).card+(goodCollisionPairs x H x).card ∧
    Set.BijOn (fun τ : TotientTuple (R x H) => tupleValue τ) (↑(tupleFinset x H x \ discardedTuples x H))
      (↑(totientValues x \ nonuniqueValues x H)) := by
  filter_upwards [basic_tuple_isTotient,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hreal hH hP
  filter_upwards [hreal,uncovered_values_subset (P_lt_self hH) hP] with x hx hcover
  have hPH := (P_lt_self hH).le
  have hmap : ∀ τ ∈ tupleFinset x H x, tupleValue τ ∈ totientValues x := by
    intro τ hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    exact basic_tuple_mem_values hPH hb (hx x τ hb)
  have hg : goodTupleFinset x H x ⊆ tupleFinset x H x := Finset.filter_subset _ _
  have hpart : tupleFinset x H x=goodTupleFinset x H x ∪ badTupleFinset x H x :=
    (Finset.union_sdiff_of_subset hg).symm
  have hdis : Disjoint (goodTupleFinset x H x) (badTupleFinset x H x) :=
    Finset.disjoint_left.mpr (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₂).2 h₁)
  have hcov : totientValues x \ exceptionalTotients x H ⊆ (tupleFinset x H x).image tupleValue := by
    intro v hv
    obtain ⟨hv,he⟩ := Finset.mem_sdiff.mp hv
    by_contra hn
    have hexc := hcover x le_rfl (Finset.mem_sdiff.mpr ⟨hv,hn⟩)
    exact he (Finset.mem_inter.mpr ⟨hv,hexc⟩)
  have hc := FiniteMap.counting (tupleFinset x H x) (goodTupleFinset x H x)
    (badTupleFinset x H x) (totientValues x) (exceptionalTotients x H) tupleValue
    hpart hdis hmap Finset.inter_subset_left hcov
  rw [good_collision_count_eq (fun τ hτ => hmap τ (hg hτ))] at hc
  have he : ((exceptionalTotients x H).card : ℝ) ≤ (basicExceptionValues x H).card := by
    exact_mod_cast Finset.card_le_card (show exceptionalTotients x H ⊆ basicExceptionValues x H from Finset.inter_subset_right)
  exact ⟨hc.2.2.1.trans (by linarith),hc.2.2.2.1.trans (by linarith),hc.2.2.2.2⟩

/-- All inverse images of an ordinary value have the same displayed prime
prefix. This uses all-preimage extraction, not merely existence of a witness. -/
lemma common_prefix_inverse_fiber {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop,
    ∀ τ ∈ tupleFinset x H x \ discardedTuples x H,
    (Set.InjOn (fun σ : TotientTuple (R x H) => tupleValue σ) (↑(tupleFinset x H x \ discardedTuples x H))) →
    tupleValue τ ∈ totientValues x \ nonuniqueValues x H →
    ∀ n : ℕ, 0 < n → n.totient=tupleValue τ →
      ∃ w : ℕ, 0 < w ∧ w.totient=τ.tail.d ∧ n=tuplePrimeProduct τ*w := by
  filter_upwards [all_preimages_tuple_value hPH hP,all_preimages_basic hPH hP,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hval hbasic hm
  intro τ hτ hinj hv n hn hnv
  have hE : tupleValue τ ∉ basicExceptionValues x H := by
    intro he
    apply (Finset.mem_sdiff.mp hv).2
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1,he⟩
  have hσ := hval _ (Finset.mem_sdiff.mp hv).1 hE n hn hnv
  have hσout : witnessTuple (fordPrime n 0) (fordRemainder x H n) ∈
      tupleFinset x H x \ discardedTuples x H := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hσ.1,?_⟩
    intro h
    have hb := (Finset.mem_filter.mp h).2
    rw [hσ.2] at hb
    exact (Finset.mem_sdiff.mp hv).2 hb
  have heq := hinj hσout hτ hσ.2
  obtain ⟨hbt,hfact⟩ := hbasic _ (Finset.mem_sdiff.mp hv).1 hE n hn hnv
  have hη : IsBasicRemainder x H (fordRemainder x H n) := by
    have hsout : tupleValue τ ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) := by
      intro h
      exact hE (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hs := (outside_preimageExceptions_iff (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1).mp hsout n hn hnv
    have ha : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
      apply le_of_not_gt
      intro h
      exact hE (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,n,hn,hnv,hs,hbt.2.1,h⟩)))
    exact fordRemainder_basic (by unfold L; omega) hs ha
  refine ⟨remainderTail x H (fordRemainder x H n),suffixPreimage_pos (i := R x H) hη,?_,?_⟩
  · have hh := congrArg (fun σ : TotientTuple (R x H) => σ.tail.d) heq
    exact hh
  · calc
      n = wholePreimage (fordPrime n 0) (fordRemainder x H n) := hfact.symm
      _ = _ := by rw [wholePreimage_prefix_split _ _ (by unfold R L; omega),heq]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_LeastPrefix
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

/-- The exact least-preimage identity on the bijective part of the actual
representation map. Every preimage, including the least one, has this prefix. -/
theorem unique_tuple_least_preimage : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ τ ∈ tupleFinset x H x \ discardedTuples x H,
      ell (tupleValue τ)=tupleLeastCandidate τ := by
  filter_upwards [unique_prefix_finite_comparison,basic_tuple_candidate_realizes,
    eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hbij hc hH hP
  have hPH := P_lt_self hH
  filter_upwards [hbij,hc,common_prefix_inverse_fiber hPH hP,
    theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H)]
    with x hbij hc hcommon hs hm
  intro τ hτ
  have hb := (mem_tupleFinset hPH.le).mp (Finset.mem_sdiff.mp hτ).1
  have hv := hbij.2.2.1 hτ
  have hvφ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have hd := (prefix_tail_support hPH hm hs hb.2.2.1).1
  exact ell_of_common_prefix hvφ hd (tuplePrimeProduct_pos hPH.le hb) (hc x τ hb)
    (hcommon τ hτ hbij.2.2.2.1 hv)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedFiber
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

lemma tupleLeastCandidate_eq_head {r p : ℕ} (ζ : PrefixDatum r) :
    tupleLeastCandidate (TotientTuple.mk p ζ)=p*prefixCandidateFactor ζ := by
  simp only [tupleLeastCandidate,tuplePrimeProduct,tuplePrimes,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,prefixCandidateFactor]
  ring

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullPrefixRatio
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

lemma tuple_least_ratio_identity {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    {τ : TotientTuple (R x H)} (hτ : IsBasicTuple x H x τ)
    (hell : ell (tupleValue τ)=tupleLeastCandidate τ) :
    ((ell (tupleValue τ) : ℝ)/tupleValue τ)*tupleQ τ=(ell τ.tail.d : ℝ)/τ.tail.d := by
  have hp := hτ.1
  have hp1 : (1 : ℝ)<τ.head := by exact_mod_cast hp.one_lt
  have hD : (0 : ℝ)<prefixDenominator τ.tail := by
    exact_mod_cast basic_prefix_denominator_pos hPH hτ.2.2.1
  have hq := prefixQ_bounds hPH hτ.2.2.1
  have hr := prefix_candidate_ratio hPH hτ.2.2.1
  calc
    _ = ((prefixCandidateFactor τ.tail : ℝ)/prefixDenominator τ.tail)*prefixQ τ.tail := by
      rw [hell]
      change ((tupleLeastCandidate (TotientTuple.mk τ.head τ.tail) : ℝ)/
        tupleValue (TotientTuple.mk τ.head τ.tail))*tupleQ τ=_
      rw [tupleLeastCandidate_eq_head,tupleValue_eq_head]
      change ((τ.head*prefixCandidateFactor τ.tail : ℕ) : ℝ)/
        (((τ.head-1)*prefixDenominator τ.tail : ℕ) : ℝ)*
          (prefixQ τ.tail*(1-(1 : ℝ)/τ.head))=_
      simp only [Nat.cast_mul,Nat.cast_sub hp.one_lt.le,Nat.cast_one]
      field_simp [hD.ne',sub_ne_zero.mpr hp1.ne', (zero_lt_one.trans hp1).ne']
    _ = _ := (eq_div_iff hq.1.ne').mp hr

/-- The product including the largest prime tends uniformly to one. -/
lemma full_prefix_defect {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ τ : TotientTuple (R x H), IsBasicTuple x H x τ →
        0<tupleQ τ ∧ 1-ε ≤ tupleQ τ ∧ tupleQ τ ≤ 1 := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<9/10))
  filter_upwards [prefix_reciprocal_sum,eventually_ge_atTop 2,
    prefixReciprocalError_tendsto.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity))]
    with H hsum hH herr
  filter_upwards [theta_eventually_mem,m_tendsto.eventually (eventually_ge_atTop H),
    hi.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity)),
    eventually_gt_atTop (0 : ℝ)] with x hs hm hx hx0
  simp only [Function.comp_def,← one_div] at hx
  intro τ hτ
  have hq := prefixQ_bounds (P_lt_self hH).le hτ.2.2.1
  have hsum := hsum x hs.1 hm τ.tail hτ.2.2.1
  have hp1 : (1 : ℝ)<τ.head := by exact_mod_cast hτ.1.one_lt
  have hp0 : (0 : ℝ)<τ.head := zero_lt_one.trans hp1
  have hpε : (1 : ℝ)/τ.head < ε/2 :=
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx0 _) hτ.2.1).trans_lt hx
  have hh : 0<1-(1 : ℝ)/τ.head := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
  have hhle : 1-(1 : ℝ)/τ.head ≤ 1 := by
    linarith [div_nonneg zero_le_one hp0.le]
  refine ⟨mul_pos hq.1 hh,?_,?_⟩
  · dsimp [tupleQ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq.2.1) (div_nonneg zero_le_one hp0.le)]
  · exact (mul_le_mul_of_nonneg_left hhle hq.1.le).trans (by simpa using hq.2.1)

lemma fk_lower_on_interval {k : ℕ} {a b r : ℝ}
    (hka : (k : ℝ)<a) (ha : a ≤ r) (hrb : r≤b) :
    min 1 (a-k)/b ≤ fk k r := by
  have hr : 0 < r := ((Nat.cast_nonneg k).trans_lt hka).trans_le ha
  have hb : 0<b := hr.trans_le hrb
  have hδ : 0 ≤ min 1 (a-k) := le_min zero_le_one (sub_pos.mpr hka).le
  by_cases hk1 : r≤k+1
  · rw [fk_eq_one_sub hr (hka.le.trans ha) hk1]
    have hh : min 1 (a-k) ≤ r-k := (min_le_right _ _).trans (by linarith)
    calc
      min 1 (a-k)/b ≤ min 1 (a-k)/r := div_le_div_of_nonneg_left hδ hr hrb
      _ ≤ (r-k)/r := div_le_div_of_nonneg_right hh hr.le
      _ = 1-k/r := by field_simp
  · rw [fk_eq_inv hr (le_of_not_ge hk1)]
    exact (div_le_div_of_nonneg_right (min_le_left _ _) hb.le).trans
      (one_div_le_one_div_of_le hr hrb)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedFiniteMap
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace TotientAsymptotic.FiniteMap

/-- A positive weight on all ordinary representatives converts a count of
values into a lower bound for the weighted representation count. -/
lemma weighted_lower {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T D : Finset α) (W E U : Finset β) (F : α → β) (w : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hU : U⊆W) (hbij : Set.BijOn F (↑(T\D)) (↑(W\E)))
    (hw : ∀ t∈T, 0≤w t)
    (hweight : ∀ t∈T\D, F t∈U → c≤w t) :
    c*((U.card : ℝ)-E.card) ≤ ∑ t∈T, w t := by
  let S := (T\D).filter (fun t => F t∈U)
  have hcard : S.card=(U\E).card := by
    apply Finset.card_bij (fun t _ => F t)
    · intro t ht
      obtain ⟨ht,hU⟩ := Finset.mem_filter.mp ht
      exact Finset.mem_sdiff.mpr ⟨hU,(Finset.mem_sdiff.mp (hbij.1 ht)).2⟩
    · intro t ht s hs he
      exact hbij.2.1 (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hs).1 he
    · intro v hv
      obtain ⟨t,ht,he⟩ := hbij.2.2 (Finset.mem_sdiff.mpr ⟨hU (Finset.mem_sdiff.mp hv).1,(Finset.mem_sdiff.mp hv).2⟩)
      refine ⟨t,Finset.mem_filter.mpr ⟨ht,?_⟩,he⟩
      exact he ▸ (Finset.mem_sdiff.mp hv).1
  have hs : S⊆T := fun _ ht => (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1
  have hce : (U.card : ℝ)-E.card≤(S.card : ℝ) := by
    have he := Finset.card_sdiff_add_card_inter U E
    have hle := Finset.card_le_card (show U∩E⊆E from Finset.inter_subset_right)
    have her : ((U\E).card : ℝ)+(U∩E).card=U.card := by exact_mod_cast he
    have hler : ((U∩E).card : ℝ)≤E.card := by exact_mod_cast hle
    rw [hcard]
    linarith
  calc
    c*((U.card : ℝ)-E.card) ≤ c*(S.card : ℝ) := mul_le_mul_of_nonneg_left hce hc
    _ = ∑ t∈S, c := by simp [mul_comm]
    _ ≤ ∑ t∈S, w t := Finset.sum_le_sum (fun t ht => hweight t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)
    _ ≤ ∑ t∈T, w t := Finset.sum_le_sum_of_subset_of_nonneg hs (fun t ht _ => hw t ht)

end TotientAsymptotic.FiniteMap

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PositiveTupleWeight
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

lemma bounded_ratio_tuple_weight_oai (k : ℕ) {a b : ℝ} (hka : (k : ℝ)<a) (hb : 0<b) :
    ∃ β : ℝ, 0<β ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      β*(((boundedRatioValues x a b).card : ℝ)-(nonuniqueValues x H).card) ≤
        weightedTupleCount x H x (fk k) := by
  have ha : 0<a := (Nat.cast_nonneg k).trans_lt hka
  let ε : ℝ := (a-k)/(2*a)
  have hε : 0<ε := div_pos (sub_pos.mpr hka) (by positivity)
  let β : ℝ := min 1 ((a+k)/2-k)/b
  have hβ : 0<β := div_pos (lt_min zero_lt_one (by linarith)) hb
  refine ⟨β,hβ,?_⟩
  filter_upwards [full_prefix_defect hε,unique_prefix_finite_comparison,
    unique_tuple_least_preimage,eventually_ge_atTop 2] with H hQ hbij hleast hH
  filter_upwards [hQ,hbij,hleast] with x hQ hbij hleast
  apply FiniteMap.weighted_lower (tupleFinset x H x) (discardedTuples x H)
    (totientValues x) (nonuniqueValues x H) (boundedRatioValues x a b) tupleValue
    (fun τ => fk k ((ell τ.tail.d : ℝ)/τ.tail.d)) β hβ.le
    (Finset.filter_subset _ _) hbij.2.2
  · intro τ _
    exact fk_nonneg k (by positivity)
  · intro τ hτ hv
    have hbasic := (mem_tupleFinset (P_lt_self hH).le).mp (Finset.mem_sdiff.mp hτ).1
    obtain ⟨hq0,hql,hqu⟩ := hQ τ hbasic
    have hid := tuple_least_ratio_identity (P_lt_self hH).le hbasic (hleast τ hτ)
    obtain ⟨_,hva,hvb⟩ := Finset.mem_filter.mp hv
    have hv0 : 0≤(ell (tupleValue τ) : ℝ)/tupleValue τ := by positivity
    have hl : (a+k)/2 ≤ (ell τ.tail.d : ℝ)/τ.tail.d := by
      have hm := mul_le_mul_of_nonneg_right hva hq0.le
      have hm' := mul_le_mul_of_nonneg_left hql ha.le
      have heq : a*(1-ε)=(a+k)/2 := by dsimp [ε]; field_simp <;> ring
      rw [←heq]
      exact hm'.trans (hm.trans_eq hid)
    have hu : (ell τ.tail.d : ℝ)/τ.tail.d≤b := by
      rw [←hid]
      exact (mul_le_of_le_one_right hv0 hqu).trans hvb
    exact fk_lower_on_interval (by linarith : (k : ℝ)<(a+k)/2) hl hu

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.bounded_ratio_tuple_weight_oai := @OAI.TotientAsymptotic.bounded_ratio_tuple_weight_oai
