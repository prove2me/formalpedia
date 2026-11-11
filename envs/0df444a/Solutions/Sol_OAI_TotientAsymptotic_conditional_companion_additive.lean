-- Prove2me | solution 1 for OAI.TotientAsymptotic.conditional_companion_additive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:35:56.279231+00:00
-- url     : https://prove2.me/submissions/9dba6a3c-ddd4-42d6-bf23-1bbb25b2417a

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
import Theorems.Thm_OAI_TotientAsymptotic_actual_block_count
import Theorems.Thm_OAI_TotientAsymptotic_actual_positive_collision_count
import Theorems.Thm_OAI_TotientAsymptotic_bad_tuple_discard
import Theorems.Thm_OAI_TotientAsymptotic_basic_exception_values_negligible
import Theorems.Thm_OAI_TotientAsymptotic_candidate_count_comparison
import Theorems.Thm_OAI_TotientAsymptotic_candidate_mass_normalized
import Theorems.Thm_OAI_TotientAsymptotic_mass_volume_coefficient_approximation

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

lemma psi_continuousOn {b : ℝ} (hb : 1 < b) : ContinuousOn psi (Set.Ici b) := by
  intro y hy
  have hy1 : 1 < y := hb.trans_le hy
  have hy0 : 0 < y := zero_lt_one.trans hy1
  have hlog : 0 < Real.log y := Real.log_pos hy1
  exact (((Real.continuousAt_log hy0.ne').sub
    ((Real.continuousAt_log hlog.ne').comp (Real.continuousAt_log hy0.ne'))).div_const
      lam).continuousWithinAt

lemma B_exp_exp (b : ℝ) : B (Real.exp (Real.exp b)) = b := by
  simp only [B, Real.log_exp]

lemma theta_of_phase {x s : ℝ} {n : ℕ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (hx : psi (B x) = n+s) : m x = n ∧ theta x = s := by
  have hh : m x = n := by
    unfold m
    rw [hx, Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg n) hs.1)]
    constructor <;> linarith [hs.1, hs.2]
  exact ⟨hh, by simp only [theta, hx, hh] <;> ring⟩

theorem exact_phase_cofinal {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (X : ℝ) :
    ∃ x : ℝ, X ≤ x ∧ theta x = s := by
  let b₀ : ℝ := max 2 X
  have hb₀ : 1 < b₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨n, hn⟩ := exists_nat_gt (psi b₀-s)
  have hnmem : (n : ℝ)+s ∈ Set.Ici (psi b₀) := by
    change psi b₀ ≤ (n : ℝ)+s
    linarith
  obtain ⟨b, hb, hphase⟩ :=
    intermediate_value_Ici (psi_continuousOn hb₀) psi_tendsto hnmem
  refine ⟨Real.exp (Real.exp b), ?_, ?_⟩
  · have h₁ := Real.add_one_le_exp b
    have h₂ := Real.add_one_le_exp (Real.exp b)
    have hxb : X ≤ b := (le_max_right 2 X).trans hb
    linarith
  · apply (theta_of_phase hs (n := n) _).2
    simpa only [B_exp_exp] using hphase



lemma theta_eventually_mem : ∀ᶠ x : ℝ in atTop, theta x ∈ Set.Ico (0 : ℝ) 1 := by
  have hp : Tendsto (fun x => psi (B x)) atTop atTop :=
    psi_tendsto.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hp.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le hx)
  · have h := Nat.lt_floor_add_one (psi (B x))
    change psi (B x) - (⌊psi (B x)⌋₊ : ℕ) < 1
    linarith

theorem coefficient_convergence_from_phase_comparison (f C : ℝ → ℝ)
    (hcomp : ∀ ε : ℝ, 0 < ε → ∃ H₀ : ℕ, ∀ H ≥ H₀,
      ∀ᶠ x : ℝ in atTop, |C x - AH H f (theta x)| ≤ ε) :
    TendstoUniformlyOn (fun H => AH H f) (A f) atTop (Set.Ico (0 : ℝ) 1) ∧
    Tendsto (fun x : ℝ => C x - A f (theta x)) atTop (nhds 0) := by
  have hcauchy : UniformCauchySeqOn (fun H => AH H f) atTop (Set.Ico (0 : ℝ) 1) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨H₀, hH₀⟩ := hcomp (ε/3) (by positivity)
    refine ⟨H₀, ?_⟩
    intro H hH K hK s hs
    obtain ⟨XH, hXH⟩ := eventually_atTop.mp (hH₀ H hH)
    obtain ⟨XK, hXK⟩ := eventually_atTop.mp (hH₀ K hK)
    obtain ⟨x, hx, hphase⟩ := exact_phase_cofinal hs (max XH XK)
    have hh := hXH x ((le_max_left XH XK).trans hx)
    have hk := hXK x ((le_max_right XH XK).trans hx)
    rw [hphase] at hh hk
    rw [Real.dist_eq]
    calc |AH H f s - AH K f s| ≤ |AH H f s - C x| + |C x - AH K f s| :=
      abs_sub_le _ _ _
      _ ≤ ε/3 + ε/3 := add_le_add (by simpa only [abs_sub_comm] using hh) hk
      _ < ε := by linarith
  have hunif : TendstoUniformlyOn (fun H => AH H f) (A f) atTop (Set.Ico (0 : ℝ) 1) := by
    apply hcauchy.tendstoUniformlyOn_of_tendsto
    intro s hs
    exact (hcauchy.cauchySeq hs).tendsto_limUnder
  refine ⟨hunif, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨H₀, hH₀⟩ := hcomp (ε/3) (by positivity)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hunif (ε/3) (by positivity))
  let H := max H₀ J
  filter_upwards [hH₀ H (le_max_left _ _), theta_eventually_mem] with x hx hθ
  have hu := hJ H (le_max_right _ _) (theta x) hθ
  rw [Real.dist_eq] at hu ⊢
  rw [sub_zero]
  calc |C x - A f (theta x)| ≤
      |C x - AH H f (theta x)| + |AH H f (theta x) - A f (theta x)| := abs_sub_le _ _ _
    _ < ε/3 + ε/3 := add_lt_add_of_le_of_lt hx (by simpa only [abs_sub_comm] using hu)
    _ < ε := by linarith

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

lemma fk_le_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : fk k r ≤ 1 := by
  have hfirst : min 1 ((k+1 : ℝ) / r) ≤ 1 := min_le_left _ _
  have hsecond : 0 ≤ min 1 ((k : ℝ) / r) :=
    le_min zero_le_one (div_nonneg (Nat.cast_nonneg k) hr)
  unfold fk
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

/-- Simultaneous witnesses impose coordinatewise maximum tail thresholds. -/
lemma prefixRegion_intersection {ι : Type*} (N : ℕ) (B : ℝ)
    (T : Finset ι) (hT : T.Nonempty) (C₀ : ι → ℝ) (C : ι → Fin N → ℝ) :
    {u | ∀ η ∈ T, u ∈ prefixRegion N B (C₀ η) (C η)} =
      prefixRegion N B (T.sup' hT C₀) (fun i => T.sup' hT (fun η => C η i)) := by
  ext u
  change (∀ η ∈ T, (∀ i, C η i ≤ prefixLinear N u i) ∧
    (∑ i : Fin N, a (i.val+1)*u i) ≤ B-C₀ η) ↔ _
  constructor
  · intro hu
    refine ⟨fun i => (Finset.sup'_le_iff hT (fun η => C η i)).mpr (fun η hη => (hu η hη).1 i), ?_⟩
    have h : T.sup' hT C₀ ≤ B - ∑ i : Fin N, a (i.val+1)*u i :=
      (Finset.sup'_le_iff hT C₀).mpr (fun η hη => by have := (hu η hη).2; linarith)
    linarith
  · rintro ⟨hlo, hs⟩ η hη
    refine ⟨fun i => (Finset.le_sup' (fun η => C η i) hη).trans (hlo i), ?_⟩
    have := Finset.le_sup' C₀ hη
    linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBounds
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
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

lemma tailLog_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {l : ℕ} (hl : l ∈ Finset.Ico (P H) H) :
    0 ≤ tailLog η l := by
  have hr := rho_pos
  exact (by have := alpha_pos s; positivity :
    (0 : ℝ) ≤ (9/10 : ℝ) * alpha s * l * (rho^l)⁻¹).trans (hη.2.2.1 l hl).2.1

lemma D_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) : 0 ≤ D h η := by
  unfold D
  apply Finset.sum_nonneg
  intro l hl
  have hlH := (Finset.mem_Ico.mp hl).2
  exact mul_nonneg (a_pos (by omega)).le (tailLog_nonneg hη hl)

lemma tailMass_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) : 0 ≤ tailMass η :=
  Finset.sum_nonneg (fun _ hl => tailLog_nonneg hη hl)

lemma D_le_log {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) :
    D h η ≤ Real.log (h+1 : ℝ) * tailMass η := by
  unfold D tailMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hlH := (Finset.mem_Ico.mp hl).2
  have hj : 1 ≤ h-l := by omega
  apply mul_le_mul_of_nonneg_right _ (tailLog_nonneg hη hl)
  apply (a_le_log hj).trans
  apply Real.log_le_log (by positivity)
  have hsub : h-l ≤ h := Nat.sub_le _ _
  exact_mod_cast Nat.add_le_add_right hsub 1

lemma D_le_linear {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {h : ℕ} (hh : H ≤ h) : D h η ≤ h * tailMass η := by
  apply (D_le_log hη hh).trans
  apply mul_le_mul_of_nonneg_right _ (tailMass_nonneg hη)
  have hlog := Real.log_le_sub_one_of_pos (x := (h+1 : ℝ)) (by positivity)
  linarith

lemma maxD_nonneg {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) {h : ℕ} (hh : H ≤ h) : 0 ≤ maxD h T := by
  classical
  unfold maxD
  split_ifs with ht
  · obtain ⟨η, hη⟩ := ht
    exact (D_nonneg (hT η hη) hh).trans (Finset.le_sup' (s := T) (D h) hη)
  · exact le_rfl

lemma maxD_le_linear {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) {h : ℕ} (hh : H ≤ h) :
    maxD h T ≤ (h : ℝ) * ∑ η ∈ T, tailMass η := by
  classical
  unfold maxD
  split_ifs with ht
  · apply Finset.sup'_le
    intro η hη
    apply (D_le_linear (hT η hη) hh).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.single_le_sum (fun ξ hξ => tailMass_nonneg (hT ξ hξ)) hη
  · have hz : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [hz]

theorem summable_tail_threshold {H : ℕ} {s : ℝ} {T : Finset (TailDatum H)}
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Summable (fun n : ℕ => rho^(H+n) * maxD (H+n) T) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * rho^n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖rho‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hshift : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ) * rho^(H+n)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff H).2 hs
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg rho_pos.le _)
      (maxD_nonneg hT (by omega)))
    (fun n => ?_)
    (hshift.mul_right (∑ η ∈ T, tailMass η))
  have hb := mul_le_mul_of_nonneg_left
    (maxD_le_linear hT (h := H+n) (by omega)) (pow_nonneg rho_pos.le (H+n))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb


open MeasureTheory ProbabilityTheory
open scoped Classical

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

lemma renewalConvolution_eq_tsum (c : ℕ → ℝ) (n : ℕ) :
    renewalConvolution c n = ∑' i : ℕ,
      if i ≤ n then normalizedRenewal (n-i)*c i else 0 := by
  symm
  rw [tsum_eq_sum (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (by have := Finset.mem_range.mp hi; omega)]
  · intro i hi
    rw [ite_eq_right (by have := mt Finset.mem_range.mpr hi; omega)]

/-- Summable arithmetic tail weights can be passed through the normalized
renewal convolution without requiring any continuity in the phase. -/
theorem renewalConvolution_tendsto (hford : FordRenewalInput)
    (c : ℕ → ℝ) (hc : Summable c) :
    Tendsto (renewalConvolution c) atTop (nhds (gamma * ∑' i, c i)) := by
  obtain ⟨hlim, K, hK, hbound⟩ := normalizedRenewal_properties hford
  let F : ℕ → ℕ → ℝ := fun n i =>
    if i ≤ n then normalizedRenewal (n-i)*c i else 0
  have hpoint (i : ℕ) : Tendsto (fun n => F n i) atTop (nhds (gamma*c i)) := by
    apply ((hlim.comp (tendsto_sub_atTop_nat i)).mul_const (c i)).congr'
    filter_upwards [eventually_ge_atTop i] with n hn
    simp [F, hn]
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ i, ‖F n i‖ ≤ K*‖c i‖ := by
    apply Eventually.of_forall
    intro n i
    dsimp [F]
    split_ifs with hi
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using hbound (n-i)) (abs_nonneg _)
    · simpa using mul_nonneg hK (norm_nonneg (c i))
  have ht := tendsto_tsum_of_dominated_convergence (hc.norm.mul_left K) hpoint hdom
  simp only [tsum_mul_left] at ht
  exact ht.congr' (Eventually.of_forall (fun n => (renewalConvolution_eq_tsum c n).symm))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PowerApproximation
attribute [-instance] _root_.W21.instNorm _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform exponential approximation for the shrinking tail of a simplex. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma log_one_sub_quadratic {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    |Real.log (1-q)+q| ≤ q^2 := by
  have hq1 : q < 1 := by linarith
  have hz : ‖(-q : ℂ)‖ < 1 := by
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h := Complex.norm_log_one_add_sub_self_le hz
  have he : (1+(-q : ℂ)) = ((1-q : ℝ) : ℂ) := by push_cast <;> ring
  rw [he, ← Complex.ofReal_log (by linarith : 0 ≤ 1-q)] at h
  have hn : ‖((Real.log (1-q) : ℂ)-(-q : ℂ))‖ = |Real.log (1-q)+q| := by
    norm_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add]
  rw [hn] at h
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq] at h
  apply h.trans
  have hden : 0 < 1-q := by linarith
  rw [← div_eq_mul_inv, div_div, div_le_iff₀ (mul_pos hden (by norm_num))]
  nlinarith [sq_nonneg q]

/-- If `n*q` approaches a bounded nonnegative quantity, the simplex power
approaches its exponential, even when that quantity varies with the phase. -/
theorem simplex_power_approximation {ι : Type*} {l : Filter ι}
    (n : ι → ℕ) (q b : ι → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hn : Tendsto n l atTop)
    (hq : ∀ᶠ x in l, 0 ≤ q x)
    (hb : ∀ᶠ x in l, 0 ≤ b x ∧ b x ≤ K)
    (herr : Tendsto (fun x => (n x : ℝ)*q x-b x) l (nhds 0)) :
    Tendsto (fun x => (max (1-q x) 0)^(n x)-Real.exp (-b x)) l (nhds 0) := by
  have hnR : Tendsto (fun x => (n x : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have ha : ∀ᶠ x in l, (n x : ℝ)*q x ≤ K+1 := by
    filter_upwards [herr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)), hb]
      with x he hb
    linarith
  have hqbound : ∀ᶠ x in l, q x ≤ (K+1)*(n x : ℝ)⁻¹ := by
    filter_upwards [ha, hnR.eventually (eventually_gt_atTop 0)] with x ha hn0
    rw [← div_eq_mul_inv, le_div_iff₀ hn0]
    nlinarith
  have hq0 : Tendsto q l (nhds 0) := by
    apply squeeze_zero' hq hqbound
    simpa using (tendsto_inv_atTop_zero.comp hnR).const_mul (K+1)
  have hqhalf : ∀ᶠ x in l, q x ≤ 1/2 :=
    hq0.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hlog : Tendsto (fun x => (n x : ℝ)*(Real.log (1-q x)+q x)) l (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x => (K+1)*q x)
    · filter_upwards [hq, hqhalf, ha] with x hq hqhalf ha
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n x))]
      calc
        _ ≤ (n x : ℝ)*(q x)^2 := mul_le_mul_of_nonneg_left
          (log_one_sub_quadratic hq hqhalf) (Nat.cast_nonneg _)
        _ ≤ (K+1)*q x := by nlinarith
    · simpa using hq0.const_mul (K+1)
  have hexp : Tendsto (fun x => (n x : ℝ)*Real.log (1-q x)+b x) l (nhds 0) := by
    convert hlog.sub herr using 1
    · funext x
      ring
    · simp
  have hsmall : Tendsto (fun x => Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1)
      l (nhds 0) := by simpa using (Real.tendsto_exp_nhds_zero_nhds_one.comp hexp).sub_const 1
  apply squeeze_zero_norm' (a := fun x =>
    |Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1|)
  · filter_upwards [hq, hqhalf, hb] with x hqx hqx' hbx
    have hbase : 0 < 1-q x := by linarith
    have hp : (max (1-q x) 0)^(n x) =
        Real.exp ((n x : ℝ)*Real.log (1-q x)) := by
      rw [max_eq_left hbase.le, Real.exp_nat_mul, Real.exp_log hbase]
    rw [hp, Real.norm_eq_abs]
    have he : Real.exp ((n x : ℝ)*Real.log (1-q x))-Real.exp (-b x) =
        Real.exp (-b x)*(Real.exp ((n x : ℝ)*Real.log (1-q x)+b x)-1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      congr 2
      ring
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hbx.1))
  · simpa using hsmall.abs

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailVolume
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite-tail intersection volumes, before prime-box approximation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma prod_g_shifted (N : ℕ) :
    (∏ i : Fin N, g (i.val+1)) = ∏ i ∈ Finset.Icc 1 N, g i := by
  rw [Fin.prod_univ_eq_prod_range (fun i => g (i+1))]
  apply Finset.prod_bij (fun i _ => i+1)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro i _ j _ hij
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    refine ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

lemma tailIntersection_eq (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hT : T.Nonempty) :
    tailIntersection x H T = prefixRegion (R x H) (B x) (maxD (m x) T)
      (fun i => maxD (m x-(i.val+1)) T) := by
  unfold tailIntersection tailPrefixRegion
  rw [prefixRegion_intersection (R x H) (B x) T hT]
  simp only [maxD, dite_eq_left hT]

/-- The intersection-volume identity with the tail budget indexed by the prefix.
This form avoids a reversed-index convention in subsequent finite sums. -/
theorem volume_tailIntersection (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hT : T.Nonempty) (hR : 0 < R x H) (hB : 0 < B x) :
    volume (tailIntersection x H T) =
      ENNReal.ofReal (G x (R x H) * (max (1-tailBudget x H T/B x) 0)^(R x H)) := by
  rw [tailIntersection_eq x H T hT, volume_prefixRegion_explicit _ hR]
  have hb : max (B x-tailBudget x H T) 0 =
      B x * max (1-tailBudget x H T/B x) 0 := by
    have he : B x * (1-tailBudget x H T/B x) = B x-tailBudget x H T := by
      field_simp
    rw [mul_max_of_nonneg _ _ hB.le, he, mul_zero]
  have he : B x - maxD (m x) T -
      ∑ i : Fin (R x H), g (i.val+1)*maxD (m x-(i.val+1)) T =
      B x-tailBudget x H T := by unfold tailBudget; ring
  rw [he, hb, mul_pow, prod_g_shifted]
  congr 1
  unfold G
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailRenewal
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma tailBudget_eq_sum (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) :
    tailBudget x H T =
      ∑ i ∈ Finset.range (R x H+1), g i*maxD (m x-i) T := by
  rw [Finset.sum_range_succ']
  have hg0 : g 0 = 1 := by simp [g]
  simp only [Nat.sub_zero, hg0, one_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold tailBudget
  ring

lemma renewalConvolution_tailSequence (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hm : H ≤ m x) :
    renewalConvolution (tailSequence T) (R x H) = rho^(m x)*tailBudget x H T := by
  rw [renewalConvolution, tailBudget_eq_sum, Finset.mul_sum]
  apply Finset.sum_bij (fun i _ => R x H-i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨R x H-j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    have hR : R x H = m x-H := rfl
    have hidx : m x-(R x H-i) = H+i := by omega
    have hexp : (R x H-i)+(H+i) = m x := by omega
    have hpow : rho^(R x H-i)*rho^(H+i) = rho^(m x) := by
      rw [← pow_add, hexp]
    dsimp [normalizedRenewal, tailSequence]
    rw [hidx]
    calc
      _ = (rho^(R x H-i)*rho^(H+i)) *
          (g (R x H-i)*maxD (H+i) T) := by ring
      _ = _ := by rw [hpow]

/-- The exact tail budget converges after multiplication by `rho^m`.
This is the analytic numerator in the manuscript's finite-tail approximation. -/
theorem normalized_tailBudget_tendsto (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => rho^(m x)*tailBudget x H T) atTop
      (nhds (gamma * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)) := by
  have hc : Summable (tailSequence T) := summable_tail_threshold hT
  have hh := (renewalConvolution_tendsto hford (tailSequence T) hc).comp
    ((tendsto_sub_atTop_nat H).comp m_tendsto)
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop H)] with x hx
  exact renewalConvolution_tailSequence x H T hx

lemma alpha_ge_lam {s : ℝ} (hs : 0 ≤ s) : lam ≤ alpha s := by
  unfold alpha
  have he : 1 ≤ Real.exp (lam*s) := Real.one_le_exp (mul_nonneg lam_pos.le hs)
  nlinarith [lam_pos]

lemma phase_division_error {ι : Type*} {l : Filter ι} (z v a : ι → ℝ)
    (L c : ℝ) (hc : 0 < c) (hz : Tendsto z l (nhds L))
    (hv : Tendsto v l (nhds 1)) (ha : ∀ᶠ x in l, c ≤ a x) :
    Tendsto (fun x => z x/(a x*v x)-L/a x) l (nhds 0) := by
  have ht : Tendsto (fun x => z x/v x-L) l (nhds 0) := by
    simpa using (hz.div hv (by norm_num : (1 : ℝ) ≠ 0)).sub_const L
  apply squeeze_zero_norm' (a := fun x => |z x/v x-L|/c)
  · filter_upwards [ha] with x hx
    have he : z x/(a x*v x)-L/a x = (z x/v x-L)/a x := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos (hc.trans_le hx)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hx
  · simpa using ht.abs.div_const c

/-- The phase-dependent exponent in the simplex volume, before replacing `m`
by the prefix dimension `m-H`. -/
theorem tailBudget_exponent_error (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => (m x : ℝ)*tailBudget x H T/B x -
      (gamma / alpha (theta x)) * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)
      atTop (nhds 0) := by
  have hphase : ∀ᶠ x : ℝ in atTop, lam ≤ alpha (theta x) :=
    theta_eventually_mem.mono (fun _ hx => alpha_ge_lam hx.1)
  have hh := phase_division_error
    (fun x : ℝ => rho^(m x)*tailBudget x H T) bandCenterRatio
    (fun x => alpha (theta x))
    (gamma * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T) lam lam_pos
    (normalized_tailBudget_tendsto hford T hT) bandCenterRatio_tendsto hphase
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hm
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hr : rho^(m x) ≠ 0 := pow_ne_zero _ rho_pos.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  rw [alpha_theta_eq hB]
  unfold bandCenterRatio
  field_simp [hmn, hr, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailPower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential limit of the finite-tail simplex factor, uniformly in phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma tailBudget_nonneg {x : ℝ} {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) (hm : H ≤ m x) : 0 ≤ tailBudget x H T := by
  unfold tailBudget
  apply add_nonneg (maxD_nonneg hT hm)
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (g_pos _).le
  apply maxD_nonneg hT
  have hi := i.isLt
  unfold R at hi
  omega

/-- The exact power appearing in each intersection volume tends to its
phase-dependent exponential weight; no continuity in the phase is assumed. -/
theorem tail_simplex_power_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ =>
      (max (1-tailBudget x H T/B x) 0)^(R x H) -
      Real.exp (-(gamma/alpha (theta x)) *
        ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)) atTop (nhds 0) := by
  let S := ∑' n : ℕ, rho^(H+n)*maxD (H+n) T
  let q : ℝ → ℝ := fun x => tailBudget x H T/B x
  let b : ℝ → ℝ := fun x => (gamma/alpha (theta x))*S
  let K := (gamma/lam)*S
  have hS : 0 ≤ S := tsum_nonneg (fun n =>
    mul_nonneg (pow_nonneg rho_pos.le _) (maxD_nonneg hT (by omega)))
  have hK : 0 ≤ K := mul_nonneg (div_pos gamma_pos lam_pos).le hS
  have hq : ∀ᶠ x : ℝ in atTop, 0 ≤ q x := by
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
      B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
    exact div_nonneg (tailBudget_nonneg T hT hm) hB.le
  have hb : ∀ᶠ x : ℝ in atTop, 0 ≤ b x ∧ b x ≤ K := by
    filter_upwards [theta_eventually_mem] with x hx
    refine ⟨mul_nonneg (div_pos gamma_pos (alpha_pos _)).le hS, ?_⟩
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left gamma_pos.le lam_pos (alpha_ge_lam hx.1)) hS
  have hmerr : Tendsto (fun x => (m x : ℝ)*q x-b x) atTop (nhds 0) := by
    simpa only [q, b, S, mul_div_assoc] using tailBudget_exponent_error hford T hT
  have hbound : ∀ᶠ x : ℝ in atTop, (m x : ℝ)*q x ≤ K+1 := by
    filter_upwards [hmerr.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)), hb]
      with x he hb
    linarith
  have hq0 : Tendsto q atTop (nhds 0) := by
    apply squeeze_zero' hq
    · filter_upwards [hbound, m_tendsto.eventually (eventually_gt_atTop 0)] with x hx hm
      have hmR : (0 : ℝ) < m x := Nat.cast_pos.mpr hm
      show q x ≤ (K+1)*(m x : ℝ)⁻¹
      rw [← div_eq_mul_inv, le_div_iff₀ hmR]
      nlinarith
    · simpa using (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp m_tendsto)).const_mul (K+1)
  have hRerr : Tendsto (fun x => (R x H : ℝ)*q x-b x) atTop (nhds 0) := by
    have hh : Tendsto (fun x => (m x : ℝ)*q x-b x-(H : ℝ)*q x)
        atTop (nhds 0) := by
      simpa using hmerr.sub (hq0.const_mul (H : ℝ))
    apply hh.congr'
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H)] with x hm
    dsimp [R]
    rw [Nat.cast_sub hm]
    ring
  have hlim := simplex_power_approximation (fun x => R x H) q b K hK
    ((tendsto_sub_atTop_nat H).comp m_tendsto) hq hb hRerr
  simpa only [q, b, S, neg_mul] using hlim

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Prefactor
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma sub_div_self_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => ((m x-k : ℕ) : ℝ)/(m x : ℝ)) atTop (nhds 1) := by
  have hi : Tendsto (fun x : ℝ => (m x : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp m_tendsto)
  have hh : Tendsto (fun x : ℝ => 1-(k : ℝ)*(m x : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hi.const_mul (k : ℝ))
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hk hm
  rw [Nat.cast_sub hk]
  field_simp [show (m x : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne']

lemma normalized_prefactor_step (hford : FordRenewalInput) (k : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x) *
      (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)) atTop (nhds (gamma*rho^k)) := by
  have hn := (normalizedRenewal_properties hford).1.comp
    ((tendsto_sub_atTop_nat k).comp m_tendsto)
  have hh := (((sub_div_self_tendsto k).mul hn).mul_const (rho^k)).div
    bandCenterRatio_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hh
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop k),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hk hm
  have hpow : rho^(m x-k)*rho^k = rho^(m x) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  change (((m x-k : ℕ) : ℝ)/(m x : ℝ) * normalizedRenewal (m x-k) * rho^k) /
      bandCenterRatio x = alpha (theta x) * (((m x-k : ℕ) : ℝ)*g (m x-k)/B x)
  rw [alpha_theta_eq hB]
  unfold normalizedRenewal bandCenterRatio
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  field_simp [hmn, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']
  rw [← hpow]
  ring

lemma normalized_prefactor_limit (hford : FordRenewalInput) (H : ℕ) :
    Tendsto (fun x : ℝ => alpha (theta x)^H * G x (R x H)/G x (m x))
      atTop (nhds (rho^(H*(H-1)/2)*gamma^H)) := by
  have hh := tendsto_finsetProd (Finset.range H)
    (fun k _ => normalized_prefactor_step hford k)
  have hp : (∏ k ∈ Finset.range H, gamma*rho^k) = rho^(H*(H-1)/2)*gamma^H := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
    ring
  rw [hp] at hh
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hm hB
  rw [show R x H = m x-H from rfl, G_sub_eq_product hB (m x) H hm,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  field_simp [(G_pos hB (m x)).ne']

/-- The prefactor in the exact intersection volume has the finite-tail limit
specified in the manuscript, even though the phase itself need not converge. -/
theorem prefactor_error (hford : FordRenewalInput) (H : ℕ) :
    Tendsto (fun x : ℝ => G x (R x H)/G x (m x) -
      rho^(H*(H-1)/2)*(gamma/alpha (theta x))^H) atTop (nhds 0) := by
  have hh := phase_division_error
    (fun x : ℝ => alpha (theta x)^H * G x (R x H)/G x (m x))
    (fun _ => 1) (fun x => alpha (theta x)^H)
    (rho^(H*(H-1)/2)*gamma^H) (lam^H) (pow_pos lam_pos H)
    (normalized_prefactor_limit hford H) tendsto_const_nhds
    (theta_eventually_mem.mono (fun _ hx =>
      pow_le_pow_left₀ lam_pos.le (alpha_ge_lam hx.1) H))
  apply hh.congr'
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [mul_one, div_pow]
    field_simp [(pow_pos (alpha_pos (theta x)) H).ne'])

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_IntersectionLimit
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual finite-tail intersection volumes. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma normalized_intersection_expression_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => G x (R x H)/G x (m x) *
      (max (1-tailBudget x H T/B x) 0)^(R x H) -
      intersectionWeight (theta x) T) atTop (nhds 0) := by
  let Q : ℝ → ℝ := fun x => rho^(H*(H-1)/2)*(gamma/alpha (theta x))^H
  let U : ℝ → ℝ := fun x => (max (1-tailBudget x H T/B x) 0)^(R x H)
  let E : ℝ → ℝ := fun x => Real.exp (-(gamma/alpha (theta x)) *
    ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)
  let K := rho^(H*(H-1)/2)*(gamma/lam)^H
  have hQ : ∀ᶠ x : ℝ in atTop, 0 ≤ Q x ∧ Q x ≤ K := by
    filter_upwards [theta_eventually_mem] with x hx
    refine ⟨mul_nonneg (pow_nonneg rho_pos.le _)
      (pow_nonneg (div_pos gamma_pos (alpha_pos _)).le _), ?_⟩
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg rho_pos.le _)
    exact pow_le_pow_left₀ (div_pos gamma_pos (alpha_pos _)).le
      (div_le_div_of_nonneg_left gamma_pos.le lam_pos (alpha_ge_lam hx.1)) H
  have hU : ∀ᶠ x : ℝ in atTop, 0 ≤ U x ∧ U x ≤ 1 := by
    filter_upwards [m_tendsto.eventually (eventually_ge_atTop H),
      B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
    have hq := div_nonneg (tailBudget_nonneg T hT hm) hB.le
    exact ⟨pow_nonneg (le_max_right _ _) _, pow_le_one₀ (le_max_right _ _)
      (max_le (by linarith) zero_le_one)⟩
  have h₁ : Tendsto (fun x : ℝ => |G x (R x H)/G x (m x)-Q x|)
      atTop (nhds 0) := by simpa [Q] using (prefactor_error hford H).abs
  have h₂ : Tendsto (fun x : ℝ => |U x-E x|) atTop (nhds 0) := by
    simpa [U, E] using (tail_simplex_power_limit hford T hT).abs
  apply squeeze_zero_norm' (a := fun x =>
    |G x (R x H)/G x (m x)-Q x|+K*|U x-E x|)
  · filter_upwards [hQ, hU] with x hQx hUx
    change |G x (R x H)/G x (m x)*U x-Q x*E x| ≤ _
    calc
      _ = |(G x (R x H)/G x (m x)-Q x)*U x+Q x*(U x-E x)| := by
        congr 1; ring
      _ ≤ |(G x (R x H)/G x (m x)-Q x)*U x|+|Q x*(U x-E x)| := abs_add_le _ _
      _ = |G x (R x H)/G x (m x)-Q x| * U x+Q x * |U x-E x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hUx.1, abs_of_nonneg hQx.1]
      _ ≤ _ := add_le_add
        (by nlinarith [abs_nonneg (G x (R x H)/G x (m x)-Q x)])
        (mul_le_mul_of_nonneg_right hQx.2 (abs_nonneg _))
  · simpa using h₁.add (h₂.const_mul K)

/-- Each genuine intersection volume has its stated coefficient limit.
The hypothesis concerns only a fixed finite set of tail witnesses. -/
theorem normalized_intersection_volume_limit (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H)) (hne : T.Nonempty)
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => (volume (tailIntersection x H T)).toReal/G x (m x) -
      intersectionWeight (theta x) T) atTop (nhds 0) := by
  apply (normalized_intersection_expression_limit hford T hT).congr'
  filter_upwards [m_tendsto.eventually (eventually_gt_atTop H),
    B_tendsto.eventually (eventually_gt_atTop 0)] with x hm hB
  rw [volume_tailIntersection x H T hne (by dsimp [R]; omega) hB,
    ENNReal.toReal_ofReal (mul_nonneg (G_pos hB _).le
      (pow_nonneg (le_max_right _ _) _))]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FiniteCoefficient
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite universe for the phase-dependent inclusion-exclusion sums. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma witness_mem_allTailData {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hη : IsWitness H s η) : η ∈ allTailData H :=
  (finite_tail_data H).mem_toFinset.mpr ⟨s, hs, hη⟩

lemma tail_finsum_eq_sum (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (d : ℕ) (F : Finset (TailDatum H) → ℝ) :
    (∑ᶠ T : Finset (TailDatum H),
      if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then F T else 0) =
    ∑ T ∈ nonemptyTailSubsets H,
      if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then F T else 0 := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := nonemptyTailSubsets H)]
  · apply Finset.sum_congr rfl
    intro T hT
    have hn := (Finset.mem_filter.mp hT).2
    simp only [hn, true_and]
  · intro T hT
    have ht : T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
      by_contra h
      simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hT
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ht.1⟩
    intro η hη
    exact witness_mem_allTailData hs (ht.2 hη).1

lemma AH_eq_finiteTailCoefficient (H : ℕ) (f : ℝ → ℝ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    AH H f s = finiteTailCoefficient H f s (intersectionWeight s) := by
  classical
  unfold AH finiteTailCoefficient
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 (tailValueBound H))]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdt : IsTotient d
    · simp only [ite_eq_left hdt]
      rw [tail_finsum_eq_sum H hs d]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      split_ifs <;> (try unfold intersectionWeight) <;> ring
    · simp only [ite_eq_right hdt, mul_zero]
  · intro d hd
    by_contra hmem
    have hz : ∀ T : Finset (TailDatum H),
        ¬ (T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d) := by
      rintro T ⟨hne, hsub⟩
      obtain ⟨η, hη⟩ := hne
      have hw := hsub hη
      have hdt : IsTotient d := by
        refine ⟨w η, ?_, hw.2⟩
        unfold w
        exact Nat.mul_pos hw.1.2.1 (Finset.prod_pos (fun l hl =>
          (hw.1.2.2.1 l hl).1.pos))
      exact hmem (Finset.mem_Icc.mpr ⟨isTotient_pos hdt, witness_totient_bound hs η hw⟩)
    have hh : (∑ᶠ T : Finset (TailDatum H),
        if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1)*Real.exp (-(gamma/alpha s)*
            ∑' n : ℕ, rho^(H+n)*maxD (H+n) T) else 0) = 0 := by
      simp only [ite_eq_right (hz _), finsum_zero]
    simp only [Function.mem_support] at hd
    split_ifs at hd with hdt
    · exact hd (by rw [hh, mul_zero])
    · exact hd rfl

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionTuples
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma tuple_eq_of_value_and_primes {R : ℕ} {τ σ : TotientTuple R}
    (hp : ∀ i, 2 ≤ tuplePrimes τ i) (hv : tupleValue τ = tupleValue σ)
    (he : tuplePrimes τ = tuplePrimes σ) : τ = σ := by
  have hprod : 0 < ∏ i, (tuplePrimes τ i-1) :=
    Finset.prod_pos (fun i _ => by have := hp i; omega)
  have hd : τ.tail.d = σ.tail.d := by
    unfold tupleValue at hv
    rw [← he] at hv
    exact Nat.eq_of_mul_eq_mul_right hprod hv
  have hh : τ.head = σ.head := by
    simpa only [tuplePrimes, Fin.cons_zero] using congrFun he 0
  have ht : τ.tail.primes = σ.tail.primes := by
    funext j
    simpa only [tuplePrimes, Fin.cons_succ] using congrFun he j.succ
  cases τ with
  | mk th tt =>
    cases σ with
    | mk sh st =>
      cases tt
      cases st
      simp_all

lemma basic_collision_first_difference {x t : ℝ} {H : ℕ}
    {τ σ : TotientTuple (R x H)} (hPH : P H ≤ H)
    (hτ : IsBasicTuple x H t τ) (hv : tupleValue τ = tupleValue σ) (hne : τ ≠ σ) :
    ∃ i : Fin (R x H+1), tuplePrimes τ i ≠ tuplePrimes σ i ∧
      ∀ j, j < i → tuplePrimes τ j = tuplePrimes σ j := by
  classical
  have hex : ∃ i, tuplePrimes τ i ≠ tuplePrimes σ i := by
    by_contra! he
    exact hne (tuple_eq_of_value_and_primes
      (fun i => (basic_tuple_primes hPH hτ i).two_le) hv (funext he))
  obtain ⟨i, hi, hmin⟩ := (Finset.univ.filter (fun i => tuplePrimes τ i ≠ tuplePrimes σ i)).exists_min_image
    (fun i => i.val) (by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simpa using hi⟩)
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  intro j hji
  by_contra hj
  have hmem : j ∈ Finset.univ.filter (fun i => tuplePrimes τ i ≠ tuplePrimes σ i) := by simp [hj]
  have := hmin j hmem
  exact (not_le_of_gt hji) (by exact_mod_cast this)

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

lemma chosen_collision_first {x t : ℝ} {H : ℕ} {τ σ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) (hσ : IsBasicTuple x H t σ)
    (hv : tupleValue τ=tupleValue σ) (hne : τ ≠ σ) :
    ∃ i ≤ R x H,
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) i ≠
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) i ∧
      ∀ j < i, wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j := by
  obtain ⟨i,hi,hcommon⟩ := basic_collision_first_difference hPH hτ hv hne
  have heτ (j : Fin (R x H+1)) :
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j.val=tuplePrimes τ j := by
    rw [wholeWitnessPrime_tuple,chosenRemainder_tuple hτ]
  have heσ (j : Fin (R x H+1)) :
      wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j.val=tuplePrimes σ j := by
    rw [wholeWitnessPrime_tuple,chosenRemainder_tuple hσ]
  refine ⟨i.val,by have := i.isLt; omega,?_,?_⟩
  · simpa only [heτ,heσ] using hi
  · intro j hj
    let j' : Fin (R x H+1) := ⟨j,by have := i.isLt; omega⟩
    exact (heτ j').trans ((hcommon j' hj).trans (heσ j').symm)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ActualComparison
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ford's comparison bound applied to finite families of actual tuple pairs. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma tuple_eq_of_head_tail {n : ℕ} {τ σ : TotientTuple n}
    (hh : τ.head=σ.head) (ht : τ.tail=σ.tail) : τ=σ := by
  cases τ
  cases σ
  simp_all

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

lemma witnessBlockValue_zero {x : ℝ} {H k p : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hL : L x H < m x) (hR : R x H < L x H) (hk : k < L x H) :
    witnessBlockValue p η 0 k=tupleValue (witnessTuple p η) :=
  (witness_tuple_value_at_cut hη hL hR hk).symm

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

lemma tupleSuffix_zero_injective (R : ℕ) : Function.Injective (fun τ : TotientTuple R => tupleSuffix τ 0) := by
  intro τ σ he
  have hp := congrArg PrefixDatum.primes he
  have hd := congrArg PrefixDatum.d he
  have hh : τ.head=σ.head := by
    have h := congrFun hp ⟨0,by omega⟩
    simpa [tupleSuffix,tuplePrimes] using h
  have htp : τ.tail.primes=σ.tail.primes := by
    funext j
    have h := congrFun hp j.succ
    simpa [tupleSuffix,tuplePrimes] using h
  exact tuple_eq_of_head_tail hh (congrArg₂ PrefixDatum.mk htp hd)

lemma pairSuffix_zero_injective (R : ℕ) : Function.Injective (fun q : TotientTuple R × TotientTuple R => pairSuffix q 0) := by
  intro q q' he
  exact Prod.ext (tupleSuffix_zero_injective R (congrArg Prod.fst he))
    (tupleSuffix_zero_injective R (congrArg Prod.snd he))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionHeadCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete comparison estimate for pairs with different head primes. -/

noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma head_collision_block {x t : ℝ} {H : ℕ}
    (hPH : P H ≤ H) (hL : L x H < m x) (hR : R x H < L x H)
    (hk : collisionLastIndex x 0 < L x H) (ht : t ≤ x)
    {q : TotientTuple (R x H) × TotientTuple (R x H)} (hq : q ∈ headCollisionPairs x H t) :
    GoodCollisionBlock x t H 0 x q := by
  obtain ⟨hq,hne⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpair,_,hvalue⟩ := Finset.mem_filter.mp hq
  obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpair
  have hl' := (mem_goodTupleFinset hPH).mp hl
  have hr' := (mem_goodTupleFinset hPH).mp hr
  refine ⟨hl',hr',hvalue,?_,?_,hl'.1.2.1,hr'.1.2.1,?_,fun _ => rfl⟩
  · exact hne
  · intro j hj
    omega
  · rw [witnessBlockValue_zero (chosenRemainder_spec hl'.1.2.2.1).1 hL hR hk,
      chosenRemainder_tuple hl'.1]
    exact hl'.1.2.2.2.trans ht

/-- All grids, canceled index sets, canceled primes, and both residual tuple
factorizations are summed. There is no fixed-prefix cost at index zero. -/
theorem head_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput) :
    ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
    ((headCollisionPairs x H t).card : ℝ) ≤
      x/Real.log x*Real.exp (-B x/(8*(m x : ℝ)^4)) := by
  obtain ⟨y₀,hy₀,hcount⟩ := actual_block_count hford hmertens
  filter_upwards [hcount,eventually_collision_indices,eventually_tail_cut_separated]
    with H hc hind hsep
  filter_upwards [hc,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),eventually_ge_atTop y₀]
    with x hx hm hBx hxy
  intro t ht
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  have hk : collisionLastIndex x 0 < L x H := (hind x hm 0 (Nat.zero_le _)).2.2
  have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
  have he := hx 0 (Nat.zero_le _) hL hR t x hxy hBx
    (by rw [hzero]; linarith) (by rw [hzero]; linarith)
    (headCollisionPairs x H t)
    (fun q hq => head_collision_block (by omega) hL hR hk ht hq)
    (fun q _ q' _ he => pairSuffix_zero_injective _ he)
  simpa only [Nat.sub_zero] using he

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CollisionTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The summable, phase-independent tail in the prefix collision estimate. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma collisionKernel_nonneg (c : ℝ) (h : ℕ) : 0 ≤ collisionKernel c h := by
  unfold collisionKernel
  positivity

lemma collisionKernel_le_geometric {c : ℝ} (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, collisionKernel c h ≤ Real.exp (-1)^h := by
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one 4 rho_pos.le rho_lt_one
  filter_upwards [ht.eventually (eventually_lt_nhds (div_pos hc (by norm_num : (0:ℝ)<5))),
    eventually_ge_atTop 1] with h hh hpos
  have hhR : (0 : ℝ) < h := by exact_mod_cast hpos
  have hden : 0 < (h : ℝ)^3*rho^h := mul_pos (pow_pos hhR _) (pow_pos rho_pos _)
  have hsave : (5 : ℝ)*h ≤ c/((h : ℝ)^3*rho^h) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hh]
  have hexp : (h : ℝ)^4 ≤ Real.exp (4*(h : ℝ)) := by
    have hh' : (h : ℝ) ≤ Real.exp (h : ℝ) := by linarith [Real.add_one_le_exp (h : ℝ)]
    calc
      _ ≤ (Real.exp (h : ℝ))^4 := pow_le_pow_left₀ hhR.le hh' _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  unfold collisionKernel
  calc
    _ ≤ Real.exp (4*(h : ℝ))*Real.exp (-5*(h : ℝ)) :=
      mul_le_mul hexp (Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hsave))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(h : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ = Real.exp (-1)^h := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem summable_collisionKernel {c : ℝ} (hc : 0 < c) : Summable (collisionKernel c) := by
  have hg : Summable (fun h : ℕ => Real.exp (-1)^h) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by simp)
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [collisionKernel_le_geometric hc] with h hh
  simpa only [Real.norm_eq_abs, abs_of_nonneg (collisionKernel_nonneg c h)] using hh

/-- The final error can be chosen independently of the phase and tends to zero. -/
theorem collisionTail_tendsto (c : ℝ) : Tendsto (collisionTail c) atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, collisionKernel c (H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using (_root_.tendsto_sum_nat_add (collisionKernel c))

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

lemma collision_exponential_kernel {x : ℝ} {i : ℕ} (hi : i < m x)
    (hband : (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) ≤ fordBandScale x i) :
    ((m x-i : ℕ) : ℝ)^4*Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) ≤
      collisionKernel (lam/32) (m x-i) := by
  have hh : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have hpow := pow_pos rho_pos (m x-i)
  have hsave : lam/(32*(((m x-i : ℕ) : ℝ)^3*rho^(m x-i))) ≤
      fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : lam/(32*(((m x-i : ℕ) : ℝ)^3*rho^(m x-i)))*
        (16*((m x-i : ℕ) : ℝ)^4)=lam*((m x-i : ℕ) : ℝ)/(2*rho^(m x-i)) := by
      field_simp
      ring
    rw [he]
    apply le_trans _ hband
    calc
      lam*((m x-i : ℕ) : ℝ)/(2*rho^(m x-i)) =
          (1/2 : ℝ)*(lam*((m x-i : ℕ) : ℝ)/rho^(m x-i)) := by ring
      _ ≤ (99/100 : ℝ)*(lam*((m x-i : ℕ) : ℝ)/rho^(m x-i)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (mul_nonneg lam_pos.le hh.le) hpow.le)
      _ = _ := by ring
  unfold collisionKernel
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  first | (convert neg_le_neg hsave using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((neg_le_neg hsave).trans (le_of_eq (by ring)))

lemma good_collision_card_le_first_sum {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (goodCollisionPairs x H t).card ≤
      ∑ i ∈ Finset.Icc 0 (R x H), (firstCollisionPairs x H t i).card := by
  have hsub : goodCollisionPairs x H t ⊆
      (Finset.Icc 0 (R x H)).biUnion (firstCollisionPairs x H t) := by
    intro q hq
    obtain ⟨hpairs,hne,hv⟩ := Finset.mem_filter.mp hq
    obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpairs
    have hl' := (mem_goodTupleFinset hPH).mp hl
    have hr' := (mem_goodTupleFinset hPH).mp hr
    obtain ⟨i,hi,hfirst,hcommon⟩ := chosen_collision_first hPH hl'.1 hr'.1 hv hne
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩,
      Finset.mem_filter.mpr ⟨hq,hfirst,hcommon⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma firstCollisionPairs_zero (x : ℝ) (H : ℕ) (t : ℝ) :
    firstCollisionPairs x H t 0=headCollisionPairs x H t := by
  ext q
  simp only [firstCollisionPairs,headCollisionPairs,Finset.mem_filter,FirstDifferenceAt,
    wholeWitnessPrime,ite_true, if_true,not_lt_zero,IsEmpty.forall_iff,forall_const,and_true]

lemma first_index_kernel_sum {m H : ℕ} (hHm : H ≤ m) {c : ℝ} (hc : 0 < c) :
    (∑ i ∈ Finset.Icc 0 (m-H), collisionKernel c (m-i)) ≤ collisionTail c H := by
  let T := (Finset.Icc 0 (m-H)).image (fun i => m-i-H)
  have hinj : Set.InjOn (fun i => m-i-H) (↑(Finset.Icc 0 (m-H)) : Set ℕ) := by
    intro i hi j hj he
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    change m-i-H=m-j-H at he
    omega
  have he : (∑ i ∈ Finset.Icc 0 (m-H), collisionKernel c (m-i)) =
      ∑ n ∈ T, collisionKernel c (H+n) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    congr 1
    omega
  rw [he]
  apply ((summable_collisionKernel hc).comp_injective (fun n k he => by omega)).sum_le_tsum
  intro n _
  exact collisionKernel_nonneg c (H+n)

lemma head_exponential_le_block {b h : ℝ} (hb : 0 ≤ b) (hh : 1 ≤ h) :
    Real.exp (-b/(8*h^4)) ≤ h^4*Real.exp (-b/(16*h^4)) := by
  have hpow : 1 ≤ h^4 := one_le_pow₀ hh
  have hdiv : b/(16*h^4) ≤ b/(8*h^4) :=
    div_le_div_of_nonneg_left hb (by positivity) (by nlinarith [sq_nonneg (h^2)])
  have he : Real.exp (-b/(8*h^4)) ≤ Real.exp (-b/(16*h^4)) := by
    simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hdiv)
  exact he.trans (le_mul_of_one_le_left (Real.exp_pos _).le hpow)

/-- The full ordered collision count, including every common prefix and
both residual tuple factorizations, has a phase-independent vanishing error. -/
theorem good_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      ((goodCollisionPairs x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  let C : ℝ := 160/Real.log 2
  let ε := fun H => C*collisionTail (lam/32) H
  have hC : 1 ≤ C := by
    dsimp [C]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mpr
    linarith [Real.log_two_lt_d9]
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa only [ε,mul_zero] using (collisionTail_tendsto (lam/32)).const_mul C
  refine ⟨ε,hε,?_⟩
  filter_upwards [actual_positive_collision_count hford hmertens hbox hren,
    head_collision_count hford hmertens,eventually_tail_cut_separated,eventually_ge_atTop 1]
    with H hpos hhead hsep hH
  filter_upwards [hpos,hhead,G_eventually_one_le hren,ford_band_lower,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hp hh hG hf hm hx hB
  intro t ht
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hA : 0 ≤ C*(x/Real.log x)*G x (m x) := by positivity
  have hindex : ∀ i ∈ Finset.Icc 0 (R x H),
      ((firstCollisionPairs x H t i).card : ℝ) ≤
        C*(x/Real.log x)*G x (m x)*collisionKernel (lam/32) (m x-i) := by
    intro i hi
    have hiR := (Finset.mem_Icc.mp hi).2
    have him : i < m x := by unfold R at hiR; omega
    have hk := collision_exponential_kernel him (hf i him)
    by_cases hi0 : i=0
    · subst i
      rw [firstCollisionPairs_zero]
      have hm1 : (1 : ℝ) ≤ m x := by exact_mod_cast hH.trans hm
      have he := head_exponential_le_block hB.le hm1
      have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
      rw [hzero,Nat.sub_zero] at hk
      have hcoef : x/Real.log x ≤ C*(x/Real.log x)*G x (m x) := by
        have hxdiv : 0 ≤ x/Real.log x := by positivity
        have hm := mul_le_mul_of_nonneg_right hC hxdiv
        have hg := mul_le_mul_of_nonneg_left hG (mul_nonneg (by linarith : 0 ≤ C) hxdiv)
        nlinarith
      calc
        _ ≤ x/Real.log x*Real.exp (-B x/(8*(m x : ℝ)^4)) := hh t ht
        _ ≤ (x/Real.log x)*((m x : ℝ)^4*Real.exp (-B x/(16*(m x : ℝ)^4))) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ (C*(x/Real.log x)*G x (m x))*
            ((m x : ℝ)^4*Real.exp (-B x/(16*(m x : ℝ)^4))) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ ≤ (C*(x/Real.log x)*G x (m x))*collisionKernel (lam/32) (m x) :=
          mul_le_mul_of_nonneg_left hk hA
        _ = _ := by simp only [Nat.sub_zero]
    · have hip : 1 ≤ i := by omega
      apply (hp i hip hiR t ht).trans
      simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hk hA
  calc
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H), ((firstCollisionPairs x H t i).card : ℝ) := by
      exact_mod_cast good_collision_card_le_first_sum (x := x) (t := t) (by omega : P H ≤ H)
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H),
        C*(x/Real.log x)*G x (m x)*collisionKernel (lam/32) (m x-i) :=
      Finset.sum_le_sum hindex
    _ = (C*(x/Real.log x)*G x (m x))*
        ∑ i ∈ Finset.Icc 0 (R x H), collisionKernel (lam/32) (m x-i) := by rw [Finset.mul_sum]
    _ ≤ (C*(x/Real.log x)*G x (m x))*collisionTail (lam/32) H :=
      mul_le_mul_of_nonneg_left (first_index_kernel_sum hm (div_pos lam_pos (by norm_num))) hA
    _ = ε H*(x/Real.log x*G x (m x)) := by dsimp [ε] <;> ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnionVolume
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact union-volume coefficient and its finite-tail limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_witnessFinset {H : ℕ} {s : ℝ} {d : ℕ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    η ∈ witnessFinset H s d ↔ η ∈ witnesses H s d := by
  simp only [witnessFinset, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨witness_mem_allTailData hs h.1, h⟩⟩

lemma measurableSet_tailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    MeasurableSet (tailPrefixRegion x H η) := by
  unfold tailPrefixRegion
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable
    (measurableSet_weightedSimplex _ _)

lemma volume_tailPrefixRegion_ne_top {x : ℝ} {H : ℕ} (hR : 0 < R x H)
    (η : TailDatum H) : volume (tailPrefixRegion x H η) ≠ ⊤ := by
  unfold tailPrefixRegion
  rw [volume_prefixRegion_explicit _ hR]
  exact ENNReal.ofReal_ne_top

lemma subset_witnessFinset {H : ℕ} {s : ℝ} {d : ℕ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (T : Finset (TailDatum H)) :
    T ⊆ witnessFinset H s d ↔ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
  exact ⟨fun h η hη => (mem_witnessFinset hs).mp (h hη),
    fun h η hη => (mem_witnessFinset hs).mpr (h hη)⟩

lemma union_volume_inclusion_exclusion {x : ℝ} {H : ℕ} {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hR : 0 < R x H) (d : ℕ) :
    (volume (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η)).toReal =
      ∑ T ∈ nonemptyTailSubsets H,
        if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
          (-1 : ℝ)^(T.card-1) * (volume (tailIntersection x H T)).toReal else 0 := by
  rw [show (volume (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η)).toReal =
      volume.real (⋃ η ∈ witnessFinset H s d, tailPrefixRegion x H η) from rfl,
    measureReal_biUnion_eq_sum_powerset
      (fun η _ => measurableSet_tailPrefixRegion x H η)
      (fun η _ => volume_tailPrefixRegion_ne_top hR η)]
  let W := (witnessFinset H s d).powerset.filter Finset.Nonempty
  have hsub : W ⊆ nonemptyTailSubsets H := by
    intro T hT
    obtain ⟨hTW, hne⟩ := Finset.mem_filter.mp hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hne⟩
    exact (Finset.mem_powerset.mp hTW).trans (Finset.filter_subset _ _)
  calc
    _ = ∑ T ∈ W, if (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
        (-1 : ℝ)^(T.card-1)*(volume (tailIntersection x H T)).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨hTW, hne⟩ := Finset.mem_filter.mp hT
      rw [ite_eq_left ((subset_witnessFinset hs T).mp (Finset.mem_powerset.mp hTW))]
      have hc : T.card+1 = T.card-1+2 := by
        have := Finset.card_pos.mpr hne
        omega
      rw [hc, pow_add]
      norm_num
      change (volume (⋂ i ∈ T, tailPrefixRegion x H i)).toReal = _
      congr 2
      ext u
      simp [tailIntersection]
    _ = _ := Finset.sum_subset hsub (by
      intro T hT hnot
      rw [ite_eq_right]
      intro hW
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((subset_witnessFinset hs T).mpr hW),
          (Finset.mem_filter.mp hT).2⟩))

lemma unionVolumeCoefficient_eq {x : ℝ} {H : ℕ} (f : ℝ → ℝ)
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (hR : 0 < R x H) :
    unionVolumeCoefficient H f x = finiteTailCoefficient H f (theta x)
      (fun T => (volume (tailIntersection x H T)).toReal/G x (m x)) := by
  unfold unionVolumeCoefficient finiteTailCoefficient
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with hdt
  · rw [union_volume_inclusion_exclusion hs hR d, mul_div_assoc]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro T hT
    split_ifs <;> ring
  · rfl

lemma tendsto_ite_zero {ι : Type*} {l : Filter ι} (p : ι → Prop) (F : ι → ℝ)
    (hF : Tendsto F l (nhds 0)) :
    Tendsto (fun x => if p x then F x else 0) l (nhds 0) := by
  apply squeeze_zero_norm' (a := fun x => ‖F x‖)
  · exact Eventually.of_forall (fun x => by split_ifs <;> simp)
  · simpa using hF.norm

theorem unionVolumeCoefficient_limit (hford : FordRenewalInput) (H : ℕ)
    (f : ℝ → ℝ) :
    Tendsto (fun x => unionVolumeCoefficient H f x-AH H f (theta x)) atTop (nhds 0) := by
  let E : ℕ → Finset (TailDatum H) → ℝ → ℝ := fun d T x =>
    if IsTotient d then
      if (↑T : Set (TailDatum H)) ⊆ witnesses H (theta x) d then
        f ((ell d : ℝ)/d)/d * (-1 : ℝ)^(T.card-1) *
          ((volume (tailIntersection x H T)).toReal/G x (m x)-intersectionWeight (theta x) T)
      else 0
    else 0
  have he (d : ℕ) (T : Finset (TailDatum H)) (hT : T ∈ nonemptyTailSubsets H) :
      Tendsto (E d T) atTop (nhds 0) := by
    by_cases hd : IsTotient d
    · by_cases hadm : ∃ s ∈ Set.Ico (0 : ℝ) 1, ∀ η ∈ T, IsWitness H s η
      · obtain ⟨s, hs, hTs⟩ := hadm
        have hh := (normalized_intersection_volume_limit hford T
          (Finset.mem_filter.mp hT).2 hTs).const_mul
          (f ((ell d : ℝ)/d)/d * (-1 : ℝ)^(T.card-1))
        simpa only [E, ite_eq_left hd] using tendsto_ite_zero
          (fun x => (↑T : Set (TailDatum H)) ⊆ witnesses H (theta x) d) _
          (by simpa using hh)
      · apply tendsto_const_nhds.congr'
        filter_upwards [theta_eventually_mem] with x hx
        dsimp [E]
        rw [ite_eq_left hd, ite_eq_right]
        intro hsub
        exact hadm ⟨theta x, hx, fun η hη => (hsub hη).1⟩
    · simpa only [E, ite_eq_right hd] using (tendsto_const_nhds (x := (0 : ℝ)))
  have hh := tendsto_finsetSum (Finset.Icc 1 (tailValueBound H))
    (fun d _ => tendsto_finsetSum (nonemptyTailSubsets H) (he d))
  simp only [Finset.sum_const_zero] at hh
  apply hh.congr'
  filter_upwards [theta_eventually_mem,
    m_tendsto.eventually (eventually_gt_atTop H)] with x hx hm
  rw [unionVolumeCoefficient_eq f hx (by dsimp [R]; omega),
    AH_eq_finiteTailCoefficient H f hx]
  unfold finiteTailCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdt : IsTotient d
  · simp only [ite_eq_left hdt]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    dsimp [E]
    rw [ite_eq_left hdt]
    split_ifs <;> ring
  · simp only [E, ite_eq_right hdt, sub_self, Finset.sum_const_zero]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_MassVolumeApproximation
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arithmetic prime mass approximates the exact witness-union
volume, uniformly in all bounded nonnegative weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

/-- The manuscript's finite arithmetic coefficient approximates each fixed
bounded nonnegative weight, with an error vanishing as the tail cut grows. -/
theorem mass_finite_coefficient_approximation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |M x H f/G x (m x)-AH H f (theta x)| ≤ δ H+ε := by
  obtain ⟨δ, hδ, hm⟩ := mass_volume_coefficient_approximation hbox hmertens hren hford
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hm] with H hH
  intro f hf ε hε
  have ht := (unionVolumeCoefficient_limit hren H f).abs
  filter_upwards [hH, ht.eventually (eventually_lt_nhds (by simpa using hε : |(0 : ℝ)| < ε))] with x hx hlim
  exact (abs_sub_le (M x H f/G x (m x)) (unionVolumeCoefficient H f x)
    (AH H f (theta x))).trans (add_le_add (hx f hf) hlim.le)

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CandidateComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

/-- The same negligible error controls every least-preimage interval; it counts
all exceptional values and all tuples above them. -/
theorem candidate_value_comparison (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ k : ℕ,
        |((candidateTuples x H k).card : ℝ)-N k x| ≤ (δ H+ε)*tupleNormalization x := by
  obtain ⟨δe,hδe,he⟩ := basic_exception_values_negligible hscale hstruct hbox hren hmertens
  obtain ⟨δd,hδd,hd⟩ := bad_tuple_discard hbox hren hmertens h26
  obtain ⟨δc,hδc,hc⟩ := good_collision_count h51 hmertens hbox hren
  refine ⟨fun H => 2*|δe H|+3*|δd H|+2*|δc H|,?_,?_⟩
  · simpa only [abs_zero,mul_zero,add_zero] using ((hδe.abs.const_mul 2).add
      (hδd.abs.const_mul 3)).add (hδc.abs.const_mul 2)
  filter_upwards [he,hd,hc,candidate_count_comparison,unique_prefix_finite_comparison]
    with H he hd hc hcompare hfinite
  intro ε hε
  filter_upwards [he (ε/2) (by positivity),hd,hc,hcompare,hfinite,scale_eventually_pos]
    with x he hd hc hcompare hfinite hN
  intro k
  have hd := hd x le_rfl
  have hc := hc x le_rfl
  have hEc : ((basicExceptionValues x H).card : ℝ) ≤ (|δe H|+ε/2)*tupleNormalization x :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (δe H)]) hN.le)
  have hDc : ((badTupleFinset x H x).card : ℝ) ≤ |δd H| *tupleNormalization x :=
    hd.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hCc : ((goodCollisionPairs x H x).card : ℝ) ≤ |δc H| *tupleNormalization x :=
    hc.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hN.le)
  have hh := hcompare k
  have hC0 : (0 : ℝ) ≤ (goodCollisionPairs x H x).card := Nat.cast_nonneg _
  nlinarith [hfinite.1,hfinite.2.1]

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WeightedCoefficient
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

/-- The weighted mass comparison includes every exceptional value and tuple. -/
theorem weighted_value_mass_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |normalizedCount (N k) x-M x H (fk k)/G x (m x)| ≤ δ H+ε := by
  obtain ⟨δv,hδv,hv⟩ := candidate_value_comparison hscale hstruct hbox hren hmertens h26 h51
  obtain ⟨δm,hδm,hm⟩ := candidate_mass_normalized hpnt hbox hren hmertens k hk
  refine ⟨fun H => δv H+δm H,by simpa using hδv.add hδm,?_⟩
  filter_upwards [hv,hm] with H hv hm
  intro ε hε
  filter_upwards [hv (ε/2) (by positivity),hm (ε/2) (by positivity),scale_eventually_pos]
    with x hv hm hN
  change 0 < tupleNormalization x at hN
  have he : |normalizedCount (N k) x-((candidateTuples x H k).card : ℝ)/tupleNormalization x| ≤ δv H+ε/2 := by
    change |N k x/tupleNormalization x-_| ≤ _
    rw [← sub_div,abs_div,abs_of_pos hN,abs_sub_comm]
    exact (div_le_iff₀ hN).mpr (hv k)
  exact (abs_sub_le _ _ _).trans ((add_le_add he hm).trans_eq (by ring))

theorem weighted_value_coefficient_approximation (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        |normalizedCount (N k) x-AH H (fk k) (theta x)| ≤ δ H+ε := by
  obtain ⟨δv,hδv,hv⟩ := weighted_value_mass_approximation hscale hstruct hpnt hbox hren hmertens h26 h51 k hk
  obtain ⟨δm,hδm,hm⟩ := mass_finite_coefficient_approximation hbox hmertens hren hconc
  refine ⟨fun H => δv H+δm H,by simpa using hδv.add hδm,?_⟩
  let f : ℝ → ℝ := fun r => fk k (max r 0)
  have hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1 := fun r =>
    ⟨fk_nonneg k (le_max_right _ _),fk_le_one k (le_max_right _ _)⟩
  have hsame (d : ℕ) : f ((ell d : ℝ)/d)=fk k ((ell d : ℝ)/d) := by
    dsimp [f]
    rw [max_eq_left (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hmass (x : ℝ) (H : ℕ) : M x H f=M x H (fk k) := by
    simp only [mass_eq_prefix_denominators,hsame]
  have hcoeff (H : ℕ) (s : ℝ) : AH H f s=AH H (fk k) s := by
    unfold AH
    simp only [hsame]
  filter_upwards [hv,hm] with H hv hm
  intro ε hε
  filter_upwards [hv (ε/2) (by positivity),hm f hf (ε/2) (by positivity)] with x hv hm
  rw [hmass,hcoeff] at hm
  exact (abs_sub_le _ _ _).trans ((add_le_add hv hm).trans_eq (by ring))

/-- The additive weighted asymptotic and its uniform arithmetic coefficient. -/
theorem conditional_companion_additive_oai (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (k : ℕ) (hk : 1 ≤ k) :
    TendstoUniformlyOn (fun H => AH H (fk k)) (A (fk k)) atTop (Set.Ico (0 : ℝ) 1) ∧
      Tendsto (fun x => normalizedCount (N k) x-A (fk k) (theta x)) atTop (nhds 0) := by
  obtain ⟨δ,hδ,happ⟩ := weighted_value_coefficient_approximation hscale hstruct hpnt
    hbox hren hmertens h26 h51 hconc k hk
  apply coefficient_convergence_from_phase_comparison
  intro ε hε
  have he : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      |normalizedCount (N k) x-AH H (fk k) (theta x)| ≤ ε := by
    filter_upwards [happ,hδ.eventually (eventually_lt_nhds (show (0 : ℝ)<ε/2 by positivity))]
      with H hH hδH
    filter_upwards [hH (ε/2) (by positivity)] with x hx
    exact hx.trans (by linarith)
  exact eventually_atTop.mp he

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.conditional_companion_additive_oai := @OAI.TotientAsymptotic.conditional_companion_additive_oai
