-- Prove2me | solution 1 for OAI.TotientAsymptotic.tuple_mass_normalized_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:40:10.471962+00:00
-- url     : https://prove2.me/submissions/9d7a540c-9c13-455e-b7ff-933485b738c0

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
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_Mass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness and order properties of the actual arithmetic prefix mass. -/

noncomputable section
open scoped BigOperators Topology Classical

namespace TotientAsymptotic

lemma mass_summand_support_finite (x : ℝ) (H : ℕ) (f : ℝ → ℝ) :
    (Function.support (fun ζ : PrefixDatum (R x H) =>
      if IsPrefixDatum x H ζ then
        f ((ell ζ.d : ℝ) / ζ.d) / ((ζ.d : ℝ) * ∏ i : Fin (R x H), (ζ.primes i - 1 : ℕ))
      else 0)).Finite := by
  apply (prefixData_finite x H).subset
  intro ζ hζ
  by_contra h
  change ¬ IsPrefixDatum x H ζ at h
  simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hζ

theorem mass_mono (x : ℝ) (H : ℕ) {f g : ℝ → ℝ} (hfg : ∀ r, f r ≤ g r) :
    M x H f ≤ M x H g := by
  unfold M
  apply finsum_le_finsum' (mass_summand_support_finite x H f)
    (mass_summand_support_finite x H g)
  intro ζ
  dsimp only
  split_ifs
  · exact div_le_div_of_nonneg_right (hfg _) (by positivity)
  · exact le_rfl

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

lemma sum_image_nonneg_le {α β : Type*} (s : Finset α) (f : α → β) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b) : (∑ b ∈ s.image f, w b) ≤ ∑ a ∈ s, w (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hfa : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hfa]
      exact ih.trans (le_add_of_nonneg_left (hw _))
    · rw [Finset.sum_insert hfa]
      exact add_le_add le_rfl ih

lemma prefixDataFinset_eq_image (x : ℝ) (H : ℕ) :
    prefixDataFinset x H = (basicRemainderFinset x H).image (prefixOfRemainder x H) := by
  classical
  ext ζ
  simp only [mem_prefixDataFinset, Finset.mem_image, mem_basicRemainderFinset,
    isPrefixDatum_iff]

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

/-- The finite prefix mass is bounded by a sum over complete witnesses with
the reciprocal totient of the small cofactor separated out. -/
theorem mass_le_remainder_sum {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (f : ℝ → ℝ) (hf : ∀ r, f r ≤ 1) :
    M x H f ≤ ∑ η ∈ basicRemainderFinset x H, remainderReciprocalWeight η := by
  apply (mass_mono x H hf).trans
  rw [mass_eq_sum_prefixData, prefixDataFinset_eq_image]
  apply (sum_image_nonneg_le _ _
    (fun ζ : PrefixDatum (R x H) => 1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)))
    (fun _ => by positivity)).trans
  apply Finset.sum_le_sum
  intro η hη
  exact prefix_reciprocal_majorant (mem_basicRemainderFinset.mp hη) hPH

/-- The entire cost of the discrete cofactor separates from the reciprocal
prime sum. The latter still retains all the basic simplex restrictions. -/
theorem mass_le_cofactor_sum_mul_prime_sum {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ∀ r, f r ≤ 1) :
    M x H f ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
      ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p := by
  classical
  apply (mass_le_remainder_sum hPH.le f hf).trans
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor, η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F, Prod.mk.injEq, RemainderDatum.mk.injEq, and_comm] using h
  have hsum : (∑ η ∈ basicRemainderFinset x H, remainderReciprocalWeight η) =
      ∑ z ∈ (basicRemainderFinset x H).image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image]
    · rfl
    · intro η _ ξ _ h
      exact hinj h
  rw [hsum]
  have hsubset : (basicRemainderFinset x H).image F ⊆
      Finset.Icc 1 (tailCofactorBound H) ×ˢ fullPrimeTuples x H := by
    intro z hz
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hz
    have hb := witness_cofactor_bound hs
      (extractTail_isWitness (mem_basicRemainderFinset.mp hη) hPH hHm)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hb, Finset.mem_image.mpr ⟨η, hη, rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ fullPrimeTuples x H,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro z _ _
      exact mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2)
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum, ← Finset.sum_mul]

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

/-- The fixed enlargement `C = 4` absorbs the unit-box errors once the
smallest retained scale is large. All constants are independent of dimension. -/
theorem basic_prime_box_enclosure {x : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam)
    (hL : 0 < L x H) {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) {v : Fin (L x H) → ℝ}
    (hdist : ∀ i, |primePrefixCoord η.primes i-v i| ≤ 1) :
    v ∈ enlargedSimplex (L x H) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hP : 1 ≤ P H := by
    by_contra hn
    have : P H=0 := by omega
    simp only [this, Nat.cast_zero, mul_zero] at hcut
    norm_num at hcut
  have hlower (i : Fin (L x H)) : 1 ≤ rho^(m x-(i.val+1))*v i := by
    apply cube_band_lower hs hcut
    · have := i.isLt; unfold L at this; omega
    · have hh := (hη.2.1 (i.val+1)
        (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)).2.1
      simpa only [remainderCoord_fin] using hh
    · exact hdist i
  have hv (i : Fin (L x H)) : 0 ≤ v i := by
    have hp := pow_pos rho_pos (m x-(i.val+1))
    have hh := hlower i
    by_contra hn
    have : rho^(m x-(i.val+1))*v i < 0 := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    linarith
  have herr (i : Fin (L x H)) :
      ((L x H-i.val : ℕ) : ℝ)^2+1 ≤
        (4*((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1)))*v i := by
    have hi := i.isLt
    have hn : 1 ≤ m x-(i.val+1) := by unfold L at hi; omega
    have hnR : (1 : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast hn
    have hh : ((L x H-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show L x H-i.val ≤ m x-(i.val+1) by unfold L; omega)
    have hsq : ((L x H-i.val : ℕ) : ℝ)^2 ≤ ((m x-(i.val+1) : ℕ) : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hh 2
    have he := mul_le_mul_of_nonneg_left (hlower i)
      (show 0 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have htop : (L x H : ℝ)^2 ≤ (4*(m x : ℝ)^2*rho^(m x))*B x := by
    have hmP : (P H : ℝ) ≤ m x := by exact_mod_cast hPm
    have hm4 : 4 ≤ lam*(m x : ℝ) := hcut.trans (mul_le_mul_of_nonneg_left hmP lam_pos.le)
    have hx := (div_le_div_iff₀ (mul_pos hB (pow_pos rho_pos _)) lam_pos).mp hscale
    have h1 : 1 ≤ B x*rho^(m x) := by nlinarith
    have hsq : (L x H : ℝ)^2 ≤ (m x : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le (m x) (P H)) 2
    have he := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4*(m x : ℝ)^2 by positivity)
    nlinarith
  have hh := enlargedSimplex_cube (basic_remainder_enlargedSimplex hL hη)
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual full prime tuples are controlled by one enlarged-simplex
volume, with the discrete cofactor kept separate. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma fullPrimeTuples_subset_grid (x : ℝ) (H : ℕ) :
    fullPrimeTuples x H ⊆ gridPrimeTuples (fullPrimeGrid x H) := by
  intro p hp
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
  have hbasic := mem_basicRemainderFinset.mp hη
  have hbands : primePrefixCoord η.primes ∈ prefixBandRegion x (P H) := by
    intro i
    have hi : i.val < L x H := by simpa only [R, L] using i.isLt
    have hh := (hbasic.2.1 (i.val+1)
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
    rw [remainderCoord_fin x η i] at hh
    exact hh
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (prefixBandRegion_covered x (P H) hbands)
  obtain ⟨hb, hc⟩ := Set.mem_iUnion.mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨hb, η.primes, ?_, hc⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨η, hη, rfl⟩
  · apply mem_primeBoxTuples_iff.mpr
    refine ⟨fun i => ?_, hc⟩
    have hh := (hbasic.2.1 (i.val+1)
      (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)).1
    simpa [remainderPrime, i.isLt] using hh

lemma fullPrimeGrid_enclosure {x : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < L x H) :
    gridRegion (fullPrimeGrid x H) ⊆ enlargedSimplex (L x H) (B x)
      (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  intro v hv
  obtain ⟨b, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb, hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_, p, hp, hu⟩ := Finset.mem_filter.mp hb
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
  exact basic_prime_box_enclosure hs hcut hB hscale hL
    (mem_basicRemainderFinset.mp hη) (unitGridCell_coordinate_distance hu hv)

lemma volume_zero_prefixRegion {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : 0 < N) :
    volume (prefixRegion N (B x) 0 0) = ENNReal.ofReal (G x N) := by
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, max_eq_left hB]
  rw [G, prod_fin_shifted N g]

theorem fullPrimeGrid_volume_bound {x : ℝ} {H : ℕ}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ)) (hB : 0 < B x)
    (hscale : (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam) (hL : 0 < L x H) :
    volume.real (gridRegion (fullPrimeGrid x H)) ≤
      Real.exp (simplexBoxTail 4 (P H))*G x (L x H) := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hj := reverse_enlargement_jacobian hPm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4)
  rw [← simplexBoxTail_eq_tsum] at hj
  have he : volume (gridRegion (fullPrimeGrid x H)) ≤
      ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) := by
    calc
      _ ≤ volume (enlargedSimplex (L x H) (B x) (β 0)
          (fun i => β (i.val+1))) := by
        apply measure_mono
        simpa only [β, Nat.sub_zero] using fullPrimeGrid_enclosure hs hcut hB hscale hL
      _ ≤ ENNReal.ofReal (∏ i : Fin (L x H), enlargementScale β i)*
          volume (prefixRegion (L x H) (B x) 0 0) :=
        volume_enlargedSimplex_product_bound (B x) β hβ
      _ ≤ ENNReal.ofReal (Real.exp (simplexBoxTail 4 (P H)))*
          volume (prefixRegion (L x H) (B x) 0 0) := by
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal hj) le_rfl
      _ = _ := by
        rw [volume_zero_prefixRegion hB.le hL, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (G_pos hB _).le))

/-- Full prime mass, before the independent smooth-cofactor sum. -/
theorem full_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ},
      0 ≤ theta x → 4 ≤ lam*(P H : ℝ) → 0 < B x →
      (m x : ℝ)/(B x*rho^(m x)) ≤ 2/lam → 0 < L x H →
      (∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (P H))*
          Real.exp (simplexBoxTail 4 (P H))*G x (L x H) := by
  obtain ⟨C, hC, hc⟩ := banded_grid_prime_mass_error hford
  refine ⟨C, hC, ?_⟩
  intro x H hs hcut hB hscale hL
  have hPm : P H ≤ m x := by unfold L at hL; omega
  have hh := hc hs (by norm_num : (0 : ℝ)<9/10) hPm (fullPrimeGrid x H) (by
    intro b hb i
    exact bandGrid_bounds (Finset.mem_filter.mp hb).1 i)
  change |gridPrimeMass (N := L x H) (fullPrimeGrid x H) -
    (volume (gridRegion (N := L x H) (fullPrimeGrid x H))).toReal| ≤
    (volume (gridRegion (N := L x H) (fullPrimeGrid x H))).toReal *
      bandPrimeError C (9/10) (P H) at hh
  have hnon : 0 ≤ 1+bandPrimeError C (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ)<9/10) (P H)]
  calc
    _ ≤ gridPrimeMass (fullPrimeGrid x H) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (fullPrimeTuples_subset_grid x H)
      intro p _ _
      exact reciprocalShiftWeight_nonneg p
    _ ≤ (1+bandPrimeError C (9/10) (P H))*volume.real (gridRegion (fullPrimeGrid x H)) := by
      have he := (le_abs_self _).trans hh
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at he
      change gridPrimeMass _ ≤ _*(volume (gridRegion _)).toReal
      calc
        _ ≤ (volume (gridRegion (fullPrimeGrid x H))).toReal +
            (volume (gridRegion (fullPrimeGrid x H))).toReal * bandPrimeError C (9/10) (P H) := by
          exact (sub_le_iff_le_add.mp he).trans_eq (add_comm _ _)
        _ = _ := by ring
    _ ≤ (1+bandPrimeError C (9/10) (P H))*
        (Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) :=
      mul_le_mul_of_nonneg_left (fullPrimeGrid_volume_bound hs hcut hB hscale hL) hnon
    _ = _ := by ring

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
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma fullPrimeFactor_tendsto (C : ℝ) {K : ℝ} (hK : 0 < K) :
    Tendsto (fullPrimeFactor C K) atTop (nhds 0) := by
  have hb := (bandPrimeError_tendsto C (by norm_num : (0 : ℝ)<9/10)).comp P_tendsto
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp
    ((simplexBoxTail_tendsto 4).comp P_tendsto)
  have hp := (summable_projectedEnvelope hK).tendsto_atTop_zero.comp P_tendsto
  have hh := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hb).mul he).mul hp
  change Tendsto (fun H => (1+bandPrimeError C (9/10) (P H))*
    Real.exp (simplexBoxTail 4 (P H))*projectedEnvelope K (P H)) atTop (nhds 0)
  simpa only [Function.comp_def, add_zero, Real.exp_zero, one_mul, mul_zero] using hh

/-- The manuscript's mass upper estimate, for every weight bounded above by
one. Its only inputs are the published prime-box, renewal, and Mertens bounds. -/
theorem mass_upper (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput)
    (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ f : ℝ → ℝ, (∀ r, f r ≤ 1) →
        M x H f ≤ C*Real.exp ((4*(lam/rho))*cofactorScale H)*G x (m x) := by
  obtain ⟨C, hC, hcof⟩ := tail_cofactor_sum hmertens
  obtain ⟨Cp, hCp, hp⟩ := full_prime_mass_bound hbox
  obtain ⟨K, hK, hproj⟩ := uniform_projected_volume_bound hren
  refine ⟨C, hC, ?_⟩
  have hcut : ∀ᶠ H : ℕ in atTop, 4 ≤ lam*(P H : ℝ) := by
    exact ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [eventually_ge_atTop 2, hcut,
    (fullPrimeFactor_tendsto Cp hK).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))]
      with H hH hcutH hfac
  have hPH := P_lt_self hH
  filter_upwards [theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)), inverse_scale_bound,
    hproj, m_tendsto.eventually (eventually_ge_atTop H)] with x hs hB hscale hpr hHm
  intro f hf
  have hL : 0 < L x H := by unfold L; omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hprime := hp hs.1 hcutH hB hscale hL
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hpr (P H) hPm)
  have hcof' : (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹) ≤
      C*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    have he : 4*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ =
        (4*(lam/rho))*cofactorScale H := by unfold cofactorScale; ring
    simpa only [he] using hcof H
  have hA : 0 ≤ (1+bandPrimeError Cp (9/10) (P H))*
      Real.exp (simplexBoxTail 4 (P H)) := mul_nonneg
    (by linarith [bandPrimeError_nonneg hCp.le (by norm_num : (0 : ℝ)<9/10) (P H)])
    (Real.exp_pos _).le
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p :=
      mass_le_cofactor_sum_mul_prime_sum hPH hHm hs f hf
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ∑ p ∈ fullPrimeTuples x H, reciprocalShiftWeight p :=
      mul_le_mul_of_nonneg_right hcof'
        (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError Cp (9/10) (P H))*
          Real.exp (simplexBoxTail 4 (P H))*G x (L x H)) :=
      mul_le_mul_of_nonneg_left hprime (by positivity)
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError Cp (9/10) (P H))*Real.exp (simplexBoxTail 4 (P H))*
          (projectedEnvelope K (P H)*G x (m x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG hA) (by positivity)
    _ = (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        (fullPrimeFactor Cp K H*G x (m x)) := by unfold fullPrimeFactor; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_of_le_one_left (G_pos hB _).le hfac.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleCounting
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

/-- The tuple fiber over a fixed tail is exactly the allowed largest-prime
interval. The prime number theorem is applied to this finite set later. -/
lemma tuple_fiber_card (x : ℝ) (H : ℕ) (t : ℝ) (ζ : PrefixDatum (R x H)) :
    ((tupleFinset x H t).filter (fun τ : TotientTuple (R x H) => τ.tail = ζ)).card =
      if IsPrefixDatum x H ζ then
        ((Finset.range (⌊t⌋₊+2)).filter (fun p : ℕ => p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧
          (tupleValue (TotientTuple.mk p ζ) : ℝ) ≤ t)).card
      else 0 := by
  classical
  by_cases hζ : IsPrefixDatum x H ζ
  · rw [ite_eq_left hζ]
    apply Finset.card_bij (fun τ _ => τ.head)
    · intro τ hτ
      obtain ⟨hτ, ht⟩ := Finset.mem_filter.mp hτ
      obtain ⟨hu, hb⟩ := Finset.mem_filter.mp hτ
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hu
      have hpr : τ.head ∈ Finset.range (⌊t⌋₊+2) := by
        rw [← he]
        exact (Finset.mem_product.mp hp).1
      exact Finset.mem_filter.mpr ⟨hpr, hb.1, hb.2.1, by simpa [← ht] using hb.2.2.2⟩
    · intro τ hτ σ hσ hh
      have ht := (Finset.mem_filter.mp hτ).2
      have hs := (Finset.mem_filter.mp hσ).2
      cases τ
      cases σ
      simp_all
    · intro p hp
      obtain ⟨hr, hprime, hlo, hval⟩ := Finset.mem_filter.mp hp
      refine ⟨⟨p, ζ⟩, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hprime, hlo, hζ, hval⟩
      exact Finset.mem_image.mpr ⟨(p, ζ), Finset.mem_product.mpr
        ⟨hr, mem_prefixDataFinset.mpr hζ⟩, rfl⟩
  · rw [ite_eq_right hζ]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro τ hτ
    obtain ⟨hτ, ht⟩ := Finset.mem_filter.mp hτ
    have hb := (Finset.mem_filter.mp hτ).2.2.2.1
    exact hζ (ht ▸ hb)

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

/-- The classical PNT is uniform over all denominators allowed by the
proved basic-witness size bound, at every fixed comparable endpoint. -/
theorem largest_prime_uniform_asymptotic (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t → t ≤ x →
      |(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)-t/(D*Real.log x)| ≤
        ε*(t/(D*Real.log x)) := by
  let δ := min (1/4 : ℝ) (ε/6)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδq : δ ≤ 1/4 := min_le_left _ _
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hpnt δ hδ)
  filter_upwards [small_denominator_window ha hδ hδq,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).eventually (eventually_ge_atTop Y),
    eventually_gt_atTop (1 : ℝ)] with x hx hYx hx1
  intro D t hD hlogD ht htx
  obtain ⟨hz, hzy, hy, hlo, hhi⟩ := hx D t hD hlogD ht htx
  have hp := hY (1+t/D) (hYx.trans (hz.trans hzy))
  have he := prime_count_change_scale (Real.log_pos hx1)
    (div_nonneg ((mul_pos ha (zero_lt_one.trans hx1)).trans_le ht).le (by linarith))
    hδ.le hδq ⟨hlo,hhi⟩ ⟨hzy,hy⟩ hp
  rw [div_div] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by dsimp [δ] <;> linarith [min_le_right (1/4 : ℝ) (ε/6)])
    (div_nonneg ((mul_pos ha (zero_lt_one.trans hx1)).trans_le ht).le
      (mul_nonneg (by linarith) (Real.log_pos hx1).le)))

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

lemma tuple_fiber_eq_shiftedPrimeSet {x t : ℝ} {H : ℕ}
    (hPH : P H ≤ H) (ht : 0 ≤ t) {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    ((tupleFinset x H t).filter (fun τ => τ.tail=ζ)).card =
      (shiftedPrimeSet x t (prefixDenominator ζ)).card := by
  rw [tuple_fiber_card, ite_eq_left hζ]
  congr 1
  ext p
  rw [Finset.mem_filter, mem_shiftedPrimeSet (D := prefixDenominator ζ) ht (basic_prefix_denominator_pos hPH hζ)]
  constructor
  · rintro ⟨_,hp,hlo,hv⟩
    exact ⟨hp,hlo,by simpa only [tupleValue_eq_head, prefixDenominator] using hv⟩
  · rintro ⟨hp,hlo,hv⟩
    have hb : IsBasicTuple x H t ⟨p,ζ⟩ := ⟨hp,hlo,hζ,by
      simpa only [tupleValue_eq_head, prefixDenominator] using hv⟩
    exact ⟨Finset.mem_range.mpr (basic_tuple_head_bound hPH hb), hp,hlo,hb.2.2.2⟩

lemma shiftedPrimeSet_cutoff_error {x : ℝ} (hx : 0 ≤ x) (t : ℝ) (D : ℕ) :
    |((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)| ≤
      x^(9/10 : ℝ)+1 := by
  let P := Nat.primesLE ⌊1+t/D⌋₊
  let E := P.filter (fun p : ℕ => ¬ x^(9/10 : ℝ) ≤ p)
  have he : E.card ≤ ⌊x^(9/10 : ℝ)⌋₊+1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊x^(9/10 : ℝ)⌋₊+1)) ?_).trans_eq
      (Finset.card_range _)
    intro p hp
    have ht := lt_of_not_ge (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ht.le))
  have hsplit : (shiftedPrimeSet x t D).card+E.card = Nat.primeCounting ⌊1+t/D⌋₊ := by
    simpa only [P, E, shiftedPrimeSet, Nat.primesLE_card_eq_primeCounting] using
      Finset.card_filter_add_card_filter_not (s := P) (fun p : ℕ => x^(9/10 : ℝ) ≤ p)
  have hsplitR := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  push_cast at hsplitR
  rw [show ((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ) = -(E.card : ℝ) by linarith,
    abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  have hf : (⌊x^(9/10 : ℝ)⌋₊ : ℝ) ≤ x^(9/10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx _)
  exact (by exact_mod_cast he : (E.card : ℝ) ≤ (⌊x^(9/10 : ℝ)⌋₊ : ℝ)+1).trans (by linarith)

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

/-- Complete largest-prime asymptotic, with the manuscript's lower cutoff. -/
theorem shifted_prime_uniform_asymptotic (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D : ℕ, 0 < D →
      Real.log (D : ℝ) ≤ (Real.log x)^(4/5 : ℝ) → ∀ t : ℝ, a*x ≤ t → t ≤ x →
      |((shiftedPrimeSet x t D).card : ℝ)-t/(D*Real.log x)| ≤ ε*(t/(D*Real.log x)) := by
  filter_upwards [largest_prime_uniform_asymptotic hpnt ha (show 0 < ε/2 by positivity),
    lower_prime_cutoff_negligible ha (show 0 < ε/2 by positivity), eventually_gt_atTop (1 : ℝ)]
    with x hp hc hx
  intro D hD hlogD t ht htx
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  calc
    _ ≤ |((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)|+
        |(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)-t/(D*Real.log x)| := abs_sub_le _ _ _
    _ ≤ (ε/2)*(t/(D*Real.log x))+(ε/2)*(t/(D*Real.log x)) :=
      add_le_add ((shiftedPrimeSet_cutoff_error (zero_lt_one.trans hx).le t D).trans
        (hc D t hD1 hlogD ht)) (hp D t hD1 hlogD ht htx)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleMassApproximation
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Largest-prime summation over the actual finite tuple set, with all weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma weightedTupleCount_eq_fibers {x t : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (f : ℝ → ℝ) :
    weightedTupleCount x H t f = ∑ ζ ∈ prefixDataFinset x H,
      f ((ell ζ.d : ℝ)/ζ.d)*((tupleFinset x H t).filter (fun τ => τ.tail=ζ)).card := by
  have hmap : ∀ τ ∈ tupleFinset x H t, τ.tail ∈ prefixDataFinset x H := by
    intro τ hτ
    exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp hτ).2.2.1
  have he := Finset.sum_fiberwise_of_maps_to' hmap
    (fun ζ : PrefixDatum (R x H) => f ((ell ζ.d : ℝ)/ζ.d))
  rw [weightedTupleCount, ← he]
  apply Finset.sum_congr rfl
  intro ζ _
  simp [mul_comm]

/-- Relative error in largest-prime summation, uniformly over all bounded
weights and all endpoints in a fixed interval `[a*x,x]`. -/
theorem weighted_tuple_mass_relative (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, a*x ≤ t → t ≤ x →
      ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |weightedTupleCount x H t f-(t/Real.log x)*M x H f| ≤
        ε*(t/Real.log x)*M x H (fun _ => 1) := by
  filter_upwards [shifted_prime_uniform_asymptotic hpnt ha hε,
    basic_prefix_denominator_log_small hPH hP, eventually_gt_atTop (1 : ℝ)] with x hp hs hx
  intro t ht htx f hf
  have ht0 : 0 < t := (mul_pos ha (zero_lt_one.trans hx)).trans_le ht
  rw [weightedTupleCount_eq_fibers hPH.le, mass_eq_sum_prefixData, mass_eq_sum_prefixData,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro ζ hζ
  have hz := mem_prefixDataFinset.mp hζ
  rw [tuple_fiber_eq_shiftedPrimeSet hPH.le ht0.le hz]
  have hD := basic_prefix_denominator_pos hPH.le hz
  have hc := hp (prefixDenominator ζ) hD (hs ζ hz) t ht htx
  have hD0 : (prefixDenominator ζ : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hden : (ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ) = prefixDenominator ζ := by
    simp only [prefixDenominator, Nat.cast_mul, Nat.cast_prod]
  rw [hden]
  have he : f ((ell ζ.d : ℝ)/ζ.d)*(↑(shiftedPrimeSet x t (prefixDenominator ζ)).card : ℝ)-
      t/Real.log x*(f ((ell ζ.d : ℝ)/ζ.d)/(prefixDenominator ζ : ℝ)) =
      f ((ell ζ.d : ℝ)/ζ.d)*((↑(shiftedPrimeSet x t (prefixDenominator ζ)).card : ℝ)-
        t/((prefixDenominator ζ : ℝ)*Real.log x)) := by ring
  rw [he, abs_mul, abs_of_nonneg (hf _).1]
  calc
    _ ≤ f ((ell ζ.d : ℝ)/ζ.d)*(ε*(t/((prefixDenominator ζ : ℝ)*Real.log x))) :=
      mul_le_mul_of_nonneg_left hc (hf _).1
    _ ≤ ε*(t/((prefixDenominator ζ : ℝ)*Real.log x)) :=
      mul_le_of_le_one_left
        (mul_nonneg hε.le (div_nonneg ht0.le (mul_nonneg
          (Nat.cast_nonneg _) (Real.log_pos hx).le))) (hf _).2
    _ = _ := by field_simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TupleCoefficient
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tuple count approximates the finite arithmetic coefficient. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma tupleNormalization_pos {x : ℝ} (hx : 1 < x) (hB : 0 < B x) :
    0 < tupleNormalization x :=
  mul_pos (div_pos (zero_lt_one.trans hx) (Real.log_pos hx)) (G_pos hB _)

/-- The largest-prime summation error tends to zero for each fixed cutoff,
uniformly over all bounded weights and all comparable endpoints. -/
theorem tuple_mass_normalized_approximation_oai (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ H : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      ∀ t : ℝ, a*x ≤ t → t ≤ x → ∀ f : ℝ → ℝ, (∀ r, 0 ≤ f r ∧ f r ≤ 1) →
      |weightedTupleCount x H t f/tupleNormalization x-(t/x)*(M x H f/G x (m x))| ≤ ε := by
  obtain ⟨C,hC,hupper⟩ := mass_upper hbox hren hmertens
  filter_upwards [hupper, eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hH hH2 hP
  let C₀ := C*Real.exp ((4*(lam/rho))*cofactorScale H)
  have hC₀ : 0 < C₀ := mul_pos hC (Real.exp_pos _)
  intro ε hε
  filter_upwards [weighted_tuple_mass_relative hpnt ha (P_lt_self hH2) hP (div_pos hε hC₀),
    hH, eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x herr hmass hx hB
  intro t ht htx f hf
  have hnorm := tupleNormalization_pos hx hB
  have hG := G_pos hB (m x)
  have ht0 : 0 < t := (mul_pos ha (zero_lt_one.trans hx)).trans_le ht
  have hlog := Real.log_pos hx
  have heq : weightedTupleCount x H t f/tupleNormalization x-(t/x)*(M x H f/G x (m x)) =
      (weightedTupleCount x H t f-(t/Real.log x)*M x H f)/tupleNormalization x := by
    unfold tupleNormalization
    field_simp
  rw [heq, abs_div, abs_of_pos hnorm]
  apply (div_le_iff₀ hnorm).mpr
  apply (herr t ht htx f hf).trans
  have hm : M x H (fun _ => 1) ≤ C₀*G x (m x) := hmass _ (fun _ => le_rfl)
  calc
    (ε/C₀)*(t/Real.log x)*M x H (fun _ => 1) ≤
        (ε/C₀)*(t/Real.log x)*(C₀*G x (m x)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = ε*(t/Real.log x)*G x (m x) := by field_simp
    _ ≤ ε*tupleNormalization x := by
      unfold tupleNormalization
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htx hlog.le) hε.le) hG.le

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.tuple_mass_normalized_approximation_oai := @OAI.TotientAsymptotic.tuple_mass_normalized_approximation_oai
