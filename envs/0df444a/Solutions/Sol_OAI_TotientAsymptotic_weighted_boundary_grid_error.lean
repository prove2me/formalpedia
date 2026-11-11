-- Prove2me | solution 1 for OAI.TotientAsymptotic.weighted_boundary_grid_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:40:43.440752+00:00
-- url     : https://prove2.me/submissions/a7d6fc06-e1bd-4970-a946-7d03a3ffb759

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

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

lemma tailLog_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) {l : ℕ} (hl : l ∈ Finset.Ico (P H) H) :
    0 ≤ tailLog η l := by
  have hr := rho_pos
  exact (by have := alpha_pos s; positivity :
    (0 : ℝ) ≤ (9/10 : ℝ) * alpha s * l * (rho^l)⁻¹).trans (hη.2.2.1 l hl).2.1


open MeasureTheory ProbabilityTheory
open scoped Classical

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

lemma tail_reciprocal_majorant {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) :
    ((w η).totient : ℝ)⁻¹ ≤ (η.cofactor.totient : ℝ)⁻¹ *
      ∏ h ∈ Finset.Ico (P H) H, (tailPrime η h-1 : ℝ)⁻¹ := by
  exact reciprocal_totient_prime_product _ _ _ hη.2.1
    (fun h hh => (hη.2.2.1 h hh).1)

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_SimplexShell
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma pow_sub_positivePart_le {T w : ℝ} (hT : 0 ≤ T) (hw : 0 ≤ w) (N : ℕ) :
    T^N-(max (T-w) 0)^N ≤ w*N*T^(N-1) := by
  have hb0 : 0 ≤ max (T-w) 0 := le_max_right _ _
  have hbT : max (T-w) 0 ≤ T := max_le (by linarith) hT
  have hdiff : 0 ≤ T^N-(max (T-w) 0)^N :=
    sub_nonneg.mpr (pow_le_pow_left₀ hb0 hbT N)
  have hh := abs_pow_sub_pow_le (a := T) (b := max (T-w) 0) (n := N)
  rw [abs_of_nonneg hdiff, abs_of_nonneg (sub_nonneg.mpr hbT),
    abs_of_nonneg hT, abs_of_nonneg hb0, max_eq_left hbT] at hh
  apply hh.trans
  have hgap : T-max (T-w) 0 ≤ w := by linarith [le_max_left (T-w) 0]
  gcongr

lemma weighted_raiseThreshold {N : ℕ} (C : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    (∑ j, g (j.val+1)*raiseThreshold C i t j) =
      (∑ j, g (j.val+1)*C j)+g (i.val+1)*t := by
  classical
  have he (j : Fin N) : g (j.val+1)*raiseThreshold C i t j =
      g (j.val+1)*C j + if j=i then g (i.val+1)*t else 0 := by
    by_cases hji : j=i
    · subst j
      simp [raiseThreshold, mul_add]
    · simp [raiseThreshold, hji]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

lemma raised_region_subset {N : ℕ} (B C₀ : ℝ) (C : Fin N → ℝ)
    (i : Fin N) {t : ℝ} (ht : 0 ≤ t) :
    prefixRegion N B C₀ (raiseThreshold C i t) ⊆ prefixRegion N B C₀ C := by
  intro u hu
  refine ⟨fun j => ?_, hu.2⟩
  have hj := hu.1 j
  by_cases hji : j=i
  · subst j
    simp only [raiseThreshold, Function.update_self] at hj
    linarith
  · simpa [raiseThreshold, hji] using hj

lemma measurableSet_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasurableSet (prefixRegion N B C₀ C) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable (measurableSet_weightedSimplex _ _)

/-- Removing a band of thickness `t` in one slack coordinate loses at most
its slice coefficient times `t`. This holds with every fixed tail threshold. -/
theorem prefix_slack_shell_bound {N : ℕ} (hN : 0 < N)
    (B C₀ : ℝ) (C : Fin N → ℝ) (i : Fin N) {t : ℝ} (ht : 0 ≤ t)
    (hT : 0 ≤ B-C₀-∑ j, g (j.val+1)*C j) :
    (volume (prefixRegion N B C₀ C \ prefixRegion N B C₀ (raiseThreshold C i t))).toReal ≤
      (t*N*g (i.val+1)*(B-C₀-∑ j, g (j.val+1)*C j)^(N-1)) /
        ((N.factorial : ℝ)*∏ j : Fin N, g (j.val+1)) := by
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  have hfinite : volume (prefixRegion N B C₀ C) ≠ ⊤ := by
    rw [volume_prefixRegion_explicit _ hN]
    exact ENNReal.ofReal_ne_top
  change volume.real _ ≤ _
  rw [measureReal_sdiff (raised_region_subset B C₀ C i ht)
    (measurableSet_prefixRegion _ _ _ _) hfinite]
  change (volume (prefixRegion N B C₀ C)).toReal-
    (volume (prefixRegion N B C₀ (raiseThreshold C i t))).toReal ≤ _
  rw [volume_prefixRegion_explicit _ hN, volume_prefixRegion_explicit _ hN,
    weighted_raiseThreshold, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), max_eq_left hT, ← sub_div]
  apply (div_le_div_iff_of_pos_right hden).mpr
  have hh := pow_sub_positivePart_le hT (mul_nonneg (g_pos (i.val+1)).le ht) N
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (ring_nf)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixRelaxation
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
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

lemma xi_sub_one_pos (x : ℝ) (i : ℕ) : 0 < xi x i-1 := by
  dsimp [xi]
  have := Real.exp_pos (-((m x-i : ℕ) : ℝ)/40)
  linarith

lemma bandScale_nonneg (x : ℝ) (i : ℕ) : 0 ≤ bandScale x i := by
  unfold bandScale
  exact mul_nonneg (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _))
    (inv_nonneg.mpr (pow_nonneg rho_pos.le _))

lemma topPerturbation_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ topPerturbation x :=
  mul_nonneg (xi_sub_one_pos _ _).le hB

lemma banded_tailRegion_subset_perturbed {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hB : 0 ≤ B x) :
    tailPrefixRegion x H η ∩ prefixBandRegion x H ⊆ perturbedTailPrefixRegion x H η := by
  rintro u ⟨hu, hb⟩
  constructor
  · intro i
    have h0 : 0 ≤ u i :=
      (mul_nonneg (by norm_num) (bandScale_nonneg x (i.val+1))).trans (hb i).1
    exact (hu.1 i).trans (le_add_of_nonneg_right (mul_nonneg (xi_sub_one_pos _ _).le h0))
  · have hh := hu.2
    have he : B x ≤ xi x 0*B x := by nlinarith [xi_sub_one_pos x 0]
    linarith

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailArray
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The discrete tail, in the coordinate order used by the full simplex. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tailVector_nonneg {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) : 0 ≤ tailVector η i := by
  apply tailLog_nonneg hη
  apply Finset.mem_Ico.mpr
  have := i.isLt
  omega

lemma D_eq_tailVector_sum {H : ℕ} (η : TailDatum H) (hPH : P H ≤ H) (h : ℕ) :
    D h η = ∑ i : Fin (H-P H), a (h-(H-1-i.val))*tailVector η i := by
  unfold D
  apply Finset.sum_bij (fun l hl => (⟨H-1-l, by
    have := Finset.mem_Ico.mp hl
    omega⟩ : Fin (H-P H)))
  · intro l hl
    exact Finset.mem_univ _
  · intro l hl k hk he
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · intro i _
    have hi := i.isLt
    refine ⟨H-1-i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp only
    omega
  · intro l hl
    have := Finset.mem_Ico.mp hl
    dsimp only [tailVector]
    have he : H-1-(H-1-l)=l := by omega
    rw [he]

lemma tailVector_row {H : ℕ} (η : TailDatum H) (i : Fin (H-P H)) :
    (∑ j : Fin (H-P H), if i < j then a (j.val-i.val)*tailVector η j else 0) =
      ∑ l ∈ Finset.Ico (P H) (H-1-i.val), a (H-1-i.val-l)*tailLog η l := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => H-1-j.val)
  · intro j hj
    have hj' : i < j := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hjb := j.isLt
    exact Finset.mem_Ico.mpr (by simp only [Fin.lt_def] at hj'; omega)
  · intro j hj k hk he
    apply Fin.ext
    have := j.isLt
    have := k.isLt
    omega
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    refine ⟨⟨H-1-l, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change i.val < H-1-l
      omega
    · simp only
      omega
  · intro j hj
    have hij : i < j := (Finset.mem_filter.mp hj).2
    have hi := i.isLt
    have hjb := j.isLt
    dsimp only [tailVector]
    congr 2
    simp only [Fin.lt_def] at hij
    omega

lemma tailVector_simplex {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) :
    (∑ j : Fin (H-P H), if i < j then a (j.val-i.val)*tailVector η j else 0) ≤
      (1+(1/10000 : ℝ)*Real.exp (-((H-1-i.val : ℕ) : ℝ)/40))*tailVector η i := by
  rw [tailVector_row]
  have hi : H-1-i.val ∈ Finset.Ico (P H) H := by
    have := i.isLt
    exact Finset.mem_Ico.mpr (by omega)
  exact (hη.2.2.1 _ hi).2.2.2

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

lemma mem_gridPrimeTuples_iff {N : ℕ} {K : Finset (Fin N → ℕ)} {p : Fin N → ℕ} :
    p ∈ gridPrimeTuples K ↔ (∀ i, (p i).Prime) ∧ primePrefixCoord p ∈ gridRegion K := by
  simp only [gridPrimeTuples, Finset.mem_biUnion, mem_primeBoxTuples_iff,
    gridRegion, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm, hp, hu⟩
    exact ⟨hp, m, hm, hu⟩
  · rintro ⟨hp, m, hm, hu⟩
    exact ⟨m, hm, hp, hu⟩

lemma gridInner_subset_outer {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    gridInner K S ⊆ gridOuter K S := by
  intro m hm
  obtain ⟨hm, hs⟩ := Finset.mem_filter.mp hm
  have hc : (fun i => (m i : ℝ)-1) ∈ unitGridCell m := by
    intro i _
    constructor <;> linarith
  exact Finset.mem_filter.mpr ⟨hm, _, hc, hs hc⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBoxAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Aggregate all discrete tails in a box before measuring the continuous
prefix. No factor counting the number of tail witnesses occurs. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma volume_tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (hU : ∀ b ∈ K, MeasurableSet (U b)) :
    volume (tailBoxLift K U) = ∑ b ∈ K, volume (U b) := by
  unfold tailBoxLift
  rw [measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Measure.volume_eq_prod, Measure.prod_prod, volume_unitGridCell, mul_one]
  · intro b _ c _ hbc
    exact Set.disjoint_left.mpr (fun z hz hw =>
      Set.disjoint_left.mp (unitGridCell_disjoint hbc) hz.2 hw.2)
  · intro b hb
    exact (hU b hb).prod (measurableSet_unitGridCell b)

lemma volumeReal_tailBoxLift {R T : ℕ} (K : Finset (Fin T → ℕ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (hU : ∀ b ∈ K, MeasurableSet (U b)) (hfin : ∀ b ∈ K, volume (U b) ≠ ⊤) :
    volume.real (tailBoxLift K U) = ∑ b ∈ K, volume.real (U b) := by
  simp only [measureReal_def, volume_tailBoxLift K U hU, ENNReal.toReal_sum hfin]

/-- A common prefix envelope for every tail in one unit box costs only the
reciprocal prime mass of that box. Summing disjoint tail boxes then gives
one full-dimensional volume. -/
theorem tail_box_aggregation {R T : ℕ} (K : Finset (Fin T → ℕ))
    (S : (Fin T → ℕ) → Set (Fin R → ℝ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ)) (C : ℝ)
    (hU : ∀ b ∈ K, MeasurableSet (U b)) (hfin : ∀ b ∈ K, volume (U b) ≠ ⊤)
    (hsub : ∀ b ∈ K, ∀ p ∈ primeBoxTuples b, S p ⊆ U b)
    (hmass : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C) :
    (∑ p ∈ gridPrimeTuples K, reciprocalShiftWeight p * volume.real (S p)) ≤
      C * volume.real (tailBoxLift K U) := by
  classical
  rw [gridPrimeTuples, Finset.sum_biUnion
    (fun b _ c _ hbc => primeBoxTuples_disjoint hbc),
    volumeReal_tailBoxLift K U hU hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  calc
    _ ≤ ∑ p ∈ primeBoxTuples b, reciprocalShiftWeight p * volume.real (U b) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (measureReal_mono (hsub b hb p hp) (hfin b hb))
        (reciprocalShiftWeight_nonneg p)
    _ = (∏ i, unitPrimeWeight (b i))*volume.real (U b) := by
      rw [← Finset.sum_mul, prime_box_mass]
    _ ≤ C*volume.real (U b) := mul_le_mul_of_nonneg_right (hmass b hb) measureReal_nonneg

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailBoxCoordinates
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prefix-times-tail-box measure is the usual full-coordinate volume. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma joinCoordinates_left {R T : ℕ} (u : (Fin R → ℝ) × (Fin T → ℝ)) (i : Fin R) :
    joinCoordinates R T u (Fin.castAdd T i) = u.1 i := by
  simp [joinCoordinates, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, finSumFinEquiv]
  rfl

lemma joinCoordinates_right {R T : ℕ} (u : (Fin R → ℝ) × (Fin T → ℝ)) (i : Fin T) :
    joinCoordinates R T u (Fin.natAdd R i) = u.2 i := by
  simp [joinCoordinates, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, finSumFinEquiv]
  rfl

lemma joinCoordinates_preserves_volume (R T : ℕ) :
    MeasurePreserving (joinCoordinates R T) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (R+T) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin R ⊕ Fin T => ℝ))

lemma volume_joinCoordinates_image {R T : ℕ}
    (S : Set ((Fin R → ℝ) × (Fin T → ℝ))) :
    volume (joinCoordinates R T '' S) = volume S := by
  have hh := (joinCoordinates_preserves_volume R T).measure_preimage_equiv
    (joinCoordinates R T '' S)
  rw [Set.preimage_image_eq S (joinCoordinates R T).injective] at hh
  exact hh.symm

/-- A full-dimensional enclosure bounds the aggregated weighted prefix
volumes without multiplying by the number of tail witnesses. -/
theorem tail_box_aggregation_enclosure {R T : ℕ} (K : Finset (Fin T → ℕ))
    (S : (Fin T → ℕ) → Set (Fin R → ℝ))
    (U : (Fin T → ℕ) → Set (Fin R → ℝ))
    (W : Set (Fin (R+T) → ℝ)) (C : ℝ)
    (hC : 0 ≤ C) (hU : ∀ b ∈ K, MeasurableSet (U b))
    (hfin : volume W ≠ ⊤)
    (hsub : ∀ b ∈ K, ∀ p ∈ primeBoxTuples b, S p ⊆ U b)
    (hmass : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C)
    (henclose : joinCoordinates R T '' tailBoxLift K U ⊆ W) :
    (∑ p ∈ gridPrimeTuples K, reciprocalShiftWeight p * volume.real (S p)) ≤
      C * volume.real W := by
  have hmeasure : volume (tailBoxLift K U) ≤ volume W := by
    rw [← volume_joinCoordinates_image]
    exact measure_mono henclose
  have hUfin (b) (hb : b ∈ K) : volume (U b) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfin
    apply le_trans _ hmeasure
    have hh : U b ×ˢ unitGridCell b ⊆ tailBoxLift K U := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hz⟩⟩
    have hm : volume (U b ×ˢ unitGridCell b) ≤ volume (tailBoxLift K U) := measure_mono hh
    simpa only [Measure.volume_eq_prod, Measure.prod_prod, volume_unitGridCell, mul_one] using hm
  exact (tail_box_aggregation K S U C hU hUfin hsub hmass).trans
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfin hmeasure) hC)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PrefixLower
attribute [-instance] _root_.OAI.TotientAsymptotic.expOne_probability _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagating the first discrete tail coordinate through the prefix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The renewal recurrence propagates any terminal lower bound through the
triangular prefix inequalities. This includes the first discrete tail prime. -/
theorem renewal_prefix_lower (N : ℕ) (u : ℕ → ℝ)
    (hs : ∀ i < N, (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*u j) ≤ u i)
    {i : ℕ} (hi : i ≤ N) : g (N-i)*u N ≤ u i := by
  have hmain : ∀ d : ℕ, ∀ j : ℕ, j+d=N → g d*u N ≤ u j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj
      by_cases hd : d = 0
      · subst d
        have hjN : j = N := by omega
        simp [hjN, g]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have hrec := g_convolution hdpos
        calc
          g d*u N = ∑ r ∈ Finset.range d, a (d-r)*(g r*u N) := by
            rw [hrec, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ ≤ ∑ r ∈ Finset.range d, a (d-r)*u (N-r) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrd := Finset.mem_range.mp hr
            apply mul_le_mul_of_nonneg_left
              (ih r hrd (N-r) (by omega)) (a_pos (by omega)).le
          _ = ∑ k ∈ Finset.Icc (j+1) N, a (k-j)*u k := by
            apply Finset.sum_bij (fun r _ => N-r)
            · intro r hr
              have := Finset.mem_range.mp hr
              exact Finset.mem_Icc.mpr (by omega)
            · intro r hr s hs hrs
              have := Finset.mem_range.mp hr
              have := Finset.mem_range.mp hs
              omega
            · intro k hk
              have := Finset.mem_Icc.mp hk
              exact ⟨N-k, Finset.mem_range.mpr (by omega), by omega⟩
            · intro r hr
              have := Finset.mem_range.mp hr
              congr 2
              omega
          _ ≤ u j := hs j (by omega)
  exact hmain (N-i) i (Nat.add_sub_of_le hi)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RegionLower
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A terminal tail prime forces lower bounds throughout the actual witness region. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma prefixLinear_terminal_lower {N : ℕ} (u : Fin N → ℝ) (T : ℝ)
    (hu : ∀ i, a (N-i.val)*T ≤ prefixLinear N u i) :
    ∀ i, g (N-i.val)*T ≤ u i := by
  let v : ℕ → ℝ := fun j => if hj : j < N then u ⟨j, hj⟩ else T
  have hv (j : ℕ) (hj : j < N) : v j = u ⟨j, hj⟩ := by simp [v, hj]
  have hvN : v N = T := by simp [v]
  have hslack (i : ℕ) (hi : i < N) :
      (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) ≤ v i := by
    let i' : Fin N := ⟨i, hi⟩
    have hh := hu i'
    rw [prefixLinear_apply] at hh
    have hsum : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
        ∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j := by
      have heq : (∑ j : Fin N, if i' < j then a (j.val-i'.val)*u j else 0) =
          ∑ j : Fin N, if i < j.val then a (j.val-i)*v j.val else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        change (if i < j.val then a (j.val-i)*u j else 0) = _
        rw [hv j.val j.isLt]
      rw [heq, Fin.sum_univ_eq_sum_range
        (fun k => if i < k then a (k-i)*v k else 0), ← Finset.sum_filter]
      have he : (Finset.range N).filter (fun j => i < j) = Finset.Icc (i+1) (N-1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        omega
      rw [he]
    rw [hsum] at hh
    have hsplit : (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*v j) =
        (∑ j ∈ Finset.Icc (i+1) (N-1), a (j-i)*v j)+a (N-i)*T := by
      have hN : N-1+1=N := by omega
      rw [← hN, Finset.sum_Icc_succ_top (by omega : i+1 ≤ N-1+1), hN, hvN]
    rw [hsplit, hv i hi]
    change a (N-i)*T ≤ u ⟨i, hi⟩ - _ at hh
    linarith
  intro i
  simpa only [hvN, hv i.val i.isLt] using
    (renewal_prefix_lower N v hslack (Nat.le_of_lt i.isLt))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_JoinedSimplex
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-dimensional completion of a continuous prefix by its discrete tail. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma joined_prefix_row {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) (i : Fin R) :
    (∑ j : Fin (R+T), if Fin.castAdd T i < j then
      a (j.val-i.val)*joinCoordinates R T (u,v) j else 0) =
    (∑ j : Fin R, if i < j then a (j.val-i.val)*u j else 0) +
      ∑ j : Fin T, a (R+j.val-i.val)*v j := by
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.lt_def, Fin.val_castAdd, joinCoordinates_left]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ite_eq_left (by simp [Fin.lt_def]; omega), joinCoordinates_right]
    rfl

lemma joined_tail_row {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) (i : Fin T) :
    (∑ j : Fin (R+T), if Fin.natAdd R i < j then
      a (j.val-(R+i.val))*joinCoordinates R T (u,v) j else 0) =
    ∑ j : Fin T, if i < j then a (j.val-i.val)*v j else 0 := by
  rw [Fin.sum_univ_add]
  have hz : (∑ j : Fin R, if Fin.natAdd R i < Fin.castAdd T j then
      a ((Fin.castAdd T j).val-(R+i.val))*joinCoordinates R T (u,v) (Fin.castAdd T j) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by simp [Fin.lt_def]; omega)]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.natAdd_lt_natAdd_iff, Fin.val_natAdd, Nat.add_sub_add_left,
    joinCoordinates_right]

lemma joined_budget {R T : ℕ} (u : Fin R → ℝ) (v : Fin T → ℝ) :
    (∑ j : Fin (R+T), a (j.val+1)*joinCoordinates R T (u,v) j) =
      (∑ j : Fin R, a (j.val+1)*u j) + ∑ j : Fin T, a (R+j.val+1)*v j := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd, joinCoordinates_left, joinCoordinates_right]

lemma prefix_D_tailVector {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) (i : Fin (R x H)) :
    D (m x-(i.val+1)) η =
      ∑ j : Fin (H-P H), a (R x H+j.val-i.val)*tailVector η j := by
  rw [D_eq_tailVector_sum η hPH]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have hi := i.isLt
  have hj := j.isLt
  unfold R at *
  omega

lemma top_D_tailVector {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) :
    D (m x) η = ∑ j : Fin (H-P H), a (R x H+j.val+1)*tailVector η j := by
  rw [D_eq_tailVector_sum η hPH]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have hj := j.isLt
  unfold R
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ShellCost
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous summation of the unit-box slack-shell costs. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma uniform_slice_bound (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ i ≤ m x,
      (m x : ℝ)*g i/B x ≤ C*rho^(m x-i) := by
  obtain ⟨_, K, hK, hg⟩ := normalizedRenewal_properties hford
  let C := 2*(K+1)/lam
  refine ⟨C, div_pos (mul_pos (by norm_num) (by linarith)) lam_pos, ?_⟩
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro i hi
  have hgn : g i*rho^i ≤ K+1 := by
    have hh := hg i
    change |g i*rho^i| ≤ K at hh
    exact (le_abs_self _).trans (hh.trans (by linarith))
  have hg' : g i ≤ (K+1)/rho^i := (le_div_iff₀ (pow_pos rho_pos _)).mpr hgn
  have hpow : rho^i*rho^(m x-i) = rho^(m x) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  calc
    _ ≤ (m x : ℝ)*((K+1)/rho^i)/B x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg' (Nat.cast_nonneg _)) hB.le
    _ = ((K+1)*((m x : ℝ)/(B x*rho^(m x))))*rho^(m x-i) := by
      rw [← hpow]
      field_simp [rho_pos.ne']
    _ ≤ ((K+1)*(2/lam))*rho^(m x-i) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by linarith))
        (pow_nonneg rho_pos.le _)
    _ = C*rho^(m x-i) := by dsimp [C] <;> ring

lemma sum_reverse_prefix {m H : ℕ} (hHm : H ≤ m) (f : ℕ → ℝ) :
    (∑ i : Fin (m-H), f (m-(i.val+1))) =
      ∑ j ∈ Finset.range (m-H), f (H+j) := by
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

lemma quadraticShellTail_tendsto : Tendsto quadraticShellTail atTop (nhds 0) := by
  change Tendsto (fun H => ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)) atTop (nhds 0)
  simpa only [Nat.add_comm] using
    (_root_.tendsto_sum_nat_add (fun n : ℕ => (n : ℝ)^2*rho^n))

/-- Summing the slice bounds for all unit-box boundary errors has a vanishing
tail uniform in the moving dimension and phase. -/
theorem prefix_cube_shell_cost (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x * (∑ i : Fin (R x H),
        g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) ≤ C*quadraticShellTail H := by
  obtain ⟨C, hC, hslice⟩ := uniform_slice_bound hford
  refine ⟨C, hC, ?_⟩
  filter_upwards [hslice, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx hB
  intro H hHm
  have hg : Summable (fun n : ℕ => (n : ℝ)^2*rho^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hterm (i : Fin (R x H)) :
      (R x H : ℝ)/B x*(g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) ≤
        C*(((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1))) := by
    have hi : i.val+1 ≤ m x := by have := i.isLt; unfold R at *; omega
    have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
    have hs : (R x H : ℝ)*g (i.val+1)/B x ≤ C*rho^(m x-(i.val+1)) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRm (g_pos _).le) hB.le).trans
        (hx (i.val+1) hi)
    calc
      _ = ((R x H : ℝ)*g (i.val+1)/B x)*((m x-(i.val+1) : ℕ) : ℝ)^2 := by ring
      _ ≤ (C*rho^(m x-(i.val+1)))*((m x-(i.val+1) : ℕ) : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = _ := by ring
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hC.le
  change (∑ i : Fin (m x-H), ((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1))) ≤
    ∑' n : ℕ, ((H+n : ℕ) : ℝ)^2*rho^(H+n)
  rw [sum_reverse_prefix hHm (fun n => (n : ℝ)^2*rho^n)]
  exact (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum _
    (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))

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

lemma cofactor_quadraticShellTail_tendsto (C : ℝ) :
    Tendsto (fun H => Real.exp (C*cofactorScale H)*quadraticShellTail H)
      atTop (nhds 0) :=
  cofactor_polynomialGeometricTail_tendsto C 2 rho_pos.le rho_lt_one

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PerturbationCost
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of all prefix perturbations, uniformly in dimension and phase. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma exp_shell_power (h : ℕ) :
    (Real.exp (-1/40))^h = Real.exp (-(h : ℝ)/40) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma exponentialShellTail_nonneg (H : ℕ) : 0 ≤ exponentialShellTail H :=
  polynomialGeometricTail_nonneg 1 (Real.exp_pos _).le H

lemma exponentialShell_summable : Summable (fun h : ℕ => (h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
  have hr : ‖Real.exp (-1/40)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  simpa only [pow_one, exp_shell_power] using
    summable_pow_mul_geometric_of_norm_lt_one 1 hr

lemma exponentialShellTail_term {H h : ℕ} (hh : H ≤ h) :
    (h : ℝ)*Real.exp (-(h : ℝ)/40) ≤ exponentialShellTail H := by
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)*Real.exp (-((H+n : ℕ) : ℝ)/40)) :=
    exponentialShell_summable.comp_injective (fun n m (he : H+n=H+m) => by omega)
  have hb := hs.sum_le_tsum {h-H} (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  simpa only [Finset.sum_singleton, Nat.add_sub_of_le hh, exponentialShellTail,
    polynomialGeometricTail, pow_one, exp_shell_power] using hb

lemma sum_prefix_exponentialShell {x : ℝ} {H : ℕ} (hHm : H ≤ m x) :
    (∑ i : Fin (R x H), ((m x-(i.val+1) : ℕ) : ℝ)*
      Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) ≤ exponentialShellTail H := by
  unfold R
  rw [sum_reverse_prefix hHm (fun h => (h : ℝ)*Real.exp (-(h : ℝ)/40))]
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)*Real.exp (-((H+n : ℕ) : ℝ)/40)) :=
    exponentialShell_summable.comp_injective (fun n m (he : H+n=H+m) => by omega)
  simpa only [exponentialShellTail, polynomialGeometricTail, pow_one, exp_shell_power] using
    hs.sum_le_tsum (Finset.range (m x-H))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

/-- The relaxation of every prefix inequality has a small total weighted
budget. The bound includes index zero and has no dimension factor. -/
theorem uniform_prefix_perturbation_cost (hford : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x*(topPerturbation x+
        ∑ i : Fin (R x H), g (i.val+1)*prefixPerturbation x H i) ≤
        C*exponentialShellTail H := by
  obtain ⟨K, hK, hslice⟩ := uniform_slice_bound hford
  let A := (11/100000 : ℝ)*(lam/rho)
  have hA : 0 < A := mul_pos (by norm_num) (div_pos lam_pos rho_pos)
  refine ⟨1+K*A, by positivity, ?_⟩
  filter_upwards [hslice, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hθ hB
  intro H hHm
  have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
  have htop : (R x H : ℝ)/B x*topPerturbation x ≤ exponentialShellTail H := by
    have he : (R x H : ℝ)/B x*topPerturbation x =
        (1/10000 : ℝ)*(R x H : ℝ)*Real.exp (-(m x : ℝ)/40) := by
      simp only [topPerturbation, xi, Nat.sub_zero]
      field_simp
      ring
    rw [he]
    apply le_trans _ (exponentialShellTail_term hHm)
    have hR0 : (0 : ℝ) ≤ R x H := Nat.cast_nonneg _
    have hfac : (1/10000 : ℝ)*(R x H : ℝ) ≤ m x := by linarith
    exact mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le
  have hterm (i : Fin (R x H)) :
      (R x H : ℝ)/B x*(g (i.val+1)*prefixPerturbation x H i) ≤
        K*A*(((m x-(i.val+1) : ℕ) : ℝ)*Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) := by
    let h := m x-(i.val+1)
    have hi : i.val+1 ≤ m x := by have := i.isLt; unfold R at *; omega
    have hs : (R x H : ℝ)*g (i.val+1)/B x ≤ K*rho^h :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRm (g_pos _).le) hB.le).trans
        (hx (i.val+1) hi)
    have he : prefixPerturbation x H i =
        (11/100000 : ℝ)*alpha (theta x)*(h : ℝ)*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40) := by
      dsimp [prefixPerturbation, xi, bandScale, h]
      ring
    rw [he]
    calc
      _ = ((R x H : ℝ)*g (i.val+1)/B x)*
          ((11/100000 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40)) := by ring
      _ ≤ (K*rho^h)*((11/100000 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹*Real.exp (-(h : ℝ)/40)) := by
        apply mul_le_mul_of_nonneg_right hs
        have := alpha_pos (theta x)
        have := pow_pos rho_pos h
        positivity
      _ = K*((11/100000 : ℝ)*alpha (theta x))*((h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
        field_simp [rho_pos.ne']
      _ ≤ K*A*((h : ℝ)*Real.exp (-(h : ℝ)/40)) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (alpha_le _ hθ) (by norm_num)) hK.le)
          (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  calc
    _ = (R x H : ℝ)/B x*topPerturbation x+
        ∑ i : Fin (R x H), (R x H : ℝ)/B x*(g (i.val+1)*prefixPerturbation x H i) := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ exponentialShellTail H +
        ∑ i : Fin (R x H), K*A*(((m x-(i.val+1) : ℕ) : ℝ)*
          Real.exp (-((m x-(i.val+1) : ℕ) : ℝ)/40)) :=
      add_le_add htop (Finset.sum_le_sum (fun i _ => hterm i))
    _ ≤ exponentialShellTail H+K*A*exponentialShellTail H := by
      rw [← Finset.mul_sum]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_prefix_exponentialShell hHm)
        (mul_nonneg hK.le hA.le))
    _ = _ := by ring

lemma cofactor_exponentialShellTail_tendsto (C : ℝ) :
    Tendsto (fun H => Real.exp (C*cofactorScale H)*exponentialShellTail H) atTop (nhds 0) := by
  apply cofactor_polynomialGeometricTail_tendsto C 1 (Real.exp_pos _).le
  rw [Real.exp_lt_one_iff]
  norm_num

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveEnclosure
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Banded perturbed witness regions and their unit boxes have an additive
full-dimensional enclosure with explicit coordinate errors. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma boxSlackError_nonneg (x : ℝ) (k : ℕ) : 0 ≤ boxSlackError x k := by
  exact add_nonneg (mul_nonneg (xi_sub_one_pos _ _).le
    (mul_nonneg (by norm_num) (bandScale_nonneg _ _))) (by positivity)

lemma boxTopError_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ boxTopError x :=
  add_nonneg (topPerturbation_nonneg hB) (by positivity)

lemma join_witness_perturbed_enlarged {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H < H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hu : u ∈ perturbedTailPrefixRegion x H η)
    (hb : u ∈ prefixBandRegion x H) :
    joinCoordinates (R x H) (H-P H) (u,tailVector η) ∈
      enlargedSimplex (R x H+(H-P H)) (B x) (xi x 0) (fun i => xi x (i.val+1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using
        (mul_nonneg (by norm_num) (bandScale_nonneg _ _)).trans (hb j).1
    · simpa only [joinCoordinates_right] using tailVector_nonneg hη j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.val_castAdd]
      rw [joined_prefix_row, joinCoordinates_left, ← prefix_D_tailVector η hPH.le hHm j]
      have hh := hu.1 j
      rw [prefixLinear_apply] at hh
      change D (m x-(j.val+1)) η ≤ u j-_+(xi x (j.val+1)-1)*u j at hh
      linarith
    · simp only [Fin.val_natAdd]
      rw [joined_tail_row, joinCoordinates_right]
      have hj := j.isLt
      have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
      simpa only [xi, he] using tailVector_simplex hη j
  · rw [joined_budget, ← top_D_tailVector η hPH.le hHm]
    have hh := hu.2
    change (∑ j, a (j.val+1)*u j) ≤ xi x 0*B x-D (m x) η at hh
    linarith

lemma join_witness_band_upper {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H ≤ H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hb : u ∈ prefixBandRegion x H) :
    ∀ i, joinCoordinates (R x H) (H-P H) (u,tailVector η) i ≤
      (11/10 : ℝ)*bandScale x (i.val+1) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [joinCoordinates_left, Fin.val_castAdd] using (hb j).2
  · simp only [joinCoordinates_right, Fin.val_natAdd]
    have hj := j.isLt
    have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
    have hm : H-1-j.val ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    simpa only [tailVector, bandScale, he, mul_assoc] using (hη.2.2.1 _ hm).2.2.1

lemma banded_simplex_cube_additive {x : ℝ} {N : ℕ} (hN : N < m x)
    {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hb : ∀ i, u i ≤ (11/10 : ℝ)*bandScale x (i.val+1))
    (hdist : ∀ i, |u i-v i| ≤ 1) :
    v ∈ prefixRegion N (B x+boxTopError x) 0 (fun i => -boxSlackError x (i.val+1)) := by
  constructor
  · intro i
    have hs := hu.2.1 i
    have hd := (le_abs_self _).trans (prefixLinear_cube_error u v hdist i)
    have hp := mul_le_mul_of_nonneg_left (hb i) (xi_sub_one_pos x (i.val+1)).le
    have hi := i.isLt
    have hh : ((N-i.val : ℕ) : ℝ)^2 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 := by
      have ht' : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) ht' 2
      nlinarith [sq_nonneg (((m x-(i.val+1) : ℕ) : ℝ))]
    simp only [prefixLinear_apply] at hd ⊢
    dsimp [boxSlackError]
    nlinarith
  · have hd := (neg_le_abs _).trans (prefixBudget_cube_error u v hdist)
    have hs : (N : ℝ)^2 ≤ (m x : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hN.le) 2
    dsimp [boxTopError, topPerturbation]
    have hb := hu.2.2
    linarith [sq_nonneg (m x : ℝ)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveCost
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation of the additive box errors with their exact slice coefficients. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma quadraticShellTail_nonneg (H : ℕ) : 0 ≤ quadraticShellTail H :=
  tsum_nonneg (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))

lemma boxErrorTail_nonneg (H : ℕ) : 0 ≤ boxErrorTail H :=
  add_nonneg (exponentialShellTail_nonneg H) (quadraticShellTail_nonneg H)

lemma boxErrorTail_tendsto : Tendsto boxErrorTail atTop (nhds 0) := by
  have he : Tendsto exponentialShellTail atTop (nhds 0) :=
    polynomialGeometricTail_tendsto 1 (Real.exp (-1/40))
  change Tendsto (fun H => exponentialShellTail H+quadraticShellTail H) atTop (nhds 0)
  simpa only [add_zero] using he.add quadraticShellTail_tendsto

lemma cofactor_boxErrorTail_tendsto (K : ℝ) :
    Tendsto (fun H => Real.exp (K*cofactorScale H)*boxErrorTail H) atTop (nhds 0) := by
  simpa only [boxErrorTail, mul_add, add_zero] using
    (cofactor_exponentialShellTail_tendsto K).add (cofactor_quadraticShellTail_tendsto K)

lemma quadraticShellTail_term {H h : ℕ} (hh : H ≤ h) :
    (h : ℝ)^2*rho^h ≤ quadraticShellTail H := by
  have hs0 : Summable (fun n : ℕ => (n : ℝ)^2*rho^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by simpa only [Real.norm_eq_abs, abs_of_pos rho_pos] using rho_lt_one)
  have hs : Summable (fun n : ℕ => ((H+n : ℕ) : ℝ)^2*rho^(H+n)) :=
    hs0.comp_injective (fun _ _ he => Nat.add_left_cancel he)
  have hb := hs.sum_le_tsum {h-H} (fun _ _ => mul_nonneg (sq_nonneg _) (pow_nonneg rho_pos.le _))
  simpa only [Finset.sum_singleton, Nat.add_sub_of_le hh, quadraticShellTail] using hb

lemma boxSlackError_eq {x : ℝ} {H : ℕ} (i : Fin (R x H)) :
    boxSlackError x (i.val+1) = prefixPerturbation x H i+
      4*((m x-(i.val+1) : ℕ) : ℝ)^2 := rfl

/-- The total additive error has a tail bound with no dimension factor. -/
theorem uniform_box_error_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H ≤ m x,
      (R x H : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail H := by
  obtain ⟨A, hA, hexp⟩ := uniform_prefix_perturbation_cost hren
  obtain ⟨D, hD, hquad⟩ := prefix_cube_shell_cost hren
  have hlam := lam_pos
  refine ⟨A+4*D+8/lam, by positivity, ?_⟩
  filter_upwards [hexp, hquad, inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hy hscale hB
  intro H hHm
  have hp := mul_pos hB (pow_pos rho_pos (m x))
  have hmB : (m x : ℝ)/B x ≤ (2/lam)*rho^(m x) := by
    have hh := (div_le_iff₀ hp).mp hscale
    apply (div_le_iff₀ hB).mpr
    nlinarith [hh]
  have htop : (R x H : ℝ)/B x*(m x : ℝ)^2 ≤ (2/lam)*quadraticShellTail H := by
    have hRm : (R x H : ℝ) ≤ m x := by exact_mod_cast Nat.sub_le (m x) H
    calc
      _ ≤ ((m x : ℝ)/B x)*(m x : ℝ)^2 := by gcongr
      _ ≤ ((2/lam)*rho^(m x))*(m x : ℝ)^2 :=
        mul_le_mul_of_nonneg_right hmB (sq_nonneg _)
      _ = (2/lam)*((m x : ℝ)^2*rho^(m x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quadraticShellTail_term hHm) (by positivity)
  have heq : (R x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) =
      (R x H : ℝ)/B x*(topPerturbation x+
        ∑ i : Fin (R x H), g (i.val+1)*prefixPerturbation x H i)+
      4*((R x H : ℝ)/B x*(∑ i : Fin (R x H),
        g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2))+
      4*((R x H : ℝ)/B x*(m x : ℝ)^2) := by
    simp only [boxTopError, boxSlackError_eq, mul_add, Finset.sum_add_distrib]
    simp_rw [show ∀ i : Fin (R x H), g (i.val+1)*(4*((m x-(i.val+1) : ℕ) : ℝ)^2) =
      4*(g (i.val+1)*((m x-(i.val+1) : ℕ) : ℝ)^2) by intro i; ring]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  have h1 := hx H hHm
  have h2 := hy H hHm
  have he0 := exponentialShellTail_nonneg H
  have hq0 := quadraticShellTail_nonneg H
  have ht := mul_le_mul_of_nonneg_left htop (by norm_num : (0 : ℝ)≤4)
  have he8 : 4*((2/lam)*quadraticShellTail H) = (8/lam)*quadraticShellTail H := by ring
  rw [he8] at ht
  have h8 : 0 ≤ 8/lam := by positivity
  dsimp [boxErrorTail]
  nlinarith [mul_nonneg h8 he0, mul_nonneg hA.le hq0,
    mul_nonneg hD.le he0]


/-- The same retained-coordinate cost with any larger ambient dimension
bounded by `m`; the harmless factor two uses `m ≥ 2H`. -/
theorem ambient_box_error_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H N : ℕ, 2*H ≤ m x → N ≤ m x →
      (N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ 2*C*boxErrorTail H := by
  obtain ⟨C, hC, hcost⟩ := uniform_box_error_cost hren
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcost, B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hB
  intro H N hH hN
  have hnr : (N : ℝ) ≤ 2*(R x H : ℝ) := by
    have hh : N ≤ 2*R x H := by unfold R; omega
    exact_mod_cast hh
  have hE : 0 ≤ boxTopError x+∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1) :=
    add_nonneg (boxTopError_nonneg hB.le) (Finset.sum_nonneg
      (fun i _ => mul_nonneg (g_pos _).le (boxSlackError_nonneg _ _)))
  calc
    _ ≤ (2*(R x H : ℝ))/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnr hB.le) hE
    _ = 2*((R x H : ℝ)/B x*(boxTopError x+
        ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1))) := by ring
    _ ≤ 2*(C*boxErrorTail H) :=
      mul_le_mul_of_nonneg_left (hx H (by omega)) (by norm_num)
    _ = _ := by ring

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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
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

lemma volume_zero_prefixRegion {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : 0 < N) :
    volume (prefixRegion N (B x) 0 0) = ENNReal.ofReal (G x N) := by
  rw [volume_prefixRegion_explicit N hN]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, max_eq_left hB]
  rw [G, prod_fin_shifted N g]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveShell
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Slice bounds for the additive enlargement needed by banded witness boxes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma pow_budget_bound {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (n : ℕ) :
    (B+E)^n ≤ B^n*Real.exp ((n : ℝ)*E/B) := by
  have hr : 0 ≤ 1+E/B := by positivity
  have hp := pow_le_pow_left₀ hr (show 1+E/B ≤ Real.exp (E/B) by
    simpa only [add_comm] using Real.add_one_le_exp (E/B)) n
  rw [← Real.exp_nat_mul] at hp
  have he : (B+E)^n = B^n*(1+E/B)^n := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [he]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hp (pow_nonneg hB.le n)

lemma pow_budget_pred_bound {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E) (n : ℕ) :
    (B+E)^(n-1) ≤ B^(n-1)*Real.exp ((n : ℝ)*E/B) := by
  apply (pow_budget_bound hB hE (n-1)).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB.le _)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hB.le
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hE

/-- A single slack slice has its usual linear slice cost even in the
additively enlarged simplex. -/
theorem additive_slack_shell_bound {x : ℝ} {N : ℕ} (hB : 0 < B x) (hN : 0 < N)
    (δ₀ : ℝ) (δ : Fin N → ℝ) (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i)
    (i : Fin N) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (prefixRegion N (B x+δ₀) 0 (-δ) \
      prefixRegion N (B x+δ₀) 0 (raiseThreshold (-δ) i t)) ≤
      (t*N*g (i.val+1)/B x)*
        Real.exp ((N : ℝ)/B x*(δ₀+∑ j, g (j.val+1)*δ j))*G x N := by
  let E := δ₀+∑ j, g (j.val+1)*δ j
  have hE : 0 ≤ E := add_nonneg hδ₀
    (Finset.sum_nonneg (fun j _ => mul_nonneg (g_pos _).le (hδ j)))
  have he : B x+δ₀-0-∑ j, g (j.val+1)*(-δ) j = B x+E := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_zero]
    dsimp [E]
    ring
  have hs := prefix_slack_shell_bound hN (B x+δ₀) 0 (-δ) i ht
    (by rw [he]; positivity)
  rw [he] at hs
  apply hs.trans
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_budget_pred_bound hB hE N)
      (mul_nonneg (mul_nonneg ht (Nat.cast_nonneg _)) (g_pos _).le)) hden.le).trans_eq
  have hp : (B x)^N = B x*(B x)^(N-1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  unfold G
  rw [prod_fin_shifted]
  rw [hp]
  dsimp [E]
  field_simp

/-- The top-budget slice obeys the same estimate, with coefficient one. -/
theorem additive_top_shell_bound {x : ℝ} {N : ℕ} (hB : 0 < B x) (hN : 0 < N)
    (δ₀ : ℝ) (δ : Fin N → ℝ) (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i)
    {t : ℝ} (ht : 0 ≤ t) :
    volume.real (prefixRegion N (B x+δ₀) 0 (-δ) \
      prefixRegion N (B x+δ₀-t) 0 (-δ)) ≤
      (t*N/B x)*Real.exp ((N : ℝ)/B x*(δ₀+∑ j, g (j.val+1)*δ j))*G x N := by
  let E := δ₀+∑ j, g (j.val+1)*δ j
  have hE : 0 ≤ E := add_nonneg hδ₀
    (Finset.sum_nonneg (fun j _ => mul_nonneg (g_pos _).le (hδ j)))
  have hsub : prefixRegion N (B x+δ₀-t) 0 (-δ) ⊆ prefixRegion N (B x+δ₀) 0 (-δ) := by
    intro u hu
    exact ⟨hu.1, by have := hu.2; linarith⟩
  have hf : volume (prefixRegion N (B x+δ₀) 0 (-δ)) ≠ ⊤ := by
    rw [volume_prefixRegion_explicit _ hN]
    exact ENNReal.ofReal_ne_top
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  rw [measureReal_sdiff hsub (measurableSet_prefixRegion _ _ _ _) hf]
  change (volume _).toReal-(volume _).toReal ≤ _
  rw [volume_prefixRegion_explicit _ hN, volume_prefixRegion_explicit _ hN,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have he : B x+δ₀-0-∑ j, g (j.val+1)*(-δ) j = B x+E := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sub_zero]
    dsimp [E]
    ring
  have he' : B x+δ₀-t-0-∑ j, g (j.val+1)*(-δ) j = B x+E-t := by
    linarith [he]
  rw [he, he', max_eq_left (show 0 ≤ B x+E by positivity), ← sub_div]
  apply (div_le_div_of_nonneg_right (pow_sub_positivePart_le (by positivity) ht N) hden.le).trans
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_budget_pred_bound hB hE N)
      (show 0 ≤ t*N by positivity)) hden.le).trans_eq
  have hp : (B x)^N = B x*(B x)^(N-1) := by
    rw [← pow_succ', Nat.sub_add_cancel hN]
  unfold G
  rw [prod_fin_shifted, hp]
  dsimp [E]
  field_simp

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_AdditiveShellUnion
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing all retained slack slices in one enlarged full-dimensional simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma additiveBoxSimplex_volume_ne_top (x : ℝ) {N : ℕ} (hN : 0 < N) :
    volume (additiveBoxSimplex x N) ≠ ⊤ := by
  rw [additiveBoxSimplex, volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

lemma additiveBoxShell_volume_ne_top (x : ℝ) {R N : ℕ} (hRN : R ≤ N) (hN : 0 < N) :
    volume (additiveBoxShell x R N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (additiveBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  rcases hu with hu | hu
  · exact hu.1
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
    exact hi.1

/-- The union of all retained coordinate slices costs their sum, not the
number of tail witnesses or full-dimensional boxes. -/
theorem additiveBoxShell_volume_bound {x : ℝ} {R N : ℕ}
    (hB : 0 < B x) (hN : 0 < N) (hRN : R ≤ N) :
    volume.real (additiveBoxShell x R N hRN) ≤
      (2*(N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin R, g (i.val+1)*boxSlackError x (i.val+1)))*
      Real.exp ((N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N := by
  let F := Real.exp ((N : ℝ)/B x*(boxTopError x+
    ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N
  have htop := additive_top_shell_bound hB hN (boxTopError x)
    (fun i => boxSlackError x (i.val+1)) (boxTopError_nonneg hB.le)
    (fun i => boxSlackError_nonneg _ _) (t := 2*boxTopError x) (mul_nonneg (by norm_num) (boxTopError_nonneg hB.le))
  have htop' : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x-boxTopError x) 0 (fun i => -boxSlackError x (i.val+1))) ≤
      (2*boxTopError x*N/B x)*F := by
    have he : B x+boxTopError x-2*boxTopError x = B x-boxTopError x := by ring
    simpa only [he, Pi.neg_def, additiveBoxSimplex, F, mul_assoc] using htop
  have hrow (i : Fin R) : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x) 0
        (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
          (2*boxSlackError x (i.val+1)))) ≤
      (2*boxSlackError x (i.val+1)*N*g (i.val+1)/B x)*F := by
    have hh := additive_slack_shell_bound hB hN (boxTopError x)
      (fun j => boxSlackError x (j.val+1)) (boxTopError_nonneg hB.le)
      (fun j => boxSlackError_nonneg _ _) (Fin.castLE hRN i)
      (t := 2*boxSlackError x (i.val+1)) (mul_nonneg (by norm_num) (boxSlackError_nonneg _ _))
    simpa only [Pi.neg_def, Fin.val_castLE, additiveBoxSimplex, F, mul_assoc] using hh
  apply (measureReal_union_le _ _).trans
  apply (add_le_add htop' ((measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun i _ => hrow i)))).trans_eq
  have heq : (∑ i : Fin R, 2*boxSlackError x (i.val+1)*N*g (i.val+1)/B x) =
      (2*(N : ℝ)/B x)*∑ i : Fin R, g (i.val+1)*boxSlackError x (i.val+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.sum_mul, heq]
  dsimp [F]
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TailEncoding
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed cofactor and the ordered tail-prime vector determine a witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tailVector_eq_primeCoord {H : ℕ} (η : TailDatum H) :
    tailVector η = primePrefixCoord (tailPrimeVector η) := rfl

lemma tailPrimeVector_prime {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) : (tailPrimeVector η i).Prime := by
  apply (hη.2.2.1 _ _).1
  have := i.isLt
  exact Finset.mem_Ico.mpr (by omega)

lemma tailDatum_eq_of_primeVector {H : ℕ} {s t : ℝ} {η ξ : TailDatum H}
    (hη : IsWitness H s η) (hξ : IsWitness H t ξ)
    (hcof : η.cofactor=ξ.cofactor) (hvec : tailPrimeVector η=tailPrimeVector ξ) : η=ξ := by
  have hQ : η.Q=ξ.Q := by
    funext i
    by_cases hi : i.val < P H
    · rw [hη.1 i hi, hξ.1 i hi]
    · have hib := i.isLt
      let j : Fin (H-P H) := ⟨H-1-i.val, by omega⟩
      have hh := congrFun hvec j
      have he : H-1-j.val=i.val := by dsimp [j]; omega
      simpa only [tailPrimeVector, he, tailPrime, dite_eq_left i.isLt] using hh
  cases η
  cases ξ
  cases hQ
  cases hcof
  rfl

lemma prod_tail_indices {M : Type*} [CommMonoid M] {H : ℕ} (hPH : P H ≤ H) (f : ℕ → M) :
    (∏ l ∈ Finset.Ico (P H) H, f l) = ∏ i : Fin (H-P H), f (H-1-i.val) := by
  apply Finset.prod_bij (fun l hl => (⟨H-1-l, by
    have := Finset.mem_Ico.mp hl
    omega⟩ : Fin (H-P H)))
  · intro l hl
    exact Finset.mem_univ _
  · intro l hl k hk he
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · intro i _
    have hi := i.isLt
    refine ⟨H-1-i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp only
    omega
  · intro l hl
    have := Finset.mem_Ico.mp hl
    have he : H-1-(H-1-l)=l := by omega
    rw [he]

lemma tail_reciprocal_vector {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (hPH : P H ≤ H) :
    ((w η).totient : ℝ)⁻¹ ≤
      (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η) := by
  have hh := tail_reciprocal_majorant hη
  rw [prod_tail_indices hPH] at hh
  have he : (∏ i : Fin (H-P H), (tailPrime η (H-1-i.val)-1 : ℝ)⁻¹) =
      reciprocalShiftWeight (tailPrimeVector η) := by
    unfold reciprocalShiftWeight
    rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (tailPrimeVector_prime hη i).one_lt.le, Nat.cast_one]
    rfl
  rwa [he] at hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full-dimensional aggregation of a finite witness family with fixed cofactor. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma witnessPrimeRegion_eq {H R a : ℕ} {s : ℝ} (W : Finset (TailDatum H))
    (S : TailDatum H → Set (Fin R → ℝ))
    (hW : ∀ η ∈ W, IsWitness H s η) (hcof : ∀ η ∈ W, η.cofactor=a)
    {η : TailDatum H} (hη : η ∈ W) : witnessPrimeRegion W S (tailPrimeVector η) = S η := by
  ext u
  simp only [witnessPrimeRegion, Set.mem_iUnion, Finset.mem_filter]
  constructor
  · rintro ⟨ξ, ⟨hξ, he⟩, hu⟩
    have hh : ξ=η := tailDatum_eq_of_primeVector (hW ξ hξ) (hW η hη)
      ((hcof ξ hξ).trans (hcof η hη).symm) he
    simpa only [hh] using hu
  · intro hu
    exact ⟨η, ⟨hη, rfl⟩, hu⟩

/-- Aggregation counts the prime mass of each tail box once. The bound has
no factor equal to the number of witnesses in the box. -/
theorem witness_tail_box_aggregation {H R a : ℕ} {s : ℝ}
    (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
    (K : Finset (Fin (H-P H) → ℕ)) (T : Set (Fin (R+(H-P H)) → ℝ)) (C : ℝ)
    (hC : 0 ≤ C) (hW : ∀ η ∈ W, IsWitness H s η) (hcof : ∀ η ∈ W, η.cofactor=a)
    (hS : ∀ η ∈ W, MeasurableSet (S η)) (hT : volume T ≠ ⊤)
    (hcover : ∀ η ∈ W, tailPrimeVector η ∈ gridPrimeTuples K)
    (hbox : ∀ b ∈ K, (∏ i, unitPrimeWeight (b i)) ≤ C)
    (henclose : ∀ η ∈ W, ∀ b ∈ K, tailVector η ∈ unitGridCell b →
      ∀ u ∈ S η, ∀ v ∈ unitGridCell b, joinCoordinates R (H-P H) (u,v) ∈ T) :
    (∑ η ∈ W, reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η)) ≤ C*volume.real T := by
  classical
  have hinj : Set.InjOn tailPrimeVector (↑W : Set (TailDatum H)) := by
    intro η hη ξ hξ he
    exact tailDatum_eq_of_primeVector (hW η hη) (hW ξ hξ)
      ((hcof η hη).trans (hcof ξ hξ).symm) he
  have heq : (∑ η ∈ W, reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η)) =
      ∑ p ∈ W.image tailPrimeVector, reciprocalShiftWeight p *
        volume.real (witnessPrimeRegion W S p) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro η hη
    rw [witnessPrimeRegion_eq W S hW hcof hη]
  rw [heq]
  have hsub : W.image tailPrimeVector ⊆ gridPrimeTuples K := by
    intro p hp
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hp
    exact hcover η hη
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    mul_nonneg (reciprocalShiftWeight_nonneg p) measureReal_nonneg)).trans
  apply tail_box_aggregation_enclosure K (witnessPrimeRegion W S) (witnessBoxRegion W S) T C hC
  · intro b _
    exact (W.filter _).measurableSet_biUnion (fun η hη => hS η (Finset.mem_filter.mp hη).1)
  · exact hT
  · intro b _ p hp u hu
    obtain ⟨η, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, he⟩ := Finset.mem_filter.mp hη
    have hc : tailVector η ∈ unitGridCell b := by
      rw [tailVector_eq_primeCoord, he]
      exact (mem_primeBoxTuples_iff.mp hp).2
    exact Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hη, hc⟩, hu⟩⟩
  · exact hbox
  · intro z hz
    obtain ⟨⟨u,v⟩, hz, rfl⟩ := hz
    obtain ⟨b, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hb, hu, hv⟩ := Set.mem_iUnion.mp hz
    obtain ⟨η, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, hcell⟩ := Finset.mem_filter.mp hη
    exact henclose η hη b hb hcell u hu v hv

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform prime mass for the boxes occupied by discrete witness tails. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tailVector_mem_box {H : ℕ} {s : ℝ} {η : TailDatum H} (hη : IsWitness H s η) :
    tailVector η ∈ unitGridCell (tailBoxIndex η) := by
  intro i _
  simp only [tailBoxIndex, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  exact ⟨Nat.floor_le (tailVector_nonneg hη i), Nat.lt_floor_add_one _⟩

lemma tailPrimeVector_mem_grid {H : ℕ} {s : ℝ} (W : Finset (TailDatum H))
    (hW : ∀ η ∈ W, IsWitness H s η) {η : TailDatum H} (hη : η ∈ W) :
    tailPrimeVector η ∈ gridPrimeTuples (witnessGrid W) := by
  apply mem_gridPrimeTuples_iff.mpr
  refine ⟨tailPrimeVector_prime (hW η hη), ?_⟩
  rw [← tailVector_eq_primeCoord]
  exact Set.mem_iUnion.mpr ⟨tailBoxIndex η,
    Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨η, hη, rfl⟩, tailVector_mem_box (hW η hη)⟩⟩

lemma tailBoxIndex_lower {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : 0 ≤ s) (hη : IsWitness H s η) (i : Fin (H-P H)) :
    1 ≤ tailBoxIndex η i ∧ (9/10 : ℝ)*lam*(H-1-i.val : ℕ) ≤ tailBoxIndex η i := by
  refine ⟨by dsimp [tailBoxIndex]; omega, ?_⟩
  have hi : H-1-i.val ∈ Finset.Ico (P H) H := by
    have := i.isLt
    exact Finset.mem_Ico.mpr (by omega)
  have hb := (hη.2.2.1 _ hi).2.1
  have hα := alpha_ge_lam hs
  have hp : 1 ≤ (rho^(H-1-i.val))⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have hl : (9/10 : ℝ)*lam*(H-1-i.val : ℕ) ≤ tailVector η i := by
    apply le_trans _ hb
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by norm_num))
      (Nat.cast_nonneg _)).trans
      (le_mul_of_one_le_right (by have := alpha_pos s; positivity : 0 ≤ (9/10 : ℝ)*alpha s*(H-1-i.val : ℕ)) hp)
  exact hl.trans (tailVector_mem_box hη i (Set.mem_univ _)).2.le

lemma witnessGrid_exp_sum {H : ℕ} {s : ℝ} (hs : 0 ≤ s) (hPH : P H ≤ H)
    (W : Finset (TailDatum H)) (hW : ∀ η ∈ W, IsWitness H s η)
    {b : Fin (H-P H) → ℕ} (hb : b ∈ witnessGrid W) :
    (∑ i, Real.exp (-(b i : ℝ))) ≤
      (Real.exp (-(9/10 : ℝ)*lam))^(P H)/(1-Real.exp (-(9/10 : ℝ)*lam)) := by
  obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hb
  let q := Real.exp (-(9/10 : ℝ)*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; nlinarith [lam_pos]
  have ht (i : Fin (H-P H)) : Real.exp (-(tailBoxIndex η i : ℝ)) ≤ q^(H-(i.val+1)) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hl := (tailBoxIndex_lower hs (hW η hη) i).2
    have he : H-1-i.val=H-(i.val+1) := by omega
    rw [he] at hl
    nlinarith
  apply (Finset.sum_le_sum (fun i _ => ht i)).trans
  rw [sum_reverse_geometric hPH q]
  have hg := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑' n : ℕ, q^(P H+n) :=
      (hg.comp_injective (fun _ _ h => Nat.add_left_cancel h)).sum_le_tsum _
        (fun _ _ => pow_nonneg hq0 _)
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

/-- The entire prime mass of any occupied tail box is bounded by an absolute
constant, independent of the number of tail coordinates and witnesses. -/
theorem witnessGrid_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℕ} {s : ℝ}, 0 ≤ s → P H ≤ H →
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H s η) →
      ∀ b ∈ witnessGrid W, (∏ i, unitPrimeWeight (b i)) ≤ C := by
  obtain ⟨C, hC, hc⟩ := prime_unit_box_error hford
  let q := Real.exp (-(9/10 : ℝ)*lam)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; nlinarith [lam_pos]
  refine ⟨Real.exp (C/(1-q)), Real.exp_pos _, ?_⟩
  intro H s hs hPH W hW b hb
  have hb1 : ∀ i, 1 ≤ b i := by
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hb
    exact fun i => (tailBoxIndex_lower hs (hW η hη) i).1
  have he := hc Finset.univ b (fun i _ => hb1 i)
  have hsum := witnessGrid_exp_sum hs hPH W hW hb
  have hsum' : (∑ i, Real.exp (-(b i : ℝ))) ≤ 1/(1-q) := by
    apply hsum.trans
    exact div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1.le) (sub_pos.mpr hq1).le
  have hh := (le_abs_self _).trans he
  have he' : (∏ i, unitPrimeWeight (b i)) ≤ Real.exp (C*∑ i, Real.exp (-(b i : ℝ))) := by
    linarith
  apply he'.trans
  apply Real.exp_le_exp.mpr
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsum' hC.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CofactorWitnessAggregation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reciprocal totient weights can be aggregated at fixed cofactor,
including tails containing repeated prime factors. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

/-- One full-dimensional volume controls a fixed-cofactor witness family.
The only arithmetic input is the published prime-box estimate. -/
theorem cofactor_witness_aggregation (hbox : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H R a : ℕ} {s : ℝ}, 0 ≤ s → P H ≤ H →
      ∀ (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
        (T : Set (Fin (R+(H-P H)) → ℝ)),
      (∀ η ∈ W, IsWitness H s η) → (∀ η ∈ W, η.cofactor=a) →
      (∀ η ∈ W, MeasurableSet (S η)) → volume T ≠ ⊤ →
      (∀ η ∈ W, ∀ u ∈ S η, ∀ v : Fin (H-P H) → ℝ,
        (∀ i, |tailVector η i-v i| ≤ 1) → joinCoordinates R (H-P H) (u,v) ∈ T) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η)) ≤
        (a.totient : ℝ)⁻¹*C*volume.real T := by
  obtain ⟨C, hC, hgrid⟩ := witnessGrid_prime_mass_bound hbox
  refine ⟨C, hC, ?_⟩
  intro H R a s hs hPH W S T hW hcof hS hT henclose
  have hweight (η) (hη : η ∈ W) :
      ((w η).totient : ℝ)⁻¹ ≤ (a.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η) := by
    simpa only [hcof η hη] using tail_reciprocal_vector (hW η hη) hPH
  have hsum := witness_tail_box_aggregation W S (witnessGrid W) T C hC.le hW hcof hS hT
    (fun η hη => tailPrimeVector_mem_grid W hW hη) (hgrid hs hPH W hW)
    (by
      intro η hη b _ hb u hu v hv
      exact henclose η hη u hu v (unitGridCell_coordinate_distance hb hv))
  calc
    _ ≤ ∑ η ∈ W, ((a.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η))*volume.real (S η) :=
      Finset.sum_le_sum (fun η hη => mul_le_mul_of_nonneg_right (hweight η hη) measureReal_nonneg)
    _ = (a.totient : ℝ)⁻¹*∑ η ∈ W,
        reciprocalShiftWeight (tailPrimeVector η)*volume.real (S η) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      ring
    _ ≤ (a.totient : ℝ)⁻¹*(C*volume.real T) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Summing all allowed cofactors retains only the subpolynomial envelope,
not the number of witnesses. -/
theorem all_cofactor_witness_aggregation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H R : ℕ} {s : ℝ}, s ∈ Set.Ico (0 : ℝ) 1 → P H ≤ H →
      ∀ (W : Finset (TailDatum H)) (S : TailDatum H → Set (Fin R → ℝ))
        (T : Set (Fin (R+(H-P H)) → ℝ)),
      (∀ η ∈ W, IsWitness H s η) → (∀ η ∈ W, MeasurableSet (S η)) → volume T ≠ ⊤ →
      (∀ η ∈ W, ∀ u ∈ S η, ∀ v : Fin (H-P H) → ℝ,
        (∀ i, |tailVector η i-v i| ≤ 1) → joinCoordinates R (H-P H) (u,v) ∈ T) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η)) ≤
        C*Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T := by
  obtain ⟨C, hC, hfixed⟩ := cofactor_witness_aggregation hbox
  obtain ⟨D, hD, hcof⟩ := tail_cofactor_sum hmertens
  refine ⟨C*D, mul_pos hC hD, ?_⟩
  intro H R s hs hPH W S T hW hS hT henclose
  have hmaps : ∀ η ∈ W, η.cofactor ∈ Finset.Icc 1 (tailCofactorBound H) := by
    intro η hη
    exact Finset.mem_Icc.mpr (witness_cofactor_bound hs (hW η hη))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 (tailCofactorBound H),
        (a.totient : ℝ)⁻¹*C*volume.real T := by
      apply Finset.sum_le_sum
      intro a _
      apply hfixed hs.1 hPH (W.filter (fun η => η.cofactor=a)) S T
      · intro η hη
        exact hW η (Finset.mem_filter.mp hη).1
      · intro η hη
        exact (Finset.mem_filter.mp hη).2
      · intro η hη
        exact hS η (Finset.mem_filter.mp hη).1
      · exact hT
      · intro η hη
        exact henclose η (Finset.mem_filter.mp hη).1
    _ = (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*C*volume.real T := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ (D*Real.exp ((4*(lam/rho))*cofactorScale H))*C*volume.real T := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      apply mul_le_mul_of_nonneg_right _ hC.le
      have he : 4*(lam/rho)*(P H : ℝ)*(rho^(P H))⁻¹ =
          (4*(lam/rho))*cofactorScale H := by unfold cofactorScale; ring
      simpa only [he] using hcof H
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ConcentrationTail
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.TotientAsymptotic.mem_basicRemainderFinset _root_.OAI.TotientAsymptotic.mem_prefixDataFinset _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the concentration loss over all retained prefix coordinates. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

theorem sum_retained_concentration {x c : ℝ} {H : ℕ} (hc : 0 < c)
    (hHm : H ≤ m x) (hPH : 2*P H ≤ H) :
    (∑ i : Fin (R x H), Real.exp (-c*((L x H-(i.val+1) : ℕ) : ℝ))) ≤
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) := by
  let q := Real.exp (-c/2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by dsimp [q]; rw [Real.exp_lt_one_iff]; linarith
  have hterm (i : Fin (R x H)) :
      Real.exp (-c*((L x H-(i.val+1) : ℕ) : ℝ)) ≤ q^(m x-(i.val+1)) := by
    have hi : i.val+1 ≤ m x-H := by have := i.isLt; unfold R at *; omega
    have hP : P H ≤ m x-(i.val+1) := by omega
    have hhalf : ((m x-(i.val+1) : ℕ) : ℝ) ≤
        2*((L x H-(i.val+1) : ℕ) : ℝ) := by
      have hn : m x-(i.val+1) ≤ 2*(L x H-(i.val+1)) := by unfold L; omega
      exact_mod_cast hn
    change Real.exp _ ≤ (Real.exp (-c/2))^_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  change (∑ i : Fin (m x-H), q^(m x-(i.val+1))) ≤ _
  rw [sum_reverse_prefix hHm (fun h => q^h)]
  have hg : Summable (fun n : ℕ => q^n) := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑' n : ℕ, q^(H+n) := (hg.comp_injective (fun _ _ h => by omega)).sum_le_tsum
      _ (fun _ _ => pow_nonneg hq0 _)
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      rfl

lemma cofactor_concentration_tail_tendsto (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℕ => Real.exp (C*cofactorScale H)*
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2))) atTop (nhds 0) := by
  have hq0 : 0 ≤ Real.exp (-c/2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-c/2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have ht := cofactor_polynomialGeometricTail_tendsto C 0 hq0 hq1
  have he (H : ℕ) : polynomialGeometricTail 0 (Real.exp (-c/2)) H =
      (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) := by
    unfold polynomialGeometricTail
    simp only [pow_zero, one_mul, pow_add]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    rfl
  simp_rw [he] at ht
  simpa only [mul_div_assoc] using ht

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FordSimplexEmbedding
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relating our terminal coefficient to Ford's stronger terminal inequality. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma a_one_lt_one : a 1 < 1 := by
  norm_num [a]
  linarith [Real.log_two_lt_d9]

lemma prefixRegion_nonneg {N : ℕ} {B : ℝ} {u : Fin N → ℝ}
    (hu : u ∈ prefixRegion N B 0 0) : ∀ i, 0 ≤ u i := by
  have hh := prefixLinear_terminal_lower u 0 (fun i => by simpa using hu.1 i)
  simpa using hh

lemma shrinkLast_apply (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+2)) :
    shrinkLast N u i = (if i = Fin.last (N+1) then a 1 else 1)*u i := by
  simp [shrinkLast, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma shrinkLast_det (N : ℕ) : LinearMap.det (shrinkLast N) = a 1 := by
  rw [shrinkLast, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

lemma shrinkLast_le {N : ℕ} {u : Fin (N+2) → ℝ} (hu : ∀ i, 0 ≤ u i) :
    ∀ i, shrinkLast N u i ≤ u i := by
  intro i
  rw [shrinkLast_apply]
  split_ifs
  · exact mul_le_of_le_one_left (hu i) a_one_lt_one.le
  · simp

/-- Scaling only the last coordinate by `a₁` places our exact simplex inside
Ford's `S*`. All earlier coordinates, hence their band events, are preserved. -/
theorem shrinkLast_mem_fordSimplex {N : ℕ} {B : ℝ} {u : Fin (N+2) → ℝ}
    (hu : u ∈ prefixRegion (N+2) B 0 0) : shrinkLast N u ∈ fordSimplex N B := by
  have hnonneg := prefixRegion_nonneg hu
  have hle := shrinkLast_le hnonneg
  have ha : 0 < a 1 := a_pos le_rfl
  constructor
  · constructor
    · intro i
      by_cases hi : i = Fin.last (N+1)
      · subst i
        rw [prefixLinear_apply]
        have hs : (∑ j : Fin (N+2), if Fin.last (N+1) < j then
            a (j.val-(Fin.last (N+1)).val)*shrinkLast N u j else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          exact ite_eq_right (not_lt_of_ge (Fin.le_last j))
        rw [hs, sub_zero, shrinkLast_apply]
        simp only [ite_true, if_true]
        exact mul_nonneg ha.le (hnonneg _)
      · have hh := hu.1 i
        rw [prefixLinear_apply] at hh ⊢
        rw [shrinkLast_apply, ite_eq_right hi, one_mul]
        apply le_trans hh
        apply sub_le_sub_left
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hij
        · exact mul_le_mul_of_nonneg_left (hle j) (a_pos (by have := hij; simp only [Fin.lt_def] at this; omega)).le
        · exact le_rfl
    · have hh := hu.2
      simp only [sub_zero] at hh ⊢
      apply le_trans _ hh
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hle i) (a_pos (by omega)).le
  · have hh := hu.1 ⟨N, by omega⟩
    rw [prefixLinear_apply] at hh
    have hs : (∑ j : Fin (N+2), if (⟨N, by omega⟩ : Fin (N+2)) < j then
        a (j.val-N)*u j else 0) = a 1*u (Fin.last (N+1)) := by
      rw [Finset.sum_eq_single (Fin.last (N+1))]
      · have hlt : (⟨N, by omega⟩ : Fin (N+2)) < Fin.last (N+1) := by
          change N < N+1
          omega
        simp only [hlt, ite_true, if_true, Fin.val_last, Nat.add_sub_cancel_left]
      · intro j _ hj
        rw [ite_eq_right]
        simp only [Fin.lt_def]
        have hval : j.val ≠ N+1 := by
          intro he
          apply hj
          exact Fin.ext he
        have := j.isLt
        omega
      · simp
    rw [hs] at hh
    change shrinkLast N u (Fin.last (N+1)) ≤ shrinkLast N u ⟨N, by omega⟩
    rw [shrinkLast_apply, shrinkLast_apply]
    simp only [ite_true, if_true]
    rw [ite_eq_right (by intro h; have he := congrArg Fin.val h; simp at he), one_mul]
    change 0 ≤ u ⟨N, by omega⟩-a 1*u (Fin.last (N+1)) at hh
    linarith

lemma shrinkLast_preserves_prefix (N : ℕ) (u : Fin (N+2) → ℝ) (i : Fin (N+2))
    (hi : i ≠ Fin.last (N+1)) : shrinkLast N u i = u i := by
  simp [shrinkLast_apply, hi]

/-- A measurable event in Ford's simplex bounds its preimage in our simplex,
with only the fixed Jacobian factor `1/a₁`. -/
theorem shrinkLast_volume_bound {N : ℕ} {B : ℝ}
    (S T : Set (Fin (N+2) → ℝ)) (hT : MeasurableSet T)
    (hS : ∀ u ∈ S, u ∈ prefixRegion (N+2) B 0 0)
    (hST : ∀ u ∈ S, shrinkLast N u ∈ T) :
    volume S ≤ ENNReal.ofReal ((a 1)⁻¹)*volume (fordSimplex N B ∩ T) := by
  have ha := a_pos (j := 1) le_rfl
  have hford : MeasurableSet (fordSimplex N B) := by
    change MeasurableSet (prefixRegion (N+2) B 0 0 ∩
      {u : Fin (N+2) → ℝ | u (Fin.last (N+1)) ≤ u ⟨N, by omega⟩})
    exact (measurableSet_prefixRegion _ _ _ _).inter
      (measurableSet_le (measurable_pi_apply (Fin.last (N+1)))
        (measurable_pi_apply (⟨N, by omega⟩ : Fin (N+2))))
  have hincl : S ⊆ (shrinkLast N) ⁻¹' (fordSimplex N B ∩ T) := by
    intro u hu
    exact ⟨shrinkLast_mem_fordSimplex (hS u hu), hST u hu⟩
  apply (measure_mono hincl).trans_eq
  rw [← Measure.map_apply (shrinkLast N).continuous_of_finiteDimensional.measurable (hford.inter hT),
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [shrinkLast_det]; exact ha.ne'),
    shrinkLast_det, Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr ha)]

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

lemma measurableSet_fordCoordinateBad (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    MeasurableSet (fordCoordinateBad N B i) := by
  apply measurableSet_lt measurable_const
  exact ((measurable_pi_apply i).div_const _ |>.sub_const 1).abs

lemma prefixRegion_volume_ne_top {N : ℕ} (hN : 0 < N) (B : ℝ) :
    volume (prefixRegion N B 0 0) ≠ ⊤ := by
  rw [volume_prefixRegion_explicit _ hN]
  exact ENNReal.ofReal_ne_top

theorem simplex_coordinate_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := hford
  have ha := a_pos (j := 1) le_rfl
  refine ⟨C/a 1, c, N₀, div_pos hC ha, hc, ?_⟩
  intro N hN B hB i hi
  have hlast : i ≠ Fin.last (N+1) := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_last] at hh
    omega
  have hbound := shrinkLast_volume_bound
    (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)
    (fordCoordinateBad N B i) (measurableSet_fordCoordinateBad N B i)
    (fun _ hu => hu.1) (fun u hu => by
      change (1/40 : ℝ) < |shrinkLast N u i/fordSimplexCenter N B i-1|
      rw [shrinkLast_preserves_prefix N u i hlast]
      exact hu.2)
  have hfin : volume (fordSimplex N B ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono (fun _ hu => hu.1.1))
  have hrightfin : ENNReal.ofReal ((a 1)⁻¹)*volume (fordSimplex N B ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal := ENNReal.toReal_mono hrightfin hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)] at hreal
  have hvol : (volume (fordSimplex N B)).toReal ≤ (volume (prefixRegion (N+2) B 0 0)).toReal := by
    exact ENNReal.toReal_mono (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono (fun _ hu => hu.1))
  calc
    _ ≤ (a 1)⁻¹*(volume (fordSimplex N B ∩ fordCoordinateBad N B i)).toReal := hreal
    _ ≤ (a 1)⁻¹*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (fordSimplex N B)).toReal) :=
      mul_le_mul_of_nonneg_left (hconc N hN B hB i hi) (inv_nonneg.mpr ha.le)
    _ ≤ (a 1)⁻¹*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol (by positivity)) (inv_nonneg.mpr ha.le)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_CenterComparison
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparing the truncated simplex centers with the retained coarse bands. -/

noncomputable section

namespace TotientAsymptotic

lemma truncated_center_ratio {m q i ε : ℝ} (hmq : q < m) (hq : 0 ≤ q)
    (hi : 0 ≤ i) (him : i ≤ m-q) (hε : 0 ≤ ε) (hsmall : q ≤ ε*(m-i)) :
    (1-ε)*(m-i)/m ≤ (m-q-i)/(m-q) ∧ (m-q-i)/(m-q) ≤ (m-i)/m := by
  have hm : 0 < m := lt_of_le_of_lt hq hmq
  have hmq' : 0 < m-q := sub_pos.mpr hmq
  have hmi : 0 ≤ m-i := by linarith
  have h1 := mul_le_mul_of_nonneg_right hsmall hi
  have h2 := mul_le_mul_of_nonneg_left him (mul_nonneg hε hmi)
  constructor
  · apply (div_le_div_iff₀ hm hmq').mpr
    nlinarith
  · apply (div_le_div_iff₀ hmq' hm).mpr
    nlinarith [mul_nonneg hq hi]

lemma truncated_center_close {m q i : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (hqm : q < m) (hi : i ≤ m-q) (hq : 100*q ≤ m-i) :
    (99/100 : ℝ)*(S*((m-i : ℕ) : ℝ)/m) ≤ S*((m-q-i : ℕ) : ℝ)/(m-q : ℕ) ∧
      S*((m-q-i : ℕ) : ℝ)/(m-q : ℕ) ≤ S*((m-i : ℕ) : ℝ)/m := by
  have hqR : (q : ℝ) < m := by exact_mod_cast hqm
  have hiR : (i : ℝ) ≤ (m : ℝ)-q := by
    have hh : (i : ℝ)+(q : ℝ) ≤ m := by exact_mod_cast (show i+q ≤ m by omega)
    linarith
  have hsmall : (q : ℝ) ≤ (1/100 : ℝ)*((m : ℝ)-i) := by
    have hh : (100 : ℝ)*q ≤ (m : ℝ)-i := by
      have hn : 100*q+i ≤ m := by omega
      have hh : (100 : ℝ)*q+i ≤ m := by exact_mod_cast hn
      linarith
    linarith
  have hh := truncated_center_ratio hqR (Nat.cast_nonneg q) (Nat.cast_nonneg i) hiR
    (by norm_num : (0 : ℝ)≤1/100) hsmall
  have hmi : i ≤ m := by omega
  have hmqi : i ≤ m-q := hi
  rw [← Nat.cast_sub hmi, ← Nat.cast_sub (Nat.le_of_lt hqm),
    ← Nat.cast_sub hmqi] at hh
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.1 hS
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  · have h := mul_le_mul_of_nonneg_left hh.2 hS
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma outside_band_implies_deviation {b c u : ℝ} (hb : 0 < b)
    (hlo : (98/100 : ℝ)*b ≤ c) (hhi : c ≤ (102/100 : ℝ)*b)
    (hu : u < (95/100 : ℝ)*b ∨ (105/100 : ℝ)*b < u) :
    (1/40 : ℝ) < |u/c-1| := by
  have hc : 0 < c := lt_of_lt_of_le (by positivity) hlo
  by_contra! hh
  have hh' := abs_le.mp hh
  have hl : (39/40 : ℝ)*c ≤ u := (le_div_iff₀ hc).mp (by linarith [hh'.1])
  have hr : u ≤ (41/40 : ℝ)*c := (div_le_iff₀ hc).mp (by linarith [hh'.2])
  rcases hu with hu | hu <;> nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_TruncatedConcentration
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration at the full-scale bands after truncating the simplex. -/

noncomputable section
open MeasureTheory

namespace TotientAsymptotic

theorem truncated_simplex_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ (m q : ℕ) (B : ℝ), 0 < B → m-q=N+2 →
      ∀ i : Fin (N+2), i.val < N → 100*q ≤ m-(i.val+1) →
      (volume (prefixRegion (N+2) B 0 0 ∩ coarseCoordinateBad m B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := simplex_coordinate_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro N hN m q B hB hdim i hi hsmall
  have hqm : q < m := by omega
  have hik : i.val+1 ≤ m-q := by omega
  have him : i.val+1 < m := by omega
  have hmn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hS : 0 < B*rho^(i.val+1) := mul_pos hB (pow_pos rho_pos _)
  have hb : 0 < fullSimplexCenter m B (i.val+1) := by
    unfold fullSimplexCenter
    exact div_pos (mul_pos hS (Nat.cast_pos.mpr (Nat.sub_pos_of_lt him)))
      (Nat.cast_pos.mpr (by omega))
  have hcenter : fordSimplexCenter N B i =
      (B*rho^(i.val+1))*((N+2-(i.val+1) : ℕ) : ℝ)/(N+2) := by
    unfold fordSimplexCenter
    rw [Nat.cast_sub (by omega : i.val+1 ≤ N+2)]
    push_cast
    field_simp
  have hcompare := truncated_center_close hS.le hqm hik hsmall
  rw [hdim] at hcompare
  simp only [Nat.cast_add, Nat.cast_ofNat] at hcompare
  rw [← hcenter] at hcompare
  change (99/100 : ℝ)*fullSimplexCenter m B (i.val+1) ≤ fordSimplexCenter N B i ∧
    fordSimplexCenter N B i ≤ fullSimplexCenter m B (i.val+1) at hcompare
  have hbad : coarseCoordinateBad m B i ⊆ fordCoordinateBad N B i := by
    intro u hu
    apply outside_band_implies_deviation hb
      (by nlinarith [hcompare.1]) (by nlinarith [hcompare.2]) hu
  have hfin : volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i) ≠ ⊤ :=
    ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
      (measure_mono Set.inter_subset_left)
  exact (ENNReal.toReal_mono hfin (measure_mono (Set.inter_subset_inter_right _ hbad))).trans
    (hconc N hN B hB i hi)

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_ScaledConcentration
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coarse-band violations survive the small diagonal enlargement and are
therefore bounded by Ford's published coordinate concentration. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma rescaled_band_violation {b t u κ : ℝ} (hb : 0 < b)
    (ht : (99/100 : ℝ)*b ≤ t ∧ t ≤ (101/100 : ℝ)*b)
    (hκ : 1 ≤ κ ∧ κ ≤ (102/100 : ℝ))
    (hu : u < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u) :
    u/κ < (95/100 : ℝ)*b ∨ (105/100 : ℝ)*b < u/κ := by
  have hp : 0 < κ := lt_of_lt_of_le zero_lt_one hκ.1
  rcases hu with hu | hu
  · left
    apply (div_lt_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hκ.1 hb.le]
  · right
    apply (lt_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hκ.2 hb.le]

lemma volume_scaled_set_le {N : ℕ} (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    (S T : Set (Fin N → ℝ)) (hT : MeasurableSet T) (hfin : volume T ≠ ⊤)
    (hmap : Set.MapsTo (simplexScale κ) S T) :
    volume.real S ≤ (∏ i, κ i)*volume.real T := by
  have hp : 0 < ∏ i, κ i := Finset.prod_pos (fun i _ => hκ i)
  have hd : LinearMap.det (simplexScale κ) ≠ 0 := by
    rw [simplexScale_det]
    exact inv_ne_zero hp.ne'
  have hh : volume S ≤ ENNReal.ofReal (∏ i, κ i)*volume T := by
    have hsub : S ⊆ (simplexScale κ) ⁻¹' T := hmap
    apply (measure_mono hsub).trans_eq
    rw [← Measure.map_apply (simplexScale κ).continuous_of_finiteDimensional.measurable hT,
      Real.map_linearMap_volume_pi_eq_smul_volume_pi hd, simplexScale_det, inv_inv,
      abs_of_pos hp, Measure.smul_apply, smul_eq_mul]
  have hf : ENNReal.ofReal (∏ i, κ i)*volume T ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] using
    ENNReal.toReal_mono hf hh

lemma measurableSet_coarseCoordinateBad (m : ℕ) (B : ℝ) {N : ℕ} (i : Fin N) :
    MeasurableSet (coarseCoordinateBad m B i) := by
  exact ((isOpen_lt (continuous_apply i) continuous_const).union
    (isOpen_lt continuous_const (continuous_apply i))).measurableSet

/-- The concentration bound after diagonal normalization, before summing
retained coordinates. All scale and center comparisons are explicit. -/
theorem scaled_coarse_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ N ≥ N₀, ∀ (m q : ℕ) (B : ℝ), 0 < B → m-q=N+2 →
    ∀ (β₀ : ℝ) (β κ : Fin (N+2) → ℝ), 0 < β₀ →
      (∀ j, 0 < β j) → (∀ j, 0 < κ j) → (∀ j, β₀ ≤ κ j) →
      (∀ i j, i < j → β i*κ i ≤ κ j) →
    ∀ (i : Fin (N+2)) (t : ℝ), i.val < N → 100*q ≤ m-(i.val+1) →
      (99/100 : ℝ)*fullSimplexCenter m B (i.val+1) ≤ t →
      t ≤ (101/100 : ℝ)*fullSimplexCenter m B (i.val+1) →
      1 ≤ κ i → κ i ≤ (102/100 : ℝ) →
      volume.real (enlargedSimplex (N+2) B β₀ β ∩
        {u | u i < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u i}) ≤
        (∏ j, κ j)*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*
          volume.real (prefixRegion (N+2) B 0 0)) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := truncated_simplex_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro N hN m q B hB hdim β₀ β κ hβ₀ hβ hκ htop hstep i t hi hq htlo hthi hklo hkhi
  have hm : i.val+1 < m := by omega
  have hb : 0 < fullSimplexCenter m B (i.val+1) := by
    unfold fullSimplexCenter
    exact div_pos (mul_pos (mul_pos hB (pow_pos rho_pos _))
      (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hm))) (Nat.cast_pos.mpr (by omega))
  let T := prefixRegion (N+2) B 0 0 ∩ coarseCoordinateBad m B i
  have hT : MeasurableSet T := (measurableSet_prefixRegion _ _ _ _).inter
    (measurableSet_coarseCoordinateBad _ _ _)
  have hTf : volume T ≠ ⊤ := ne_top_of_le_ne_top (prefixRegion_volume_ne_top (by omega) B)
    (measure_mono Set.inter_subset_left)
  have hmap : Set.MapsTo (simplexScale κ)
      (enlargedSimplex (N+2) B β₀ β ∩
        {u | u i < (91/100 : ℝ)*t ∨ (109/100 : ℝ)*t < u i}) T := by
    intro u hu
    refine ⟨enlargedSimplex_mapsTo hβ₀ hβ hκ htop hstep hu.1, ?_⟩
    change simplexScale κ u i < _ ∨ _ < simplexScale κ u i
    rw [simplexScale_apply]
    exact rescaled_band_violation hb ⟨htlo, hthi⟩ ⟨hklo, hkhi⟩ hu.2
  exact (volume_scaled_set_le κ hκ _ T hT hTf hmap).trans
    (mul_le_mul_of_nonneg_left (hconc N hN m q B hB hdim i hi hq)
      (Finset.prod_nonneg (fun j _ => (hκ j).le)))

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PhaseBandTransfer
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase-band comparison and the actual coordinate scaling bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fullSimplexCenter_eq_fordBandScale {x : ℝ} {i : ℕ} (hi : i < m x) :
    fullSimplexCenter (m x) (B x) i = fordBandScale x i := by
  have hmR : (m x : ℝ) ≠ 0 := by exact_mod_cast (show m x ≠ 0 by omega)
  unfold fullSimplexCenter fordBandScale
  rw [Nat.cast_sub hi.le]
  field_simp

lemma phase_band_center_close : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    (99/100 : ℝ)*fullSimplexCenter (m x) (B x) i ≤ bandScale x i ∧
      bandScale x i ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) i := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    Metric.tendsto_nhds.mp bandCenterRatio_tendsto (1/200) (by norm_num)] with x hB hx
  intro i hi
  have ht := (bandScale_pos hi).le
  rw [fullSimplexCenter_eq_fordBandScale hi, fordBandScale_eq_ratio_mul hB hi]
  have hh : |bandCenterRatio x-1| < (1/200 : ℝ) := by
    simpa only [Real.dist_eq] using hx
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hh
  constructor <;> nlinarith


end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_FullBoxConcentration
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concentration for the actual phase bands in the enlarged full simplex. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

/-- Ford concentration at the actual manuscript phase bands, with the
Jacobian and truncation costs explicit. -/
theorem full_box_coordinate_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ {x : ℝ} {H N : ℕ}, N₀ ≤ N → 0 < B x → H ≤ m x →
      m x-P H=N+2 → P H+2 ≤ H → 100*P H ≤ H →
      Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) →
      (∀ k < m x, (99/100 : ℝ)*fullSimplexCenter (m x) (B x) k ≤ bandScale x k ∧
        bandScale x k ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) k) →
    ∀ i : Fin (N+2), i.val < R x H →
      volume.real (fullBoxSimplex x (N+2) ∩ phaseCoordinateBad x i) ≤
        Real.exp (simplexBoxTail 4 (P H))*C*
          Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := scaled_coarse_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro x H N hN hB hHm hdim hPH h100 hsmall hcenter i hi
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  let κ : Fin (N+2) → ℝ := enlargementScale β
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ)≤4) (m x-r)]
  have hκ : ∀ j, 0 < κ j := enlargementScale_pos hβ
  have hik : i.val+1 < m x := by unfold R at hi; omega
  have hiN : i.val < N := by unfold R at hi; omega
  have hi100 : 100*P H ≤ m x-(i.val+1) := by unfold R at hi; omega
  have hk1 : 1 ≤ κ i := Finset.one_le_prod (fun r _ => hβ r)
  have hkhi : κ i ≤ (102/100 : ℝ) := by
    apply (reverse_enlargement_coordinate hHm (simplexBoxError 4)
      (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4) i hi).trans
    rw [← simplexBoxTail_eq_tsum]
    exact hsmall
  have hb := hconc N hN (m x) (P H) (B x) hB hdim (β 0)
    (fun j => β (j.val+1)) κ (zero_lt_one.trans_le (hβ 0))
    (fun j => zero_lt_one.trans_le (hβ (j.val+1))) hκ
    (enlargementScale_top hβ) (enlargementScale_step hβ) i (bandScale x (i.val+1))
    hiN hi100 (hcenter _ hik).1 (hcenter _ hik).2 hk1 hkhi
  have hvol : volume.real (prefixRegion (N+2) (B x) 0 0) = G x (N+2) := by
    rw [measureReal_def, volume_zero_prefixRegion hB.le (by omega),
      ENNReal.toReal_ofReal (G_pos hB _).le]
  rw [hvol] at hb
  have hp := reverse_enlargement_jacobian (show P H ≤ m x by omega)
    (simplexBoxError 4) (simplexBoxError_nonneg (by norm_num))
    (summable_simplexBoxError_weighted 4)
  rw [hdim, ← simplexBoxTail_eq_tsum] at hp
  calc
    _ ≤ (∏ j, κ j)*(C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2)) := by
      simpa only [fullBoxSimplex, phaseCoordinateBad, β, Nat.sub_zero] using hb
    _ ≤ Real.exp (simplexBoxTail 4 (P H))*
        (C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*G x (N+2)) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (mul_pos hC (Real.exp_pos _)).le (G_pos hB _).le)
    _ = _ := by ring

/-- The loss for all retained coordinates is an exponential tail in `H`,
with no growing dimension factor. -/
theorem full_box_retained_concentration (hford : FordCoordinateConcentrationInput) :
    ∃ C c : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 < c ∧
    ∀ {x : ℝ} {H N : ℕ}, N₀ ≤ N → 0 < B x → H ≤ m x →
      m x-P H=N+2 → P H+2 ≤ H → 100*P H ≤ H → 2*P H ≤ H →
      Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) →
      (∀ k < m x, (99/100 : ℝ)*fullSimplexCenter (m x) (B x) k ≤ bandScale x k ∧
        bandScale x k ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) k) →
      ∀ hRN : R x H ≤ N+2,
      volume.real (retainedPhaseBad x H (N+2) hRN) ≤
        (Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
          ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))) := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := full_box_coordinate_concentration hford
  refine ⟨C, c, N₀, hC, hc, ?_⟩
  intro x H N hN hB hHm hdim hPH h100 hhalf hsmall hcenter hRN
  have heach (i : Fin (R x H)) :=
    hconc hN hB hHm hdim hPH h100 hsmall hcenter (Fin.castLE hRN i) i.isLt
  have hgeo := sum_retained_concentration hc hHm hhalf
  change (∑ i : Fin (R x H), Real.exp (-c*((m x-P H-(i.val+1) : ℕ) : ℝ))) ≤ _ at hgeo
  rw [hdim] at hgeo
  have hfactor : 0 ≤ Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2) :=
    mul_nonneg (mul_pos (Real.exp_pos _) hC).le (G_pos hB _).le
  calc
    _ ≤ ∑ i : Fin (R x H), volume.real
        (fullBoxSimplex x (N+2) ∩ phaseCoordinateBad x (Fin.castLE hRN i)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin (R x H), Real.exp (simplexBoxTail 4 (P H))*C*
        Real.exp (-c*((N+2-(i.val+1) : ℕ) : ℝ))*G x (N+2) := by
      exact Finset.sum_le_sum (fun i _ => heach i)
    _ = (Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
        ∑ i : Fin (R x H), Real.exp (-c*((N+2-(i.val+1) : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgeo hfactor

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedConcentration
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-dimensional band loss vanishes after both normalization and
the entire discrete-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma normalizedBandLoss_tendsto (K C : ℝ) {J c : ℝ} (hJ : 0 < J) (hc : 0 < c) :
    Tendsto (normalizedBandLoss K C J c) atTop (nhds 0) := by
  have h1 := (Real.continuous_exp.tendsto (0 : ℝ)).comp ((simplexBoxTail_tendsto 4).comp P_tendsto)
  have h2 := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have h3 := cofactor_concentration_tail_tendsto K hc
  have hh := ((h1.mul_const C).mul h2).mul h3
  have he : (fun H => normalizedBandLoss K C J c H) =
      (fun H => (Real.exp (simplexBoxTail 4 (P H))*C*projectedEnvelope J (P H))*
        (Real.exp (K*cofactorScale H)*(Real.exp (-c/2))^H/(1-Real.exp (-c/2)))) := by
    funext H
    unfold normalizedBandLoss
    ring
  change Tendsto (fun H => normalizedBandLoss K C J c H) atTop (nhds 0)
  rw [he]
  simpa only [Function.comp_def, Real.exp_zero, mul_zero, zero_mul] using hh

/-- For every fixed cofactor exponent, Ford concentration removes all
retained phase bands with an error tending to zero as the tail cut grows. -/
theorem normalized_retained_band_loss (hford : FordCoordinateConcentrationInput)
    (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
        ∀ N : ℕ, L x H=N+2 → ∀ hRN : R x H ≤ N+2,
        Real.exp (K*cofactorScale H)*volume.real (retainedPhaseBad x H (N+2) hRN) /
          G x (m x) ≤ δ H := by
  obtain ⟨C, c, N₀, hC, hc, hconc⟩ := full_box_retained_concentration hford
  obtain ⟨J, hJ, hproj⟩ := uniform_projected_volume_bound hren
  refine ⟨normalizedBandLoss K C J c, normalizedBandLoss_tendsto K C hJ hc, ?_⟩
  have hsmall : ∀ᶠ H : ℕ in atTop, Real.exp (simplexBoxTail 4 H) ≤ (102/100 : ℝ) := by
    have ht := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4)
    exact (ht.eventually (eventually_lt_nhds (by norm_num : Real.exp (0 : ℝ)<102/100))).mono
      (fun _ h => h.le)
  filter_upwards [eventually_tail_cut_separated, hsmall] with H hcuts hsmallH
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)), phase_band_center_close,
    hproj, m_tendsto.eventually (eventually_ge_atTop (N₀+P H+2)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hB hcenter hpr hmN hHm
  intro N hdim hRN
  have hN : N₀ ≤ N := by unfold L at hdim; omega
  have hdim' : m x-P H=N+2 := hdim
  have hv := hconc hN hB hHm hdim' hcuts.2.1 hcuts.2.2.1 hcuts.2.2.2 hsmallH hcenter hRN
  have hPm : P H ≤ m x := by omega
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hpr (P H) hPm)
  change G x (L x H) ≤ _ at hG
  rw [hdim] at hG
  have hq : Real.exp (-c/2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hgeo : 0 ≤ (Real.exp (-c/2))^H/(1-Real.exp (-c/2)) :=
    div_nonneg (pow_pos (Real.exp_pos _) _).le (sub_pos.mpr hq).le
  have hA : 0 ≤ Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
      ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))) := by positivity
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  calc
    _ ≤ Real.exp (K*cofactorScale H)*
        ((Real.exp (simplexBoxTail 4 (P H))*C*G x (N+2))*
          ((Real.exp (-c/2))^H/(1-Real.exp (-c/2)))) :=
      mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
    _ = (Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
        ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))))*G x (N+2) := by ring
    _ ≤ (Real.exp (K*cofactorScale H)*Real.exp (simplexBoxTail 4 (P H))*C*
        ((Real.exp (-c/2))^H/(1-Real.exp (-c/2))))*
        (projectedEnvelope J (P H)*G x (m x)) := mul_le_mul_of_nonneg_left hG hA
    _ = _ := by unfold normalizedBandLoss; ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PointEnclosure
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same box enclosure applies to completed continuous witness regions. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma point_cube_full_enclosure {x : ℝ} {N : ℕ} (hN : N < m x)
    (hBr : 1 ≤ B x*rho^(m x)) {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hdist : ∀ i, |u i-v i| ≤ 1)
    (hlower : ∀ i, 1 ≤ rho^(m x-(i.val+1))*v i) :
    v ∈ enlargedSimplex N (B x) (1+simplexBoxError 4 (m x))
      (fun i => 1+simplexBoxError 4 (m x-(i.val+1))) := by
  have hv (i : Fin N) : 0 ≤ v i := by
    have hp := pow_pos rho_pos (m x-(i.val+1))
    by_contra hn
    have hh := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    linarith [hlower i]
  have herr (i : Fin N) : ((N-i.val : ℕ) : ℝ)^2+1 ≤
      (4*((m x-(i.val+1) : ℕ) : ℝ)^2*rho^(m x-(i.val+1)))*v i := by
    have hi := i.isLt
    have hn : (1 : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show 1 ≤ m x-(i.val+1) by omega)
    have hh : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
      exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) hh 2
    have he := mul_le_mul_of_nonneg_left (hlower i)
      (show 0 ≤ 4*((m x-(i.val+1) : ℕ) : ℝ)^2 by positivity)
    nlinarith
  have htop : (N : ℝ)^2 ≤ (4*(m x : ℝ)^2*rho^(m x))*B x := by
    have hs : (N : ℝ)^2 ≤ (m x : ℝ)^2 := pow_le_pow_left₀
      (Nat.cast_nonneg _) (by exact_mod_cast hN.le) 2
    have he := mul_le_mul_of_nonneg_left hBr (show 0 ≤ 4*(m x : ℝ)^2 by positivity)
    nlinarith
  have hh := enlargedSimplex_cube hu (fun i => xi_bounds x (i.val+1)) hv hdist herr htop
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnionVolume
attribute [-instance] _root_.instMeasurableSpace
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

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BandRemoval
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the retained bands after aggregating complete witness boxes. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma fullBoxSimplex_volume_ne_top (x : ℝ) {N : ℕ} (hN : 0 < N) :
    volume (fullBoxSimplex x N) ≠ ⊤ := by
  let β : ℕ → ℝ := fun r => 1+simplexBoxError 4 (m x-r)
  have hβ : ∀ r, 1 ≤ β r := fun r => by
    dsimp [β]
    linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ) ≤ 4) (m x-r)]
  have hv := volume_enlargedSimplex_product_bound (N := N) (B x) β hβ
  change volume (fullBoxSimplex x N) ≤ _ at hv
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (prefixRegion_volume_ne_top hN (B x))) hv

lemma retainedPhaseBad_volume_ne_top (x : ℝ) (H : ℕ) {N : ℕ}
    (hN : 0 < N) (hRN : R x H ≤ N) : volume (retainedPhaseBad x H N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (fullBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
  exact hi.1

lemma eventually_scale_product_lower : ∀ᶠ x : ℝ in atTop, 1 ≤ B x*rho^(m x) := by
  have hgrow : Tendsto (fun x : ℝ => lam*(m x : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp m_tendsto).const_mul_atTop lam_pos
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    hgrow.eventually (eventually_ge_atTop (2 : ℝ))] with x hscale hB hm
  have hp : 0 < B x*rho^(m x) := mul_pos hB (pow_pos rho_pos _)
  have hh := (div_le_iff₀ hp).mp hscale
  rw [show 2/lam*(B x*rho^(m x)) = 2*(B x*rho^(m x))/lam by ring] at hh
  have hh' := (le_div_iff₀ lam_pos).mp hh
  nlinarith

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_PerturbationEnclosure
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The difference between the perturbed and exact witness regions lies
in the retained full-dimensional slack slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma joined_witness_prefixLinear {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hPH : P H ≤ H) (hHm : H ≤ m x) (u : Fin (R x H) → ℝ) (i : Fin (R x H)) :
    prefixLinear (R x H+(H-P H))
      (joinCoordinates (R x H) (H-P H) (u,tailVector η)) (Fin.castAdd (H-P H) i) =
      prefixLinear (R x H) u i-D (m x-(i.val+1)) η := by
  simp only [prefixLinear_apply, Fin.val_castAdd, joinCoordinates_left]
  rw [joined_prefix_row, ← prefix_D_tailVector η hPH hHm]
  ring

lemma row_cube_error_le_boxSlack {x : ℝ} {N : ℕ} (hN : N < m x) (i : Fin N) :
    ((N-i.val : ℕ) : ℝ)^2 ≤ boxSlackError x (i.val+1) := by
  have hi := i.isLt
  have hh : ((N-i.val : ℕ) : ℝ) ≤ (m x-(i.val+1) : ℕ) := by
    exact_mod_cast (show N-i.val ≤ m x-(i.val+1) by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (N-i.val) (α := ℝ)) hh 2
  have hp : 0 ≤ (xi x (i.val+1)-1)*((11/10 : ℝ)*bandScale x (i.val+1)) :=
    mul_nonneg (xi_sub_one_pos _ _).le (mul_nonneg (by norm_num) (bandScale_nonneg _ _))
  dsimp [boxSlackError]
  nlinarith [sq_nonneg (((m x-(i.val+1) : ℕ) : ℝ))]

lemma top_cube_error_le_boxTop {x : ℝ} {N : ℕ} (hB : 0 ≤ B x) (hN : N ≤ m x) :
    (N : ℝ)^2 ≤ boxTopError x := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg N (α := ℝ))
    (show (N : ℝ) ≤ m x by exact_mod_cast hN) 2
  have ht := topPerturbation_nonneg hB
  dsimp [boxTopError]
  nlinarith [sq_nonneg (m x : ℝ)]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundaryEnclosure
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A box crossing a witness-region boundary meets a retained slack slice
or a fixed-deviation band exceptional set. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma join_witness_band_lower {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H ≤ H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hb : u ∈ prefixBandRegion x H) :
    ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤
      joinCoordinates (R x H) (H-P H) (u,tailVector η) i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [joinCoordinates_left, Fin.val_castAdd] using (hb j).1
  · simp only [joinCoordinates_right, Fin.val_natAdd]
    have hj := j.isLt
    have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
    have hm : H-1-j.val ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    simpa only [tailVector, bandScale, he, mul_assoc] using (hη.2.2.1 _ hm).2.1

lemma witness_full_cube_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ))
    (hP : 1 ≤ P H) (hPH : P H < H) (hHm : H ≤ m x)
    (hBr : 1 ≤ B x*rho^(m x)) (hη : IsWitness H (theta x) η)
    {u u₀ : Fin (R x H) → ℝ}
    (hu₀ : u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hu : ∀ i, |u₀ i-u i| ≤ 1) {v : Fin (H-P H) → ℝ}
    (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      fullBoxSimplex x (R x H+(H-P H)) ∩ additiveBoxSimplex x (R x H+(H-P H)) := by
  have hN : R x H+(H-P H) < m x := by unfold R; omega
  have hz := join_witness_perturbed_enlarged hη hPH hHm hu₀.1 hu₀.2
  have hlo := join_witness_band_lower hη hPH.le hHm hu₀.2
  have hhi := join_witness_band_upper hη hPH.le hHm hu₀.2
  have hd : ∀ i, |joinCoordinates (R x H) (H-P H) (u₀,tailVector η) i-
      joinCoordinates (R x H) (H-P H) (u,v) i| ≤ 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using hu j
    · simpa only [joinCoordinates_right] using hv j
  refine ⟨point_cube_full_enclosure hN hBr hz hd ?_,
    banded_simplex_cube_additive hN hz hhi hd⟩
  intro i
  exact cube_band_lower hs hcut (by have hi := i.isLt; unfold R at hi; omega) (hlo i) (hd i)

lemma exact_failure_shell {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hB : 0 ≤ B x) (hN : R x H+(H-P H) < m x)
    (hPH : P H ≤ H) (hHm : H ≤ m x)
    {w : Fin (R x H) → ℝ} (hw : w ∉ tailPrefixRegion x H η)
    {y : Fin (R x H+(H-P H)) → ℝ} (hy : y ∈ additiveBoxSimplex x (R x H+(H-P H)))
    (hd : ∀ i, |joinCoordinates (R x H) (H-P H) (w,tailVector η) i-y i| ≤ 1) :
    y ∈ additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  let z := joinCoordinates (R x H) (H-P H) (w,tailVector η)
  by_cases htop : (∑ i, a (i.val+1)*w i) ≤ B x-D (m x) η
  · have hfail : ∃ i, prefixLinear (R x H) w i < D (m x-(i.val+1)) η := by
      by_contra! hall
      exact hw ⟨hall, htop⟩
    obtain ⟨i, hi⟩ := hfail
    have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
        Fin.castAdd (H-P H) i := Fin.ext rfl
    have hzneg : prefixLinear (R x H+(H-P H)) z (Fin.castAdd (H-P H) i) < 0 := by
      rw [joined_witness_prefixLinear η hPH hHm]
      linarith
    have hdiff := (neg_le_abs _).trans (prefixLinear_cube_error z y hd (Fin.castAdd (H-P H) i))
    have hrow := row_cube_error_le_boxSlack hN (Fin.castAdd (H-P H) i)
    simp only [Fin.val_castAdd] at hrow hdiff
    have hstrict : prefixLinear (R x H+(H-P H)) y (Fin.castAdd (H-P H) i) <
        boxSlackError x (i.val+1) := by linarith
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i, hy, ?_⟩
    intro hgood
    have hh := hgood.1 (Fin.castLE (Nat.le_add_right _ _) i)
    rw [raiseThreshold, Function.update_self, he] at hh
    simp only [Fin.val_castAdd] at hh
    linarith
  · apply Or.inl
    refine ⟨hy, ?_⟩
    intro hgood
    have hzgt : B x < ∑ j, a (j.val+1)*z j := by
      dsimp [z]
      rw [joined_budget, ← top_D_tailVector η hPH hHm]
      linarith
    have hdiff := (le_abs_self _).trans (prefixBudget_cube_error z y hd)
    have herr := top_cube_error_le_boxTop hB hN.le
    have hh := hgood.2
    linarith

lemma band_endpoint_neighborhood {x : ℝ} {H : ℕ} {u w : Fin (R x H) → ℝ}
    (hw : w ∉ prefixBandRegion x H) (hd : ∀ i, |w i-u i| ≤ 1)
    (hlarge : ∀ i : Fin (R x H), 100 < bandScale x (i.val+1)) :
    ∃ i, u i < (91/100 : ℝ)*bandScale x (i.val+1) ∨
      (109/100 : ℝ)*bandScale x (i.val+1) < u i := by
  change ¬ ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ w i ∧
    w i ≤ (11/10 : ℝ)*bandScale x (i.val+1) at hw
  push Not at hw
  obtain ⟨i, hi⟩ := hw
  refine ⟨i, ?_⟩
  have hdist := abs_le.mp (hd i)
  have hb := hlarge i
  by_cases hlo : (9/10 : ℝ)*bandScale x (i.val+1) ≤ w i
  · right
    have hh := hi hlo
    linarith
  · left
    have hh := lt_of_not_ge hlo
    linarith

/-- Every point in a crossing box belongs to one of the two already
controlled full-dimensional exceptional regions. -/
theorem witness_boundary_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hs : 0 ≤ theta x) (hB : 0 ≤ B x) (hcut : 4 ≤ lam*(P H : ℝ))
    (hP : 1 ≤ P H) (hPH : P H < H) (hHm : H ≤ m x)
    (hBr : 1 ≤ B x*rho^(m x)) (hη : IsWitness H (theta x) η)
    (hlarge : ∀ i : Fin (R x H), 100 < bandScale x (i.val+1))
    {u u₀ w : Fin (R x H) → ℝ}
    (hu₀ : u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hu : ∀ i, |u₀ i-u i| ≤ 1)
    (hw : w ∉ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hwu : ∀ i, |w i-u i| ≤ 1) {v : Fin (H-P H) → ℝ}
    (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) ∪
        retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  have hy := witness_full_cube_enclosure hs hcut hP hPH hHm hBr hη hu₀ hu hv
  by_cases hwb : w ∈ prefixBandRegion x H
  · left
    have hwt : w ∉ tailPrefixRegion x H η := fun ht =>
      hw ⟨banded_tailRegion_subset_perturbed η hB ⟨ht, hwb⟩, hwb⟩
    apply exact_failure_shell hB (by unfold R; omega) hPH.le hHm hwt hy.2
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using hwu j
    · simpa only [joinCoordinates_right] using hv j
  · right
    obtain ⟨i, hi⟩ := band_endpoint_neighborhood hwb hwu hlarge
    change _ ∈ ⋃ i : Fin (R x H), fullBoxSimplex x _ ∩
      phaseCoordinateBad x (Fin.castLE (Nat.le_add_right _ _) i)
    refine Set.mem_iUnion.mpr ⟨i, hy.1, ?_⟩
    have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
        Fin.castAdd (H-P H) i := Fin.ext rfl
    change _ < _ ∨ _ < _
    rw [he, joinCoordinates_left]
    simpa only [Fin.val_castAdd] using hi

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedShell
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Additive boundary slices vanish after the smooth-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma normalizedShellLoss_tendsto (K C : ℝ) {J : ℝ} (hJ : 0 < J) :
    Tendsto (normalizedShellLoss K C J) atTop (nhds 0) := by
  have ht0 : Tendsto (fun H => C*boxErrorTail (P H)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using (boxErrorTail_tendsto.comp P_tendsto).const_mul C
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp ht0
  have hp := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have ht := cofactor_boxErrorTail_tendsto K
  change Tendsto (fun H => normalizedShellLoss K C J H) atTop (nhds 0)
  simpa only [normalizedShellLoss, Function.comp_def, mul_zero, Real.exp_zero] using
    ((he.const_mul (4*C)).mul hp).mul ht

/-- All retained boundary slices have negligible normalized volume, even
after paying for every admissible smooth cofactor. -/
theorem normalized_additive_shell_loss (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ hRN : R x H ≤ L x H,
      Real.exp (K*cofactorScale H)*
        volume.real (additiveBoxShell x (R x H) (L x H) hRN)/G x (m x) ≤ δ H := by
  obtain ⟨C, hC, hcost⟩ := uniform_box_error_cost hren
  obtain ⟨D, hD, hambient⟩ := ambient_box_error_cost hren
  obtain ⟨J, hJ, hproj⟩ := uniform_projected_volume_bound hren
  let A := C+D
  have hA : 0 < A := add_pos hC hD
  refine ⟨normalizedShellLoss K A J, normalizedShellLoss_tendsto K A hJ, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with H hH
  have hPH := P_lt_self hH
  filter_upwards [hcost, hambient, hproj,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (2*H))] with x hx ha hp hB hm
  intro hRN
  have hHm : H ≤ m x := by omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H ≤ m x := Nat.sub_le _ _
  have hb := additiveBoxShell_volume_bound hB hL hRN
  have hE : 0 ≤ (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) := by
    apply mul_nonneg (by positivity)
    exact add_nonneg (boxTopError_nonneg hB.le) (Finset.sum_nonneg
      (fun i _ => mul_nonneg (g_pos _).le (boxSlackError_nonneg _ _)))
  have hEc : (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ A*boxErrorTail (P H) := by
    have hh := hx (P H) hPm
    change (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail (P H) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [A] <;> linarith) (boxErrorTail_nonneg _))
  have hRc := ha H (L x H) hm hLm
  have hRc' : 2*(L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ 4*A*boxErrorTail H := by
    calc
      _ = 2*((L x H : ℝ)/B x*(boxTopError x+
          ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1))) := by ring
      _ ≤ 2*(2*D*boxErrorTail H) := mul_le_mul_of_nonneg_left hRc (by norm_num)
      _ ≤ _ := by
        have hh : D ≤ A := by dsimp [A] <;> linarith
        have hmul := mul_le_mul_of_nonneg_right hh (boxErrorTail_nonneg H)
        nlinarith
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) hPm)
  change G x (L x H) ≤ projectedEnvelope J (P H)*G x (m x) at hG
  have hvol : volume.real (additiveBoxShell x (R x H) (L x H) hRN) ≤
      (4*A*boxErrorTail H)*Real.exp (A*boxErrorTail (P H))*
        (projectedEnvelope J (P H)*G x (m x)) := by
    apply hb.trans
    apply mul_le_mul (mul_le_mul hRc' (Real.exp_le_exp.mpr hEc) (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) hA.le) (boxErrorTail_nonneg H))) hG (G_pos hB _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le)
      (boxErrorTail_nonneg H)) (Real.exp_pos _).le
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  apply (mul_le_mul_of_nonneg_left hvol (Real.exp_pos _).le).trans_eq
  dsimp [normalizedShellLoss]
  ring

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundaryAggregation
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tail-box aggregation of all prefix boxes crossing a witness boundary. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

/-- A simultaneous boundary estimate for any measurable union of crossing
boxes, uniformly in the witnesses and the number of coordinates. -/
theorem witness_boundary_aggregation (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H (theta x) η) →
      ∀ S : TailDatum H → Set (Fin (R x H) → ℝ), (∀ η ∈ W, MeasurableSet (S η)) →
      (∀ η ∈ W, ∀ u ∈ S η,
        ∃ u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H,
          (∀ i, |u₀ i-u i| ≤ 1) ∧
          ∃ w, w ∉ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H ∧
            ∀ i, |w i-u i| ≤ 1) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*volume.real (S η))/G x (m x) ≤ ε H := by
  obtain ⟨C, hC, hagg⟩ := all_cofactor_witness_aggregation hbox hmertens
  obtain ⟨δ, hδ, hshell⟩ := normalized_additive_shell_loss hren (4*(lam/rho))
  obtain ⟨ζ, hζ, hband⟩ := normalized_retained_band_loss hford hren (4*(lam/rho))
  refine ⟨fun H => C*(δ H+ζ H), by simpa using (hδ.add hζ).const_mul C, ?_⟩
  have hlarge : ∀ᶠ H : ℕ in atTop, 100 < lam*(H : ℝ) :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop lam_pos)).eventually (eventually_gt_atTop (100 : ℝ))
  have hcut : ∀ᶠ H : ℕ in atTop, 4 ≤ lam*(P H : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp P_tendsto).const_mul_atTop lam_pos).eventually
      (eventually_ge_atTop (4 : ℝ))
  filter_upwards [hshell, hband, hlarge, hcut, eventually_tail_cut_separated,
    eventually_ge_atTop 2] with H hS hB hlargeH hcutH hcuts hH
  have hPH := P_lt_self hH
  filter_upwards [hS, hB, theta_eventually_mem, eventually_scale_product_lower,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+2))] with x hSx hBx hs hBr hBpos hm
  intro W hW S hSm hcross
  have hdim : L x H=R x H+(H-P H) := by unfold L R; omega
  have hn : 0 < R x H+(H-P H) := by unfold R; omega
  have hnormS : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ δ H := by
    rw [hdim] at hSx
    exact hSx (Nat.le_add_right _ _)
  have hnormB : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ ζ H := by
    obtain ⟨N, heq⟩ : ∃ N, R x H+(H-P H)=N+2 := ⟨R x H+(H-P H)-2, by omega⟩
    have hh := hBx N (hdim.trans heq)
    rw [← heq] at hh
    exact hh (Nat.le_add_right _ _)
  let T := additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) ∪
    retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _)
  have hfT : volume T ≠ ⊤ := (measure_union_lt_top
    (additiveBoxShell_volume_ne_top x (Nat.le_add_right _ _) hn).lt_top
    (retainedPhaseBad_volume_ne_top x H hn (Nat.le_add_right _ _)).lt_top).ne
  have hsum := hagg hs hPH.le W S T hW hSm hfT (by
    intro η hη u hu v hv
    obtain ⟨u₀, hu₀, hdu, w₀, hw₀, hdw⟩ := hcross η hη u hu
    apply witness_boundary_enclosure hs.1 hBpos.le hcutH hcuts.1 hPH (by omega)
      hBr (hW η hη) _ hu₀ hdu hw₀ hdw hv
    intro i
    have hi := i.isLt
    have hh : H ≤ m x-(i.val+1) := by unfold R at hi; omega
    have hcast : (H : ℝ) ≤ (m x-(i.val+1) : ℕ) := by exact_mod_cast hh
    exact (hlargeH.trans_le (mul_le_mul_of_nonneg_left hcast lam_pos.le)).trans_le
      (bandScale_lower hs.1 (i.val+1)))
  have hnormT : Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T/G x (m x) ≤ δ H+ζ H := by
    have hv := measureReal_union_le (μ := volume)
      (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))
      (retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _))
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le) (G_pos hBpos _).le).trans
    simpa only [mul_add, add_div] using add_le_add hnormS hnormB
  calc
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T)/G x (m x) :=
      div_le_div_of_nonneg_right hsum (G_pos hBpos _).le
    _ = C*(Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T/G x (m x)) := by ring
    _ ≤ C*(δ H+ζ H) := mul_le_mul_of_nonneg_left hnormT hC.le

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_WitnessUnionLoss
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the band-removal estimate to the actual unions at each tail value. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma mem_activeWitnesses {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) : η ∈ activeWitnesses H s ↔ IsWitness H s η := by
  simp only [activeWitnesses, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨witness_mem_allTailData hs h, h⟩⟩

lemma sum_witness_fibers {H : ℕ} {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (F : TailDatum H → ℝ) :
    (∑ d ∈ Finset.Icc 1 (tailValueBound H), ∑ η ∈ witnessFinset H s d, F η) =
      ∑ η ∈ activeWitnesses H s, F η := by
  have hmaps : ∀ η ∈ activeWitnesses H s,
      (w η).totient ∈ Finset.Icc 1 (tailValueBound H) := by
    intro η hη
    have hw := (mem_activeWitnesses hs).mp hη
    exact Finset.mem_Icc.mpr ⟨Nat.totient_pos.mpr (witness_w_pos hw),
      witness_totient_bound hs η ⟨hw, rfl⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  ext η
  rw [mem_witnessFinset hs, Finset.mem_filter, mem_activeWitnesses hs]
  rfl

lemma weighted_witness_fibers {H : ℕ} {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (F : TailDatum H → ℝ) :
    (∑ d ∈ Finset.Icc 1 (tailValueBound H),
      (d : ℝ)⁻¹*∑ η ∈ witnessFinset H s d, F η) =
      ∑ η ∈ activeWitnesses H s, ((w η).totient : ℝ)⁻¹*F η := by
  rw [← sum_witness_fibers hs]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [((mem_witnessFinset hs).mp hη).2]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_VolumeComparison
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The banded perturbed volume and the exact finite coefficient differ by
a vanishing normalized error. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma bandedWitnessRegion_eq {x : ℝ} {H : ℕ}
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    bandedWitnessRegion x H d = perturbedWitnessUnion x H d := by
  ext u
  simp only [bandedWitnessRegion, perturbedWitnessUnion, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hb, η, hη, hu⟩
    exact ⟨η, (mem_witnessFinset hs).mpr hη, hu, hb⟩
  · rintro ⟨η, hη, hu, hb⟩
    exact ⟨hb, η, (mem_witnessFinset hs).mp hη, hu⟩

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_BoundaryGrid
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite boundary-box error in the prime mass comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma gridBoundary_card_eq {N : ℕ} (K : Finset (Fin N → ℕ)) (S : Set (Fin N → ℝ)) :
    ((gridOuter K S).card : ℝ)-(gridInner K S).card =
      ((gridOuter K S \ gridInner K S).card : ℝ) := by
  rw [Finset.card_sdiff_of_subset (gridInner_subset_outer K S),
    Nat.cast_sub (Finset.card_le_card (gridInner_subset_outer K S))]

lemma gridBoundary_card_bound {x : ℝ} {H : ℕ}
    (hs : theta x ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    ((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ)-
      (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card ≤
    ∑ η ∈ witnessFinset H (theta x) d, ((witnessBoundaryGrid x H η).card : ℝ) := by
  rw [gridBoundary_card_eq]
  have hcover : gridOuter (bandGrid x H) (bandedWitnessRegion x H d) \
      gridInner (bandGrid x H) (bandedWitnessRegion x H d) ⊆
      (witnessFinset H (theta x) d).biUnion (witnessBoundaryGrid x H) := by
    intro b hb
    obtain ⟨ho, hn⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨hbK, u, hub, hu⟩ := Finset.mem_filter.mp ho
    rw [bandedWitnessRegion_eq hs] at hu
    obtain ⟨η, hη⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hη, huη⟩ := Set.mem_iUnion.mp hη
    apply Finset.mem_biUnion.mpr
    refine ⟨η, hη, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hbK, u, hub, huη⟩
    · intro hinner
      have hall := (Finset.mem_filter.mp hinner).2
      apply hn
      refine Finset.mem_filter.mpr ⟨hbK, ?_⟩
      intro v hv
      rw [bandedWitnessRegion_eq hs]
      exact Set.mem_iUnion.mpr ⟨η, Set.mem_iUnion.mpr ⟨hη, hall hv⟩⟩
  exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le

lemma witnessBoundaryGrid_crossing {x : ℝ} {H : ℕ} {η : TailDatum H}
    {u : Fin (R x H) → ℝ} (hu : u ∈ gridRegion (witnessBoundaryGrid x H η)) :
    ∃ u₀ ∈ witnessBandedRegion x H η, (∀ i, |u₀ i-u i| ≤ 1) ∧
      ∃ w, w ∉ witnessBandedRegion x H η ∧ ∀ i, |w i-u i| ≤ 1 := by
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hb, hub⟩ := Set.mem_iUnion.mp hb
  obtain ⟨hbout, hbin⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨hbK, u₀, h₀b, h₀⟩ := Finset.mem_filter.mp hbout
  have hnot : ¬ unitGridCell b ⊆ witnessBandedRegion x H η := by
    intro hsub
    exact hbin (Finset.mem_filter.mpr ⟨hbK, hsub⟩)
  obtain ⟨w₀, hwb, hw₀⟩ := Set.not_subset.mp hnot
  exact ⟨u₀, h₀, unitGridCell_coordinate_distance h₀b hub,
    w₀, hw₀, unitGridCell_coordinate_distance hwb hub⟩

/-- The boundary-cardinality term appearing in the actual prime-grid
sandwich has a vanishing normalized reciprocal-tail-weighted sum. -/
theorem weighted_boundary_grid_error_oai (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput)
    (hford : FordCoordinateConcentrationInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ Finset.Icc 1 (tailValueBound H), (d : ℝ)⁻¹*
        (((gridOuter (bandGrid x H) (bandedWitnessRegion x H d)).card : ℝ)-
          (gridInner (bandGrid x H) (bandedWitnessRegion x H d)).card))/G x (m x) ≤ ε H := by
  obtain ⟨ε, hε, hbound⟩ := witness_boundary_aggregation hbox hmertens hren hford
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbound] with H hH
  filter_upwards [hH, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hs hB
  have hh := hx (activeWitnesses H (theta x))
    (fun η hη => (mem_activeWitnesses hs).mp hη)
    (fun η => gridRegion (witnessBoundaryGrid x H η))
    (fun η _ => (witnessBoundaryGrid x H η).measurableSet_biUnion
      (fun b _ => measurableSet_unitGridCell b))
    (fun η _ _ hu => witnessBoundaryGrid_crossing hu)
  apply le_trans _ hh
  apply div_le_div_of_nonneg_right _ (G_pos hB _).le
  simp_rw [show ∀ η : TailDatum H, volume.real (gridRegion (witnessBoundaryGrid x H η)) =
      ((witnessBoundaryGrid x H η).card : ℝ) by intro η; exact gridRegion_volume_real _]
  rw [← weighted_witness_fibers hs]
  exact Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (gridBoundary_card_bound hs d) (by positivity))

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.weighted_boundary_grid_error_oai := @OAI.TotientAsymptotic.weighted_boundary_grid_error_oai
