-- Prove2me | solution 1 for OAI.TotientAsymptotic.strict_slack_tuple_discard
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:39:34.394712+00:00
-- url     : https://prove2.me/submissions/5ac51034-19a9-4d7d-8d0b-b56ea1ac88fe

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackCost
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The additional polynomial-width shell needed to discard failures of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma inverseSquareSum_nonneg : 0 ≤ inverseSquareSum :=
  tsum_nonneg (fun _ => by positivity)

lemma inverseSquare_summable : Summable (fun n : ℕ => 1/((n+1 : ℕ) : ℝ)^2) := by
  exact (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow).mpr (by norm_num))

lemma inverseCube_prefix_sum {H m : ℕ} (hH : 1 ≤ H) (hHm : H ≤ m) :
    (∑ i : Fin (m-H), 1/((m-(i.val+1) : ℕ) : ℝ)^3) ≤ inverseSquareSum/H := by
  rw [sum_reverse_prefix hHm (fun h => 1/(h : ℝ)^3)]
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ ∑ j ∈ Finset.range (m-H), (1/(H : ℝ))*(1/((j+1 : ℕ) : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro j _
      have ha : (0 : ℝ) < (H+j : ℕ) := by exact_mod_cast (show 0 < H+j by omega)
      have hb : (0 : ℝ) < (j+1 : ℕ) := by positivity
      have h1 : (H : ℝ) ≤ (H+j : ℕ) := by exact_mod_cast (Nat.le_add_right H j)
      have h2 : ((j+1 : ℕ) : ℝ) ≤ (H+j : ℕ) := by exact_mod_cast (show j+1 ≤ H+j by omega)
      have hsq := pow_le_pow_left₀ hb.le h2 2
      have hprod := mul_le_mul h1 hsq (sq_nonneg _) ha.le
      have hden : (H : ℝ)*((j+1 : ℕ) : ℝ)^2 ≤ ((H+j : ℕ) : ℝ)^3 := by nlinarith
      calc
        _ ≤ 1/((H : ℝ)*((j+1 : ℕ) : ℝ)^2) :=
          one_div_le_one_div_of_le (mul_pos hH0 (sq_pos_of_pos hb)) hden
        _ = _ := by field_simp
    _ = (1/(H : ℝ))*∑ j ∈ Finset.range (m-H), 1/((j+1 : ℕ) : ℝ)^2 := by rw [Finset.mul_sum]
    _ ≤ (1/(H : ℝ))*inverseSquareSum :=
      mul_le_mul_of_nonneg_left (inverseSquare_summable.sum_le_tsum _ (fun _ _ => by positivity))
        (by positivity)
    _ = _ := by ring

/-- The strict-slack width, unlike the prime-grid width, only decays
polynomially. Its total slice cost is still small enough for all cofactors. -/
theorem uniform_strict_slack_cost (hren : FordRenewalInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H N : ℕ,
      1 ≤ H → H ≤ m x → N ≤ m x →
      (N : ℝ)/B x*((B x)/(m x : ℝ)^4+
        ∑ i : Fin (R x H), g (i.val+1)*
          ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) ≤ C/H := by
  obtain ⟨A,hA,hslice⟩ := uniform_slice_bound hren
  have hlam := lam_pos
  have hrho := rho_pos
  let C := 1+(11/10 : ℝ)*A*(lam/rho)*inverseSquareSum
  have hC : 0 < C := by
    have := inverseSquareSum_nonneg
    dsimp [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hslice, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx htheta hB
  intro H N hH hHm hN
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hm0 : (0 : ℝ) < m x := by exact_mod_cast (show 0 < m x by omega)
  have htop : (N : ℝ)/B x*(B x/(m x : ℝ)^4) ≤ 1/(H : ℝ) := by
    have hn : (N : ℝ) ≤ m x := by exact_mod_cast hN
    have hmH : (H : ℝ) ≤ m x := by exact_mod_cast hHm
    have hm1 : (1 : ℝ) ≤ m x := by exact_mod_cast (show 1 ≤ m x by omega)
    have hm2 : (m x : ℝ)^2 ≤ (m x : ℝ)^4 := by nlinarith [sq_nonneg ((m x : ℝ)^2-1)]
    have hcross : (N : ℝ)*H ≤ (m x : ℝ)^4 :=
      (mul_le_mul hn hmH (Nat.cast_nonneg _) hm0.le).trans (by simpa [sq] using hm2)
    rw [show (N : ℝ)/B x*(B x/(m x : ℝ)^4) = (N : ℝ)/(m x : ℝ)^4 by field_simp]
    exact (div_le_div_iff₀ (pow_pos hm0 _) hH0).mpr (by simpa using hcross)
  have hrow (i : Fin (R x H)) :
      (N : ℝ)/B x*(g (i.val+1)*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) ≤
      ((11/10 : ℝ)*A*(lam/rho))*(1/((m x-(i.val+1) : ℕ) : ℝ)^3) := by
    have hi := i.isLt
    have him : i.val+1 < m x := by unfold R at hi; omega
    have hp : (0 : ℝ)<(m x-(i.val+1) : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt him
    have hs : (N : ℝ)*g (i.val+1)/B x ≤ A*rho^(m x-(i.val+1)) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hN)
        (g_pos _).le) hB.le).trans (hx _ him.le)
    calc
      _ = ((N : ℝ)*g (i.val+1)/B x)*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4) := by ring
      _ ≤ (A*rho^(m x-(i.val+1)))*
        ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4) :=
        mul_le_mul_of_nonneg_right hs (div_nonneg
          (mul_nonneg (by norm_num) (bandScale_nonneg _ _)) (by positivity))
      _ = ((11/10 : ℝ)*A*alpha (theta x))*(1/((m x-(i.val+1) : ℕ) : ℝ)^3) := by
        unfold bandScale
        field_simp [(pow_pos rho_pos _).ne',hp.ne']
      _ ≤ _ := by
        gcongr
        exact alpha_le _ htheta
  rw [mul_add, Finset.mul_sum]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hinv := inverseCube_prefix_sum hH hHm
  have hnn : 0 ≤ (11/10 : ℝ)*A*(lam/rho) := by positivity
  have hh := mul_le_mul_of_nonneg_left hinv hnn
  rw [Finset.mul_sum] at hh
  apply (add_le_add htop (hsum.trans hh)).trans_eq
  dsimp [C]
  ring

lemma cofactor_inverse_cutoff_tendsto (K : ℝ) :
    Tendsto (fun H : ℕ => Real.exp (K*cofactorScale H)/(H : ℝ)) atTop (nhds 0) := by
  apply (cofactor_envelope_power_decay K (by norm_num : (0 : ℝ)<1)).congr'
  filter_upwards [eventually_ge_atTop 1] with H hH
  have hH0 : (0 : ℝ)<H := by exact_mod_cast hH
  rw [one_mul, Real.exp_sub, Real.exp_log hH0]

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackShell
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-dimensional thin region associated with a failure of strict slack. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma strictTopWidth_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ strictTopWidth x := by
  exact add_nonneg (mul_nonneg (by norm_num) (boxTopError_nonneg hB)) (div_nonneg hB (by positivity))

lemma strictSlackWidth_nonneg (x : ℝ) (i : ℕ) : 0 ≤ strictSlackWidth x i := by
  exact add_nonneg (mul_nonneg (by norm_num) (boxSlackError_nonneg x i))
    (div_nonneg (mul_nonneg (by norm_num) (bandScale_nonneg x i)) (by positivity))

lemma strictSlackShell_volume_ne_top (x : ℝ) {R N : ℕ} (hRN : R ≤ N) (hN : 0 < N) :
    volume (strictSlackShell x R N hRN) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (additiveBoxSimplex_volume_ne_top x hN)
  apply measure_mono
  intro u hu
  rcases hu with hu | hu
  · exact hu.1
  · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
    exact hi.1

theorem strictSlackShell_volume_bound {x : ℝ} {R N : ℕ}
    (hB : 0 < B x) (hN : 0 < N) (hRN : R ≤ N) :
    volume.real (strictSlackShell x R N hRN) ≤
      ((N : ℝ)/B x*(strictTopWidth x+
        ∑ i : Fin R, g (i.val+1)*strictSlackWidth x (i.val+1)))*
      Real.exp ((N : ℝ)/B x*(boxTopError x+
        ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N := by
  let F := Real.exp ((N : ℝ)/B x*(boxTopError x+
    ∑ i : Fin N, g (i.val+1)*boxSlackError x (i.val+1)))*G x N
  have htop := additive_top_shell_bound hB hN (boxTopError x)
    (fun i => boxSlackError x (i.val+1)) (boxTopError_nonneg hB.le)
    (fun i => boxSlackError_nonneg _ _) (strictTopWidth_nonneg hB.le)
  have htop' : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x-strictTopWidth x) 0
        (fun i => -boxSlackError x (i.val+1))) ≤ (strictTopWidth x*N/B x)*F := by
    simpa only [Pi.neg_def, additiveBoxSimplex, F, mul_assoc] using htop
  have hrow (i : Fin R) : volume.real (additiveBoxSimplex x N \
      prefixRegion N (B x+boxTopError x) 0
        (raiseThreshold (fun j => -boxSlackError x (j.val+1)) (Fin.castLE hRN i)
          (strictSlackWidth x (i.val+1)))) ≤
      (strictSlackWidth x (i.val+1)*N*g (i.val+1)/B x)*F := by
    have hh := additive_slack_shell_bound hB hN (boxTopError x)
      (fun j => boxSlackError x (j.val+1)) (boxTopError_nonneg hB.le)
      (fun j => boxSlackError_nonneg _ _) (Fin.castLE hRN i)
      (strictSlackWidth_nonneg x (i.val+1))
    simpa only [Pi.neg_def, Fin.val_castLE, additiveBoxSimplex, F, mul_assoc] using hh
  apply (measureReal_union_le _ _).trans
  apply (add_le_add htop' ((measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum (fun i _ => hrow i)))).trans_eq
  have heq : (∑ i : Fin R, strictSlackWidth x (i.val+1)*N*g (i.val+1)/B x) =
      ((N : ℝ)/B x)*∑ i : Fin R, g (i.val+1)*strictSlackWidth x (i.val+1) := by
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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_NormalizedStrictSlack
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict-slack slices remain negligible after summing the smooth cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

lemma normalizedStrictSlackLoss_tendsto (K A D : ℝ) {J : ℝ} (hJ : 0 < J) :
    Tendsto (normalizedStrictSlackLoss K A D J) atTop (nhds 0) := by
  have h1 : Tendsto (fun H => Real.exp (A*boxErrorTail (P H))) atTop (nhds 1) := by
    simpa only [mul_zero, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp
        ((boxErrorTail_tendsto.comp P_tendsto).const_mul A)
  have h2 := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have h3 := ((cofactor_boxErrorTail_tendsto K).const_mul (4*A)).add
    ((cofactor_inverse_cutoff_tendsto K).const_mul D)
  change Tendsto (fun H => normalizedStrictSlackLoss K A D J H) atTop (nhds 0)
  simpa only [normalizedStrictSlackLoss, Function.comp_def, mul_zero, add_zero] using
    (h1.mul h2).mul h3

theorem normalized_strict_slack_shell (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ hRN : R x H ≤ L x H,
      Real.exp (K*cofactorScale H)*
        volume.real (strictSlackShell x (R x H) (L x H) hRN)/G x (m x) ≤ δ H := by
  obtain ⟨C,hC,hcost⟩ := uniform_box_error_cost hren
  obtain ⟨D,hD,hambient⟩ := ambient_box_error_cost hren
  obtain ⟨E,hE,hstrict⟩ := uniform_strict_slack_cost hren
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound hren
  let A := C+D
  have hA : 0 < A := add_pos hC hD
  refine ⟨normalizedStrictSlackLoss K A E J,
    normalizedStrictSlackLoss_tendsto K A E hJ,?_⟩
  filter_upwards [eventually_ge_atTop 2] with H hH
  have hPH := P_lt_self hH
  filter_upwards [hcost,hambient,hstrict,hproj,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (2*H))] with x hc ha hs hp hB hm
  intro hRN
  have hHm : H ≤ m x := by omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H ≤ m x := Nat.sub_le _ _
  have hW : (L x H : ℝ)/B x*(strictTopWidth x+
      ∑ i : Fin (R x H), g (i.val+1)*strictSlackWidth x (i.val+1)) ≤
      4*A*boxErrorTail H+E/(H : ℝ) := by
    have heq : (L x H : ℝ)/B x*(strictTopWidth x+
        ∑ i : Fin (R x H), g (i.val+1)*strictSlackWidth x (i.val+1)) =
        2*((L x H : ℝ)/B x*(boxTopError x+
          ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)))+
        (L x H : ℝ)/B x*(B x/(m x : ℝ)^4+
          ∑ i : Fin (R x H), g (i.val+1)*
            ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) := by
      simp only [strictTopWidth,strictSlackWidth,mul_add,Finset.sum_add_distrib]
      simp_rw [show ∀ i : Fin (R x H), g (i.val+1)*(2*boxSlackError x (i.val+1)) =
        2*(g (i.val+1)*boxSlackError x (i.val+1)) by intro i; ring]
      rw [← Finset.mul_sum]
      ring
    rw [heq]
    have hr := ha H (L x H) hm hLm
    have ht := hs H (L x H) (by omega) hHm hLm
    have hh : D ≤ A := by dsimp [A] <;> linarith
    have hh' := mul_le_mul_of_nonneg_right hh (boxErrorTail_nonneg H)
    linarith
  have hExp : (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤
      A*boxErrorTail (P H) := by
    have hh := hc (P H) hPm
    change (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail (P H) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [A] <;> linarith)
      (boxErrorTail_nonneg _))
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) hPm)
  change G x (L x H) ≤ projectedEnvelope J (P H)*G x (m x) at hG
  have hnon : 0 ≤ 4*A*boxErrorTail H+E/(H : ℝ) := by
    exact add_nonneg (mul_nonneg (by positivity) (boxErrorTail_nonneg _)) (by positivity)
  have hvol : volume.real (strictSlackShell x (R x H) (L x H) hRN) ≤
      (4*A*boxErrorTail H+E/(H : ℝ))*Real.exp (A*boxErrorTail (P H))*
        (projectedEnvelope J (P H)*G x (m x)) := by
    apply (strictSlackShell_volume_bound hB hL hRN).trans
    exact mul_le_mul
      (mul_le_mul hW (Real.exp_le_exp.mpr hExp) (Real.exp_pos _).le hnon)
      hG (G_pos hB _).le (mul_nonneg hnon (Real.exp_pos _).le)
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  apply (mul_le_mul_of_nonneg_left hvol (Real.exp_pos _).le).trans_eq
  dsimp [normalizedStrictSlackLoss]
  ring

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedPrimeGrid
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-box summation for a specified subfamily of the actual basic tuples. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma restrictedPrimeTuples_subset_grid {x : ℝ} {H : ℕ}
    {Q : Finset (Fin (L x H) → ℕ)} (hQ : Q ⊆ fullPrimeTuples x H) :
    Q ⊆ gridPrimeTuples (restrictedPrimeGrid x H Q) := by
  intro p hp
  obtain ⟨b,hb,hpb⟩ := Finset.mem_biUnion.mp (fullPrimeTuples_subset_grid x H (hQ hp))
  have hc := (mem_primeBoxTuples_iff.mp hpb).2
  exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,p,hp,hc⟩,hpb⟩

lemma restrictedPrimeGrid_enclosure {x : ℝ} {H : ℕ}
    {Q : Finset (Fin (L x H) → ℕ)} {T : Set (Fin (L x H) → ℝ)}
    (henclose : ∀ p ∈ Q, ∀ v, (∀ i, |primePrefixCoord p i-v i| ≤ 1) → v ∈ T) :
    gridRegion (restrictedPrimeGrid x H Q) ⊆ T := by
  intro v hv
  obtain ⟨b,hv⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hb,hvb⟩ := Set.mem_iUnion.mp hv
  obtain ⟨_,p,hp,hpb⟩ := Finset.mem_filter.mp hb
  exact henclose p hp v (unitGridCell_coordinate_distance hpb hvb)

theorem restricted_prime_mass_bound (hford : FordUnitPrimeBoxInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ} {H : ℕ}, 0 ≤ theta x → P H ≤ m x →
      ∀ (Q : Finset (Fin (L x H) → ℕ)) (T : Set (Fin (L x H) → ℝ)),
      Q ⊆ fullPrimeTuples x H → volume T ≠ ⊤ →
      (∀ p ∈ Q, ∀ v, (∀ i, |primePrefixCoord p i-v i| ≤ 1) → v ∈ T) →
      (∑ p ∈ Q, reciprocalShiftWeight p) ≤
        (1+bandPrimeError C (9/10) (P H))*volume.real T := by
  obtain ⟨C,hC,hgrid⟩ := banded_grid_prime_mass_error hford
  refine ⟨C,hC,?_⟩
  intro x H hs hPm Q T hQ hT he
  have hg := hgrid hs (by norm_num : (0 : ℝ) < 9/10) hPm
    (restrictedPrimeGrid x H Q) (by
      intro b hb i
      exact bandGrid_bounds (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1 i)
  change |gridPrimeMass (N := L x H) (restrictedPrimeGrid x H Q)-
    (volume (gridRegion (N := L x H) (restrictedPrimeGrid x H Q))).toReal| ≤
      (volume (gridRegion (N := L x H) (restrictedPrimeGrid x H Q))).toReal*
        bandPrimeError C (9/10) (P H) at hg
  have hfac : 0 ≤ 1+bandPrimeError C (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hC.le (by norm_num : (0 : ℝ) < 9/10) (P H)]
  have hv : volume.real (gridRegion (restrictedPrimeGrid x H Q)) ≤ volume.real T :=
    ENNReal.toReal_mono hT (measure_mono (restrictedPrimeGrid_enclosure he))
  calc
    _ ≤ gridPrimeMass (restrictedPrimeGrid x H Q) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (restrictedPrimeTuples_subset_grid hQ)
        (fun p _ _ => reciprocalShiftWeight_nonneg p)
    _ ≤ (1+bandPrimeError C (9/10) (P H))*
        volume.real (gridRegion (restrictedPrimeGrid x H Q)) := by
      have hh := (le_abs_self _).trans hg
      change gridPrimeMass _ ≤ _*(volume (gridRegion (restrictedPrimeGrid x H Q))).toReal
      change gridPrimeMass _-(volume (gridRegion _)).toReal ≤ _ at hh
      exact (sub_le_iff_le_add.mp hh).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left hv hfac

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
-- module Solutions.OAIQ233_TA.TotientAsymptotic_RestrictedWitnessCount
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counting any specified family of full basic witnesses, with their cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma restricted_remainder_weight {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hs : theta x ∈ Set.Ico (0 : ℝ) 1)
    (S : Finset (RemainderDatum (L x H))) (hS : ∀ η ∈ S, IsBasicRemainder x H η) :
    (∑ η ∈ S, remainderReciprocalWeight η) ≤
      (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ S.image RemainderDatum.primes, reciprocalShiftWeight p := by
  let F : RemainderDatum (L x H) → ℕ × (Fin (L x H) → ℕ) := fun η => (η.cofactor,η.primes)
  have hinj : Function.Injective F := by
    intro η ξ h
    cases η
    cases ξ
    simpa only [F,Prod.mk.injEq,RemainderDatum.mk.injEq,and_comm] using h
  have he : (∑ η ∈ S, remainderReciprocalWeight η) =
      ∑ z ∈ S.image F, (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 := by
    rw [Finset.sum_image]
    · rfl
    · intro η _ ξ _ hh
      exact hinj hh
  rw [he]
  have hsub : S.image F ⊆ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes := by
    intro z hz
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (witness_cofactor_bound hs
      (extractTail_isWitness (hS η hη) hPH hHm)),Finset.mem_image.mpr ⟨η,hη,rfl⟩⟩
  calc
    _ ≤ ∑ z ∈ Finset.Icc 1 (tailCofactorBound H) ×ˢ S.image RemainderDatum.primes,
        (z.1.totient : ℝ)⁻¹*reciprocalShiftWeight z.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => mul_nonneg (by positivity) (reciprocalShiftWeight_nonneg z.2))
    _ = _ := by rw [Finset.sum_product]; simp only [← Finset.mul_sum,← Finset.sum_mul]

lemma witnessFamily_card {x : ℝ} {H : ℕ} (t : ℝ) (S : Finset (RemainderDatum (L x H))) :
    (witnessFamily t S).card = ∑ η ∈ S, (witnessHeadSet t η).card := by
  simp only [witnessFamily,witnessHeadSet,Finset.card_eq_sum_ones,Finset.sum_filter,
    Finset.sum_product]

theorem restricted_witness_count : ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
    ∀ t : ℝ, t ≤ x → ∀ S : Finset (RemainderDatum (L x H)),
    (∀ η ∈ S, IsBasicRemainder x H η) →
    ((witnessFamily t S).card : ℝ) ≤
      (10*x/Real.log x)*(∑ η ∈ S, remainderReciprocalWeight η) := by
  filter_upwards [largest_prime_count_upper,eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro H hPH t ht S hS
  rw [witnessFamily_card,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro η hη
  let ζ := prefixOfRemainder x H η
  have hz : IsPrefixDatum x H ζ := (isPrefixDatum_iff x H ζ).mpr ⟨η,hS η hη,rfl⟩
  let D := ζ.d*∏ i, (ζ.primes i-1)
  have hD : 0 < D := basic_prefix_denominator_pos hPH hz
  have hh := hx D hD (witnessHeadSet t η) (by
    intro p hp
    have hb := (Finset.mem_filter.mp hp).2
    refine ⟨hb.1,hb.2.1,?_⟩
    have hv := hb.2.2.2
    change (tupleValue (TotientTuple.mk p ζ) : ℝ) ≤ t at hv
    rw [tupleValue_eq_head] at hv
    exact hv.trans ht)
  have hw := prefix_reciprocal_majorant (hS η hη) hPH
  change 1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ)) ≤ remainderReciprocalWeight η at hw
  have hcoef : 0 ≤ 10*x/Real.log x := by
    exact div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hx1).le) (Real.log_pos hx1).le
  apply hh.trans
  calc
    _ = (10*x/Real.log x)*(1/((ζ.d : ℝ)*∏ i, (ζ.primes i-1 : ℕ))) := by
      dsimp [D]
      push_cast
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw hcoef

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackEnclosure
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A failing strict-slack witness puts its entire unit prime box in a thin shell. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma strict_slack_cube_enclosure {x : ℝ} {R N : ℕ} (hRN : R ≤ N)
    (hB : 0 ≤ B x) (hN : N < m x) {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hb : ∀ i, u i ≤ (11/10 : ℝ)*bandScale x (i.val+1))
    (hf : u ∈ strictSlackFailure x R N hRN)
    (hd : ∀ i, |u i-v i| ≤ 1) : v ∈ strictSlackShell x R N hRN := by
  have hv := banded_simplex_cube_additive hN hu hb hd
  rcases hf with hf | ⟨i,hi⟩
  · apply Or.inl
    refine ⟨hv,?_⟩
    intro hgood
    have he := (le_abs_self _).trans (prefixBudget_cube_error u v hd)
    have ht := top_cube_error_le_boxTop hB hN.le
    have hh := hgood.2
    dsimp [strictTopWidth] at hh
    linarith
  · apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i,hv,?_⟩
    intro hgood
    have hh := hgood.1 (Fin.castLE hRN i)
    rw [raiseThreshold, Function.update_self] at hh
    have he := (neg_le_abs _).trans
      (prefixLinear_cube_error u v hd (Fin.castLE hRN i))
    have herr := row_cube_error_le_boxSlack hN (Fin.castLE hRN i)
    have hub := div_le_div_of_nonneg_right (hb (Fin.castLE hRN i))
      (show 0 ≤ ((m x-(i.val+1) : ℕ) : ℝ)^4 by positivity)
    simp only [Fin.val_castLE] at hh he herr hub
    dsimp [strictSlackWidth] at hh
    linarith

lemma failing_remainder_strict_slack {x : ℝ} {H : ℕ}
    (hPH : P H ≤ H) {η : RemainderDatum (L x H)} (hf : FailsStrictSlack η) :
    primePrefixCoord η.primes ∈ strictSlackFailure x (R x H) (L x H)
      (by unfold R L; omega) := by
  have hRL : R x H ≤ L x H := by unfold R L; omega
  change primePrefixCoord η.primes ∈ strictSlackFailure x (R x H) (L x H) hRL
  change _ ∨ ∃ j : Fin (R x H), _
  obtain ⟨i,hi,hfail⟩ := hf
  have hiR := (Finset.mem_Icc.mp hi).2
  by_cases hi0 : i=0
  · subst i
    left
    have hsum : (∑ r ∈ Finset.Icc (0+1) (L x H), a (r-0)*remainderCoord x η r) =
        ∑ j : Fin (L x H), a (j.val+1)*primePrefixCoord η.primes j := by
      rw [prefix_sum_fin]
      simp only [Nat.zero_lt_succ,ite_true, if_true,Nat.sub_zero,remainderCoord_fin]
    rw [hsum,show remainderCoord x η 0=B x from rfl] at hfail
    simp only [Nat.sub_zero] at hfail
    convert hfail using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · right
    let j : Fin (R x H) := ⟨i-1,by omega⟩
    have he : j.val+1=i := by dsimp [j]; omega
    refine ⟨j,?_⟩
    have hc : remainderCoord x η i =
        primePrefixCoord η.primes (Fin.castLE hRL j) := by
      rw [← he]
      exact remainderCoord_fin x η (Fin.castLE hRL j)
    have hsum : (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) =
        primePrefixCoord η.primes (Fin.castLE hRL j)-
          prefixLinear (L x H) (primePrefixCoord η.primes) (Fin.castLE hRL j) := by
      rw [prefix_sum_fin, prefixLinear_apply]
      simp only [remainderCoord_fin, Fin.val_castLE]
      have hh : ∀ k : Fin (L x H), (i < k.val+1) = (j.val < k.val) := by
        intro k
        apply propext
        omega
      simp only [hh, Fin.lt_def,Fin.val_castLE]
      have hd : ∀ k : Fin (L x H), k.val+1-i=k.val-j.val := by
        intro k
        omega
      simp only [hd]
      ring
    rw [hc,hsum] at hfail
    have hfail' := hfail
    simp only [sub_mul,one_mul,div_eq_mul_inv,one_mul] at hfail'
    change prefixLinear (L x H) (primePrefixCoord η.primes) (Fin.castLE hRL j) <
      primePrefixCoord η.primes (Fin.castLE hRL j)/((m x-(j.val+1) : ℕ) : ℝ)^4
    rw [he,div_eq_mul_inv]
    nlinarith

lemma failing_remainder_box_enclosure {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hP : 1 ≤ P H) (hB : 0 ≤ B x)
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) (hf : FailsStrictSlack η)
    {v : Fin (L x H) → ℝ} (hd : ∀ i, |primePrefixCoord η.primes i-v i| ≤ 1) :
    v ∈ strictSlackShell x (R x H) (L x H) (by unfold R L; omega) := by
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H < m x := by unfold L; omega
  apply strict_slack_cube_enclosure _ hB hLm (basic_remainder_enlargedSimplex hL hη)
    _ (failing_remainder_strict_slack hPH.le hf) hd
  intro i
  have hh := (hη.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := i.isLt; omega⟩)).2.2
  simpa only [remainderCoord_fin] using hh

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_StrictSlackDiscard
attribute [-instance] _root_.instMeasurableSpace
attribute [-simp] _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.SelbergSieve.selbergBoundingSum _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.toSchwartz_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tuple discard caused by failure of the strict-slack condition. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma strictSlackTuples_card_le {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (strictSlackTuples x H t).card ≤ (witnessFamily t (strictSlackRemainders x H)).card := by
  have hsub : strictSlackTuples x H t ⊆
      (witnessFamily t (strictSlackRemainders x H)).image (fun q => witnessTuple q.2 q.1) := by
    intro τ hτ
    obtain ⟨hτ,η,hη,he⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    have hw : witnessTuple τ.head η=τ := by
      cases τ
      simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
    refine Finset.mem_image.mpr ⟨(η,τ.head),?_,hw⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hη,Finset.mem_range.mpr (basic_tuple_head_bound hPH hb)⟩,?_⟩
    exact hw.symm ▸ hb
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem strict_slack_reciprocal_mass (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ η ∈ strictSlackRemainders x H, remainderReciprocalWeight η) ≤ ε H*G x (m x) := by
  obtain ⟨C,hC,hcof⟩ := tail_cofactor_sum hmertens
  obtain ⟨D,hD,hprime⟩ := restricted_prime_mass_bound hbox
  obtain ⟨δ,hδ,hshell⟩ := normalized_strict_slack_shell hren (4*(lam/rho))
  let ε := fun H => C*(1+bandPrimeError D (9/10) (P H))*δ H
  have he : Tendsto ε atTop (nhds 0) := by
    have hb := (bandPrimeError_tendsto D (by norm_num : (0 : ℝ) < 9/10)).comp P_tendsto
    simpa only [ε,Function.comp_def,add_zero,mul_zero] using
      (((tendsto_const_nhds.add hb).const_mul C).mul hδ)
  refine ⟨ε,he,?_⟩
  filter_upwards [hshell,eventually_ge_atTop 2,P_tendsto.eventually (eventually_ge_atTop 1)]
    with H hH hH2 hP
  have hPH := P_lt_self hH2
  filter_upwards [hH,theta_eventually_mem,B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop H)] with x hx hs hB hHm
  let S := strictSlackRemainders x H
  let Q := S.image RemainderDatum.primes
  let T := strictSlackShell x (R x H) (L x H) (by unfold R L; omega)
  have hS : ∀ η ∈ S, IsBasicRemainder x H η := by
    intro η hη
    exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1
  have hQ : Q ⊆ fullPrimeTuples x H := by
    intro p hp
    obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨η,mem_basicRemainderFinset.mpr (hS η hη),rfl⟩
  have hL : 0 < L x H := by unfold L; omega
  have hp := hprime hs.1 (hPH.le.trans hHm) Q T hQ (strictSlackShell_volume_ne_top x _ hL)
    (by
      intro p hp v hd
      obtain ⟨η,hη,rfl⟩ := Finset.mem_image.mp hp
      exact failing_remainder_box_enclosure hPH hHm hP hB.le (hS η hη)
        (Finset.mem_filter.mp hη).2 hd)
  have hc : (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹) ≤
      C*Real.exp ((4*(lam/rho))*cofactorScale H) := by
    simpa only [cofactorScale,mul_assoc] using hcof H
  have hf : 0 ≤ 1+bandPrimeError D (9/10) (P H) := by
    linarith [bandPrimeError_nonneg hD.le (by norm_num : (0 : ℝ) < 9/10) (P H)]
  have hv : Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T ≤ δ H*G x (m x) :=
    (div_le_iff₀ (G_pos hB (m x))).mp (hx _)
  calc
    _ ≤ (∑ a ∈ Finset.Icc 1 (tailCofactorBound H), (a.totient : ℝ)⁻¹)*
        ∑ p ∈ Q, reciprocalShiftWeight p := restricted_remainder_weight hPH hHm hs S hS
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ∑ p ∈ Q, reciprocalShiftWeight p :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun p _ => reciprocalShiftWeight_nonneg p))
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H))*
        ((1+bandPrimeError D (9/10) (P H))*volume.real T) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (C*(1+bandPrimeError D (9/10) (P H)))*
        (Real.exp ((4*(lam/rho))*cofactorScale H)*volume.real T) := by ring
    _ ≤ (C*(1+bandPrimeError D (9/10) (P H)))*(δ H*G x (m x)) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg hC.le hf)
    _ = _ := by dsimp [ε] <;> ring

theorem strict_slack_tuple_discard_oai (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, t ≤ x →
      ((strictSlackTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨δ,hδ,hsmall⟩ := strict_slack_reciprocal_mass hbox hren hmertens
  refine ⟨fun H => 10*δ H,by simpa using hδ.const_mul 10,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 2] with H hH hH2
  have hPH := (P_lt_self hH2).le
  filter_upwards [hH,restricted_witness_count,eventually_gt_atTop (1 : ℝ)] with x hx hcount hx1
  intro t ht
  have hc : 0 ≤ 10*x/Real.log x := by
    exact div_nonneg (mul_nonneg (by norm_num) (zero_lt_one.trans hx1).le) (Real.log_pos hx1).le
  calc
    _ ≤ ((witnessFamily t (strictSlackRemainders x H)).card : ℝ) :=
      Nat.cast_le.mpr (strictSlackTuples_card_le hPH)
    _ ≤ (10*x/Real.log x)*(∑ η ∈ strictSlackRemainders x H, remainderReciprocalWeight η) :=
      hcount H hPH t ht _ (by
        intro η hη
        exact mem_basicRemainderFinset.mp (Finset.mem_filter.mp hη).1)
    _ ≤ (10*x/Real.log x)*(δ H*G x (m x)) := mul_le_mul_of_nonneg_left hx hc
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.strict_slack_tuple_discard_oai := @OAI.TotientAsymptotic.strict_slack_tuple_discard_oai
