-- Prove2me | solution 1 for OAI.TotientAsymptotic.coefficient_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:30:13.294908+00:00
-- url     : https://prove2.me/submissions/96018310-1a28-455a-9748-72e9bf1d21ca

import Batteries.Tactic.Lemma
import Mathlib
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Squarefree
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Fin.Tuple
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
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

lemma expOne_real_Ioi {t : ℝ} (ht : 0 ≤ t) :
    (expMeasure 1).real (Set.Ioi t) = Real.exp (-t) := by
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one, ite_eq_left ht, one_mul]
  ring

lemma expOne_Ioi {t : ℝ} (ht : 0 ≤ t) :
    expMeasure 1 (Set.Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [← expOne_real_Ioi ht, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma exponential_box_probability (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (hbs : Summable b) :
    exponentialProduct.real (Set.univ.pi (fun n => Set.Ioi (b n))) =
      Real.exp (-(∑' n, b n)) := by
  have hp : HasProd (fun n : ℕ => ENNReal.ofReal (Real.exp (-b n)))
      (ENNReal.ofReal (Real.exp (-∑' n, b n))) := by
    have hs := hbs.hasSum.neg.rexp
    have he := (ENNReal.continuous_ofReal.tendsto (Real.exp (-∑' n, b n))).comp hs
    unfold HasProd
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ext T
    exact (ENNReal.ofReal_prod_of_nonneg (fun n _ => Real.exp_nonneg (-b n))).symm
  unfold Measure.real exponentialProduct
  rw [Measure.infinitePi_pi_univ _ (fun _ => measurableSet_Ioi)]
  simp_rw [expOne_Ioi (hb _)]
  rw [hp.tprod_eq, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma measurableSet_witnessEvent {H : ℕ} (s : ℝ) (η : TailDatum H) :
    MeasurableSet (witnessEvent s η) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi)

lemma threshold_coefficient_pos (H n : ℕ) (s : ℝ) :
    0 < (gamma / alpha s) * rho^(H+n) :=
  mul_pos (div_pos gamma_pos (alpha_pos s)) (pow_pos rho_pos _)

lemma witnessEvent_intersection {H : ℕ} (s : ℝ) (T : Finset (TailDatum H)) (ht : T.Nonempty) :
    (⋂ η ∈ T, witnessEvent s η) =
      Set.univ.pi (fun n => Set.Ioi ((gamma / alpha s) * rho^(H+n) * maxD (H+n) T)) := by
  classical
  ext u
  simp only [Set.mem_iInter, witnessEvent, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioi]
  constructor
  · intro h n
    unfold maxD
    rw [dite_eq_left ht]
    rw [mul_comm ((gamma / alpha s) * rho^(H+n))]
    apply (lt_div_iff₀ (threshold_coefficient_pos H n s)).mp
    rw [Finset.sup'_lt_iff ht]
    intro η hη
    apply (lt_div_iff₀ (threshold_coefficient_pos H n s)).mpr
    simpa only [mul_comm] using h η hη n
  · intro h η hη n
    apply lt_of_le_of_lt _ (h n)
    apply mul_le_mul_of_nonneg_left _ (threshold_coefficient_pos H n s).le
    unfold maxD
    rw [dite_eq_left ht]
    exact Finset.le_sup' (s := T) (D (H+n)) hη

lemma witnessEvent_intersection_probability {H : ℕ} {s : ℝ}
    (T : Finset (TailDatum H)) (ht : T.Nonempty) (hT : ∀ η ∈ T, IsWitness H s η) :
    exponentialProduct.real (⋂ η ∈ T, witnessEvent s η) =
      Real.exp (-(gamma / alpha s) * ∑' n, rho^(H+n) * maxD (H+n) T) := by
  rw [witnessEvent_intersection s T ht]
  have hs : Summable (fun n => (gamma / alpha s) * rho^(H+n) * maxD (H+n) T) := by
    simpa only [mul_assoc] using (summable_tail_threshold hT).mul_left (gamma / alpha s)
  rw [exponential_box_probability _ (fun n => mul_nonneg
    (threshold_coefficient_pos H n s).le (maxD_nonneg hT (by omega))) hs]
  congr 1
  simp only [mul_assoc, tsum_mul_left, neg_mul]

lemma coefficient_eq_union_probability (H : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (d : ℕ) :
    (∑ᶠ T : Finset (TailDatum H),
      if T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d then
        (-1 : ℝ)^(T.card-1) * Real.exp (-(gamma / alpha s) *
          ∑' n : ℕ, rho^(H+n) * maxD (H+n) T)
      else 0) =
    exponentialProduct.real (⋃ η ∈ (witnesses_finite H hs d).toFinset, witnessEvent s η) := by
  classical
  let W := (witnesses_finite H hs d).toFinset
  have hW (T : Finset (TailDatum H)) :
      (↑T : Set (TailDatum H)) ⊆ witnesses H s d ↔ T ⊆ W := by
    constructor
    · intro h η hη
      exact ((witnesses_finite H hs d).mem_toFinset).mpr (h hη)
    · intro h η hη
      exact ((witnesses_finite H hs d).mem_toFinset).mp (h hη)
  rw [finsum_eq_sum_of_support_subset _ (s := W.powerset.filter Finset.Nonempty)]
  · rw [measureReal_biUnion_eq_sum_powerset (fun η _ => measurableSet_witnessEvent s η)]
    apply Finset.sum_congr rfl
    intro T hT
    obtain ⟨hTW, ht⟩ := Finset.mem_filter.mp hT
    have hsub : (↑T : Set (TailDatum H)) ⊆ witnesses H s d :=
      (hW T).mpr (Finset.mem_powerset.mp hTW)
    rw [ite_eq_left ⟨ht, hsub⟩, witnessEvent_intersection_probability T ht
      (fun η hη => (hsub hη).1)]
    congr 1
    have hc : T.card + 1 = T.card - 1 + 2 := by
      have := Finset.card_pos.mpr ht
      omega
    rw [hc, pow_add]
    norm_num
  · intro T hT
    have ht : T.Nonempty ∧ (↑T : Set (TailDatum H)) ⊆ witnesses H s d := by
      by_contra h
      simp only [Function.mem_support, ite_eq_right h, ne_eq, not_true_eq_false] at hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((hW T).mp ht.2), ht.1⟩

theorem AH_nonneg (H : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : ∀ r : ℝ, 1 ≤ r → 0 ≤ f r ∧ f r ≤ 1) :
    0 ≤ AH H f s := by
  classical
  unfold AH
  apply mul_nonneg (mul_nonneg (pow_nonneg rho_pos.le _)
    (pow_nonneg (div_pos gamma_pos (alpha_pos s)).le _))
  apply finsum_nonneg
  intro d
  split_ifs with hd
  · apply mul_nonneg (div_nonneg (hf _ (one_le_ell_ratio hd)).1 (Nat.cast_nonneg d))
    rw [coefficient_eq_union_probability H hs d]
    exact measureReal_nonneg
  · exact le_rfl

end TotientAsymptotic

end

end OAI
end

section
-- module Solutions.OAIQ233_TA.TotientAsymptotic_UnconditionalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Asymptotic counting and least-preimage interval theorems. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem coefficient_nonnegative_oai (H : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ AH H (fun _ => 1) s :=
  AH_nonneg H hs (fun _ => 1) (fun _ _ => ⟨zero_le_one, le_rfl⟩)

end TotientAsymptotic

end

end OAI
end

theorem solution : type_of% @OAI.TotientAsymptotic.coefficient_nonnegative_oai := @OAI.TotientAsymptotic.coefficient_nonnegative_oai
