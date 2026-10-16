-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_bounded_grid_site_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T22:10:27.890887+00:00
-- url     : https://prove2.me/submissions/6d34f916-9c32-48f3-9f0d-8b0fc431288a

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

variable {σ R W Z : Type*} [CommRing R] [AddCommGroup W] [Module R W]
  [AddCommGroup Z] [Module R Z]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {I R S W : Type*} [CommRing R] [CommRing S] [AddCommGroup W] [Module R W]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped TensorProduct Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem principalCoefficientChoice_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientChoice (G := G) (B := B) h d) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy).symm)
  | some b =>
    cases y with
    | none =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy))
    | some b' =>
      exact congrArg some (principalCoefficientSlot_injective h d hd hxy)

theorem principalCoefficientMarginal {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (p : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → PMF ℤ) :
    (independentProductPMF p).map (fun a r => a (principalCoefficientChoice h d r)) =
      independentProductPMF (fun r => p (principalCoefficientChoice h d r)) :=
  independentProductPMF_marginal p _ (principalCoefficientChoice_injective h d hd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {O : Type*} [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {O : Type*} [Fintype O]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem integerMonomialArrayPolynomial_principal_sum {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hzero : ∀ j, j ≠ j₀ → j ∉ P → a j = 0) :
    integerMonomialArrayPolynomial e a =
      MvPolynomial.C (a j₀) + ∑ j ∈ P, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hsum : (∑ j ∈ insert j₀ P, MvPolynomial.monomial (e j) (a j)) =
      ∑ j, MvPolynomial.monomial (e j) (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hne : j ≠ j₀ := fun he => hj (he ▸ Finset.mem_insert_self _ _)
    have hnot : j ∉ P := fun hp => hj (Finset.mem_insert_of_mem hp)
    simp [hzero j hne hnot]
  rw [integerMonomialArrayPolynomial, ← hsum, Finset.sum_insert hj₀, he₀]
  rfl

theorem productBlockExponent_monomial_int {V : Type*} {h : ℕ}
    (principal : Fin h → V) (c : ℤ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

theorem integerPrincipalPolynomial_eval {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (a : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℤ)
    (hzero : ∀ e, e ≠ constantCoefficientSlot _ _ → e ∉ principalCoefficientSlots h d → a e = 0)
    (x : SamplerTupleIndex G B h → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B d,
        a (principalCoefficientSlot h d b) * ∏ v : Fin (h d), x (.inr ⟨d, b, v⟩) := by
  classical
  rw [integerMonomialArrayPolynomial_principal_sum Subtype.val a
    (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
    (constantCoefficientSlot_not_principal h d hd) rfl hzero]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  rw [principalCoefficientSlots, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b _
    change MvPolynomial.eval x
      (MvPolynomial.monomial (productBlockExponent (fun v => .inr ⟨d, b, v⟩)) _) = _
    rw [productBlockExponent_monomial_int]
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  · intro b _ b' _ hb
    exact principalCoefficientSlot_injective h d hd hb

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)


end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) (x : J → ℝ)
    (hx : ∀ j, |x j| ≤ H) : normalizedSupportPlateau H x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg hH).mpr (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizedSupportPlateau_support {H : ℝ} (x : J → ℝ)
    (hx : normalizedSupportPlateau H x ≠ 0) : ∀ j, |x j| < H + 1 / 4 := by
  have hn : ‖x‖ < H + 1 / 4 := by
    apply lt_of_not_ge
    intro h
    apply hx
    exact linearCutoff_eq_zero H (1 / 4) (by simpa using h)
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  exact hj.trans_lt hn

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

variable [DecidableEq α] [∀ a, Fintype (κ a)]

variable [∀ a, PseudoMetricSpace (X a)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerTailZero
namespace OAI

section

namespace Erdos3

section Coordinate

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerCoordinate_tail_pure (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) : laws j = PMF.pure 0 := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF
  simp only [hj₀, hjP, ↓reduceIte]
  exact integerAxisTailPMF_small T hT hK hL hTL (tailProfileSize_pos hR hσ _) hεL (e j) (he j) hsmall

theorem allocatedIntegerCoordinate_tail_zero (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) {k : ℤ} (hk : k ∈ (laws j).support) : k = 0 := by
  rw [allocatedIntegerCoordinate_tail_pure P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ
    hgap hεL hsmall j hj₀ hjP] at hk
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk

end Coordinate

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortDependence
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (j : Fin m) (i : Fin (n j))
variable {X α O : Type} [Fintype X] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (p : FiniteProbabilityWeights X)
variable (a : X → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
variable (ha : ∀ x, p.weight x ≠ 0 → ∀ d,
  a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
variable (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
variable (rows : O → Finset α) (q : ℕ) (hrows : ∀ o, (rows o).card ≤ q)
variable (hx : ∀ x, p.weight x ≠ 0 → ∀ o t, t ∈ (rows o).powerset →
  ∀ v, |(vertices x t v : ℝ)| ≤ layerSamplerBox B U basis S v)

include hR hσ S hσ1 ha hrows hx

variable {T : ℕ} (hT : 0 < T) (hTS : T ≤ S.value)
variable (hshort : integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) < T)

include hT hTS hshort

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerInteger_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerInteger_moderate_tail_zero B U basis hR hσ S j i hmoderate a ha) x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentPMFOption
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentProductPMF_option {B X : Type*} [Fintype B]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option B → PMF X) :
    independentProductPMF p = (p none).bind (fun c =>
      (independentProductPMF (fun b => p (some b))).map
        (fun x q => q.elim c x)) := by
  ext z
  have hz : (fun q : Option B => q.elim (z none) (fun b => z (some b))) = z := by
    funext q
    cases q <;> rfl
  have hinj (c : X) : Function.Injective (fun (x : B → X) (q : Option B) => q.elim c x) := by
    intro x y h
    funext b
    exact congrFun h (some b)
  rw [PMF.bind_apply, tsum_eq_single (z none)]
  · have hm := pmf_map_injective_at (independentProductPMF (fun b => p (some b)))
      (fun (x : B → X) (q : Option B) => q.elim (z none) x) (hinj (z none))
      (fun b => z (some b))
    rw [hz] at hm
    rw [hm]
    simp only [independentProductPMF_apply, Fintype.prod_option]
  · intro c hc
    have hr : z ∉ Set.range (fun (x : B → X) (q : Option B) => q.elim c x) := by
      rintro ⟨x, he⟩
      exact hc (congrFun he none)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem scalarSupportPlateau_norm (H x : ℝ) : ‖scalarSupportPlateau H x‖ ≤ 1 := by
  rw [scalarSupportPlateau, Complex.norm_real,
    Real.norm_of_nonneg (normalizedSupportPlateau_range H _).1]
  exact (normalizedSupportPlateau_range H _).2

theorem scalarSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    scalarSupportPlateau H x = 1 := by
  simp only [scalarSupportPlateau, normalizedSupportPlateau_one hH _ (fun _ => hx), Complex.ofReal_one]

theorem scalarSupportPlateau_support (H x : ℝ) (hx : scalarSupportPlateau H x ≠ 0) :
    |x| < H + 1 / 4 := by
  apply normalizedSupportPlateau_support (fun _ : Unit => x) _ ()
  intro hz
  exact hx (by simp only [scalarSupportPlateau, hz, Complex.ofReal_zero])

theorem scalarSupportPlateau_zero {H x : ℝ} (hx : H + 1 / 4 ≤ |x|) :
    scalarSupportPlateau H x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (scalarSupportPlateau_support H x hn)

theorem scalarSupportPlateau_lipschitz (H : ℝ) : LipschitzWith 4 (scalarSupportPlateau H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (normalizedSupportPlateau_lipschitz (J := Unit) H).dist_le_mul
    (fun _ => x) (fun _ => y)
  rw [dist_pi_const] at h
  simpa only [scalarSupportPlateau, dist_eq_norm,
    ← Complex.ofReal_sub, Complex.norm_real] using h

theorem scalarSupportPlateau_mul_lipschitz (H : ℝ) (f : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) (hf : ∀ x, ‖f x‖ ≤ 1) :
    LipschitzWith (L + 4) (fun x => scalarSupportPlateau H x * f x) := by
  simpa only [one_mul] using lipschitz_mul_of_bounds (scalarSupportPlateau H) f
    (scalarSupportPlateau_lipschitz H) hL (Bf := 1) (Bg := 1)
    (scalarSupportPlateau_norm H) hf

theorem finite_site_cutoff_error {T S : Type*} [Fintype T] [Fintype S]
    (target : ℂ) (c : T → ℂ) (f : T → S → ℂ) (χ : S → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (hkeep : target ≠ 0 → ∀ s, χ s = 1)
    (he : (∀ s, χ s ≠ 0) → ‖target - ∑ k, c k * ∏ s, f k s‖ ≤ ε) :
    ‖target - ∑ k, c k * ∏ s, χ s * f k s‖ ≤ ε := by
  have hid : (∑ k, c k * ∏ s, χ s * f k s) =
      (∏ s, χ s) * ∑ k, c k * ∏ s, f k s := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ht : (∏ s, χ s) * target = target := by
    by_cases hz : target = 0
    · simp only [hz, mul_zero]
    · simp only [hkeep hz, Finset.prod_const_one, one_mul]
  rw [hid, ← ht, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hp : ‖∏ s, χ s‖ ≤ 1 := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hχ s)).trans_eq
        (Finset.prod_const_one)
    exact (mul_le_mul hp (he (fun s hs => hz ⟨s, hs⟩)) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {I : A → Type*} [∀ a, Fintype (I a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {T K L S U : Type*} [Fintype T] [Fintype K] [Fintype L] [Fintype S]
variable (c : T → ℂ) (a : K → L → ℂ)
variable (g : T → S → U → ℂ) (f : K → L → S → U → ℂ) (v : S → U)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem selectedBooleanSiteRows_lipschitz (axis : A) (rows : Finset (Finset α)) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (selectedBooleanSiteRows axis rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  change |booleanCoefficient (fun s => x s axis) t - booleanCoefficient (fun s => y s axis) t| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s axis - y s axis| ≤ dist (x s) (y s) from
      dist_le_pi_dist (x s) (y s) axis).trans (dist_le_pi_dist x y s)

omit [Fintype α] [Fintype A] [DecidableEq A] in
theorem selectedBooleanSiteRows_integer (axis : A) (rows : Finset (Finset α))
    (N : A → ℕ) (y : Finset α → A → ℤ) :
    selectedBooleanSiteRows axis rows (fun s d => (y s d : ℝ) / N d) =
      fun t : rows => ((booleanCoefficient (fun s => y s axis) t : ℤ) : ℝ) / N axis := by
  funext t
  rw [selectedBooleanSiteRows, booleanCoefficient_div]
  congr 1
  exact (booleanCoefficient_map (Int.castRingHom ℝ) (fun s => y s axis) t).symm

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α T : Type*} [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A]

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedJetChartSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem boundedCoefficientJetMatrix_scaled_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (A : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hA : ∀ i k, |(A i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    |(boundedCoefficientJetMatrix root A h rows o e : ℝ)| / monomialScale T e.val ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  let e' := boundedCoefficientIntegerExponentEquiv K h e
  have he := congrFun (congrFun (normalizedBoundedIntegerJetMatrix_eq root A h rows T
    (H := 1) one_ne_zero) o) e'
  rw [normalizedIntegerColumns_entry_div] at he
  have hb := boundedDegreeRealJetMatrix_entry_bound _ _ hroot hA h rows o e'
  rw [← he] at hb
  change |(boundedDegreeIntegerJetMatrix root A h rows o e' : ℝ)| / monomialScale T e'.val ≤ _
  simpa only [div_one, mul_one_div, abs_div, abs_of_pos (monomialScale_pos T hT e'.val)] using hb

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integer_boolean_reconstruction (y : Finset α → ℤ) (s : Finset α) :
    y s = ∑ t : Finset α, if t ⊆ s then booleanCoefficient y t else 0 := by
  have h := congrArg (fun M : Matrix (Finset α) (Finset α) ℤ => M *ᵥ y)
    (booleanReconstruction_mul_extraction (α := α))
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  have hv : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := by
    funext t
    exact booleanJetExtractionMatrix_mulVec id y t
  rw [hv] at h
  have hs := congrFun h s
  simpa only [Matrix.mulVec, dotProduct, booleanReconstructionMatrix,
    ite_mul, one_mul, zero_mul] using hs.symm

theorem integer_boolean_reconstruction_rows (y : Finset α → ℤ)
    (rows : Finset (Finset α)) (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (s : Finset α) :
    y s = ∑ t ∈ rows, if t ⊆ s then booleanCoefficient y t else 0 := by
  rw [integer_boolean_reconstruction y s]
  symm
  apply Finset.sum_subset (Finset.subset_univ rows)
  intro t _ ht
  simp only [hrows t ht, ite_self]

theorem integer_boolean_sites_bound (y : Finset α → ℤ) (rows : Finset (Finset α))
    (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    {H N : ℝ} (hH : 0 ≤ H) (hN : 0 < N)
    (hcoeff : ∀ t ∈ rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ H * N) (s : Finset α) :
    |(y s : ℝ) / N| ≤ rows.card * H := by
  have hs : |(y s : ℝ)| ≤ (rows.card : ℝ) * (H * N) := by
    rw [integer_boolean_reconstruction_rows y rows hrows s, Int.cast_sum]
    calc
      _ ≤ ∑ t ∈ rows, |((if t ⊆ s then booleanCoefficient y t else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ rows, H * N := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact hcoeff t ht
        · simp only [Int.cast_zero, abs_zero]
          positivity
      _ = _ := by simp
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_assoc] using hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalCube_vertex (t : Finset α) :
    integerAffineCube (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) t =
      fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k := by
  funext k
  cases k <;> simp only [integerAffineCube, allocatedPhysicalCubeRoot,
    allocatedPhysicalCubeDirections, Sum.elim_inl, Sum.elim_inr, integerScalarCubeValue] <;> ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

open BooleanCubeKernel Polynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootAllowance_zero :
    allocatedPhysicalRootAllowance B U b S (fun _ => 0) = 1 := by
  simp [allocatedPhysicalRootAllowance]

variable {α : Type*} (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))

theorem allocatedPhysicalCube_tuple_coordinate_bound (a : Option α) (k : LayerSamplerVariables G I n B) :
    |((Sum.elim (fun g => (x g a : ℤ)) (fun j => (y j a : ℤ)) k : ℤ) : ℝ)| ≤ layerSamplerBox B U b S k := by
  cases k with
  | inl g =>
    have hx := Finset.mem_Ico.mp (x g a).property
    change |((x g a : ℤ) : ℝ)| ≤ (S.value : ℝ)
    exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
  | inr j =>
    have hy := Finset.mem_Ico.mp (y j a).property
    change |((y j a : ℤ) : ℝ)| ≤ (allocatedPrincipalSides B U b S j : ℝ)
    exact_mod_cast abs_le.mpr ⟨hy.1, hy.2.le⟩

theorem allocatedPhysicalCube_directions_normalized (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U b S x y i k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  rw [abs_div, abs_of_pos hT, div_le_one hT]
  exact allocatedPhysicalCube_tuple_coordinate_bound B U b S x y (some i) k

theorem allocatedPhysicalCube_root_normalized (c : LayerSamplerVariables G I n B → ℤ)
    (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ) / layerSamplerBox B U b S k| ≤
      allocatedPhysicalRootAllowance B U b S c := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  have hsum : |(c k : ℝ)| / layerSamplerBox B U b S k ≤
      ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k :=
    Finset.single_le_sum (fun v _ => div_nonneg (abs_nonneg (c v : ℝ))
      (zero_le_one.trans (layerSamplerBox_one_le B U b S v))) (Finset.mem_univ k)
  have hx := allocatedPhysicalCube_tuple_coordinate_bound B U b S x y none k
  rw [abs_div, abs_of_pos hT]
  have hr : |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ)| ≤
      |(c k : ℝ)| + layerSamplerBox B U b S k := by
    unfold allocatedPhysicalCubeRoot
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hx)
  calc
    _ ≤ (|(c k : ℝ)| + layerSamplerBox B U b S k) / layerSamplerBox B U b S k :=
      div_le_div_of_nonneg_right hr hT.le
    _ = |(c k : ℝ)| / layerSamplerBox B U b S k + 1 := by rw [add_div, div_self hT.ne']
    _ ≤ allocatedPhysicalRootAllowance B U b S c := by
      dsimp [allocatedPhysicalRootAllowance]
      linarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedWeightedGridMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedLayerInteger_moderate_jet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : LayerSamplerVariables G I n B → Option α → ℤ)
    (rows : O → Finset α) (o : O) :
    (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * x v r) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) r) (rows o) := by
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval
      (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) = _
  have he (t : Finset α) := allocatedLayerInteger_moderate_eval B U basis hR hσ S j i
    hmoderate a ha (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
  simp_rw [he, booleanCoefficient_add, booleanCoefficient_sum, booleanCoefficient_const_mul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) (o : O) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o) := by
  let tuple : LayerSamplerVariables G I n B → Option α → ℤ := fun v r =>
    Sum.elim (fun g => (x g r : ℤ)) (fun q => (y q r : ℤ)) v
  have hvert : integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) =
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * tuple v r) := by
    funext t v
    rw [allocatedPhysicalCube_vertex]
    cases v <;> simp [tuple, integerScalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]
  change (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
    (integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) rows *ᵥ a) o = _
  rw [hvert]
  exact allocatedLayerInteger_moderate_jet_blocks B U basis hR hσ S j i hmoderate a ha tuple rows o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))


theorem allocatedPhysicalGridJetPMF_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
        (fun a o => booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩,
            a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
              integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  unfold integerMatrixImagePMF
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i) a = 0
  · simp only [ha, ite_self]
  · have hs : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support := by
      intro d
      change allocatedLayerIntegerPMFs B U basis hR hσ S j i d (a d) ≠ 0
      rw [independentProductPMF_apply] at ha
      exact (Finset.prod_ne_zero_iff.mp ha) d (Finset.mem_univ d)
    have he := funext (fun o => allocatedPhysicalGridJet_blocks B U basis hR hσ S j i
      hmoderate a hs x y rows o)
    rw [he]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))


theorem allocatedPhysicalGridJetPMF_principal
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (fun r : Option (B ⟨j, Sum.inr i⟩) =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ r))).map
        (fun c o => booleanCoefficient (fun _ => c none) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩, c (some b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  rw [allocatedPhysicalGridJetPMF_blocks B U basis hR hσ S j i hmoderate x y rows]
  rw [← principalCoefficientMarginal (G := G) (B := B) (layerSamplerDegree I n)
    ⟨j, Sum.inr i⟩ (Nat.zero_lt_succ _) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)]
  rw [PMF.map_comp]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α O : Type*} [Fintype α] [DecidableEq α] (rows : O → Finset α)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α O : Type*} [Fintype α] [DecidableEq α] (rows : O → Finset α)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSiteApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem pmf_bind_zero_of_support {X Y : Type*} (p : PMF X) (q : X → PMF Y) (z : Y)
    (hz : ∀ x ∈ p.support, q x z = 0) : p.bind q z = 0 := by
  rw [PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : p x = 0
  · rw [hx, zero_mul]
  · rw [hz x hx, mul_zero]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)


variable {α : Type*} [Fintype α] [DecidableEq α]

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable {M : ℕ} [NeZero M] (rows : Finset (Finset α)) (P ε : ℝ)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedResidueJetPMF_constant_mixture
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value) :
    (conditioned).toPMF.bind (fun y =>
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun z => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows
          (fun t => booleanCoefficient (fun _ : Finset α => z) t)) := by
  let p := (conditioned).toPMF
  let a := dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
  let constLaw := allocatedLayerIntegerPMFs B U basis hR hσ S j i
    (principalCoefficientChoice (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)
  let f (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
      (z : ℤ) (coeff : B ⟨j, Sum.inr i⟩ → ℤ) : rows → ℤ :=
    (fun t : rows => booleanCoefficient (fun _ : Finset α => z) t) +
      ∑ b, fun t : rows => coeff b * integerBooleanBlockJet
        (fun v k => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ k : ℤ)) t
  have hpoint y : integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      constLaw.bind (fun z => a.map (f y z)) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid,
      independentProductPMF_option, PMF.map_bind]
    simp only [PMF.map_comp]
    apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
    funext z
    apply congrArg (fun g : (B ⟨j, Sum.inr i⟩ → ℤ) → rows → ℤ => a.map g)
    funext coeff t
    simp only [Function.comp_apply, f, Pi.add_apply, Finset.sum_apply,
      Option.elim_none, Option.elim_some]
  simp_rw [hpoint]
  change p.bind (fun y => constLaw.bind (fun z => a.map (f y z))) =
    constLaw.bind (fun z => a.bind (fun coeff => p.map (fun y => f y z coeff)))
  refine (PMF.bind_comm p constLaw (fun y z => a.map (f y z))).trans ?_
  apply congrArg (fun k : ℤ → PMF (rows → ℤ) => constLaw.bind k)
  funext z
  exact PMF.bind_comm p a (fun y coeff => PMF.pure (f y z coeff))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerMatrixPMFSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_preimage_of_toReal_ne_zero
    (A : Matrix O J ℤ) (p : J → PMF ℤ) (y : O → ℤ)
    (hy : (integerMatrixImagePMF A p y).toReal ≠ 0) :
    ∃ z : J → ℤ, (∀ j, z j ∈ (p j).support) ∧ A *ᵥ z = y := by
  have hy' : y ∈ (integerMatrixImagePMF A p).support := by
    apply (PMF.mem_support_iff _ _).mpr
    intro h
    exact hy (by rw [h, ENNReal.toReal_zero])
  obtain ⟨z, hz, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hy'
  refine ⟨z, ?_, heq⟩
  intro j
  apply (PMF.mem_support_iff _ _).mpr
  intro h
  apply (PMF.mem_support_iff _ _).mp hz
  rw [independentProductPMF_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) h

omit [Fintype O] [DecidableEq O] [DecidableEq J] in
theorem integerMatrixImagePMF_scaled_support_bound
    (A : Matrix O J ℤ) (p : J → PMF ℤ) (T : J → ℝ) (hT : ∀ j, 0 < T j)
    {H M R : ℝ} (hM : 0 ≤ M)
    (hA : ∀ o j, |(A o j : ℝ)| / T j ≤ M)
    (hp : ∀ j z, z ∈ (p j).support → |(z : ℝ) / H| * T j ≤ R)
    (y : O → ℤ) (hy : (integerMatrixImagePMF A p y).toReal ≠ 0) (o : O) :
    |(y o : ℝ) / H| ≤ (Fintype.card J : ℝ) * M * R := by
  obtain ⟨z, hz, rfl⟩ := integerMatrixImagePMF_preimage_of_toReal_ne_zero A p y hy
  calc
    _ = |∑ j, (A o j : ℝ) * ((z j : ℝ) / H)| := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, mul_div_assoc]
    _ ≤ ∑ j, |(A o j : ℝ) * ((z j : ℝ) / H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, M * R := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      calc
        _ ≤ (M * T j) * |(z j : ℝ) / H| :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ (hT j)).mp (hA o j)) (abs_nonneg _)
        _ = M * (|(z j : ℝ) / H| * T j) := by ring
        _ ≤ M * R := mul_le_mul_of_nonneg_left (hp j (z j) (hz j)) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

theorem exists_bounded_grid_site_expansion
    {α : Type uα} [Fintype α] [DecidableEq α]
    (rows : Finset (Finset α)) (p : PMF (rows → ℤ)) {K Kmax : ℕ}
    (hK : 0 < K) (hKmax : K ≤ Kmax) {H ε P : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / K| ≤ H)
    (hε : 0 < ε) (hP : 0 ≤ P) (hHP : H + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (H + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval K y‖ ≤ ε := by
  let F (x : Finset α → Unit → ℝ) : ℂ :=
    integerRowMassInterpolation K p (selectedBooleanSiteRows () rows x)
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKnn : (1 : ℝ≥0) ≤ K := by exact_mod_cast hK
  have hmax : (K : ℝ≥0) ≤ Kmax := by exact_mod_cast hKmax
  have hF (x) : ‖F x‖ ≤ (Kmax : ℝ≥0) ^ rows.card := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_of_nonneg (integerRowMassInterpolation_range hKreal.le p _).1]
    apply (integerRowMassInterpolation_range hKreal.le p _).2.trans
    simpa only [Fintype.card_coe, NNReal.coe_pow, NNReal.coe_natCast] using
      pow_le_pow_left₀ hKreal.le (show (K : ℝ) ≤ Kmax by exact_mod_cast hKmax) rows.card
  have hLF : LipschitzWith
      ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
        (2 : ℝ≥0) ^ Fintype.card α) F := by
    have h := (integerRowMassInterpolation_lipschitz (K : ℝ≥0) hKnn p).comp
      (selectedBooleanSiteRows_lipschitz () rows)
    have hc : LipschitzWith
        ((rows.card * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ rows.card) *
          (2 : ℝ≥0) ^ Fintype.card α) F := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [F, Function.comp_def, Fintype.card_coe, dist_eq_norm,
        ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_natCast] using h.dist_le_mul x y
    apply hc.weaken
    gcongr
  obtain ⟨N, hN, c, f, hc, hf, hLf, he⟩ := exists_grouped_site_approximation F
    ((Kmax : ℝ≥0) ^ rows.card) _ hF hLF
    (show 0 < H + 1 / 4 by linarith only [hH]) hε hP hHP
    (by simpa only [NNReal.coe_pow, NNReal.coe_natCast] using hcap) hLip hεP
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := Finset α × Unit → Fin N
      period := fun _ => 1
      coefficient := c
      factor := fun k u _ x => scalarSupportPlateau H x * f k u (fun _ => x) }
  refine ⟨e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (Fintype.card (Finset α × Unit → Fin N) : ℝ) ≤ _
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_unit,
      mul_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _).trans_eq (Real.exp_nat_mul _ _).symm
  · exact fun _ => zero_lt_one
  · intro k
    norm_num only [e, Nat.cast_one]
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k u r x
    change ‖scalarSupportPlateau H x * f k u (fun _ => x)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u r
    apply scalarSupportPlateau_mul_lipschitz H (fun x => f k u (fun _ => x)) _ (fun x => hf k u _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k u).dist_le_mul (fun _ => x) (fun _ => y)
  · intro k u r x hx
    change scalarSupportPlateau H x * f k u (fun _ => x) = 0
    rw [scalarSupportPlateau_zero hx, zero_mul]
  · intro y hy
    let target : ℂ := (((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau H ((y u : ℝ) / K) = 1 := by
      intro ht u
      have hp : p (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply ht
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hH (hsupport y hy hp u)
    apply finite_site_cutoff_error target c (fun k u => f k u (fun _ => (y u : ℝ) / K))
      (fun u => scalarSupportPlateau H ((y u : ℝ) / K)) hε.le
      (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have herr := he (fun u _ => (y u : ℝ) / K)
      (fun u _ => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have heq : F (fun u _ => (y u : ℝ) / K) = target := by
      dsimp only [F, target]
      rw [show selectedBooleanSiteRows () rows (fun u _ => (y u : ℝ) / K) =
        (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) by
          simpa only using selectedBooleanSiteRows_integer () rows (fun _ => K) (fun u _ => y u)]
      rw [integerRowMassInterpolation_grid hKreal, Fintype.card_coe]
    rwa [heq] at herr

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerIntegerCoefficient_scaled_bound (j : Fin m) (hσ1 : σ j ≤ 1)
    (i : Fin (n j)) (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (z : ℤ) (hz : z ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i e).support) :
    |(z : ℝ) / basisAxisScale (b j) i| * monomialScale (layerSamplerBox B U b S) e.val ≤ R j := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
    (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) hσ1 (S.gap j i) (S.width j)
    (layerIntegerPrincipalSlots_not_constant B j i) rfl
    (layerSamplerSides_integer_principal B U b R S.value j i) e hz).trans (by linarith [hR j])

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)


variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "height" => basisAxisScale (basis j) i


theorem allocatedSupportedSlicedPhysicalGridPMF_scaled_support
    (hσ1 : σ j ≤ 1) (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (z : rows → ℤ)
    (hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z ≠ 0)
    (t : rows) : |(z t : ℝ) / height| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  by_contra hbad
  apply hmass
  unfold allocatedSupportedSlicedPhysicalGridPMF
  apply pmf_bind_zero_of_support
  intro y _
  by_contra hmass'
  have hreal := (ENNReal.toReal_pos hmass' (PMF.apply_ne_top _ _)).ne'
  have hT : ∀ k, 0 < layerSamplerBox B U basis S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U basis S k)
  have hroot (k) : |(allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y k : ℝ) /
      layerSamplerBox B U basis S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U basis S x y (fun _ => 0) k
  apply hbad
  exact integerMatrixImagePMF_scaled_support_bound _ _
    (fun e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) =>
      monomialScale (layerSamplerBox B U basis S) e.val)
    (fun e => monomialScale_pos _ hT e.val) (by positivity)
    (boundedCoefficientJetMatrix_scaled_entry_bound _ _ _ hT hroot
      (allocatedPhysicalCube_directions_normalized B U basis S x y) _ (fun t : rows => (t : Finset α)))
    (fun e z hz => allocatedLayerIntegerCoefficient_scaled_bound B U basis hR hσ S j hσ1 i e z hz)
    z hreal t

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))


local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

theorem allocatedSupportedSlicedPhysicalGridPMF_base_independent
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x x' : G → IntegerScalarCubeBox α S.value) :
    allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x =
      allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x' := by
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x,
    allocatedSupportedSlicedResidueJetPMF_constant_mixture B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x']

theorem exists_allocatedSupportedSliced_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : height ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  let p := allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x₀
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / height| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 rows x₀
      (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  obtain ⟨e, he, herr⟩ := exists_bounded_grid_site_expansion rows p
    (basisAxisScale_pos (basis j) i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP
  refine ⟨e, he, ?_⟩
  intro x y hy
  rw [allocatedSupportedSlicedPhysicalGridPMF_base_independent B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x x₀]
  exact herr y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))


variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))


variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))



end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_bounded_grid_site_expansion.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_bounded_grid_site_expansion.{uα, u_1, u_2, u_3, u_4}
