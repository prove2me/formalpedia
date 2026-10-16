-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-15T22:10:50.238496+00:00
-- url     : https://prove2.me/submissions/32292bff-2a8c-461f-9b40-f7a9b3bb7a64

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactivePhysicalGridApproximation_error
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_bounded_grid_site_expansion
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_grid_site_expansion
import Theorems.Thm_OAI_Erdos3_exists_affineCube_plateau_site_approximation

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_common_rational_approximations {I : Type*} [Fintype I] [DecidableEq I]
    (θ : I → ℝ) {Q E : ℝ}
    (h : ∀ i, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Q ∧ ∃ m : ℤ, |θ i-(m : ℝ)/q| ≤ E) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Q^Fintype.card I ∧
      ∃ a : I → ℤ, ∀ i, |θ i-(a i : ℝ)/D| ≤ E := by
  choose q hq hqQ m hm using h
  let D := ∏ i, q i
  let rest := fun i => ∏ j ∈ Finset.univ.erase i, q j
  have hrest (i : I) : 0 < rest i := Finset.prod_pos (fun j _ => hq j)
  have hD (i : I) : q i * rest i = D :=
    Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  have hDp : 0 < D := Finset.prod_pos (fun i _ => hq i)
  refine ⟨D,hDp,?_,(fun i => (rest i : ℤ)*m i),?_⟩
  · calc
      (D : ℝ) = ∏ i, (q i : ℝ) := by simp [D]
      _ ≤ ∏ _i : I, Q := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hqQ i)
      _ = Q^Fintype.card I := by simp
  · intro i
    have hqr : (0 : ℝ) < q i := by exact_mod_cast hq i
    have hrr : (0 : ℝ) < rest i := by exact_mod_cast hrest i
    have hd : (D : ℝ) = (q i : ℝ)*rest i := by exact_mod_cast (hD i).symm
    have he : (((rest i : ℤ)*m i : ℤ) : ℝ)/(D : ℝ) = (m i : ℝ)/q i := by
      push_cast
      rw [hd]
      field_simp
    rw [he]
    exact hm i

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

theorem length_small_grid_bound {N V L C ζ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hsize : N ≤ V * L ^ t) (hsmall : L ≤ C / ζ ^ c) :
    N ≤ V * C ^ t / ζ ^ (c * t) := by
  calc
    _ ≤ V * L ^ t := hsize
    _ ≤ V * (C / ζ ^ c) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hsmall t) hV
    _ = _ := by rw [div_pow, pow_mul]; ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

theorem unscale_grid_interval {M H d : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ)
    (h : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) / M - (a : ℝ) / d =
      ((k.val : ℝ) - M * ((a : ℝ) / d)) / M := by field_simp
  rw [he, abs_div, abs_of_pos hM']
  exact div_le_div_of_nonneg_right h hM'.le

theorem rationalGridMajorSet_rational {M Q H : ℕ} (hM : 0 < M) (k : Fin M)
    (hk : k ∈ rationalGridMajorSet M Q H) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ (Q + 1 : ℝ) ∧
      ∃ a : ℤ, |(k.val : ℝ) / M - (a : ℝ) / d| ≤ (H : ℝ) / M := by
  classical
  obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨a, _, hk⟩ := Finset.mem_biUnion.mp ha
  have he := (Finset.mem_filter.mp hk).2
  by_cases hd0 : d = 0
  · refine ⟨1, by omega, by exact_mod_cast (show 1 ≤ Q + 1 by omega), 0, ?_⟩
    apply unscale_grid_interval hM k 0
    simpa only [hd0, Nat.cast_zero, div_zero, Int.cast_zero, zero_div, mul_zero, sub_zero] using he
  · refine ⟨d, Nat.pos_of_ne_zero hd0, ?_, a, unscale_grid_interval hM k a he⟩
    exact_mod_cast (Finset.mem_range.mp hd).le

theorem rationalGridMajorBox_character {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ξ j / M := by
  have hj := Fintype.mem_piFinset.mp hk
  obtain ⟨D, hD, hDQ, a, ha⟩ := exists_common_rational_approximations
    (fun j => ((k j).val : ℝ) / M) (fun j => rationalGridMajorSet_rational hM (k j) (hj j))
  let ξ j := (M : ℝ) * (((k j).val : ℝ) / M - (a j : ℝ) / D)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨D, hD, hDQ, a, ξ, ?_, ?_⟩
  · intro j
    dsimp only [ξ]
    rw [abs_mul, abs_of_pos hM']
    calc
      _ ≤ (M : ℝ) * ((H : ℝ) / M) := mul_le_mul_of_nonneg_left (ha j) hM'.le
      _ = H := by field_simp
  · intro j
    dsimp only [ξ]
    field_simp
    ring

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

theorem rationalGridMajorBox_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M Q H : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    (k : J → Fin M) (hk : k ∈ rationalGridMajorBox J M Q H) :
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ (Q + 1 : ℝ) ^ Fintype.card J ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ H) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hM0 : (M : ℝ) ≠ 0 := (Nat.cast_pos.mpr hM).ne'
  obtain ⟨D, hD, hDQ, a, ξ, hξ, he⟩ := rationalGridMajorBox_character hM k hk
  refine ⟨D, hD, hDQ, a, (fun j => (K : ℝ) * ξ j / M), ?_, ?_⟩
  · intro j
    simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
      abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
    calc
      (K : ℝ) * |ξ j| ≤ (K : ℝ) * H := mul_le_mul_of_nonneg_left (hξ j) (Nat.cast_nonneg K)
      _ ≤ (M : ℝ) * H := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hKM) (Nat.cast_nonneg H)
      _ = (H : ℝ) * M := mul_comm _ _
  · intro j
    rw [he j]
    congr 1
    field_simp

theorem lengthAwarePolynomialGrid_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M)
    {C L V A ζ : ℝ} {c t r : ℕ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ V * L ^ t)
    (k : J → Fin M)
    (hk : k ∈ lengthAwareSpectrumCover C L c (polynomialGridCover J M A r) ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ max ((⌈A / ζ ^ r⌉₊ + 1 : ℝ) ^ Fintype.card J)
        (V * C ^ t / ζ ^ (c * t)) ∧
      ∃ (a : J → ℤ) (ω : J → ℝ), (∀ j, |ω j| ≤ (⌈A / ζ ^ r⌉₊ : ℝ)) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · have hk' : k ∈ rationalGridMajorBox J M ⌈A / ζ ^ r⌉₊ ⌈A / ζ ^ r⌉₊ := by
      simpa only [lengthAwareSpectrumCover, if_pos hstart, polynomialGridCover] using hk
    obtain ⟨D, hD, hb, a, ω, hω, he⟩ := rationalGridMajorBox_scaled_character hK hKM k hk'
    exact ⟨D, hD, hb.trans (le_max_left _ _), a, ω, hω, he⟩
  · cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨1, Nat.zero_lt_one, ?_, (fun j => isEmptyElim j),
        (fun j => isEmptyElim j), (fun j => isEmptyElim j), (fun j => isEmptyElim j)⟩
      simpa only [Fintype.card_eq_zero, pow_zero, Nat.cast_one] using
        (le_max_left (1 : ℝ) (V * C ^ t / ζ ^ (c * t)))
    | inr hJ =>
      let := hJ
      have hM : 0 < M := lt_of_lt_of_le hK hKM
      have hpow : (M : ℝ) ≤ (M : ℝ) ^ Fintype.card J :=
        le_self_pow₀ (by exact_mod_cast hM) (Fintype.card_pos.ne')
      have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
      refine ⟨M, hM, (hpow.trans hb).trans (le_max_right _ _),
        (fun j => ((k j).val : ℤ)), (fun _ => 0), ?_, ?_⟩
      · intro j
        simpa only [abs_zero] using (Nat.cast_nonneg ⌈A / ζ ^ r⌉₊ : (0 : ℝ) ≤ _)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem uniformBlockSpectrumCover_scaled_character {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (k : J → Fin M) (hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
      ∃ (a : J → ℤ) (ω : J → ℝ),
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K :=
  lengthAwarePolynomialGrid_character hK hKM hL hW hsize k hk

theorem uniformBlockSpectrumCover_modes {J : Type*} [Fintype J] [DecidableEq J]
    {K M : ℕ} (hK : 0 < K) (hKM : K ≤ M) (n t : ℕ) {U V W L ζ : ℝ}
    (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ∃ (D : (J → Fin M) → ℕ) (a : (J → Fin M) → J → ℤ) (ω : (J → Fin M) → J → ℝ),
      (∀ k, 0 < D k) ∧ ∀ k ∈ uniformBlockSpectrumCover J M n U V L ζ,
        (D k : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω k j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a k j : ℝ) / D k + ω k j / K := by
  classical
  have hex (k : J → Fin M) : ∃ D : ℕ, 0 < D ∧ ∃ (a : J → ℤ) (ω : J → ℝ),
      k ∈ uniformBlockSpectrumCover J M n U V L ζ →
        (D : ℝ) ≤ uniformScaledRetainedDenominatorBound n (Fintype.card J) t U V W ζ ∧
        (∀ j, |ω j| ≤ uniformScaledRetainedFrequencyBound n (Fintype.card J) U V ζ) ∧
        ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K := by
    by_cases hk : k ∈ uniformBlockSpectrumCover J M n U V L ζ
    · obtain ⟨D, hD, hb, a, ω, hω, he⟩ :=
        uniformBlockSpectrumCover_scaled_character hK hKM n t hL hW hsize k hk
      exact ⟨D, hD, a, ω, fun _ => ⟨hb, hω, he⟩⟩
    · exact ⟨1, Nat.zero_lt_one, 0, 0, fun h => (hk h).elim⟩
  choose D hD a ω h using hex
  exact ⟨D, a, ω, hD, h⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

theorem grid_scale_factor_le_one (R K j : ℕ) (hR : 0 < R) (hK : 0 < K) :
    ((K : ℝ) / (R * K)) ^ j ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  apply pow_le_one₀ (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]
attribute [local instance] ScalarSiteExpansion.termFinite

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {α : Type*} [Fintype α] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {X A V : Type*} [Fintype X] [Fintype A]
variable (spatialPeriod : ℕ) (q : X → ℕ) (e : A → ScalarSiteExpansion V)
variable (k : ∀ a, (e a).Term) (idealPeriod : ℕ)

namespace BooleanCubeKernel

variable {K α : Type*} [Fintype K] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ)
variable (b : ℝ) (r : ℝ≥0) {spatialPeriod M : ℕ}
variable (hM : ∀ x, q x * spatialPeriod ∣ M)
variable (t : X → SpatialSiteLabel α spatialPeriod b r) (s : Finset α)

end BooleanCubeKernel
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

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

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) (q d T : ℕ)
local notation "degree" => j.val + 1
local notation "b" => Fintype.card (B (Sigma.mk j (Sum.inr i)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

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


local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

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
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hq hsize in
theorem exists_allocatedSupportedSliced_inactive_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let freq := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val rows.card P V ζ)
    let cap := uniformSpectrumAbsoluteCap j.val rows.card t P V W
    let R0 := (rows.card : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j)
    ∀ {η Q : ℝ}, 0 < η → 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (η / (cap + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        ((uniformSpectrumSizeConstant j.val rows.card t P V W /
          ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t)) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (uniformScaledRetainedDenominatorBound j.val rows.card t P V W ζ)
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + η := by
  intro V t W ζ freq cap R0 η Q hη hQ hRQ hηQ hLQ
  let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
  have hMK : (M : ℝ) ≤ (torus : ℝ) * height := by simp only [hM, Nat.cast_mul, le_refl]
  have hscale : ((height : ℝ) / M) ^ rows.card ≤ 1 := by
    rw [hM, Nat.cast_mul]
    exact grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ ((torus : ℝ) * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg torus))
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hKM : height ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left _ (blockTorusFactor_pos _ _ _ _)
  obtain ⟨D, a, ω, hD, hmodes⟩ := uniformBlockSpectrumCover_modes (J := rows)
    (basisAxisScale_pos (basis j) i) hKM j.val t hL hW
    (by simpa only [Fintype.card_coe] using hcard) (U := P) (V := V) (ζ := ζ)
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  obtain ⟨hF, hcap, hpoint⟩ := allocatedSupportedSlicedInactivePhysicalGridApproximation_error
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride hM rows hrows hB hε hε1
  have hRj : 0 ≤ R j := (hR j).le
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  obtain ⟨N, hN, hcount, β, f, hβ, hf, hLf, he⟩ := exists_affineCube_plateau_site_approximation
    sources lower strides constantLaw (basisAxisScale_pos (basis j) i) radius rows F D a ω
    (fun k hk => (hmodes k hk).2.2)
    (fun zeta t => booleanCoefficient (fun _ : Finset α => zeta) t) hscale
    hcap freq
    (fun k hk t => (by simpa only [Fintype.card_coe] using (hmodes k hk).2.1 t :
      |ω k t| ≤ uniformScaledRetainedFrequencyBound j.val rows.card P V ζ).trans (Real.le_coe_toNNReal _))
    (R := R0 + 1 / 4) (by positivity) hη hQ hRQ hηQ hLQ
  let g (k : PlateauSiteIndex α F N) (u : Finset α) (v : ZMod (D k.1)) (z : ℝ) : ℂ :=
    scalarSupportPlateau R0 z * f k u v z
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := g }
  refine ⟨e, ⟨?_, (fun k => hD k.1), ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hcount.trans (mul_le_mul_of_nonneg_right hF (Real.exp_nonneg _))
  · intro k
    simpa only [Fintype.card_coe] using (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau R0 z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz R0 (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau R0 z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    have hkeep :
        (((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) ≠ 0 →
        ∀ u, scalarSupportPlateau R0 ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      apply scalarSupportPlateau_one hR0
      apply integer_boolean_sites_bound y rows hy (by positivity) (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
      intro t ht
      have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support B U basis hR hσ S q r H step c hH hsubset hcell
        j i hσ1 rows x (fun t => booleanCoefficient y t) hmass ⟨t, ht⟩
      have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
      rw [abs_div, abs_of_pos hk] at hb
      exact (div_le_iff₀ hk).mp hb
    exact finite_site_cutoff_error _ β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau R0 ((y u : ℝ) / height))
      (by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
      (fun hcut => (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (hpoint x (fun t => booleanCoefficient y t))
          (he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le))))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite
namespace OAI

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
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_mixed_grid_site_expansion
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let d := rows.card
    let ta := (layerTailDegree m + 1) * d
    let ti := degree * d
    let Va := ((torusA : ℝ) / (2 * gamma)) / δ ^ degree
    let Vi := (torusI : ℝ) * cost / δ ^ degree
    let Wa := (torusA : ℝ) ^ d / δ ^ ta
    let Wi := ((torusI : ℝ) * cost) ^ d / δ ^ ti
    let ζa := positiveModerateRetainedBias j.val d ta P Va Wa ε
    let ζi := uniformBlockRetainedBias j.val d ti P Vi Wi ε
    let fa := Real.toNNReal (positiveRetainedFrequencyBound j.val d P Va ζa)
    let fi := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val d P Vi ζi)
    let ca := positiveModerateSpectrumCardBudget j.val d ta P Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap j.val d ti P Vi Wi
    let Kmax := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
    let R0 := (d : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q → (ε / (ci + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fa) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fi) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      (Kmax : ℝ) ^ d ≤ Real.exp Q →
      ((d * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max 1 (max (positiveModerateSpectrumCardBudget j.val d ta P Va Wa ε)
          (uniformSpectrumSizeConstant j.val d ti P Vi Wi /
            ε ^ max (majorArcSpectrumExponent j.val d) (majorArcLengthExponent j.val * ti))) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (max 1 (max (positiveRetainedDenominatorBound j.val d ta P Va Wa ζa)
          (uniformScaledRetainedDenominatorBound j.val d ti P Vi Wi ζi)))
        (max 1 (max ca ci) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  intro d ta ti Va Vi Wa Wi ζa ζi fa fi ca ci Kmax R0 Q hQ hRQ hεa hεi hfa hfi hKQ hKLQ hεQ
  rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
      ((Fintype.card α + 1) * q) T hQT with hsmall | ⟨hsize, hcases⟩
  · obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_bounded_grid_site_expansion
      B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 hgrid rows hsmall hε hQ hRQ hKQ hKLQ hεQ
    refine ⟨e, he.mono ?_ (le_max_left _ _) ?_ le_rfl le_rfl, ?_⟩
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · intro x y hy
      exact (herr x y hy).trans (by linarith)
  · rcases hcases with ⟨ha, hlength⟩ | ⟨hi, hl, hlength⟩
    · let M := torusA * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_grid_site_expansion
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i ha hsize hgrid hδ hlength hstep
        A hA P hcP hsP hstride (M := M) rfl rows hrows hBa hε hε1 hσ1 hε hQ hRQ hεa hfa
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy
    · let M := torusI * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_inactive_grid_site_expansion
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hi hl hδ hlength hstep
        A hA P hP hsP hstride (M := M) rfl rows hrows hBi hε hε1 hσ1 hε hQ hRQ hεi hfi
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
variable (α : Type*) [Fintype α] (d T : ℕ)

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
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

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
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

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
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

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
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion.{uα, u_1, u_2, u_3, u_4}
