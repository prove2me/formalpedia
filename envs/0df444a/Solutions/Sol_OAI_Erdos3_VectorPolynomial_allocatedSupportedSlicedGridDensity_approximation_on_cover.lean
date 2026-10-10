-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T17:10:36.641024+00:00
-- url     : https://prove2.me/submissions/93750260-db2e-4c42-8278-c9fd21951d62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_source
import Theorems.Thm_OAI_Erdos3_weightedPositiveAffineModerateGridCoefficient_minor_polynomial

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem cyclicIntegerCharacter_intCast (M : ℕ) [NeZero M] (r z : ℤ) :
    cyclicIntegerCharacter M z (r : ZMod M) =
      character (((r : ℝ) * (z : ℝ) / M : ℝ) : CircleFourier.Circle) := by
  change character (ZMod.toAddCircle ((r : ZMod M) * (z : ZMod M))) = _
  rw [← Int.cast_mul, ZMod.toAddCircle_intCast]
  simp only [Int.cast_mul]

theorem cyclicIntegerCharacter_eq_zero_iff (M : ℕ) [NeZero M] (z : ℤ) :
    cyclicIntegerCharacter M z = 0 ↔ (z : ZMod M) = 0 := by
  constructor
  · intro h
    have he := DFunLike.congr_fun h (1 : ZMod M)
    change character (ZMod.toAddCircle ((1 : ZMod M) * (z : ZMod M))) = 1 at he
    rw [one_mul, character_eq_one_iff, ZMod.toAddCircle_eq_zero] at he
    exact he
  · intro h
    apply AddChar.ext
    intro r
    change character (ZMod.toAddCircle (r * (z : ZMod M))) = 1
    simp only [h, mul_zero, map_zero, character_zero]

theorem cyclicIntegerCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ r : ZMod M, cyclicIntegerCharacter M z r) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  classical
  simpa only [cyclicIntegerCharacter_eq_zero_iff, ZMod.card] using
    AddChar.sum_eq_ite (cyclicIntegerCharacter M z)

theorem integerGridCharacter_eq (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) :
    integerGridCharacter M k z =
      character ((((k.val : ℝ) / M) * z : ℝ) : CircleFourier.Circle) := by
  have h := cyclicIntegerCharacter_intCast M (k.val : ℤ) z
  simpa only [integerGridCharacter, gridResidueEquiv, Equiv.coe_fn_mk,
    Int.cast_natCast, div_mul_eq_mul_div] using h

theorem integerGridCharacter_sum (M : ℕ) [NeZero M] (z : ℤ) :
    (∑ k : Fin M, integerGridCharacter M k z) =
      if (z : ZMod M) = 0 then (M : ℂ) else 0 := by
  rw [← cyclicIntegerCharacter_sum M z]
  exact (Equiv.sum_comp (gridResidueEquiv M) (cyclicIntegerCharacter M z))

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem circle_coe_fintype_sum {J : Type*} [Fintype J] (f : J → ℝ) :
    ((∑ j, f j : ℝ) : CircleFourier.Circle) = ∑ j, (f j : CircleFourier.Circle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ

theorem rectangularGridCharacter_eq {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularGridCharacter M k y =
      character ((∑ j, (((k j).val : ℝ) / M) * (y j : ℝ) : ℝ) : CircleFourier.Circle) := by
  simp only [rectangularGridCharacter, integerGridCharacter_eq, circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_norm {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    ‖rectangularGridCharacter M k y‖ = 1 := by
  rw [rectangularGridCharacter_eq, norm_character]

theorem rectangularGridCharacter_add {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y + z) =
      rectangularGridCharacter M k y * rectangularGridCharacter M k z := by
  simp only [rectangularGridCharacter_eq, Pi.add_apply, Int.cast_add, mul_add,
    Finset.sum_add_distrib, AddCircle.coe_add, character_add]

theorem rectangularGridCharacter_sub {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y - z) =
      rectangularGridCharacter M k y * star (rectangularGridCharacter M k z) := by
  simp only [rectangularGridCharacter_eq, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
  rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]

theorem rectangularGridCharacter_fintype_sum {J B : Type*} [Fintype J] [Fintype B]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : B → J → ℤ) :
    rectangularGridCharacter M k (∑ b, y b) = ∏ b, rectangularGridCharacter M k (y b) := by
  classical
  simp only [rectangularGridCharacter_eq, Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_sum {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y) =
      if integerGridResidue M y = 0 then (M : ℂ) ^ Fintype.card J else 0 := by
  classical
  change (∑ k : J → Fin M, ∏ j, integerGridCharacter M (k j) (y j)) = _
  rw [← Fintype.prod_sum (fun j (k : Fin M) => integerGridCharacter M k (y j))]
  simp only [integerGridCharacter_sum]
  by_cases hy : integerGridResidue M y = 0
  · have hz j : (y j : ZMod M) = 0 := congrFun hy j
    simp only [hz, ite_true, Finset.prod_const, Finset.card_univ, hy]
  · have hz : ∃ j, (y j : ZMod M) ≠ 0 := by
      by_contra! h
      exact hy (funext h)
    obtain ⟨j, hj⟩ := hz
    rw [if_neg hy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem rectangularGridCharacter_orthogonality {J : Type*} [Fintype J] [DecidableEq J]
    (M : ℕ) [NeZero M] (y z : J → ℤ) :
    (∑ k : J → Fin M, rectangularGridCharacter M k y * star (rectangularGridCharacter M k z)) =
      if integerGridResidue M y = integerGridResidue M z then
        (M : ℂ) ^ Fintype.card J else 0 := by
  simp only [← rectangularGridCharacter_sub, rectangularGridCharacter_sum]
  have h : integerGridResidue M (y - z) = 0 ↔ integerGridResidue M y = integerGridResidue M z := by
    simp only [funext_iff, integerGridResidue, Pi.sub_apply, Pi.zero_apply, Int.cast_sub, sub_eq_zero]
  simp only [h]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H]

variable [Fintype H]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω H : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

variable [Fintype H]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]

theorem complexMean_pi_product (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (v : ∀ j, Ω j → ℂ) :
    (pi p).complexMean (fun x => ∏ j, v j (x j)) = ∏ j, (p j).complexMean (v j) := by
  classical
  change (∑ x : ∀ j, Ω j, ((∏ j, (p j).weight (x j) : ℝ) : ℂ) * (∏ j, v j (x j))) =
    ∏ j, ∑ x, ((p j).weight x : ℂ) * v j x
  simp_rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j (x : Ω j) => ((p j).weight x : ℂ) * v j x)).symm

end Erdos3.FiniteProbabilityWeights

end

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem spectrumTail_le_card {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) : spectrumTail S f ≤ Fintype.card K * w := by
  calc
    _ ≤ ∑ _k : K, w := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false]
      · exact hw
      · exact h k hk
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem spectrumTail_step {K : Type*} [Fintype K] [DecidableEq K]
    (S T : Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) {w : ℝ} (hw : 0 ≤ w)
    (h : ∀ k, k ∉ S → f k ≤ w) :
    spectrumTail S f ≤ T.card * w + spectrumTail T f := by
  have hp (k : K) : (if k ∈ S then 0 else f k) ≤
      (if k ∈ T then w else 0) + (if k ∈ T then 0 else f k) := by
    by_cases hs : k ∈ S <;> by_cases ht : k ∈ T <;>
      simp only [hs, ht, ite_true, ite_false, zero_add, add_zero]
    · exact hw
    · exact hf k
    · exact h k hs
    · exact le_rfl
  calc
    _ ≤ ∑ k, ((if k ∈ T then w else 0) + (if k ∈ T then 0 else f k)) :=
      Finset.sum_le_sum (fun k _ => hp k)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, spectrumTail]

theorem spectrumTail_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k)
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (h : ∀ i k, k ∉ S i → f k ≤ w i) (n : ℕ) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  induction n generalizing S w with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, zero_add] using
      spectrumTail_le_card (S 0) f (hw 0) (h 0)
  | succ n ih =>
      have hstep := spectrumTail_step (S 0) (S 1) f hf (hw 0) (h 0)
      have htail := ih (fun i => S (i + 1)) (fun i => w (i + 1))
        (fun i => hw (i + 1)) (fun i => h (i + 1))
      calc
        _ ≤ (S 1).card * w 0 + ((∑ i ∈ Finset.range n, (S (i + 1 + 1)).card * w (i + 1)) +
            Fintype.card K * w (n + 1)) := hstep.trans (add_le_add le_rfl htail)
        _ = _ := by rw [Finset.sum_range_succ']; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_series_truncation_le {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (c ψ : K → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k‖ ≤ spectrumTail S (fun k => ‖c k‖) := by
  have hid : (∑ k, c k * ψ k) - ∑ k ∈ S, c k * ψ k =
      ∑ k, if k ∈ S then 0 else c k * ψ k := by
    calc
      _ = ∑ k, (c k * ψ k - if k ∈ S then c k * ψ k else 0) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, sub_self, sub_zero]
  rw [hid]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · simp only [hk, ite_true, norm_zero, le_refl]
  · simp only [hk, ite_false, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hψ k)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem spectrumTail_finite_levels {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i) :
    spectrumTail (S 0) f ≤ (∑ i ∈ Finset.range n, (S (i + 1)).card * w i) +
      Fintype.card K * w n := by
  have hs := spectrumTail_levels (fun i => S (min i n)) f hf (fun i => w (min i n))
    (fun i => hw _ (Nat.min_le_right i n)) (fun i => h _ (Nat.min_le_right i n)) n
  simp only [Nat.zero_min, Nat.min_self] at hs
  have heq : (∑ i ∈ Finset.range n, (S (min (i + 1) n)).card * w (min i n)) =
      ∑ i ∈ Finset.range n, (S (i + 1)).card * w i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.min_eq_left (by omega : i + 1 ≤ n), Nat.min_eq_left (by omega : i ≤ n)]
  rwa [heq] at hs

theorem spectrumTail_finite_geometric {K : Type*} [Fintype K] [DecidableEq K]
    (S : ℕ → Finset K) (f : K → ℝ) (hf : ∀ k, 0 ≤ f k) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i ≤ n, 0 ≤ w i) (h : ∀ i ≤ n, ∀ k, k ∉ S i → f k ≤ w i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * w i ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) f ≤ 2 * C + Fintype.card K * w n := by
  apply (spectrumTail_finite_levels S f hf w n hw h).trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ i ∈ Finset.range n, C * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i hi => hlevel i (Finset.mem_range.mp hi))
    _ = C * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := (Finset.mul_sum _ _ _).symm
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hC
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IndependentPhaseCoefficients
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem norm_product_coefficients_le {B : Type*} [Fintype B] (c : B → ℂ) {ζ : ℝ}
    (h : ∀ b, ‖c b‖ ≤ ζ) : ‖∏ b, c b‖ ≤ ζ ^ Fintype.card B := by
  classical
  rw [norm_prod]
  calc
    _ ≤ ∏ _b : B, ζ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun index _ => h index)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialSpectrumAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem product_spectrumTail_geometric {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (ζ : ℕ → ℝ) (n : ℕ)
    (hζ : ∀ i ≤ n, 0 ≤ ζ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ i)
    {C : ℝ} (hC : 0 ≤ C)
    (hlevel : ∀ i < n, (S (i + 1)).card * (ζ i) ^ Fintype.card B ≤ C * (1 / 2 : ℝ) ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * C + Fintype.card K * (ζ n) ^ Fintype.card B := by
  apply spectrumTail_finite_geometric S _ (fun _ => norm_nonneg _) _ n
    (fun i hi => pow_nonneg (hζ i hi) _) _ hC hlevel
  intro i hi k hk
  exact norm_product_coefficients_le _ (fun b => hsmall i hi b k hk)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem dyadic_power_ratio {a b : ℕ} (hab : a + 1 ≤ b) (i : ℕ) :
    (2 : ℝ) ^ (a * i) / 2 ^ (b * i) ≤ (1 / 2 : ℝ) ^ i := by
  rw [one_div_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right i hab

theorem dyadic_level_mass_bound {a b i : ℕ} {C ζ count : ℝ}
    (hab : a + 1 ≤ b) (hC : 0 ≤ C) (hζ : 0 ≤ ζ)
    (hcount : count ≤ C * ((2 : ℝ) ^ a) ^ i) :
    count * (ζ / 2 ^ i) ^ b ≤ (C * ζ ^ b) * (1 / 2 : ℝ) ^ i := by
  calc
    _ ≤ (C * ((2 : ℝ) ^ a) ^ i) * (ζ / 2 ^ i) ^ b :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C * ζ ^ b) * ((2 : ℝ) ^ (a * i) / 2 ^ (b * i)) := by
      rw [div_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm i b]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_power_ratio hab i) (by positivity)

theorem product_spectrumTail_dyadic {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a : ℕ) {C ζ : ℝ}
    (hC : 0 ≤ C) (hζ : 0 ≤ ζ) (hab : a + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ C * ((2 : ℝ) ^ a) ^ i)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * (C * ζ ^ Fintype.card B) + Fintype.card K * (ζ / 2 ^ n) ^ Fintype.card B := by
  apply product_spectrumTail_geometric c S (fun i => ζ / 2 ^ i) n
    (fun _ _ => by positivity) hsmall (by positivity)
  intro i hi
  exact dyadic_level_mass_bound hab hC hζ (hcount i hi)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem cutoff_power_mass_bound {N T δ ζ : ℝ} {p b : ℕ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) (hδζ : δ ≤ ζ) (hpb : p ≤ b)
    (hcutoff : N * δ ^ p ≤ T) : N * δ ^ b ≤ T * ζ ^ (b - p) := by
  have he : δ ^ b = δ ^ p * δ ^ (b - p) := by
    rw [← pow_add, Nat.add_sub_of_le hpb]
  rw [he, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hcutoff (pow_nonneg hδ _)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ hδζ _) hT)

theorem dyadic_polynomial_count_factor (A ζ : ℝ) (a i : ℕ) :
    A * ((2 : ℝ) ^ (i + 1) / ζ) ^ a = (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
  simp only [pow_succ', mul_pow, div_pow, ← pow_mul]
  rw [Nat.mul_comm i a]
  ring

theorem polynomial_bias_mass_factor {A ζ : ℝ} {a b : ℕ}
    (hζ : 0 < ζ) (hab : a ≤ b) :
    (A * (2 / ζ) ^ a) * ζ ^ b = A * 2 ^ a * ζ ^ (b - a) := by
  rw [div_pow, pow_sub₀ ζ hζ.ne' hab]
  ring

theorem product_spectrumTail_polynomial_cutoff {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤
      2 * A * 2 ^ a * ζ ^ (Fintype.card B - a) + T * ζ ^ (Fintype.card B - p) := by
  have hc : ∀ i < n, ((S (i + 1)).card : ℝ) ≤
      (A * (2 / ζ) ^ a) * ((2 : ℝ) ^ a) ^ i := by
    intro i hi
    rw [← dyadic_polynomial_count_factor]
    exact hcount i hi
  have ht := product_spectrumTail_dyadic c S n a (by positivity) hζ.le hab hc hsmall
  rw [polynomial_bias_mass_factor hζ (by omega)] at ht
  have hδ : ζ / 2 ^ n ≤ ζ := by
    exact div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hb := cutoff_power_mass_bound hT (by positivity) hδ hpb hcutoff
  exact ht.trans (by nlinarith only [hb])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem product_spectrumTail_le_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : ℕ → Finset K) (n a p : ℕ) {A T ζ ε : ℝ}
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hab : a + 1 ≤ Fintype.card B) (hpb : p + 1 ≤ Fintype.card B)
    (hcount : ∀ i < n, ((S (i + 1)).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a)
    (hsmall : ∀ i ≤ n, ∀ b k, k ∉ S i → ‖c b k‖ ≤ ζ / 2 ^ i)
    (hcutoff : (Fintype.card K : ℝ) * (ζ / 2 ^ n) ^ p ≤ T)
    (haccuracy : (2 * A * 2 ^ a + T) * ζ ≤ ε) :
    spectrumTail (S 0) (fun k => ‖∏ b, c b k‖) ≤ ε := by
  have ht := product_spectrumTail_polynomial_cutoff c S n a p hA hT hζ hab (by omega)
    hcount hsmall hcutoff
  have ha : ζ ^ (Fintype.card B - a) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  have hp : ζ ^ (Fintype.card B - p) ≤ ζ :=
    pow_le_of_le_one hζ.le hζ1 (by omega)
  apply ht.trans
  calc
    _ ≤ 2 * A * 2 ^ a * ζ + T * ζ := by gcongr
    _ = (2 * A * 2 ^ a + T) * ζ := by ring
    _ ≤ ε := haccuracy

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

theorem exists_length_dyadic_cutoff {C L ζ : ℝ} {c : ℕ}
    (hC : 0 < C) (hζ : 0 < ζ) (hc : 0 < c) (hstart : C / ζ ^ c ≤ L) :
    ∃ n : ℕ, (∀ i ≤ n, C / (ζ / 2 ^ i) ^ c ≤ L) ∧
      L * (ζ / 2 ^ n) ^ c ≤ 2 ^ c * C := by
  have hpow : 0 < ζ ^ c := pow_pos hζ _
  have hstart' : C ≤ L * ζ ^ c := (div_le_iff₀ hpow).mp hstart
  have hx : 1 ≤ L * ζ ^ c / C := (le_div_iff₀ hC).mpr (by simpa)
  have hy : (1 : ℝ) < 2 ^ c := one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hy
  have hswitch (i : ℕ) : ((2 : ℝ) ^ c) ^ i = (2 ^ i) ^ c := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm c i]
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hi' : ((2 : ℝ) ^ c) ^ i ≤ L * ζ ^ c / C :=
      (pow_le_pow_right₀ hy.le hi).trans hn
    have hi'' : C * (2 ^ i) ^ c ≤ L * ζ ^ c := by
      have hh := (le_div_iff₀ hC).mp hi'
      rw [hswitch] at hh
      linarith only [hh]
    rw [div_pow]
    apply (div_le_iff₀ (div_pos hpow (by positivity))).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 ^ i) ^ c)).mpr
    exact hi''
  · have hh := (div_lt_iff₀ hC).mp hn'
    rw [pow_succ, hswitch] at hh
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ n) ^ c)).mpr
    nlinarith only [hh]

theorem length_cutoff_mass_bound {N V L C δ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsize : N ≤ V * L ^ t) (hcutoff : L * δ ^ c ≤ C) :
    N * δ ^ (c * t) ≤ V * C ^ t := by
  calc
    _ ≤ (V * L ^ t) * δ ^ (c * t) :=
      mul_le_mul_of_nonneg_right hsize (pow_nonneg hδ _)
    _ = V * (L * δ ^ c) ^ t := by rw [mul_pow, pow_mul]; ring
    _ ≤ V * C ^ t := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hL (pow_nonneg hδ _)) hcutoff t) hV

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

theorem frequencyGridInterval_card (M : ℕ) (center : ℝ) {radius : ℝ} (hr : 0 ≤ radius) :
    ((frequencyGridInterval M center radius).card : ℝ) ≤ 2 * radius + 1 := by
  classical
  let A := frequencyGridInterval M center radius
  have hinj : Function.Injective (fun k : Fin M => (k.val : ℤ)) := by
    intro x y h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hc := card_integer_set_le_diameter_add_one (A.image (fun k => (k.val : ℤ)))
    (by positivity : (0 : ℝ) ≤ 2 * radius) (by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hi' := abs_le.mp (Finset.mem_filter.mp hi).2
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      push_cast
      rw [abs_le]
      constructor <;> linarith)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalGridMajorSet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerSymmetricInterval_card (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  omega

theorem rationalGridMajorSet_card (M Q H : ℕ) :
    ((rationalGridMajorSet M Q H).card : ℝ) ≤
      (Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
  classical
  let A := Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)
  have hA : (A.card : ℝ) = 2 * Q * (H + 1) + 1 := by
    have h := integerSymmetricInterval_card (Q * (H + 1))
    dsimp only [A]
    norm_cast at h ⊢
    simpa only [Nat.mul_assoc] using h
  have hd (d : ℕ) :
      ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) ≤
        (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
    calc
      _ ≤ ∑ a ∈ A, ((frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ A, (2 * (H : ℝ) + 1) :=
        Finset.sum_le_sum (fun a _ => frequencyGridInterval_card M _ (Nat.cast_nonneg H))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hA]
  unfold rationalGridMajorSet
  calc
    _ ≤ ∑ d ∈ Finset.range (Q + 1),
        ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ Finset.range (Q + 1), ((2 * (Q : ℝ) * (H + 1) + 1) * (2 * H + 1)) :=
      Finset.sum_le_sum (fun d _ => hd d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

theorem rationalGridMajorBox_card (J : Type*) [Fintype J] [DecidableEq J] (M Q H : ℕ) :
    ((rationalGridMajorBox J M Q H).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ Fintype.card J := by
  classical
  unfold rationalGridMajorBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (rationalGridMajorSet_card M Q H) _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

theorem one_le_inverse_power {C ζ : ℝ} (hC : 1 ≤ C) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (r : ℕ) : 1 ≤ C / ζ ^ r := by
  apply (le_div_iff₀ (pow_pos hζ r)).mpr
  simpa only [one_mul] using (pow_le_one₀ hζ.le hζ1 : ζ ^ r ≤ 1).trans hC

theorem rationalGridMajorBox_ceil_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((rationalGridMajorBox J M ⌈X⌉₊ ⌈X⌉₊).card : ℝ) ≤
      (195 * X ^ 4) ^ Fintype.card J := by
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : (0 : ℝ) ≤ ⌈X⌉₊ := Nat.cast_nonneg _
  have hQ : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one hX0
    linarith
  have hQ1 : (⌈X⌉₊ : ℝ) + 1 ≤ 3 * X := by linarith
  have hp := mul_le_mul hQ hQ1 (by positivity : 0 ≤ (⌈X⌉₊ : ℝ) + 1) (by positivity)
  have hm : 2 * (⌈X⌉₊ : ℝ) * (⌈X⌉₊ + 1) + 1 ≤ 13 * X ^ 2 := by
    nlinarith [sq_nonneg (X - 1)]
  have hr : 2 * (⌈X⌉₊ : ℝ) + 1 ≤ 5 * X := by linarith
  have hbase : ((⌈X⌉₊ : ℝ) + 1) * (2 * ⌈X⌉₊ * (⌈X⌉₊ + 1) + 1) *
      (2 * ⌈X⌉₊ + 1) ≤ 195 * X ^ 4 := by
    calc
      _ ≤ (3 * X) * (13 * X ^ 2) * (5 * X) := by gcongr
      _ = _ := by ring
  exact (rationalGridMajorBox_card J M ⌈X⌉₊ ⌈X⌉₊).trans
    (pow_le_pow_left₀ (by positivity) hbase _)

theorem polynomialGridCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {C ζ : ℝ} (r : ℕ) (hC : 1 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M C r ζ).card : ℝ) ≤
      (195 * C ^ 4) ^ Fintype.card J / ζ ^ (4 * r * Fintype.card J) := by
  have h := rationalGridMajorBox_ceil_card J M (one_le_inverse_power hC hζ hζ1 r)
  unfold polynomialGridCover
  apply h.trans_eq
  simp only [div_pow, ← mul_div_assoc, ← pow_mul]
  rw [Nat.mul_comm r 4]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem lengthAwareSpectrumCover_card {K : Type*} [Fintype K]
    (cover : ℝ → Finset K) {C L V A ζ : ℝ} {c t a : ℕ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ((cover ζ).card : ℝ) ≤ A / ζ ^ a) :
    ((lengthAwareSpectrumCover C L c cover ζ).card : ℝ) ≤
      A / ζ ^ a + V * C ^ t / ζ ^ (c * t) := by
  classical
  unfold lengthAwareSpectrumCover
  split_ifs with hstart
  · exact hcover.trans (le_add_of_nonneg_right (by positivity))
  · rw [Finset.card_univ]
    have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
    exact hb.trans (le_add_of_nonneg_left (by positivity))

theorem lengthAwareSpectrumCover_accuracy {B K : Type*}
    [Fintype B] [Fintype K] [DecidableEq K]
    (coeff : B → K → ℂ) (cover : ℝ → Finset K) {C L V A ζ ε : ℝ} {c t a : ℕ}
    (hC : 0 < C) (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε) (hc : 0 < c)
    (haB : a + 1 ≤ Fintype.card B) (htB : c * t + 1 ≤ Fintype.card B)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ∀ δ, 0 < δ → δ ≤ 1 → ((cover δ).card : ℝ) ≤ A / δ ^ a)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → C / δ ^ c ≤ L →
      ∀ b k, k ∉ cover δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : (2 * A * 2 ^ a + V * (2 ^ c * C) ^ t) * ζ ≤ ε) :
    spectrumTail (lengthAwareSpectrumCover C L c cover ζ)
      (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  classical
  by_cases hstart : C / ζ ^ c ≤ L
  · obtain ⟨n, hn, hlast⟩ := exists_length_dyadic_cutoff hC hζ hc hstart
    have hδ (i : ℕ) : 0 < ζ / 2 ^ i ∧ ζ / 2 ^ i ≤ 1 := by
      refine ⟨by positivity, ?_⟩
      exact (div_le_self hζ.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hζ1
    have hb := length_cutoff_mass_bound hV hL (hδ n).1.le hsize hlast
    have hcount (i : ℕ) (_hi : i < n) :
        ((cover (ζ / 2 ^ (i + 1))).card : ℝ) ≤ A * (2 ^ (i + 1) / ζ) ^ a := by
      have hh := hcover (ζ / 2 ^ (i + 1)) (hδ _).1 (hδ _).2
      apply hh.trans_eq
      simp only [div_pow, div_div_eq_mul_div]
      ring
    have hsmall (i : ℕ) (hi : i ≤ n) :=
      hminor (ζ / 2 ^ i) (hδ i).1 (hδ i).2 (hn i hi)
    have ht := product_spectrumTail_le_accuracy coeff (fun i => cover (ζ / 2 ^ i))
      n a (c * t) hA (by positivity) hζ hζ1 haB htB hcount hsmall hb haccuracy
    simpa only [lengthAwareSpectrumCover, if_pos hstart, pow_zero, div_one] using ht
  · simpa only [lengthAwareSpectrumCover, if_neg hstart, spectrumTail,
      Finset.mem_univ, ite_true, Finset.sum_const_zero] using hε

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

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

end Erdos3

end

section

namespace Erdos3

theorem majorArcBiasConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcBiasConstant n U := by
  have h := localizedMajorArcBudget_pos n hU (by norm_num : (0 : ℝ) < 1)
  rw [localizedMajorArcBudget_eq_power n hU (by norm_num)] at h
  simpa only [majorArcBiasConstant, majorArcBiasExponent, one_pow, div_one] using h

theorem majorArcLocalizationConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLocalizationConstant n U := by
  have : 0 < U := lt_of_lt_of_le (by norm_num) hU
  unfold majorArcLocalizationConstant
  positivity

theorem majorArcLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLengthConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcLengthConstant
  positivity

theorem majorArcErrorConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcErrorConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3

theorem majorArcCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ majorArcCoverConstant n j U V := by
  have hq := (majorArcBiasConstant_pos n hU).le
  have he := (majorArcErrorConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  unfold majorArcCoverConstant
  nlinarith only [hd, mul_nonneg hV he]

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

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
namespace OAI

section

namespace Erdos3

theorem positiveModerateLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < positiveModerateLengthConstant n U := by
  have h0 := majorArcLengthConstant_pos n hU
  have h1 := majorArcLengthConstant_pos (n + 1) hU
  unfold positiveModerateLengthConstant
  positivity

theorem positiveModerateLengthExponent_pos (n : ℕ) :
    0 < positiveModerateLengthExponent n := by
  unfold positiveModerateLengthExponent majorArcLengthExponent
  omega

theorem positiveModerateCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ positiveModerateCoverConstant n j U V := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  unfold positiveModerateCoverConstant
  nlinarith

end Erdos3

end

end OAI

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedExpectationWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ofDensity_mean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) (f : X → ℝ) :
    (ofDensity w hw htotal).mean f = 𝔼 x, w x * f x := by
  simp only [mean, ofDensity, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem reweight_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) (f : X → ℝ) :
    (p.reweight w hw htotal).mean f = p.mean (fun x => w x * f x) := by
  simp only [mean, reweight, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
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

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

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

open scoped BigOperators

namespace NormalizedScalarCubeSource

theorem source_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.source.mean (fun x => f (x none : ℤ)) = (s.coefficientWeights).mean (fun z => f z) := by
  apply (FiniteProbabilityWeights.reweight_mean s.baseLaw
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized
    (fun x => f (x none : ℤ))).trans
  rw [coefficientWeights, FiniteProbabilityWeights.ofDensity_mean]
  simp only [s.weight_empty_coordinate, coefficientDensity]
  exact s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length) * f z)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

namespace FiniteCoefficientSlice

end FiniteCoefficientSlice

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dif_pos S.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerGridFourier_inversion {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (z : J → ℤ) :
    (∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ) ^ Fintype.card J * integerGridMass p Y M z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) *
        (∑ k : J → Fin M, rectangularGridCharacter M k (Y x) * star (rectangularGridCharacter M k z)) := by
      simp only [integerGridCoefficient, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [rectangularGridCharacter_orthogonality, integerGridMass, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : integerGridResidue M (Y x) = integerGridResidue M z <;> simp [hx, mul_comm]

theorem independent_integerGridCoefficient {B J : Type*} [Fintype B] [DecidableEq B] [Fintype J]
    {X : B → Type*} [∀ b, Fintype (X b)] (p : ∀ b, FiniteProbabilityWeights (X b))
    (Y : ∀ b, X b → J → ℤ) (shift : J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient (FiniteProbabilityWeights.pi p) (fun x => shift + ∑ b, Y b (x b)) M k =
      rectangularGridCharacter M k shift * ∏ b, integerGridCoefficient (p b) (Y b) M k := by
  simp only [integerGridCoefficient, rectangularGridCharacter_add, rectangularGridCharacter_fintype_sum]
  rw [FiniteProbabilityWeights.complexMean_mul_left]
  congr 1
  exact FiniteProbabilityWeights.complexMean_pi_product p
    (fun b x => rectangularGridCharacter M k (Y b x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerGridDensity_fourier {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (K M : ℕ) [NeZero M] (z : J → ℤ) :
    (integerGridDensity p Y K M z : ℂ) =
      ((K : ℂ) / M) ^ Fintype.card J *
        ∑ k : J → Fin M, integerGridCoefficient p Y M k * star (rectangularGridCharacter M k z) := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [integerGridFourier_inversion, div_pow]
  simp only [integerGridDensity, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp

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

theorem integerBooleanBlockValue_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (t : Finset I) :
    (integerBooleanBlockValue x t : ℝ) = booleanBlockValue (fun g r => (x g r : ℝ)) t := by
  have hf (r : Option I) : ((booleanFeature r t : ℤ) : ℝ) = (booleanFeature r t : ℝ) := by
    cases r with
    | none => simp only [booleanFeature, Int.cast_one]
    | some i =>
        by_cases hi : i ∈ t <;> simp only [booleanFeature, hi, ite_true, ite_false, Int.cast_one, Int.cast_zero]
  simp only [integerBooleanBlockValue, booleanBlockValue, Int.cast_prod, Int.cast_sum, Int.cast_mul, hf]

theorem integerBooleanBlockJet_cast {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (S : Finset I) :
    (integerBooleanBlockJet x S : ℝ) =
      booleanCoefficient (booleanBlockValue (fun g r => (x g r : ℝ))) S := by
  have h := booleanCoefficient_map (Int.castRingHom ℝ) (integerBooleanBlockValue x) S
  change (integerBooleanBlockJet x S : ℝ) =
    booleanCoefficient (fun t => (integerBooleanBlockValue x t : ℝ)) S at h
  simpa only [integerBooleanBlockValue_cast] using h

theorem gridJetFrequency_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (v : Finset I → ℝ) :
    (∑ S, gridJetFrequency M J k S * v S) = ∑ S : J, (((k S).val : ℝ) / M) * v S := by
  classical
  calc
    _ = ∑ S ∈ J, gridJetFrequency M J k S * v S := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro S _ hS
      simp only [gridJetFrequency, dif_neg hS, zero_mul]
    _ = ∑ S : J, gridJetFrequency M J k S * v S := (Finset.sum_coe_sort J _).symm
    _ = _ := Finset.sum_congr rfl (fun S _ => by rw [gridJetFrequency_apply])

theorem integerBooleanBlockJet_pairing {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    (∑ S : J, (((k S).val : ℝ) / M) * (integerBooleanBlockJet x S : ℝ)) =
      booleanBlockPhase (gridJetFrequency M J k) (fun g r => (x g r : ℝ)) := by
  simp only [integerBooleanBlockJet_cast, booleanBlockPhase, gridJetFrequency_pairing]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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
open CircleFourier

theorem integerBooleanBlockJet_scaled_pairing {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (x : G → Option I → ℤ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (c : ℤ) :
    (∑ S : J, (((k S).val : ℝ) / M) * ((c * integerBooleanBlockJet x S : ℤ) : ℝ)) =
      (c : ℝ) * booleanBlockPhase (gridJetFrequency M J k) (fun j r => (x j r : ℝ)) := by
  rw [← integerBooleanBlockJet_pairing x M J k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Int.cast_mul]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

theorem normalizedScalarCubeSourceOfIntegerPMF_mean (f : ℤ → ℝ) :
    (intervalSource).source.mean (fun x => f (x none : ℤ)) =
      ∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal * f k := by
  apply ((intervalSource).source_coefficient_mean f).trans
  change (FiniteProbabilityWeights.ofDensity _ _ _).mean _ = _
  rw [FiniteProbabilityWeights.ofDensity_mean]
  change (𝔼 k : coefficientResidueSet L 1 0,
    w (fun _ => (k.val : ℝ) / L) * f k.val) = _
  have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
    ext k
    simp only [coefficientResidueSet, Finset.mem_filter]
    exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
  rw [hr, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Int.card_Ico, sub_zero, Int.toNat_natCast]
  simp_rw [hgrid, mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  exact Finset.sum_coe_sort (Finset.Ico 0 (L : ℤ)) (fun k => (p k).toReal * f k)

theorem normalizedScalarCubeSourceOfIntegerPMF_law :
    (intervalSource).source.toPMF.map (fun x => (x none : ℤ)) = p := by
  ext z
  let q := (intervalSource).source.toPMF.map (fun x => (x none : ℤ))
  have hreal : (q z).toReal = (p z).toReal := by
    change (((intervalSource).source.toPMF.map (fun x => (x none : ℤ))) z).toReal = _
    rw [FiniteProbabilityWeights.toPMF_map_toReal]
    refine (normalizedScalarCubeSourceOfIntegerPMF_mean L hL p hs w B T hB hw hLip hgrid
      (fun k => @ite ℝ (k = z) (Classical.propDecidable (k = z)) 1 0)).trans ?_
    by_cases hz : z ∈ Finset.Ico 0 (L : ℤ)
    · simp [mul_ite, hz]
    · have hpz : p z = 0 := by
        by_contra h
        exact hz (hs z h)
      simp [mul_ite, hz, hpz]
  exact (ENNReal.ofReal_toReal (q.apply_ne_top z)).symm.trans
    ((congrArg ENNReal.ofReal hreal).trans (ENNReal.ofReal_toReal (p.apply_ne_top z)))

end IntegerSourceLaw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedModeratePointMass
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ}
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

theorem ScalarCubePrimitiveBudget.mono {I : Type*} [Fintype I] [DecidableEq I]
    {s : NormalizedScalarCubeSource I} {A : ℝ≥0} {U V : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hUV : U ≤ V) : ScalarCubePrimitiveBudget s A V :=
  ⟨h.one_le.trans hUV, h.dimension_le.trans hUV, h.modulus_le.trans hUV,
    h.weight_le.trans hUV, h.weightLipschitz_le.trans hUV, h.boundary_le.trans hUV,
    h.grid_le.trans hUV, h.derivative_le.trans hUV, h.density_le.trans hUV⟩

theorem scalarCubePrimitiveBudget_of_raw_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (scalarCubePrimitiveEnvelope I A B T M) := by
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  let X := 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2
  let Y := 2 * scalarCubeGridBoundaryConstant I * V
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X, V]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, V, scalarCubeGridBoundaryConstant]; positivity
  have hZ : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator; positivity
  have hP : 0 ≤ paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap; positivity
  have hparts :
      1 ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      q ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (M : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (B : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (T : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      X ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      Y ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      paddedResidueDensityCap I M ≤ scalarCubePrimitiveEnvelope I A B T M := by
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧ _
    dsimp only [scalarCubePrimitiveEnvelope]
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      q ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (M : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (B : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (T : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      X ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      Y ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      paddedResidueDensityCap I M ≤ 1 + q + M + B + T + X + Y + _ + _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hq, hX, hY, hZ, hP, Nat.cast_nonneg (α := ℝ) M, B.coe_nonneg, T.coe_nonneg]
  obtain ⟨h1, hq', hM', hB', hT', hX', hY', hZ', hP'⟩ := hparts
  have hvol : scalarCubeDomainDensity I ≤ V := scalarCubeDomainDensity_le_power I
  have hboundary : scalarCubeBoundaryConstant I ≤ X := by
    unfold scalarCubeBoundaryConstant
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num)) (by positivity)
  have hgrid : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hvol
      (show 0 ≤ 2 * scalarCubeGridBoundaryConstant I by unfold scalarCubeGridBoundaryConstant; positivity)
    simpa only [scalarCubeDomainDensity, div_eq_mul_inv, Y] using hh
  refine ⟨h1, hq', ?_, ?_, ?_, hboundary.trans hX', hgrid.trans hY', hZ', ?_⟩
  · exact (by exact_mod_cast hM : (s.modulusBound : ℝ) ≤ M).trans hM'
  · exact (by exact_mod_cast hB : (s.weightBound : ℝ) ≤ B).trans hB'
  · exact (by exact_mod_cast hT : (s.weightLipschitz : ℝ) ≤ T).trans hT'
  · exact (paddedResidueDensityCap_mono I hM).trans hP'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalizedUniformCubeSource_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedUniformCubeSource I L M hL m r hm hmM hsize) A
      (scalarCubePrimitiveEnvelope I A 1 0 M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 M le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

theorem principalNormalizedSource_law :
    (principalNormalizedSource hK hT hγ hlarge).source.toPMF.map (fun x => (x none : ℤ)) =
      principalIntegerPMF K T γ hK hT hγ hlarge :=
  normalizedScalarCubeSourceOfIntegerPMF_law
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

theorem principalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (principalNormalizedSource hK hT hγ hlarge) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 16 (128 * probabilityProfileLipschitz) 1
    le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "profile" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (allocatedPrincipalNormalizedSource B U basis hR S j i hactive) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  principalNormalizedSource_primitive _ _ _ _ A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

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

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "gridAxes" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem principalIntervalLength_mul_scale_bounds {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    2 * γ * K ≤ (principalIntervalLength K T γ : ℝ) * T ∧
      (principalIntervalLength K T γ : ℝ) * T ≤ 4 * γ * K := by
  have hb := principalIntervalLength_bounds hK hT hγ hlarge
  constructor
  · calc
      2 * γ * K = (2 * γ * (K / T)) * T := by field_simp
      _ ≤ (principalIntervalLength K T γ : ℝ) * T := mul_le_mul_of_nonneg_right hb.1 hT.le
  · calc
      (principalIntervalLength K T γ : ℝ) * T ≤ (4 * γ * (K / T)) * T :=
        mul_le_mul_of_nonneg_right hb.2 hT.le
      _ = 4 * γ * K := by field_simp

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCoefficientPositiveSupport
namespace OAI

section

namespace Erdos3

theorem principalNormalizedSource_positive_support {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    (z : IntegerScalarCubeBox Empty (principalNormalizedSource hK hT hγ hlarge).length)
    (hz : (principalNormalizedSource hK hT hγ hlarge).source.weight z ≠ 0) :
    ((principalNormalizedSource hK hT hγ hlarge).length : ℝ) / 4 ≤ (z none : ℝ) := by
  have hsupport : z ∈ (principalNormalizedSource hK hT hγ hlarge).source.toPMF.support := by
    intro hzero
    apply hz
    rw [← FiniteProbabilityWeights.toPMF_toReal, hzero]
    rfl
  have hmap : (z none : ℤ) ∈
      ((principalNormalizedSource hK hT hγ hlarge).source.toPMF.map
        (fun x => (x none : ℤ))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hsupport, rfl⟩
  rw [principalNormalizedSource_law] at hmap
  have hb := (principalIntegerPMF_support hK hT hγ hlarge hmap).1
  have he : T * (z none : ℝ) / K = (z none : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb
  have hlength := (principalIntervalLength_bounds hK hT hγ hlarge).2
  change (principalIntervalLength K T γ : ℝ) / 4 ≤ _
  linarith

namespace VectorPolynomial

theorem allocatedPrincipalNormalizedSource_positive_support {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (z : IntegerScalarCubeBox Empty (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length)
    (hz : (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.weight z ≠ 0) :
    ((allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length : ℝ) / 4 ≤
      (z none : ℝ) :=
  principalNormalizedSource_positive_support _ _ _ _ z hz

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
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
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalNormalizedSource_scale_bounds :
    2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
        ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ∧
      ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ≤
        4 * gamma * (basisAxisScale (basis j) i : ℝ) := by
  change 2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
      (principalIntervalLength (basisAxisScale (basis j) i) ((S.value : ℝ) ^ (j.val + 1)) gamma : ℝ) *
        (S.value : ℝ) ^ (j.val + 1) ∧ _
  exact principalIntervalLength_mul_scale_bounds
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

theorem allocatedPrincipalNormalizedSource_grid_ratio {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i) :
    (M : ℝ) / (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) ≤
      C / (2 * gamma) := by
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlength : 0 < ((csource).length : ℝ) := Nat.cast_pos.mpr (csource).length_pos
  have hscale : 0 < (S.value : ℝ) ^ (j.val + 1) :=
    pow_pos (by exact_mod_cast S.positive) _
  apply (div_le_iff₀ (mul_pos hlength hscale)).mpr
  calc
    (M : ℝ) ≤ C * basisAxisScale (basis j) i := hM
    _ = (C / (2 * gamma)) * (2 * gamma * basisAxisScale (basis j) i) := by field_simp
    _ ≤ (C / (2 * gamma)) * (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) :=
      mul_le_mul_of_nonneg_left
        (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).1
        (div_nonneg hC (by positivity))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedGridSpectrumSize
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedGrid_modulus_cardinality (j : Fin m) (i : Fin (n j))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {C : ℝ} {M : ℕ} (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (d : ℕ) :
    (M : ℝ) ^ d ≤ C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
  change basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) at hgrid
  have hK : (basisAxisScale (basis j) i : ℝ) ≤
      (S.value : ℝ) ^ (layerTailDegree m + 1) := by exact_mod_cast hgrid
  calc
    (M : ℝ) ^ d ≤ (C * (S.value : ℝ) ^ (layerTailDegree m + 1)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg M)
        (hM.trans (mul_le_mul_of_nonneg_left hK hC)) d
    _ = C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
      rw [mul_pow, ← pow_mul]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem positiveModerateSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L ζ).card : ℝ) ≤
      positiveModerateSpectrumConstant n (Fintype.card J) U V /
        ζ ^ positiveModerateSpectrumExponent n (Fintype.card J) +
      W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t) := by
  apply lengthAwareSpectrumCover_card _ hL hW
    (show 0 ≤ positiveModerateSpectrumConstant n (Fintype.card J) U V by
      unfold positiveModerateSpectrumConstant; positivity)
    (positiveModerateLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact polynomialGridCover_card J M _ (positiveModerateCoverConstant_one_le n _ hU hV) hζ hζ1

theorem positiveModerateSpectrum_tail {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L ζ ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hB : positiveModerateSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 →
      positiveModerateLengthConstant n U / δ ^ positiveModerateLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (positiveModerateCoverConstant n (Fintype.card J) U V)
        (positiveModerateCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ)
    (haccuracy : (2 * positiveModerateSpectrumConstant n (Fintype.card J) U V *
        2 ^ positiveModerateSpectrumExponent n (Fintype.card J) +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ) (fun k => ‖∏ b, coeff b k‖) ≤ ε := by
  apply lengthAwareSpectrumCover_accuracy coeff _ (t := t)
    (a := positiveModerateSpectrumExponent n (Fintype.card J))
    (positiveModerateLengthConstant_pos n hU) hL hW
    (show 0 ≤ positiveModerateSpectrumConstant n (Fintype.card J) U V by
      unfold positiveModerateSpectrumConstant; positivity) hζ hζ1 hε
    (positiveModerateLengthExponent_pos n)
  · unfold positiveModerateSpectrumBlockCount at hB; omega
  · unfold positiveModerateSpectrumBlockCount at hB; omega
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · intro δ hδ hδ1
    exact polynomialGridCover_card J M _ (positiveModerateCoverConstant_one_le n _ hU hV) hδ hδ1
  · exact hminor
  · exact haccuracy

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerate_uniform_spectrum_tail {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ζ ε : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hε : 0 ≤ ε)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (haccuracy : (2 * positiveModerateSpectrumConstant n J.card U V *
        2 ^ positiveModerateSpectrumExponent n J.card +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) * ζ ≤ ε) :
    spectrumTail (positiveModerateSpectrumCover J M n U V L ζ)
      (fun k => ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤ ε := by
  refine positiveModerateSpectrum_tail M n t
    (fun b k => weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k) hU hV hW hL hζ hζ1 hε
    (by simpa only [Fintype.card_coe] using hB)
    (by simpa only [Fintype.card_coe] using hsize) ?_
    (by simpa only [Fintype.card_coe] using haccuracy)
  intro δ hδ hδ1 hstart b k hk
  apply weightedPositiveAffineModerateGridCoefficient_minor_polynomial (c b) (s b) A hA
    (hc b) (h b) (u b) (v b) (hv b) (hstride b) (hpositive b) hV hδ hδ1 (fun j => hstart.trans (hlen b j))
    hM (hscale b) J hJ k
  simpa only [Fintype.card_coe] using hk

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveModerateAccuracyScale_one_le (n j t : ℕ) {U V W : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) :
    1 ≤ positiveModerateAccuracyScale n j t U V W := by
  have hL := (positiveModerateLengthConstant_pos n hU).le
  have hC : 0 ≤ positiveModerateSpectrumConstant n j U V := by
    unfold positiveModerateSpectrumConstant
    positivity
  unfold positiveModerateAccuracyScale
  exact le_add_of_nonneg_right (by positivity)

theorem positiveModerateRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < positiveModerateRetainedBias n j t U V W ε ∧
    positiveModerateRetainedBias n j t U V W ε ≤ 1 ∧
    (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) *
        positiveModerateRetainedBias n j t U V W ε ≤ ε := by
  have hD := positiveModerateAccuracyScale_one_le n j t (V := V) hU hW
  have hD0 : 0 < positiveModerateAccuracyScale n j t U V W := lt_of_lt_of_le zero_lt_one hD
  have hb : 0 < positiveModerateRetainedBias n j t U V W ε := div_pos hε hD0
  refine ⟨hb, (div_le_one hD0).mpr (hε1.trans hD), ?_⟩
  calc
    _ ≤ positiveModerateAccuracyScale n j t U V W *
        positiveModerateRetainedBias n j t U V W ε := by
      apply mul_le_mul_of_nonneg_right _ hb.le
      unfold positiveModerateAccuracyScale
      linarith
    _ = ε := by
      unfold positiveModerateRetainedBias
      field_simp

theorem positiveModerateSpectrumCover_card_budget (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
        positiveModerateSpectrumCardBudget n (Fintype.card J) t U V W ε := by
  obtain ⟨hζ, hζ1, _⟩ := positiveModerateRetainedBias_spec n (Fintype.card J) t hU hW hε hε1
  exact positiveModerateSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

theorem weightedAffineModerateGridCoefficient_eq_image {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℤ) (v : Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerSource c s) (weightedAffineModerateIntegerBlock c s u v J offset) M k =
      weightedAffineModerateGridCoefficient c s (fun j i => (u j i : ℝ)) v (offset : ℝ) M J k := by
  unfold integerGridCoefficient weightedModerateIntegerSource
  rw [FiniteProbabilityWeights.complexMean_prod]
  change c.source.complexMean _ = c.source.complexMean _
  congr 1
  funext z
  congr 1
  funext x
  rw [rectangularGridCharacter_eq]
  simp only [weightedAffineModerateIntegerBlock, integerBooleanBlockJet_scaled_pairing]
  simp only [affineIntegerCubeCoordinates, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rfl

theorem weightedAffineModerateIntegerJetSum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) (k : J → Fin M) :
    integerGridCoefficient (weightedModerateIntegerProductSource c s)
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) M k =
        rectangularGridCharacter M k shift * ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k := by
  have h := independent_integerGridCoefficient (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => weightedAffineModerateIntegerBlock (c b) (s b) (u b) (v b) J (offset b)) shift M k
  unfold weightedModerateIntegerProductSource weightedAffineModerateIntegerJetSum
  simpa only [weightedAffineModerateGridCoefficient_eq_image] using h

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

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedAffineModerateGridDensity_fourier {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ) :
    (integerGridDensity (weightedModerateIntegerProductSource c s)
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) K M z : ℂ) =
        weightedAffineModerateGridApproximation c s u v K M J offset shift z Finset.univ := by
  rw [integerGridDensity_fourier]
  simp only [weightedAffineModerateGridApproximation, Fintype.card_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedAffineModerateIntegerJetSum_coefficient]
  ring

theorem weightedAffineModerateGridDensity_error_of_tail {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (K M : ℕ) [NeZero M] (J : Finset (Finset I)) (offset : B → ℤ) (S : Finset (J → Fin M))
    {ε : ℝ} (htail : spectrumTail S (fun k =>
      ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k‖) ≤ ε)
    (shift z : J → ℤ) :
    ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
        (weightedAffineModerateIntegerJetSum c s u v J offset shift) K M z : ℂ) -
      weightedAffineModerateGridApproximation c s u v K M J offset shift z S‖ ≤ ((K : ℝ) / M) ^ J.card * ε := by
  let ψ k := rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)
  have hψ k : ‖ψ k‖ ≤ 1 := by
    simp only [ψ, norm_mul, norm_star, rectangularGridCharacter_norm, one_mul, le_refl]
  have hb := (finite_series_truncation_le S
    (fun k => ∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M J k) ψ hψ).trans htail
  rw [weightedAffineModerateGridDensity_fourier]
  unfold weightedAffineModerateGridApproximation
  rw [← mul_sub, norm_mul, norm_pow, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

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
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem principalSupportedAxisSources_primitive (b : B a) (v : Fin (h a)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q)
    (r ⟨a, b, v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize b v) A

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights (α := α) B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "sides_pos" => allocatedPrincipalSides_pos B U basis S

variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

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

theorem dense_slice_product_ratio {n : ℕ} {δ S C M V : ℝ} (H : Fin n → ℝ)
    (hδ : 0 < δ) (hS : 0 < S) (hC : 0 < C) (hM : 0 ≤ M)
    (hH : ∀ j, δ * S ≤ H j)
    (hbase : M / (C * S ^ n) ≤ V) :
    M / (C * ∏ j, H j) ≤ V / δ ^ n := by
  have hp : δ ^ n * S ^ n ≤ ∏ j, H j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using
      Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => δ * S) (g := H)
        (fun _ _ => (mul_pos hδ hS).le) (fun j _ => hH j)
  have hd : 0 < δ ^ n * (C * S ^ n) := by positivity
  have hden : δ ^ n * (C * S ^ n) ≤ C * ∏ j, H j := by
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  calc
    M / (C * ∏ j, H j) ≤ M / (δ ^ n * (C * S ^ n)) :=
      div_le_div_of_nonneg_left hM hd hden
    _ = (M / (C * S ^ n)) / δ ^ n := by ring
    _ ≤ V / δ ^ n := div_le_div_of_nonneg_right hbase (pow_pos hδ _).le

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem positiveAffineModerate_grid_approximation_on_cover
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℤ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (hs : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlen : ∀ b j, L ≤ (s b j).length)
    (K M t : ℕ) [NeZero M]
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t) :
    let F := positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n J.card t U V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget n J.card t U V W ε ∧
      ∀ shift z : J → ℤ,
        ‖(integerGridDensity (weightedModerateIntegerProductSource c s)
            (weightedAffineModerateIntegerJetSum c s u v J (fun _ => 0) shift) K M z : ℂ) -
          weightedAffineModerateGridApproximation c s u v K M J (fun _ => 0) shift z F‖ ≤
            ((K : ℝ) / M) ^ J.card * ε := by
  intro F
  obtain ⟨hζ, hζ1, hacc⟩ := positiveModerateRetainedBias_spec n J.card t (V := V) hU hW hε hε1
  have htail := weightedPositiveAffineModerate_uniform_spectrum_tail c s A hA hU hc hs
    (fun b j i => (u b j i : ℝ)) v hv hstride hpositive hV hW hL hζ hζ1 hε.le hlen
    (Nat.pos_of_ne_zero (NeZero.ne M)) hscale J hJ hB hsize hacc
  refine ⟨?_, fun shift z => ?_⟩
  · simpa only [Fintype.card_coe] using
      positiveModerateSpectrumCover_card_budget J M n t hU hV hW hL hε hε1
        (by simpa only [Fintype.card_coe] using hsize)
  · exact weightedAffineModerateGridDensity_error_of_tail c s u v K M J (fun _ => 0) F
      (by simpa only [Int.cast_zero] using htail) shift z

end Erdos3

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedProgressionResidueLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q hq r hsize

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

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
variable (hsize : ∀ t, (Fintype.card α + 1) * q ≤ H t)
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) (fun b v => hsize (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

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

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSupportedSlicedGridDensity_approximation_on_cover
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
          weightedAffineModerateGridApproximation coeff sources lower strides
            (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
          ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro V t W F
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  obtain ⟨hF, he⟩ := positiveAffineModerate_grid_approximation_on_cover coeff sources lower strides A hA
    hc.one_le (fun _ => hc) hs (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hε hε1 hlength
    (basisAxisScale (basis j) i) M t hscale rows hrows hB hcard
  refine ⟨hF,fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source B U basis hR hσ S q hq r H step c hH hsubset hcell
    j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw (basisAxisScale (basis j) i) M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
      (basisAxisScale (basis j) i) M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  rw [← hd']
  exact he shift z

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover.{u_1, u_2, u_3, u_4, u_5}
