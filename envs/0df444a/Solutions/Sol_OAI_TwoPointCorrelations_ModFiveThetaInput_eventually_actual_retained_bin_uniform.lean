-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_retained_bin_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:36:10.95326+00:00
-- url     : https://prove2.me/submissions/bea976c5-e174-4473-b422-a88fb78966bf

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_progression_block_testing_uniform

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h




theorem liouville_oneBounded : OneBounded liouville := by
  intro n hn
  have hs : ‖liouville n‖ ^ 2 = 1 := by
    rw [← norm_pow, liouville_sq hn.ne', norm_one]
  nlinarith [norm_nonneg (liouville n)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenterDegree
namespace OAI

/-!
# Degree control for products of prime centers

The argument is uniform in the indicators, so it applies both to integer
residues and to independent product residues. One prime is chosen from each
family, and the total number of lit prime coordinates controls the sum of
squared tuple weights.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma nonneg_product_le_power_card {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (C : ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, b i ≤ C * Fintype.card ι) :
    ∏ i, b i ≤ C ^ Fintype.card ι := by
  classical
  by_cases hn : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmean := Real.geom_mean_le_arith_mean (univ : Finset ι) (fun _ => (1 : ℝ)) b
    (fun _ _ => zero_le_one) (by simpa using hp) (fun i _ => hb i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at hmean
  have hbound : (∏ i, b i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ C :=
    hmean.trans ((div_le_iff₀ hp).mpr hsum)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg (fun i _ => hb i)) _) hbound
    (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow (prod_nonneg (fun i _ => hb i)) hn] at hpow
  exact hpow







lemma sum_degree_budget {ι : Type*} [Fintype ι] (ω V : ι → ℝ) (W : ℝ)
    (hV : ∀ i, V i ≤ 2 * W)
    (hdegree : ∑ i, ω i ≤ 6 * W * Fintype.card ι) :
    ∑ i, (ω i + V i) ≤ (8 * W) * Fintype.card ι := by
  have hv : (∑ i, V i) ≤ (2 * W) * Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, 2 * W := sum_le_sum (fun i _ => hV i)
      _ = _ := by simp; ring
  rw [sum_add_distrib]
  exact (add_le_add hdegree hv).trans_eq (by ring)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl

lemma matrixOperator_selfAdjoint (A : ι → ι → ℂ)
    (hA : ∀ i j, A i j = star (A j i)) : IsSelfAdjoint (matrixOperator A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  change (Matrix.toEuclideanLin A).IsSymmetric
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact (hA i j).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.InitialAverage
namespace OAI

/-! Compare a nonnegative average on an initial interval with the average
on an integer multiple of that interval. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma uniformAverage_initial_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (l N : ℕ) (hl : 0 < l) (hN : 0 < N) :
    uniformAverage (fun t : Fin N => f t.val) ≤
      (l : ℝ) * uniformAverage (fun t : Fin (l * N) => f t.val) := by
  have hNl : N ≤ l * N := by nlinarith
  have hs : (∑ t ∈ range N, f t) ≤ ∑ t ∈ range (l * N), f t :=
    sum_le_sum_of_subset_of_nonneg (range_mono hNl) (fun t _ _ => hf t)
  have hlr : (l : ℝ) ≠ 0 := by positivity
  have hNr : (N : ℝ) ≠ 0 := by positivity
  simp only [uniformAverage, Fintype.card_fin, Fin.sum_univ_eq_sum_range f,
    Nat.cast_mul]
  calc
    _ ≤ (∑ t ∈ range (l * N), f t) / N :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg N)
    _ = _ := by field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary
namespace OAI

/-!
# The endpoint error in the rough-shift averaging argument

These are finite identities and bounds from the proof of (q:rough-shifts)
in quantitative/03-analytic.tex. No short-sum or sieve estimate is assumed.
The averages below use the positive integers `1,...,Y` and translations
`1,...,D`; the resulting error is at most `2D/Y` times the total weight.
-/

namespace TwoPointCorrelations

open scoped _root_.BigOperators



theorem positivePrefix_translate_identity (u : ℕ → ℂ) (Y m : ℕ) :
    positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y =
      positivePrefix (fun n => u (n + Y)) m - positivePrefix u m := by
  have hsplit : positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m =
      positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
    have h₁ : positivePrefix u (Y + m) =
        positivePrefix u Y + positivePrefix (fun n => u (n + Y)) m := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) Y m
    have h₂ : positivePrefix u (m + Y) =
        positivePrefix u m + positivePrefix (fun n => u (n + m)) Y := by
      simpa only [positivePrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        Finset.sum_range_add (fun n => u (n + 1)) m Y
    exact h₁.symm.trans ((congrArg (positivePrefix u) (Nat.add_comm Y m)).trans h₂)
  linear_combination -hsplit

theorem norm_positivePrefix_le (u : ℕ → ℂ) (Y : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) : ‖positivePrefix u Y‖ ≤ Y * B := by
  calc
    _ ≤ ∑ v ∈ Finset.range Y, ‖u (v + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.range Y, B :=
      Finset.sum_le_sum (fun v _ => hu (v + 1) (by omega))
    _ = _ := by simp

/-- Translating by `m` loses at most `m` terms at each endpoint. No relation
between the prefix length and the translation is needed. -/
theorem norm_positivePrefix_translate_sub_le (u : ℕ → ℂ) (Y m : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖positivePrefix (fun n => u (n + m)) Y - positivePrefix u Y‖ ≤ 2 * m * B := by
  rw [positivePrefix_translate_identity]
  calc
    _ ≤ ‖positivePrefix (fun n => u (n + Y)) m‖ + ‖positivePrefix u m‖ :=
      norm_sub_le _ _
    _ ≤ (m : ℝ) * B + m * B := add_le_add
      (norm_positivePrefix_le _ _ _ (fun n hn => hu _ (by omega)))
      (norm_positivePrefix_le _ _ _ hu)
    _ = _ := by ring

/-- Averaging positive translations has the same finite endpoint bound. -/
theorem norm_translatedPrefixAverage_sub_le (u : ℕ → ℂ) (Y D : ℕ)
    (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖translatedPrefixAverage u Y D - positivePrefix u Y‖ ≤ 2 * D * B := by
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have heq : translatedPrefixAverage u Y D - positivePrefix u Y =
      (D : ℂ)⁻¹ * ∑ m ∈ Finset.range D,
        (positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y) := by
    simp only [translatedPrefixAverage, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_sub]
    field_simp
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (D : ℝ)⁻¹ * ∑ m ∈ Finset.range D,
        ‖positivePrefix (fun n => u (n + (m + 1))) Y - positivePrefix u Y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hDr.le)
    _ ≤ (D : ℝ)⁻¹ * ∑ _m ∈ Finset.range D, (2 * D * B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hDr.le)
      apply Finset.sum_le_sum
      intro m hm
      apply (norm_positivePrefix_translate_sub_le u Y (m + 1) B hu).trans
      have hmD : ((m + 1 : ℕ) : ℝ) ≤ D := by
        exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmD (by norm_num : (0 : ℝ) ≤ 2)) hB
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- The normalized endpoint error, in exactly the `D/Y` scale used in
the rough-shift lemma. -/
theorem norm_normalized_translation_error (u : ℕ → ℂ) (Y D : ℕ)
    (hY : 0 < Y) (hD : 0 < D) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) :
    ‖(translatedPrefixAverage u Y D - positivePrefix u Y) / (Y : ℂ)‖ ≤
      2 * (D : ℝ) / Y * B := by
  rw [norm_div, Complex.norm_natCast]
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  apply (div_le_div_of_nonneg_right
    (norm_translatedPrefixAverage_sub_le u Y D hD B hB hu) hYr.le).trans
  exact le_of_eq (by ring)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OverlapPrefix
namespace OAI

/-! Overlapping blocks recover a positive prefix. The missing terminal
edges cost displacement/block length, and translation costs block/prefix length. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma edgeBlockSum_error {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M R t : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hr : ∀ e ∈ edges, r e ≤ R)
    (hc : ∀ n, 0 < n → (∑ e ∈ edges, ‖c e n‖) ≤ D) :
    ‖edgeBlockSum edges r c M t - fullBlockSum edges c M t‖ ≤ R * D := by
  have hterm (i : ℕ) :
      ‖(∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
        ∑ e ∈ edges, c e (t + i + 2)‖ ≤ if M - R ≤ i then D else 0 := by
    by_cases hi : M - R ≤ i
    · rw [if_pos hi, ← sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply le_trans _ (hc (t + i + 2) (by omega))
      apply sum_le_sum
      intro e _
      split_ifs <;> simp
    · rw [if_neg hi]
      have he (e : E) (he : e ∈ edges) : i + 1 + r e ≤ M := by
        have := hr e he
        omega
      have hz : (∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) =
          ∑ e ∈ edges, c e (t + i + 2) := by
        apply sum_congr rfl
        intro e he'
        rw [if_pos (he e he')]
      simp only [hz, sub_self, norm_zero, le_refl]
  have hfilter : (range M).filter (fun i => M - R ≤ i) = Ico (M - R) M := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  calc
    _ = ‖∑ i ∈ range M,
        ((∑ e ∈ edges, if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
          ∑ e ∈ edges, c e (t + i + 2))‖ := by rw [sum_sub_distrib]; rfl
    _ ≤ ∑ i ∈ range M, ‖(∑ e ∈ edges,
        if i + 1 + r e ≤ M then c e (t + i + 2) else 0) -
          ∑ e ∈ edges, c e (t + i + 2)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range M, if M - R ≤ i then D else 0 := sum_le_sum (fun i _ => hterm i)
    _ = (M - (M - R) : ℕ) * D := by
      rw [← sum_filter, hfilter]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show M - (M - R) ≤ R by omega)) hD

lemma fullBlockSum_prefix_identity {E : Type*} (edges : Finset E)
    (c : E → ℕ → ℂ) (M N : ℕ) :
    (M : ℂ)⁻¹ * ∑ t ∈ range N, fullBlockSum edges c M t =
      translatedPrefixAverage (fun n => ∑ e ∈ edges, c e n) N M := by
  unfold fullBlockSum translatedPrefixAverage positivePrefix
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  rw [show t + i + 2 = t + 1 + (i + 1) by omega]

lemma edgeBlockSum_prefix_error {E : Type*} (edges : Finset E) (r : E → ℕ)
    (c : E → ℕ → ℂ) (M R N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (D : ℝ) (hD : 0 ≤ D) (hr : ∀ e ∈ edges, r e ≤ R)
    (hc : ∀ n, 0 < n → (∑ e ∈ edges, ‖c e n‖) ≤ D) :
    ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) / (N : ℂ) -
        positivePrefix (fun n => ∑ e ∈ edges, c e n) N / (N : ℂ)‖ ≤
      (R : ℝ) / M * D + 2 * (M : ℝ) / N * D := by
  let F := fun n => ∑ e ∈ edges, c e n
  let T := translatedPrefixAverage F N M
  have htranslate := norm_normalized_translation_error F N M hN hM D hD
    (fun n hn => (norm_sum_le _ _).trans (hc n hn))
  have hblock : ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
      (N : ℂ) - T / (N : ℂ)‖ ≤ (R : ℝ) / M * D := by
    have heq : ((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
        (N : ℂ) - T / (N : ℂ) =
        ((∑ t ∈ range N, (edgeBlockSum edges r c M t - fullBlockSum edges c M t)) /
          (M : ℂ)) / (N : ℂ) := by
      dsimp [T, F]
      rw [← fullBlockSum_prefix_identity edges c M N, sum_sub_distrib]
      ring
    rw [heq, norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hs : ‖∑ t ∈ range N, (edgeBlockSum edges r c M t - fullBlockSum edges c M t)‖ ≤
        (N : ℝ) * ((R : ℝ) * D) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _t ∈ range N, (R : ℝ) * D :=
          sum_le_sum (fun t _ => edgeBlockSum_error edges r c M R t D hD hr hc)
        _ = _ := by simp
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    calc
      _ ≤ ((N : ℝ) * ((R : ℝ) * D) / M) / N :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hs hMr.le) hNr.le
      _ = _ := by field_simp
  calc
    _ ≤ ‖((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
        (N : ℂ) - T / (N : ℂ)‖ + ‖(T - positivePrefix F N) / (N : ℂ)‖ := by
      have heq : ((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
          (N : ℂ) - positivePrefix F N / (N : ℂ) =
          (((∑ t ∈ range N, edgeBlockSum edges r c M t) / (M : ℂ)) /
            (N : ℂ) - T / (N : ℂ)) + (T - positivePrefix F N) / (N : ℂ) := by ring
      rw [heq]
      exact norm_add_le _ _
    _ ≤ _ := add_le_add hblock htranslate

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SelfAdjointPath
namespace OAI

/-!
# Positivity along an invertible self-adjoint path

The resolvent path in manuscript Lemma `q:noncommuting` starts at the
identity and is self-adjoint and invertible throughout a real interval.
Its positivity follows from continuity of the least Rayleigh quotient.
The argument is carried out in finite dimension.
-/

open _root_.Filter

namespace TwoPointCorrelations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Nontrivial E]






@[simp] lemma leastRayleigh_id : leastRayleigh (ContinuousLinearMap.id ℂ E) = 1 := by
  let : Nonempty {x : E // x ≠ 0} := ⟨⟨Classical.choose (exists_ne (0 : E)),
    Classical.choose_spec (exists_ne (0 : E))⟩⟩
  have hpoint (x : {x : E // x ≠ 0}) :
      (ContinuousLinearMap.id ℂ E).rayleighQuotient x = 1 := by
    have hn : ‖(x : E)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr x.property)
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.id_apply,
      inner_self_eq_norm_sq_to_K]
    norm_cast
    exact div_self hn
  simp [leastRayleigh, hpoint]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail
namespace OAI

/-! Exact exponential moments and elementary upper tails for the finite
independent Boolean laws used by the two prime-degree deletions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoordinateProjection
namespace OAI

/-! The orthogonal projection deleting the high-degree vertices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V : Type*} [Fintype V] [DecidableEq V]


lemma coordinateProjection_apply (keep : V → Prop) (v : EuclideanSpace ℂ V) (i : V) :
    coordinateProjection keep v i = if keep i then v i else 0 := by
  change (∑ j, Matrix.diagonal (fun i => if keep i then (1 : ℂ) else 0) i j * v j) = _
  simp [Matrix.diagonal_apply]

lemma coordinateProjection_selfAdjoint (keep : V → Prop) :
    IsSelfAdjoint (coordinateProjection keep) := by
  apply matrixOperator_selfAdjoint
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hi : keep i <;> simp [hi]
  · simp [hij, Ne.symm hij]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
namespace OAI

/-! Concrete centered integer edges and the padding-density cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset












lemma retainedPaddingAtom_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) (hL : 0 ≤ L) (hu : 0 ≤ u q) :
    0 ≤ retainedPaddingAtom Q u eligible g L K extra n q := by
  unfold retainedPaddingAtom
  split_ifs
  · exact div_nonneg (mul_nonneg hL hu) (sq_nonneg _)
  · exact le_rfl

lemma retainedPaddingAtom_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (hL : 0 < L) (hK : 0 ≤ K) :
    ∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q ≤ K := by
  classical
  by_cases hk : integerEdgeKeep Q u eligible g L K extra n
  · have heq : (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q) =
        L * paddingDensity Q u eligible g n := by
      simp only [retainedPaddingAtom, paddingDensity]
      rw [← mul_div_assoc, mul_sum, sum_div]
      apply sum_congr rfl
      intro q _
      by_cases hq : eligible q ∧ (q : ℤ) ∣ n
      · simp [hq.1, hq.2, hk]
      · simp only [show ¬(eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n) from
          fun hh => hq ⟨hh.1, hh.2.1⟩, hq, ite_false, mul_zero, zero_div]
    rw [heq]
    calc
      _ ≤ L * (K / L) := mul_le_mul_of_nonneg_left hk.1 hL.le
      _ = K := by field_simp
  · simpa [retainedPaddingAtom, hk] using hK



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerLiouville
namespace OAI

/-! The real Liouville test function on ambient integer vertices and
the exact cancellation of the square-root weights on each directed edge. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma liouville_norm_le_one (n : ℕ) : ‖liouville n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [liouville]
  · exact liouville_oneBounded n (Nat.pos_of_ne_zero hn)

lemma integerLiouville_norm_le_one (n : ℤ) : ‖integerLiouville n‖ ≤ 1 :=
  liouville_norm_le_one _


lemma star_integerLiouville (n : ℤ) : star (integerLiouville n) = integerLiouville n := by
  simp [integerLiouville, liouville]

lemma directedEdge_liouville_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ)
    (hg : ∀ z, g z ≠ 0) :
    star ((g n : ℂ) * integerLiouville n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q n m : ℂ) *
        ((g m : ℂ) * integerLiouville m) =
      if q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra m then
          (L * u q * center n : ℝ) * integerLiouville n * integerLiouville m else 0 := by
  unfold directedIntegerEdge
  split_ifs with he
  · simp only [star_mul, Complex.star_def, Complex.conj_ofReal, star_integerLiouville,
      Complex.ofReal_div, Complex.ofReal_mul]
    have hn : (g n : ℂ) ≠ 0 := by exact_mod_cast hg n
    have hm : (g m : ℂ) ≠ 0 := by exact_mod_cast hg m
    field_simp
  · simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights
namespace OAI

/-! Tuple weights in integer and product residue environments. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [Fintype α] [DecidableEq α]
  {P : α → Type*} [∀ i, Fintype (P i)]








omit [DecidableEq α] [∀ i, Fintype (P i)] in
/-- With distinct selected primes, the integer family center is exactly the
paper's product over prime divisors of the numerical tuple. -/
lemma familyCenter_zero_eq_centeredTuple (value : (i : α) → P i → ℕ)
    (hprime : ∀ i p, (value i p).Prime) (x : (i : α) → P i)
    (hinj : Function.Injective (fun i => value i (x i))) (n : ℤ) :
    familyCenter value (fun _ _ => 0) x n = centeredTuple (familyTuple value x).primeFactors n := by
  classical
  rw [familyTuple_primeFactors value hprime x hinj, centeredTuple, prod_image]
  · simp only [familyCenter, zero_add]
  · exact fun i _ j _ hij => hinj hij

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionEdgeGate
namespace OAI

/-! The progression restriction is symmetric in the two endpoints and
is fixed while the block origin moves through one residue class. -/

namespace TwoPointCorrelations


lemma progressionEdgeGate_symmetric (h l b d : ℕ) (n m : ℤ) :
    progressionEdgeGate h l b d n m ↔ progressionEdgeGate h l b d m n := by
  simp only [progressionEdgeGate, or_comm]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockTestNormalization
namespace OAI

/-! Separate the retained block test's main term from its exceptional
fraction before applying the boundary-error estimate. -/

namespace TwoPointCorrelations

lemma block_test_normalization (L K T G R S M l δ : ℝ)
    (hL : L ≠ 0) (hM : M ≠ 0) :
    l * ((3 * R) * (l * (2 * M * S)) + (M * (2 * K * T) * G) * δ) /
        (2 * L * M) =
      3 * l ^ 2 * S * R / L + l * (K / L * G * T) * δ := by
  field_simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestCodeAsymptotics
namespace OAI

/-! Absorbing the sublinear endpoint and exceptional-position costs. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_sublinear_log_cost (d C : ℝ) (hd : d < 1) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ d * Real.log L ≤ L := by
  by_cases hzero : C = 0
  · filter_upwards [eventually_ge_atTop 0] with L hL
    simpa only [hzero, zero_mul] using hL
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have hb := (isLittleO_log_rpow_atTop (show 0 < 1 - d by linarith)).bound
    (show 0 < 1 / C by positivity)
  filter_upwards [eventually_ge_atTop 1, hb] with L hL hb
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hb
  calc
    C * L ^ d * Real.log L ≤ C * L ^ d * ((1 / C) * L ^ (1 - d)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C * (1 / C)) * (L ^ d * L ^ (1 - d)) := by ring
    _ = L := by
      rw [mul_one_div_cancel hzero, one_mul, ← Real.rpow_add hLp,
        show d + (1 - d) = 1 by ring, Real.rpow_one]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma paddingBin_eq_iff (η c x : ℝ) (j : ℤ) (hη : 0 < η) :
    paddingBin η c x = j ↔ (j : ℝ) * η ≤ x + c ∧ x + c < ((j : ℝ) + 1) * η := by
  rw [paddingBin, Int.floor_eq_iff, le_div_iff₀ hη, div_lt_iff₀ hη]

lemma paddingAvailablePrimes_integer (Q : Finset ℕ) (n : ℤ) :
    paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) =
      Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    have hpQ := paddingAvailablePrimes_subset Q _ hp
    exact mem_filter.mpr ⟨hpQ, by
      simpa using (mem_paddingAvailablePrimes Q _ ⟨p, hpQ⟩).mp hp⟩
  · intro hp
    exact (mem_paddingAvailablePrimes Q _ ⟨p, (mem_filter.mp hp).1⟩).mpr
      (by simpa using (mem_filter.mp hp).2)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedLiouvilleEdges
namespace OAI

/-! A literal retained edge coefficient after testing. The vertex masks
are ambient predicates, so the coefficient is independent of the block. -/

namespace TwoPointCorrelations

open scoped _root_.Classical



lemma retainedLiouvilleScalar_star (g : ℤ → ℝ) (keep : ℤ → Prop) (n : ℤ) :
    star (retainedLiouvilleScalar g keep n) = retainedLiouvilleScalar g keep n := by
  unfold retainedLiouvilleScalar
  split_ifs <;> simp [star_mul, star_integerLiouville, mul_comm]

theorem retainedLiouvilleEdge_test (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hg : ∀ z, g z ≠ 0) :
    star (retainedLiouvilleScalar g keep n) *
        (directedIntegerEdge Q u eligible g center L K extra h d q n m : ℂ) *
        retainedLiouvilleScalar g keep m =
      (L : ℂ) * retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m := by
  by_cases hn : keep n
  · by_cases hm : keep m
    · simp only [retainedLiouvilleScalar, if_pos hn, if_pos hm]
      rw [directedEdge_liouville_test Q u eligible g center L K extra h d q n m hg]
      simp only [retainedLiouvilleEdge, hn, hm, true_and]
      split_ifs <;> simp only [Complex.ofReal_mul, mul_zero]
      ring
    · simp [retainedLiouvilleScalar, retainedLiouvilleEdge, hm]
  · simp [retainedLiouvilleScalar, retainedLiouvilleEdge, hn]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockEndpointSum
namespace OAI

/-! Summing a directed edge over the finite block keeps precisely those
starting positions whose terminal endpoint remains in the block. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma block_endpoint_sum (M r : ℕ) (i : Fin M) (c : ℤ) (F : ℤ → ℂ) :
    (∑ j : Fin M, if (j.val : ℤ) + c = (i.val : ℤ) + c + r then F ((j.val : ℤ) + c) else 0) =
      if i.val + r < M then F ((i.val : ℤ) + c + r) else 0 := by
  by_cases hi : i.val + r < M
  · let j₀ : Fin M := ⟨i.val + r, hi⟩
    have he (j : Fin M) : (j.val : ℤ) + c = (i.val : ℤ) + c + r ↔ j = j₀ := by
      constructor
      · intro hj
        apply Fin.ext
        dsimp only [j₀]
        omega
      · rintro rfl
        dsimp only [j₀]
        push_cast
        ring
    simp only [he, sum_ite_eq', mem_univ, ite_true, hi]
    congr 1
    dsimp [j₀]
    ring
  · have he (j : Fin M) : (j.val : ℤ) + c ≠ (i.val : ℤ) + c + r := by
      intro hj
      have hjM := j.isLt
      omega
    simp [he, hi]

lemma block_supported_edge_sum (M r : ℕ) (c : ℤ) (F : ℤ → ℤ → ℂ)
    (hsupport : ∀ n m : ℤ, m ≠ n + r → F n m = 0) (i : Fin M) :
    (∑ j : Fin M, F ((i.val : ℤ) + c) ((j.val : ℤ) + c)) =
      if i.val + r < M then F ((i.val : ℤ) + c) ((i.val : ℤ) + c + r) else 0 := by
  have he (j : Fin M) : F ((i.val : ℤ) + c) ((j.val : ℤ) + c) =
      if (j.val : ℤ) + c = (i.val : ℤ) + c + r then
        F ((i.val : ℤ) + c) ((j.val : ℤ) + c) else 0 := by
    split_ifs with h
    · rfl
    · exact hsupport _ _ h
  calc
    _ = ∑ j : Fin M, if (j.val : ℤ) + c = (i.val : ℤ) + c + r then
        F ((i.val : ℤ) + c) ((j.val : ℤ) + c) else 0 := sum_congr rfl (fun j _ => he j)
    _ = _ := block_endpoint_sum M r i c (F ((i.val : ℤ) + c))

lemma retainedLiouvilleEdge_support (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hm : m ≠ n + (h * q * d : ℕ)) :
    retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m = 0 := by
  unfold retainedLiouvilleEdge
  split_ifs with he
  · exact (hm he.2.2.2.1).elim
  · rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockEdgeForm
namespace OAI

/-! The finite directed matrix form is the overlapping edge-block sum
used in the prefix comparison, with no residual multiplicity assumption. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem directed_block_form_eq {E : Type*} [Fintype E] (r : E → ℕ)
    (F : E → ℤ → ℤ → ℂ)
    (hsupport : ∀ (e : E) (n m : ℤ), m ≠ n + r e → F e n m = 0) (M t : ℕ) :
    (∑ e : E, ∑ i : Fin M, ∑ j : Fin M,
      F e ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ))) =
      edgeBlockSum univ r (fun e n => F e n ((n : ℤ) + r e)) M t := by
  let g (i : ℕ) := ∑ e : E, if i + r e < M then
    F e ((i : ℤ) + (t + 2 : ℕ)) ((i : ℤ) + (t + 2 : ℕ) + r e) else 0
  calc
    _ = ∑ i : Fin M, ∑ e : E, ∑ j : Fin M,
        F e ((i.val : ℤ) + (t + 2 : ℕ)) ((j.val : ℤ) + (t + 2 : ℕ)) := sum_comm
    _ = ∑ i : Fin M, g i.val := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro e _
      exact block_supported_edge_sum M (r e) (t + 2 : ℕ) (F e) (hsupport e) i
    _ = ∑ i ∈ range M, g i := Fin.sum_univ_eq_sum_range g M
    _ = _ := by
      unfold edgeBlockSum g
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro e _
      have he : i + r e < M ↔ i + 1 + r e ≤ M := by omega
      simp only [he, Nat.cast_add, Nat.cast_ofNat]
      simp only [add_assoc, add_left_comm, add_comm]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockFormPrefixBound
namespace OAI

/-! Normalize an averaged quadratic form and transfer its bound to the
retained prefix, with explicit displacement and boundary errors. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma edgeBlockSum_norm_average_le {E : Type*} [Fintype E]
    (r : E → ℕ) (c : E → ℕ → ℂ) (M N : ℕ) :
    ‖((∑ t ∈ range N, edgeBlockSum univ r c M t) / (M : ℂ)) / (N : ℂ)‖ ≤
      uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) / M := by
  simp only [norm_div, Complex.norm_natCast]
  calc
    _ ≤ ((∑ t ∈ range N, ‖edgeBlockSum univ r c M t‖) / (M : ℝ)) / N := by
      gcongr
      exact norm_sum_le _ _
    _ = _ := by
      rw [uniformAverage, Fintype.card_fin, Fin.sum_univ_eq_sum_range
        (fun t => ‖edgeBlockSum univ r c M t‖) N]
      ring

theorem block_form_prefix_bound {E : Type*} [Fintype E]
    (r : E → ℕ) (c : E → ℕ → ℂ) (A : ℕ → ℂ)
    (M R N : ℕ) (hM : 0 < M) (hN : 0 < N) (L B D : ℝ)
    (hL : 0 < L) (hD : 0 ≤ D) (hr : ∀ e, r e ≤ R)
    (hrow : ∀ n : ℕ, 0 < n → (∑ e : E, ‖c e n‖) ≤ D)
    (hA : ∀ t, A t = (2 * (L : ℂ)) * edgeBlockSum univ r c M t)
    (havg : uniformAverage (fun t : Fin N => ‖A t.val‖) ≤ B) :
    ‖positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ)‖ ≤
      B / (2 * L * M) + (R : ℝ) / M * D + 2 * (M : ℝ) / N * D := by
  have he : uniformAverage (fun t : Fin N => ‖A t.val‖) =
      (2 * L) * uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) := by
    simp only [hA, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    unfold uniformAverage
    rw [← mul_sum]
    ring
  have hb : uniformAverage (fun t : Fin N => ‖edgeBlockSum univ r c M t.val‖) ≤ B / (2 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * L)).mpr
    rw [mul_comm, ← he]
    exact havg
  have hprefix := edgeBlockSum_prefix_error univ r c M R N hM hN D hD
    (fun e _ => hr e) hrow
  let Z := ((∑ t ∈ range N, edgeBlockSum univ r c M t) / (M : ℂ)) / (N : ℂ)
  have hZ : ‖Z‖ ≤ B / (2 * L * M) := by
    apply (edgeBlockSum_norm_average_le r c M N).trans
    calc
      _ ≤ (B / (2 * L)) / M := div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
      _ = _ := by ring
  have ht := norm_sub_le Z
    (Z - positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ))
  have hid : Z - (Z - positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ)) =
      positivePrefix (fun n => ∑ e : E, c e n) N / (N : ℂ) := by ring
  rw [hid] at ht
  dsimp only [Z] at ht hZ
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage
namespace OAI

/-! The literal finite bin family covers every padding divisor surviving
the degree and logarithmic-size cuts. This includes the last bin whose
left endpoint, rather than its right endpoint, is at most `100 L`. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma mem_paddingBinIndices_iff (L η : ℝ) (j : ℤ) (hη : 0 < η) :
    j ∈ paddingBinIndices L η ↔ 0 ≤ j ∧ (j : ℝ) * η ≤ 100 * L := by
  rw [paddingBinIndices, mem_Icc, Int.le_floor, le_div_iff₀ hη]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily
namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical







lemma actualProhibitedPrimeFamily_pairs (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ) :
    (d, q) ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs ↔
      d ∈ primeTupleDivisors (centeredPrimeBands E A W J) ∧
        q ∈ retainedPrimeDivisors (paddingPrimeSupply E L) ∧
          q.primeFactors.card ≤ M ∧ eligible d q := mem_primeFamilyPairs







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale
namespace OAI

/-! Harmonic masses and integer endpoints for the literal prime family.
These derive the trace theorem's prime-pool hypotheses from the single
fixed-modulus published input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma primeSupplyCount_mul_bound (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤
      ((1 / 200 : ℝ) * Real.log L) / (6 * W) := Nat.floor_le (by positivity)
  exact (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePairCatalog
namespace OAI

/-! The tuple/padding pair catalog injects into its integer product:
the two factors have disjoint prime supports. Thus the numerical bin
endpoint bounds the whole catalog, without an extra tuple factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma paddingPairEligible_product_upper {L η : ℝ} {d q : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (he : PaddingPairEligible L η d q) :
    d * q ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  by_cases hz : d * q = 0
  · simp [hz]
  let j := paddingBin η 0 (Real.log (d * q : ℕ))
  have hj := (mem_paddingBinIndices_iff L η j hη).mp he.2
  have hx := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp rfl
  simp only [add_zero] at hx
  have hu : Real.log (d * q : ℕ) ≤ 100 * L + 1 := by
    nlinarith [hj.2, hx.2]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hp : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hu


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale
namespace OAI

/-! At a fixed W the retained row majorant grows polynomially in L;
it can therefore be absorbed into a small exponential boundary budget. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma primeSupplyCount_le_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg hL]

lemma retained_row_exponential_bound (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    Real.exp (4 * primeSupplyCount W L) / L *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L ≤
      Real.exp ((4 + 400 * Real.log 5 + Real.log (8 * W)) * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hJ := primeSupplyCount_le_log W L hW hL
  have h8 : 1 ≤ 8 * W := by linarith
  have he : Real.exp (4 * primeSupplyCount W L) ≤ Real.exp (4 * Real.log L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : (8 * W) ^ primeSupplyCount W L ≤ Real.exp (Real.log (8 * W) * Real.log L) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hJ (Real.log_nonneg h8))
  have h5 : (5 : ℝ) ^ (400 * Real.log L) = Real.exp ((400 * Real.log 5) * Real.log L) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ Real.exp (4 * primeSupplyCount W L) *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L := by
      gcongr
      exact div_le_self (Real.exp_pos _).le hL
    _ ≤ Real.exp (4 * Real.log L) *
        Real.exp ((400 * Real.log 5) * Real.log L) *
        Real.exp (Real.log (8 * W) * Real.log L) := by
      rw [h5]
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

lemma eventually_retained_row_scale (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (4 * primeSupplyCount W L) / L *
        (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ primeSupplyCount W L ≤
          Real.exp (L / 4) := by
  let C := 4 + 400 * Real.log 5 + Real.log (8 * W)
  have hC : 0 ≤ C := by
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have h8 : 0 ≤ Real.log (8 * W) := Real.log_nonneg (by linarith)
    dsimp [C]
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_sublinear_log_cost 0 (4 * C) (by norm_num) (by positivity)] with L hL hb
  simp only [Real.rpow_zero, mul_one] at hb
  exact (retained_row_exponential_bound W L hW hL).trans
    (Real.exp_le_exp.mpr (by dsimp only [C] at hb ⊢; linarith))

lemma eventually_const_le_exp_quarter (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, C ≤ Real.exp (L / 4) := by
  filter_upwards [eventually_ge_atTop (4 * |C|)] with L hL
  have ha := le_abs_self C
  have he := Real.add_one_le_exp (L / 4)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedBoundaryScale
namespace OAI

/-! The explicit block-end, prefix-end, and exceptional-block errors
are exponentially small at the actual block length. -/

namespace TwoPointCorrelations

lemma retained_boundary_error_bound (L D h l M N : ℝ)
    (hL : 8 ≤ L) (hD0 : 0 ≤ D) (_hh0 : 0 ≤ h) (_hl0 : 0 ≤ l)
    (hD : D ≤ Real.exp (L / 4)) (hh : h ≤ Real.exp (L / 4))
    (hl : l ≤ Real.exp (L / 4))
    (hMlo : Real.exp (103 * L) ≤ M) (hMhi : M ≤ 2 * Real.exp (103 * L))
    (hN : Real.exp (106 * L) ≤ N) :
    l * D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) +
        (h * Real.exp (100 * L + 1)) / M * D + 2 * M / N * D ≤
      3 * Real.exp (-L) := by
  have hMp : 0 < M := (Real.exp_pos _).trans_le hMlo
  have hNp : 0 < N := (Real.exp_pos _).trans_le hN
  have hfloor := Nat.lt_floor_add_one L
  have htail : Real.exp (-(2 * ⌊L⌋₊ : ℕ)) ≤ Real.exp (-(3 * L / 2)) := by
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hfirst : l * D * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp (L / 4) * Real.exp (L / 4) * Real.exp (-(3 * L / 2)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsecond : (h * Real.exp (100 * L + 1)) / M * D ≤ Real.exp (-L) := by
    calc
      _ ≤ (Real.exp (L / 4) * Real.exp (100 * L + 1)) /
          Real.exp (103 * L) * Real.exp (L / 4) := by gcongr
      _ = Real.exp (1 - 5 * L / 2) := by
        rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp (L / 2) := by
    have hx := Real.add_one_le_exp (L / 2)
    linarith
  have hthird : 2 * M / N * D ≤ Real.exp (-L) := by
    calc
      _ ≤ 2 * (2 * Real.exp (103 * L)) / Real.exp (106 * L) * Real.exp (L / 4) := by gcongr
      _ = 4 * Real.exp (-11 * L / 4) := by
        rw [show 2 * (2 * Real.exp (103 * L)) = 4 * Real.exp (103 * L) by ring,
          mul_div_assoc, ← Real.exp_sub, mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      _ ≤ Real.exp (L / 2) * Real.exp (-11 * L / 4) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
      _ = Real.exp (-9 * L / 4) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity

lemma actualPaddingWeight_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingWeight Q n :=
  one_le_pow₀ (by norm_num)

lemma actualPaddingVertex_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingVertex Q n := by
  simpa only [actualPaddingVertex, Real.sqrt_one] using
    Real.sqrt_le_sqrt (actualPaddingWeight_one_le Q n)

lemma actualPaddingVertex_pos (Q : Finset ℕ) (n : ℤ) : 0 < actualPaddingVertex Q n :=
  zero_lt_one.trans_le (actualPaddingVertex_one_le Q n)

lemma actualPaddingVertex_ne_zero (Q : Finset ℕ) (n : ℤ) : actualPaddingVertex Q n ≠ 0 :=
  (actualPaddingVertex_pos Q n).ne'

lemma actualPaddingVertex_sq (Q : Finset ℕ) (n : ℤ) :
    actualPaddingVertex Q n ^ 2 = actualPaddingWeight Q n :=
  Real.sq_sqrt (zero_le_one.trans (actualPaddingWeight_one_le Q n))






lemma actualPaddingDegree_eq_available (Q : Finset ℕ) (n : ℤ) :
    actualPaddingDegree Q n =
      (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card := by
  rw [paddingAvailablePrimes_integer]
  rfl










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
namespace OAI

/-! The prime-degree deletion under the literal full residue law.  The
positive tuple majorant has mean `2^omega(d)/d`, and its tilted degree
tail is exponentially small in `W * omega(d)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma abs_centeredTuple_le_positivePrimeWeight (S : Finset ℕ) (n : ℤ) :
    |centeredTuple S n| ≤ positivePrimeWeight S n := by
  rw [centeredTuple, abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro p _
  have hi : 0 ≤ (if (p : ℤ) ∣ n then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hp : 0 ≤ (p : ℝ)⁻¹ := by positivity
  simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hi, abs_of_nonneg hp, one_div] using
    abs_sub_le (if (p : ℤ) ∣ n then (1 : ℝ) else 0) 0 (p : ℝ)⁻¹




lemma actualPrimeDegree_eq_count (P : Finset ℕ) (n : ℤ) :
    (actualPaddingDegree P n : ℝ) =
      booleanCount (fun p : P => decide ((p.val : ℤ) ∣ n)) := by
  rw [actualPaddingDegree_eq_available, paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualCenterDegree
namespace OAI

/-! Specialize the arithmetic-geometric mean bound to the literal tuple
centers and the degree projection of the integer graph. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma actualPaddingDegree_biUnion {J : ℕ} (P : Fin J → Finset ℕ)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    actualPaddingDegree (univ.biUnion P) n = ∑ j, actualPaddingDegree (P j) n := by
  have he : (univ.biUnion P).filter (fun p : ℕ => (p : ℤ) ∣ n) =
      univ.biUnion (fun j => (P j).filter (fun p : ℕ => (p : ℤ) ∣ n)) := by
    ext p
    simp only [mem_filter, mem_biUnion, mem_univ, true_and]
    aesop
  unfold actualPaddingDegree
  rw [he, card_biUnion]
  intro j _ l _ hjl
  exact (hdisjoint j l (Ne.symm hjl)).mono (filter_subset _ _) (filter_subset _ _)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveRowMajorant
namespace OAI

/-! The literal sum of positive tuple weights is the row majorant
whose second moment was estimated under the product law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrimeWeight_tuple {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (d : (j : Fin J) → P j) (n : ℤ) :
    positivePrimeWeight (∏ j, (d j).val).primeFactors n =
      ∏ j, ((if ((d j).val : ℤ) ∣ n then 1 else 0) + 1 / ((d j).val : ℝ)) := by
  have hinj := selectedPrimeValues_injective d hdisjoint
  have hf : (∏ j, (d j).val).primeFactors = univ.image (fun j => (d j).val) :=
    familyTuple_primeFactors (fun j (p : P j) => p.val)
      (fun j p => hprime j _ p.property) d hinj
  rw [positivePrimeWeight, hf]
  rw [prod_image]
  intro i _ j _ hij
  exact hinj hij

lemma positivePrimeWeight_tuple_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) =
      ∏ j, ((actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) := by
  rw [primeTupleDivisors, sum_image]
  · simp_rw [positivePrimeWeight_tuple P hprime hdisjoint]
    have he := (Fintype.prod_sum (fun j (p : P j) =>
      (if (p.val : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p.val : ℝ))).symm
    apply he.trans
    apply prod_congr rfl
    intro j _
    rw [sum_add_distrib, actualPrimeDegree_eq_count]
    simp only [booleanCount, primeHarmonicMass, decide_eq_true_eq, one_div]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma positivePrimeWeight_tuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeWeight d.primeFactors n) ≤ (8 * W) ^ J := by
  rw [positivePrimeWeight_tuple_sum P hprime hdisjoint]
  have hd : (∑ j, (actualPaddingDegree (P j) n : ℝ)) ≤ 6 * W * J := by
    rw [← Nat.cast_sum, ← actualPaddingDegree_biUnion P hdisjoint]
    exact hdegree
  have hb := nonneg_product_le_power_card
    (fun j => (actualPaddingDegree (P j) n : ℝ) + primeHarmonicMass (P j)) (8 * W)
    (fun j => add_nonneg (Nat.cast_nonneg _) (by unfold primeHarmonicMass; positivity))
    (sum_degree_budget (fun j => (actualPaddingDegree (P j) n : ℝ))
      (fun j => primeHarmonicMass (P j)) W hV (by simpa only [Fintype.card_fin] using hd))
  simpa only [Fintype.card_fin] using hb

/-- The deterministic first-power bound needed when testing the graph
against bounded vectors. The degree projection is the only site restriction. -/
lemma abs_centeredTuple_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d ∈ primeTupleDivisors P, |centeredTuple d.primeFactors n|) ≤ (8 * W) ^ J := by
  exact (sum_le_sum (fun d _ => abs_centeredTuple_le_positivePrimeWeight d.primeFactors n)).trans
    (positivePrimeWeight_tuple_sum_le P hprime hdisjoint n W hV hdegree)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GraphTesting
namespace OAI

/-! The deterministic quadratic-form estimate on every block, including
exceptional blocks. The projected support pays only a power of the mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma sum_familyCenter_abs_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d : (j : Fin J) → P j,
      |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d n|) ≤ (8 * W) ^ J := by
  have hb := abs_centeredTuple_sum_le P hprime hdisjoint n W hV hdegree
  rw [primeTupleDivisors, sum_image] at hb
  · simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
      _ (selectedPrimeValues_injective _ hdisjoint), familyTuple] using hb
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SymmetricEdgeTesting
namespace OAI

/-! A real symmetric edge test counts each retained directed edge twice. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem symmetric_kernel_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → ℝ) (v : EuclideanSpace ℂ V) (hv : ∀ i, star (v i) = v i) :
    inner ℂ v (matrixOperator (fun i j => ((a i j + a j i : ℝ) : ℂ)) v) =
      2 * ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
  change (∑ i, (∑ j, ((a i j + a j i : ℝ) : ℂ) * v j) * star (v i)) = _
  have hf : (∑ i, ∑ j, (a i j : ℂ) * v j * v i) =
      ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hr : (∑ i, ∑ j, (a j i : ℂ) * v j * v i) =
      ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
    rw [sum_comm]
  calc
    _ = (∑ i, ∑ j, (a i j : ℂ) * v j * v i) +
        (∑ i, ∑ j, (a j i : ℂ) * v j * v i) := by
      simp only [hv, Complex.ofReal_add, add_mul, sum_add_distrib, sum_mul]
    _ = _ := by rw [hf, hr]; ring

lemma maskedIntegerEdgeMatrix_directed {V : Type*} [Fintype V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i) (i j : V) :
    maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j =
      ((if gate i j then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site i) (site j) else 0) +
       (if gate j i then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site j) (site i) else 0) : ℝ) := by
  simp only [maskedIntegerEdgeMatrix, maskMatrix, integerEdgeMatrix,
    hgate i j, sum_add_distrib]
  split_ifs <;> simp

theorem maskedIntegerEdgeMatrix_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, star (v i) = v i) :
    inner ℂ v (matrixOperator
      (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate) v) =
      2 * ∑ i, ∑ j,
        ((if gate i j then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
          (site i) (site j) else 0) : ℝ) * v i * v j := by
  have hm : maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate =
      fun i j => (((if gate i j then ∑ q ∈ Q,
          directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) else 0) +
        (if gate j i then ∑ q ∈ Q,
          directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i) else 0) : ℝ) : ℂ) := by
    funext i j
    exact maskedIntegerEdgeMatrix_directed site Q u eligible g center L K extra h d gate hgate i j
  rw [hm]
  exact symmetric_kernel_quadratic _ v hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LiouvilleQuadraticIdentity
namespace OAI

/-! Testing the actual weighted matrix leaves twice L times the ambient
retained directed-edge correlation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem maskedLiouville_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (hg : ∀ z, g z ≠ 0) :
    let v := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
    inner ℂ v (matrixOperator
      (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate) v) =
      (2 * (L : ℂ)) * ∑ i, ∑ j, if gate i j then
        ∑ q ∈ Q, retainedLiouvilleEdge Q u eligible g center L K extra keep h d q (site i) (site j)
      else 0 := by
  dsimp only
  let v : EuclideanSpace ℂ V := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
  have hv (i : V) : star (v i) = v i := retainedLiouvilleScalar_star g keep (site i)
  have hterm (i j : V) :
      ((if gate i j then ∑ q ∈ Q,
        directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)
        else 0) : ℝ) * v i * v j =
        (L : ℂ) * (if gate i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u eligible g center L K extra keep h d q (site i) (site j)
          else 0) := by
    by_cases hij : gate i j
    · simp only [if_pos hij, Complex.ofReal_sum, sum_mul, mul_sum]
      apply sum_congr rfl
      intro q _
      have ht := retainedLiouvilleEdge_test Q u eligible g center L K extra keep h d q
        (site i) (site j) hg
      rw [retainedLiouvilleScalar_star] at ht
      calc
        _ = retainedLiouvilleScalar g keep (site i) *
            (directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) : ℂ) *
            retainedLiouvilleScalar g keep (site j) := by dsimp [v]; ring
        _ = _ := ht
    · simp [hij]
  rw [maskedIntegerEdgeMatrix_quadratic site Q u eligible g center L K extra h d gate hgate v hv]
  simp_rw [hterm]
  simp only [← mul_sum, mul_assoc]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeLiouvilleQuadratic
namespace OAI

/-! The full tuple graph tests to the literal sum of retained directed
Liouville edges, with the original numerical tuple and padding divisor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem prime_graph_liouville_quadratic {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hg : ∀ z, g z ≠ 0) :
    let v := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
    inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate d) v) =
      (2 * (L : ℂ)) * ∑ d : (j : Fin J) → P j, ∑ i, ∑ j,
        if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) g
            (centeredTuple (∏ k, (d k).val).primeFactors) L K
            (extra (∏ k, (d k).val)) keep h (∏ k, (d k).val) q (site i) (site j)
        else 0 := by
  dsimp only
  let v : EuclideanSpace ℂ V := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
  have hd (d : (j : Fin J) → P j) :
      inner ℂ v (primeFamilyGraphOperator (fun j (p : P j) => p.val)
        (fun _ _ => 0) site Q u eligible g L K extra h gate d v) =
        (2 * (L : ℂ)) * ∑ i, ∑ j,
          if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
            retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) g
              (centeredTuple (∏ k, (d k).val).primeFactors) L K
              (extra (∏ k, (d k).val)) keep h (∏ k, (d k).val) q (site i) (site j)
          else 0 := by
    have hc : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d =
        centeredTuple (∏ j, (d j).val).primeFactors := by
      funext n
      exact familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
        d (selectedPrimeValues_injective d hdisjoint) n
    unfold primeFamilyGraphOperator
    rw [hc]
    exact maskedLiouville_quadratic site Q u _ g _ L K _ keep h _ _ (hgate _) hg
  change inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
    (fun _ _ => 0) site Q u eligible g L K extra h gate d) v) = _
  rw [_root_.sum_apply, inner_sum]
  simp_rw [hd]
  rw [mul_sum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting
namespace OAI

/-! The deterministic bound for the manuscript's actual test vectors,
with both degree cutoffs and the square-root padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma paddingVertex_cut_bound (Q : Finset ℕ) (L : ℝ) (n : ℤ)
    (hn : actualPaddingDegreeCut Q L n) :
    actualPaddingVertex Q n ^ 2 ≤ (5 : ℝ) ^ (400 * Real.log L) := by
  rw [actualPaddingVertex_sq, actualPaddingWeight, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProjectedLiouvilleVector
namespace OAI

/-! The actual degree-projected Liouville test is an ambient masked scalar. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma projectedLiouvilleVector_eq {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (keep : ℤ → Prop) :
    coordinateProjection (fun i => keep (site i))
        (paddingTestVector Q L site integerLiouville) =
      WithLp.toLp 2 (fun i => retainedLiouvilleScalar (actualPaddingVertex Q)
        (fun n => keep n ∧ actualPaddingDegreeCut Q L n) (site i)) := by
  ext i
  by_cases hp : keep (site i) <;> by_cases hq : actualPaddingDegreeCut Q L (site i) <;>
    simp [coordinateProjection_apply, paddingTestVector, retainedLiouvilleScalar, hp, hq]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProjectedPrimeLiouville
namespace OAI

/-! The exact retained-edge identity for the projected vector used by
actual block testing, including both degree cutoffs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem projected_prime_liouville_quadratic {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
    let proj := coordinateProjection (fun i => keep (site i))
    let v := paddingTestVector Qp L site integerLiouville
    inner ℂ v ((proj * (∑ d, B d) * proj) v) =
      (2 * (L : ℂ)) * ∑ d : (j : Fin J) → P j, ∑ i, ∑ j,
        if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) (actualPaddingVertex Qp)
            (centeredTuple (∏ k, (d k).val).primeFactors) L K (extra (∏ k, (d k).val))
            (fun n => keep n ∧ actualPaddingDegreeCut Qp L n)
            h (∏ k, (d k).val) q (site i) (site j)
        else 0 := by
  dsimp only
  let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection (fun i => keep (site i))
  let v := paddingTestVector Qp L site integerLiouville
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    site Q u eligible (actualPaddingVertex Qp) L K extra h gate
  have hq := prime_graph_liouville_quadratic P hprime hdisjoint site Q u eligible
    (actualPaddingVertex Qp) L K extra (fun n => keep n ∧ actualPaddingDegreeCut Qp L n)
    h gate hgate (actualPaddingVertex_ne_zero Qp)
  dsimp only at hq
  rw [← projectedLiouvilleVector_eq Qp L site keep] at hq
  have he := (coordinateProjection_selfAdjoint (fun i => keep (site i))).isSymmetric
    v ((∑ d, B d) (proj v))
  exact he.symm.trans hq

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedBlockIdentity
namespace OAI

/-! The actual projected block form is the sum of its ambient directed
edges.  The identity includes every vertex deletion, so overlapping blocks
can be compared directly with a prefix of the retained correlation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sum_gated_edges {D V : Type*} [Fintype D] [Fintype V]
    (Q : Finset ℕ) (gate : D → V → V → Prop) (F : D → ℕ → V → V → ℂ) :
    (∑ d : D, ∑ i : V, ∑ j : V, if gate d i j then ∑ q ∈ Q, F d q i j else 0) =
      ∑ e : D × Q, ∑ i : V, ∑ j : V, if gate e.1 i j then F e.1 e.2.val i j else 0 := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro d _
  calc
    _ = ∑ i : V, ∑ j : V, ∑ q : Q, if gate d i j then F d q.val i j else 0 := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hg : gate d i j
      · simp only [hg, ite_true]
        exact (sum_coe_sort Q (fun q => F d q i j)).symm
      · simp only [hg, ite_false, sum_const_zero]
    _ = ∑ i : V, ∑ q : Q, ∑ j : V, if gate d i j then F d q.val i j else 0 := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := sum_comm


lemma retainedPrimeEdge_support {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (hm : m ≠ n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  unfold retainedPrimeEdge
  split_ifs
  · exact retainedLiouvilleEdge_support _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
  · rfl

theorem primeBlockCompression_retained_identity {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (c : ℤ) :
    let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + c) integerLiouville
    inner ℂ v (primeBlockCompression P M Q u eligible (actualPaddingVertex Qp)
      L K W extra h (fun d n m => gate d (n + c) (m + c)) keep c v) =
      (2 * (L : ℂ)) * ∑ e : ((j : Fin J) → P j) × Q, ∑ i : Fin M, ∑ j : Fin M,
        retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e
          ((i.val : ℤ) + c) ((j.val : ℤ) + c) := by
  dsimp only
  have hg : ∀ d (i j : Fin M),
      (gate d ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
        keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c)) ↔
      (gate d ((j.val : ℤ) + c) ((i.val : ℤ) + c) ∧
        keep ((j.val : ℤ) + c) ∧ keep ((i.val : ℤ) + c)) := by
    intro d i j
    rw [hgate]
    tauto
  have hi := projected_prime_liouville_quadratic P hprime hdisjoint
    (fun i : Fin M => (i.val : ℤ) + c) Q Qp u eligible L K W extra h
    (fun d i j => gate d ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
      keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c)) hg
  dsimp only at hi
  rw [primeBlockCompression]
  rw [hi]
  congr 1
  have hs := sum_gated_edges (D := (j : Fin J) → P j) (V := Fin M) Q
    (fun d i j => gate (∏ k, (d k).val) ((i.val : ℤ) + c) ((j.val : ℤ) + c) ∧
      keep ((i.val : ℤ) + c) ∧ keep ((j.val : ℤ) + c))
    (fun d q i j => retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val))
      (actualPaddingVertex Qp) (centeredTuple (∏ k, (d k).val).primeFactors) L K
      (extra (∏ k, (d k).val))
      (fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J ∧
        actualPaddingDegreeCut Qp L n) h (∏ k, (d k).val) q
      ((i.val : ℤ) + c) ((j.val : ℤ) + c))
  refine hs.trans ?_
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  unfold retainedPrimeEdge
  split_ifs <;> rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedEdgeRows
namespace OAI

/-! The one-orientation row majorant for the actual retained correlation.
The retained cutoffs supply the degree bound and the truncated padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma retainedLiouvilleEdge_norm_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hL : 0 < L) (hu : 0 ≤ u q) (hg : g n ≠ 0) :
    ‖retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m‖ ≤
      |center n| * retainedPaddingAtom Q u eligible g L K extra n q * ((g n) ^ 2 / L) := by
  unfold retainedLiouvilleEdge
  split_ifs with he
  · have hk : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1⟩
    rw [retainedPaddingAtom, if_pos hk]
    calc
      _ = |u q * center n| * ‖integerLiouville n‖ * ‖integerLiouville m‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |u q * center n| * 1 * 1 := by
        gcongr <;> exact integerLiouville_norm_le_one _
      _ = _ := by
        rw [abs_mul, abs_of_nonneg hu]
        field_simp
  · simpa only [norm_zero] using mul_nonneg
      (mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL.le hu))
      (div_nonneg (sq_nonneg _) hL.le)

theorem retainedPrimeEdge_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W) (n : ℤ) :
    (∑ e : ((j : Fin J) → P j) × Q,
      ‖retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))‖) ≤
      K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J := by
  let good := (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J ∧
    actualPaddingDegreeCut Qp L n
  by_cases hn : good
  · have hq (d : (j : Fin J) → P j) (q : Q) :
        ‖retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep (d, q) n
          (n + (h * q.val * ∏ j, (d j).val : ℕ))‖ ≤
        |centeredTuple (∏ j, (d j).val).primeFactors n| *
          retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
            L K (extra (∏ j, (d j).val)) n q.val *
          ((actualPaddingVertex Qp n) ^ 2 / L) := by
      unfold retainedPrimeEdge
      split_ifs
      · exact retainedLiouvilleEdge_norm_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL
          (hu q.val q.property) (actualPaddingVertex_ne_zero Qp n)
      · simpa only [norm_zero] using mul_nonneg
          (mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg _ _ _ _ _ _ _ _ _ hL.le
            (hu q.val q.property))) (div_nonneg (sq_nonneg _) hL.le)
    have hc : (∑ d : (j : Fin J) → P j,
        |centeredTuple (∏ j, (d j).val).primeFactors n|) ≤ (8 * W) ^ J := by
      have hc := sum_familyCenter_abs_le P hprime hdisjoint n W hV hn.1
      simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
        _ (selectedPrimeValues_injective _ hdisjoint), familyTuple] using hc
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ d : (j : Fin J) → P j,
          |centeredTuple (∏ j, (d j).val).primeFactors n| * K *
            ((actualPaddingVertex Qp n) ^ 2 / L) := by
        apply sum_le_sum
        intro d _
        calc
          _ ≤ ∑ q : Q, |centeredTuple (∏ j, (d j).val).primeFactors n| *
              retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
                L K (extra (∏ j, (d j).val)) n q.val *
              ((actualPaddingVertex Qp n) ^ 2 / L) := sum_le_sum (fun q _ => hq d q)
          _ = |centeredTuple (∏ j, (d j).val).primeFactors n| *
              (∑ q ∈ Q, retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
                L K (extra (∏ j, (d j).val)) n q) * ((actualPaddingVertex Qp n) ^ 2 / L) := by
            rw [← sum_mul, ← mul_sum, sum_coe_sort]
          _ ≤ _ := by
            gcongr
            exact retainedPaddingAtom_sum_le _ _ _ _ _ _ _ _ hL hK
      _ = K / L * (actualPaddingVertex Qp n) ^ 2 *
          (∑ d : (j : Fin J) → P j, |centeredTuple (∏ j, (d j).val).primeFactors n|) := by
        simp only [← sum_mul]
        ring
      _ ≤ _ := by
        gcongr
        · exact paddingVertex_cut_bound Qp L n hn.2
  · have hz (e : ((j : Fin J) → P j) × Q) :
        retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) = 0 := by
      unfold retainedPrimeEdge retainedLiouvilleEdge
      split_ifs with he he'
      · exact (hn he'.1).elim
      · rfl
      · rfl
    simp only [hz, norm_zero, sum_const_zero]
    positivity

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedActiveEdges
namespace OAI

/-! Inactive tuple/padding pairs contribute zero. Giving them step zero
lets the actual pair bound control every displacement in the block lemma. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma retainedPrimeEdge_inactive {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (he : ¬eligible (∏ j, (e.1 j).val) e.2.val) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  simp [retainedPrimeEdge, retainedLiouvilleEdge, he]

lemma retainedPrimeEdge_support_active {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ)
    (hm : m ≠ n + retainedPrimeStep eligible h e) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n m = 0 := by
  by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
  · rw [retainedPrimeStep, if_pos he] at hm
    exact retainedPrimeEdge_support P Q Qp u eligible L K W extra h gate keep e n m hm
  · exact retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n m he

lemma retainedPrimeStep_le {J : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    {L η : ℝ} {eligible : ℕ → ℕ → Prop} (h : ℕ)
    (hη : 0 < η) (hηone : η ≤ 1)
    (heligible : ∀ d q, eligible d q → PaddingPairEligible L η d q)
    (e : ((j : Fin J) → P j) × Q) :
    retainedPrimeStep eligible h e ≤ h * ⌊Real.exp (100 * L + 1)⌋₊ := by
  unfold retainedPrimeStep
  split_ifs with he
  · calc
      _ = h * ((∏ j, (e.1 j).val) * e.2.val) := by ring
      _ ≤ _ := Nat.mul_le_mul_left h (paddingPairEligible_product_upper hη hηone (heligible _ _ he))
  · exact Nat.zero_le _

lemma retainedPrimeEdge_active_step_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (e : ((j : Fin J) → P j) × Q) (n : ℤ) :
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      (n + retainedPrimeStep eligible h e) =
    retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
      (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) := by
  by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
  · rw [retainedPrimeStep, if_pos he]
  · rw [retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n _ he,
      retainedPrimeEdge_inactive P Q Qp u eligible L K W extra h gate keep e n _ he]

lemma ambientLiouvilleBlockForm_active {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (hgate : ∀ d n m, gate d n m ↔ gate d m n)
    (keep : ℤ → Prop) (t : ℕ) :
    ambientLiouvilleBlockForm P M Q Qp u eligible L K W extra h gate keep t =
      (2 * (L : ℂ)) * edgeBlockSum univ (retainedPrimeStep eligible h)
        (fun e n => retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          ((n : ℤ) + retainedPrimeStep eligible h e)) M t := by
  unfold ambientLiouvilleBlockForm
  dsimp only
  rw [primeBlockCompression_retained_identity P hprime hdisjoint M Q Qp u eligible
    L K W extra h gate hgate keep]
  rw [directed_block_form_eq _ _ (retainedPrimeEdge_support_active P Q Qp u eligible
    L K W extra h gate keep)]

lemma canonicalTraceFamily_pair_eligible (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ)
    (he : (d, q) ∈ (canonicalTraceFamily h E W L eligible hL hW hE).pairs) : eligible d q := by
  exact ((actualProhibitedPrimeFamily_pairs h _ _ E _ W L eligible _ _ hE d q).mp he).2.2.2

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualRetainedPrefix
namespace OAI

/-! Apply the spectral block estimate to the actual retained correlation.
The conclusion records all boundary errors before their asymptotic absorption. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem ModFiveThetaInput.eventually_actual_retained_prefix_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
        (l : ℝ) * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) / (2 * L * M) +
        ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * D +
        2 * (M : ℝ) / N * D := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_progression_block_testing_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb, hprime.eventually_actual_pool_masses E W hW] with L hb hmass
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  let active := fun d q => (d, q) ∈ data.pairs
  intro b N hN
  let F := ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient active
    L K W (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep
  let B := (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
    ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
      Real.exp (-(2 * ⌊L⌋₊ : ℕ))
  have hNp : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
  have hMp : 0 < M := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have havg : uniformAverage (fun t : Fin N => ‖F t.val‖) ≤ (l : ℝ) * B := by
    have ht := hb hL η hη hηone eligible he b N hN
    exact (uniformAverage_initial_le (fun t => ‖F t‖) (fun _ => norm_nonneg _) l N hl hNp).trans
      (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))
  have hp := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hd := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W := fun j => (hmass.2.1 j).2.1
  have hrow (n : ℕ) (_hn : 0 < n) :
      (∑ e : ((j : Fin J) → P j) × Q,
        ‖retainedPrimeEdge P Q Qp actualPaddingCoefficient active L K W
          (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep e n
          ((n : ℤ) + retainedPrimeStep active h e)‖) ≤ D := by
    simp only [retainedPrimeEdge_active_step_eq]
    exact retainedPrimeEdge_row_bound P hp hd Q Qp actualPaddingCoefficient active L K W
      (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep
      (by linarith) (Real.exp_pos _).le (by linarith)
      (fun q _ => actualPaddingCoefficient_nonneg q) hV n
  have hstep (e : ((j : Fin J) → P j) × Q) :
      retainedPrimeStep active h e ≤ h * ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply retainedPrimeStep_le h hη hηone
    intro d q hmem
    exact he d q (canonicalTraceFamily_pair_eligible h E W L eligible hL hW hE d q hmem)
  have ht := block_form_prefix_bound (retainedPrimeStep active h)
    (fun e n => retainedPrimeEdge P Q Qp actualPaddingCoefficient active L K W
      (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b) keep e n
      ((n : ℤ) + retainedPrimeStep active h e)) F M
    (h * ⌊Real.exp (100 * L + 1)⌋₊) N hMp hNp L ((l : ℝ) * B) D
    (by linarith) (by dsimp [D, K]; positivity) hstep hrow
    (fun t => ambientLiouvilleBlockForm_active P hp hd M Q Qp actualPaddingCoefficient active
      L K W (fun _ => actualPaddingDegreeCut Qp L) h (progressionEdgeGate h l b)
      (progressionEdgeGate_symmetric h l b) keep t) havg
  simpa only [retainedPrimeEdge_active_step_eq, retainedPrimePrefix] using ht


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualRetainedBin
namespace OAI

/-! The canonical retained-bin estimate: spectral main term plus an
exponentially small error, uniformly in the bin and progression class. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_actual_retained_bin_uniform_oai
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
      3 * (l : ℝ) ^ 2 * paddingTiltNormalizer Qp * R / L + 3 * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_retained_prefix_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb, eventually_retained_row_scale W hW,
    eventually_const_le_exp_quarter h, eventually_const_le_exp_quarter l,
    eventually_ge_atTop (212 : ℝ)] with L hb hrow hhsize hlsize hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let M := ⌈Real.exp (103 * L)⌉₊
  let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  intro b N hN
  have hLp : 0 < L := by linarith
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
  have hMlo : Real.exp (103 * L) ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (103 * L) from (Real.exp_pos _).le)
    have he : 1 ≤ Real.exp (103 * L) := Real.one_le_exp (by linarith)
    dsimp only [M]
    linarith
  have hNlarge : Real.exp (106 * L) ≤ (N : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hN
    have hp : L ^ 2 ≤ L ^ A := pow_le_pow_right₀ hL (by omega)
    nlinarith
  have herr := retained_boundary_error_bound L D h l M N (by linarith)
    (by dsimp [D, K]; positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hrow hhsize hlsize hMlo hMhi hNlarge
  have hf : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) ≤
      (h : ℝ) * Real.exp (100 * L + 1) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Nat.cast_nonneg _)
  have hboundary : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * D ≤
      ((h : ℝ) * Real.exp (100 * L + 1)) / M * D := by
    gcongr
  have ht := hb hL η hη hηone eligible he b N hN
  have hnorm := block_test_normalization L K ((8 * W) ^ J)
    ((5 : ℝ) ^ (400 * Real.log L)) R (paddingTiltNormalizer Qp) M l
    (Real.exp (-(2 * ⌊L⌋₊ : ℕ))) hLp.ne' hMp.ne'
  change ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N‖ ≤ _
  change ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N‖ ≤ _ at ht
  rw [hnorm] at ht
  change _ + _ + _ ≤ 3 * Real.exp (-L) at herr
  dsimp only [D] at herr hboundary
  linarith


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_retained_bin_uniform_oai := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_retained_bin_uniform_oai
