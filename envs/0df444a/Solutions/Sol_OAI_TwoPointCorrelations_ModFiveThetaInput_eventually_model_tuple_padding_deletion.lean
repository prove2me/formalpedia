-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_model_tuple_padding_deletion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:04:37.564125+00:00
-- url     : https://prove2.me/submissions/e1506a3a-aabd-46ae-81f6-ac26b068cd8f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_actual_family_padding_large_bin_cut

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]




lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))


lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]








lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm




end FiniteLaw

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

lemma independent_probability_all (μ : ι → FiniteLaw A) (E : ι → A → Prop) :
    (independent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  classical
  unfold probability
  calc
    _ = (independent μ).average (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      apply congrArg (independent μ).average
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := independent_average_product μ (fun i x => if E i x then 1 else 0)

lemma independent_weight_join (μ : ι → FiniteLaw A) (S : Finset ι)
    (x : S → A) (y : {i // i ∉ S} → A) :
    (independent μ).weight (joinCoordinates S x y) =
      (independent (fun i : S => μ i)).weight x *
      (independent (fun i : {i // i ∉ S} => μ i)).weight y := by
  change (∏ i, (μ i).weight (joinCoordinates S x y i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem, independent]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- Conditioning on coordinates outside `S` leaves the original product
law on `S`. -/
lemma independent_average_split (μ : ι → FiniteLaw A) (S : Finset ι) (f : (ι → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i : {i // i ∉ S} => μ i)).average (fun y =>
        (independent (fun i : S => μ i)).average (fun x => f (joinCoordinates S x y))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => A)
  calc
    _ = ∑ z : (S → A) × ({i // i ∉ S} → A),
        (independent μ).weight (joinCoordinates S z.1 z.2) *
          f (joinCoordinates S z.1 z.2) := by
      exact (e.symm.sum_comp (fun z => (independent μ).weight z * f z)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_join, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro x _
      ring



end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteLawMapping
namespace OAI

/-! Finite pushforward identities, used to identify the actual two-selection
padding experiment with its three-point difference law. -/

namespace TwoPointCorrelations.FiniteLaw

open _root_.Finset
open scoped _root_.Classical

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma average_fibers (μ : FiniteLaw α) (g : α → β) (F : β → ℝ) :
    μ.average (fun x => F (g x)) = ∑ y, μ.probability (fun x => g x = y) * F y := by
  calc
    _ = μ.average (fun x => ∑ y, if g x = y then F y else 0) := by
      congr 1
      funext x
      simp
    _ = _ := by
      rw [average_sum]
      apply sum_congr rfl
      intro y _
      simp [average, probability, sum_mul, mul_ite, ite_mul]

lemma independent_average_map [DecidableEq ι] (μ : ι → FiniteLaw α)
    (ν : ι → FiniteLaw β) (g : ι → α → β)
    (hg : ∀ i y, (μ i).probability (fun x => g i x = y) = (ν i).weight y)
    (F : (ι → β) → ℝ) :
    (independent μ).average (fun x => F (fun i => g i (x i))) =
      (independent ν).average F := by
  rw [average_fibers]
  unfold average
  apply sum_congr rfl
  intro y _
  congr 1
  have he : (fun x : ι → α => (fun i => g i (x i)) = y) =
      (fun x => ∀ i, g i (x i) = y i) := by
    funext x
    exact propext funext_iff
  rw [he, independent_probability_all μ (fun i x => g i x = y i)]
  simp only [hg, independent]



end TwoPointCorrelations.FiniteLaw

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
namespace OAI

/-! One integer realizes all coordinates of a common residue configuration. -/

namespace TwoPointCorrelations

open _root_.Finset


/-- Prime divisibility at any offset is read from that same lifted origin. -/
lemma residue_offset_divisibility {p : ℕ} (r : ZMod p) (n offset : ℤ)
    (hn : (n : ZMod p) = r) :
    (p : ℤ) ∣ n + offset ↔ r = -(offset : ZMod p) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, hn, add_eq_zero_iff_eq_neg]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveModel
namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder, using only finite probability identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw




lemma probability_complement {α : Type*} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  have hsum : μ.probability E + μ.probability (fun x => ¬E x) = 1 := by
    unfold probability average
    rw [← sum_add_distrib]
    calc
      _ = ∑ x, μ.weight x := by
        apply sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = 1 := μ.total
  linarith



end FiniteLaw







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

lemma FiniteLaw.probability_lt_exp_bound {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (Z : A → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    μ.probability (fun x => a < Z x) ≤
      Real.exp (-t * a) * μ.average (fun x => Real.exp (t * Z x)) := by
  calc
    _ ≤ μ.average (fun x => Real.exp (t * Z x) * Real.exp (-t * a)) := by
      apply μ.average_mono
      intro x
      by_cases hx : a < Z x
      · rw [if_pos hx, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      · rw [if_neg hx]
        positivity
    _ = _ := by rw [μ.average_mul_const]; ring


lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ

lemma booleanLaw_exp_average (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => Real.exp (t * (if b then 1 else 0))) =
      1 + q * (Real.exp t - 1) := by
  simp [FiniteLaw.average, booleanLaw]
  ring

lemma independent_boolean_exp_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (t : ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) =
        ∏ i, (1 + q i * (Real.exp t - 1)) := by
  have he (a : ι → Bool) : Real.exp (t * booleanCount a) =
      ∏ i, Real.exp (t * (if a i then 1 else 0)) := by
    rw [booleanCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [FiniteLaw.independent_average_product
    (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
    (fun _ b => Real.exp (t * (if b then 1 else 0)))]
  simp only [booleanLaw_exp_average]

lemma independent_boolean_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) ≤ Real.exp ((Real.exp t - 1) * M) := by
  rw [independent_boolean_exp_average]
  have hu : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  calc
    _ ≤ ∏ i, Real.exp (q i * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg zero_le_one (mul_nonneg (hq0 i) hu)
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (q i * (Real.exp t - 1))
    _ = Real.exp ((∑ i, q i) * (Real.exp t - 1)) := by
      rw [sum_mul, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The entire bound is a finite product identity followed by exponential
Markov; no probability theorem is assumed. -/
theorem independent_boolean_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M a : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => a < booleanCount b) ≤
        Real.exp ((Real.exp t - 1) * M - t * a) := by
  apply (FiniteLaw.probability_lt_exp_bound _ _ a t ht).trans
  calc
    _ ≤ Real.exp (-t * a) * Real.exp ((Real.exp t - 1) * M) :=
      mul_le_mul_of_nonneg_left (independent_boolean_exp_bound q hq0 hq1 t M ht hM)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
namespace OAI

/-! The literal `5^omega` tilt of independent divisibility indicators gives
exactly the prime availability law used in the padding anti-concentration. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingTiltNormalizer_pos (Q : Finset ℕ) : 0 < paddingTiltNormalizer Q := by
  apply prod_pos
  intro p _
  positivity

lemma padding_prime_tilt (p : ℕ) (hp : 2 ≤ p) (a : Bool) :
    (paddingOriginalPrimeLaw p hp).weight a * (if a then 5 else 1) =
      (paddingAvailabilityLaw p hp).weight a * (1 + 4 / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp4 : (p : ℝ) + 4 ≠ 0 := by positivity
  cases a <;> simp only [paddingOriginalPrimeLaw, paddingAvailabilityLaw, booleanLaw,
    Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp <;> ring

lemma padding_tilt_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) (a : Q → Bool) :
    (paddingOriginalLaw Q hQ).weight a * paddingTiltWeight Q a =
      (paddingAvailableLaw Q hQ).weight a * paddingTiltNormalizer Q := by
  simp only [paddingOriginalLaw, paddingAvailableLaw, FiniteLaw.independent,
    paddingTiltWeight, paddingTiltNormalizer, ← prod_mul_distrib]
  apply prod_congr rfl
  intro p _
  exact padding_prime_tilt p (hQ p p.property) (a p)

lemma padding_tilt_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Bool) → ℝ) :
    (paddingOriginalLaw Q hQ).average (fun a => paddingTiltWeight Q a * F a) =
      paddingTiltNormalizer Q * (paddingAvailableLaw Q hQ).average F := by
  simp only [FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, padding_tilt_weight]
  ring




lemma padding_selection_atom (a b : Bool) :
    (paddingSelectionLaw a).weight b * (if a then 5 else 1) =
      if b then (if a then 4 else 0) else 1 := by
  cases a <;> cases b <;> norm_num [paddingSelectionLaw, booleanLaw]

lemma padding_divisor_weight (Q : Finset ℕ) (a b : Q → Bool) :
    (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a =
      if PaddingSelectionSupported Q a b then paddingDivisorCoefficient Q b else 0 := by
  simp only [paddingDivisorLaw, FiniteLaw.independent, paddingTiltWeight,
    ← prod_mul_distrib, padding_selection_atom]
  by_cases hs : PaddingSelectionSupported Q a b
  · rw [if_pos hs]
    unfold paddingDivisorCoefficient
    apply prod_congr rfl
    intro p _
    cases hb : b p
    · simp
    · simp [hs p hb]
  · rw [if_neg hs]
    change ¬ ∀ p : Q, b p = true → a p = true at hs
    push Not at hs
    obtain ⟨p, hb, ha⟩ := hs
    apply prod_eq_zero (mem_univ p)
    simp [hb, ha]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeTilt
namespace OAI

/-! Tilting the prime divisibility law by the positive majorant of one
tuple of centered prime factors.  Selected primes have parameter
`(1 + q)/2`; every other prime keeps its original parameter. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







lemma positiveCenterWeight_eq (q : ι → ℝ) (S : Finset ι) (a : ι → Bool) :
    positiveCenterWeight q S a = ∏ i ∈ S, ((if a i then 1 else 0) + q i) := by
  simp only [positiveCenterWeight, ← prod_filter, filter_mem_eq_inter, univ_inter]

lemma positiveCenterNormalizer_eq (q : ι → ℝ) (S : Finset ι) :
    positiveCenterNormalizer q S = ∏ i ∈ S, 2 * q i := by
  simp only [positiveCenterNormalizer, ← prod_filter, filter_mem_eq_inter, univ_inter]


lemma positive_center_tilt_weight (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (a : ι → Bool) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).weight a *
        positiveCenterWeight q S a =
      (positiveCenterLaw q S hq0 hq1).weight a * positiveCenterNormalizer q S := by
  simp only [FiniteLaw.independent, positiveCenterLaw, positiveCenterWeight,
    positiveCenterNormalizer, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> cases a i <;>
    simp [positiveCenterParameter, hi, booleanLaw] <;> ring

lemma positive_center_tilt_average (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (F : (ι → Bool) → ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
        (fun a => positiveCenterWeight q S a * F a) =
      positiveCenterNormalizer q S * (positiveCenterLaw q S hq0 hq1).average F := by
  simp only [FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, positive_center_tilt_weight]
  ring

lemma positive_center_tilt_total (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
        (positiveCenterWeight q S) = positiveCenterNormalizer q S := by
  simpa only [mul_one, FiniteLaw.average_const] using
    positive_center_tilt_average q S hq0 hq1 (fun _ => 1)




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
namespace OAI

/-! The fixed modulus-five prime-number input used by the manuscript.

Published source: D. Koukoulopoulos, *The Distribution of Prime Numbers*,
AMS, 2019, Theorem 12.1 (Siegel--Walfisz), with modulus 5 fixed. That theorem
is stated for the prime-counting function. `ModFiveThetaInput` is its standard
partial-summation consequence for the logarithmically weighted prime count,
specialized to the two selections needed here. The complementary selection
includes the single prime 5, which changes the error by a bounded amount.
Source: https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf

The estimate includes every prime in the selected classes. Removing a finite
exceptional prime set contributes an explicit finite-deletion correction.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology









lemma modFiveTheta_eq_sum (one : Bool) (x : ℝ) :
    modFiveTheta one x = ∑ p ∈ modFivePrimesUpTo one x, Real.log p := by
  simp [modFiveTheta, modFivePrimesUpTo, modFiveLogWeight, sum_filter]





lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)

/-- The entire cost of removing a finite exceptional prime set is explicit. -/
lemma deletedModFiveTheta_error (E : Finset ℕ) (one : Bool) (x : ℝ) :
    |deletedModFiveTheta E one x - modFiveTheta one x| ≤
      ∑ p ∈ E, Real.log p := by
  rw [modFiveTheta_eq_sum]
  have he : deletedModFiveTheta E one x -
      (∑ p ∈ modFivePrimesUpTo one x, Real.log p) =
      -(∑ p ∈ modFivePrimesUpTo one x ∩ E, Real.log p) := by
    unfold deletedModFiveTheta deletedModFivePrimes
    have hs := sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ))
      (inter_subset_left : modFivePrimesUpTo one x ∩ E ⊆ modFivePrimesUpTo one x)
    rw [sdiff_inter_self_left] at hs
    linarith
  rw [he, abs_neg, abs_of_nonneg (sum_nonneg (fun p _ => log_nat_nonneg p))]
  exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => log_nat_nonneg p)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePartialSummation
namespace OAI

/-! Exact partial summation, with the prime-count error retained inside the
integral. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


theorem centered_partial_summation (c : ℕ → ℝ) (α a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - α * (∫ t in a..b, f t) =
      f b * (partialCoefficientSum c b - α * b) -
      f a * (partialCoefficientSum c a - α * a) -
      ∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t) := by
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab
  have hdfi : IntervalIntegrable (deriv f) volume a b :=
    hdf.intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    hdfi.mul_continuousOn continuous_id.continuousOn
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c ha
      (hdf.integrableOn_Icc)
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab hf hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab] at hAbel
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) =
    f b * partialCoefficientSum c b - f a * partialCoefficientSum c a -
      ∫ t in a..b, deriv f t * partialCoefficientSum c t at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x (_ : x ∈ Set.uIcc a b) => hasDerivAt_id x) hdfi intervalIntegrable_const
  simp only [id_eq] at hparts
  have hsplit : (∫ t in a..b, deriv f t * t + f t * 1) =
      (∫ t in a..b, deriv f t * t) + ∫ t in a..b, f t := by
    simp only [mul_one]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t * (partialCoefficientSum c t - α * t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum c t) -
        α * (∫ t in a..b, deriv f t * t) := by
    simp only [mul_sub, show ∀ t, deriv f t * (α * t) = α * (deriv f t * t) by
      intro t; ring]
    rw [intervalIntegral.integral_sub hsum (hdmain.const_mul α),
      intervalIntegral.integral_const_mul]
  rw [herr, hAbel]
  linear_combination -α * hparts


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ThetaLogError
namespace OAI

/-! An integrable logarithmic error bound obtained from the stated exponential
prime-number error. It also pays exactly for finite exceptional prime sets. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma exp_neg_sqrt_log_le (c x : ℝ) (hc : 0 < c) (hx : 1 < x) :
    Real.exp (-c * Real.sqrt (Real.log x)) ≤ 24 / (c ^ 4 * Real.log x ^ 2) := by
  have hl : 0 < Real.log x := Real.log_pos hx
  have hsq := Real.sq_sqrt hl.le
  have hpow : (c * Real.sqrt (Real.log x)) ^ 4 = c ^ 4 * Real.log x ^ 2 := by
    calc
      _ = c ^ 4 * ((Real.sqrt (Real.log x)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (Real.log x))
    (mul_nonneg hc.le (Real.sqrt_nonneg (Real.log x))) 4
  norm_num at he
  rw [hpow] at he
  have hmul := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-c * Real.sqrt (Real.log x))).le
  have hexp : Real.exp (c * Real.sqrt (Real.log x)) *
      Real.exp (-c * Real.sqrt (Real.log x)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hmul
  apply (le_div_iff₀ (by positivity : 0 < c ^ 4 * Real.log x ^ 2)).mpr
  nlinarith [hmul]

lemma log_sq_le_two_mul (x : ℝ) (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 2 * x := by
  have hh := Real.pow_div_factorial_le_exp (Real.log x) (Real.log_nonneg hx) 2
  norm_num at hh
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at hh
  linarith

/-- A single constant controls the logarithmic PNT error for both residue
selections and every real endpoint at least two. -/
theorem ModFiveThetaInput.log_error (hP : ModFiveThetaInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFiveTheta one x - modFiveDensity one * x| ≤ K * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, h⟩ := hP
  refine ⟨24 * C / c ^ 4, by positivity, fun one x hx => ?_⟩
  apply (h one x hx).trans
  have hh := mul_le_mul_of_nonneg_left (exp_neg_sqrt_log_le c x hc (by linarith))
    (mul_nonneg hC (by linarith : 0 ≤ x))
  convert (preTransparency := .instances) hh using 1
  ring

theorem ModFiveThetaInput.deleted_log_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |deletedModFiveTheta E one x - modFiveDensity one * x| ≤
        K * x / Real.log x ^ 2 := by
  obtain ⟨K, hK, h⟩ := hP.log_error
  let D : ℝ := ∑ p ∈ E, Real.log p
  have hD : 0 ≤ D := sum_nonneg (fun p _ => log_nat_nonneg p)
  refine ⟨K + 2 * D, by positivity, fun one x hx => ?_⟩
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hd : D ≤ 2 * D * x / Real.log x ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hl)).mpr
    have hh := mul_le_mul_of_nonneg_left (log_sq_le_two_mul x (by linarith)) hD
    nlinarith [hh]
  calc
    _ ≤ |modFiveTheta one x - modFiveDensity one * x| + D := by
      calc
        _ = |(modFiveTheta one x - modFiveDensity one * x) +
            (deletedModFiveTheta E one x - modFiveTheta one x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add (le_refl _) (deletedModFiveTheta_error E one x)
    _ ≤ K * x / Real.log x ^ 2 + 2 * D * x / Real.log x ^ 2 :=
      add_le_add (h one x hx) hd
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPrimeBands
namespace OAI

/-! Quantitative reciprocal-prime bands from the actual theta error.
Partial summation gives the reciprocal-prime estimates. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma reciprocalLog_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt reciprocalLog
      (-(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hh := (hasDerivAt_inv hx0).div (Real.hasDerivAt_log hx0) hl0
  convert (preTransparency := .instances) hh using 1
  · rfl
  · field_simp
    ring

lemma reciprocalLog_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 0 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |reciprocalLog x * E| ≤ K / Real.log x := by
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [abs_mul, abs_of_nonneg (by unfold reciprocalLog; positivity)]
  calc
    _ ≤ reciprocalLog x * (K * x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_left hE (by unfold reciprocalLog; positivity)
    _ = K / Real.log x ^ 3 := by unfold reciprocalLog; field_simp
    _ ≤ K / Real.log x := by
      apply div_le_div_of_nonneg_left hK hlp
      nlinarith [sq_nonneg (Real.log x - 1)]

lemma reciprocalLog_deriv_error_le (K x E : ℝ) (hK : 0 ≤ K)
    (hx : 1 < x) (hl : 1 ≤ Real.log x)
    (hE : |E| ≤ K * x / Real.log x ^ 2) :
    |deriv reciprocalLog x * E| ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlp : 0 < Real.log x := zero_lt_one.trans_le hl
  rw [(reciprocalLog_hasDerivAt hx).deriv, abs_mul, abs_div, abs_neg,
    abs_of_pos (by positivity : 0 < Real.log x + 1),
    abs_of_pos (by positivity : 0 < x ^ 2 * Real.log x ^ 2)]
  calc
    _ ≤ ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) *
        (K * x / Real.log x ^ 2) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 2 * K * (x⁻¹ / Real.log x ^ 2) := by
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < x * Real.log x ^ 4)).mp
      field_simp
      nlinarith [sq_nonneg (Real.log x - 1), mul_nonneg hK (sq_nonneg (Real.log x - 1))]

/-- A uniform band error. The upper endpoint is arbitrary, so this applies
simultaneously to all the logarithmically spaced supplies in the manuscript. -/
theorem reciprocal_band_error (c : ℕ → ℝ) (α K a b : ℝ) (hK : 0 ≤ K)
    (ha : Real.exp 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ x ∈ Set.Icc a b,
      |partialCoefficientSum c x - α * x| ≤ K * x / Real.log x ^ 2) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog n * c n) -
      α * (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 4 * K / Real.log a := by
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hla : 1 ≤ Real.log a := by
    simpa using Real.log_le_log (Real.exp_pos 1) ha
  have hlap : 0 < Real.log a := Real.log_pos ha1
  have hx1 (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 < x := ha1.trans_le hx.1
  have hlx (x : ℝ) (hx : x ∈ Set.Icc a b) : 1 ≤ Real.log x :=
    hla.trans (Real.log_le_log ha0 hx.1)
  have hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ reciprocalLog x :=
    fun x hx => (reciprocalLog_hasDerivAt (hx1 x hx)).differentiableAt
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 :=
    fun x hx => (zero_lt_one.trans (hx1 x hx)).ne'
  have hln : ∀ x ∈ Set.Icc a b, Real.log x ≠ 0 :=
    fun x hx => (Real.log_pos (hx1 x hx)).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hdf : ContinuousOn (deriv reciprocalLog) (Set.Icc a b) := by
    apply ContinuousOn.congr (f := fun x => -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2))
    · exact (hclog.add continuousOn_const).neg.div
        ((continuousOn_id.pow 2).mul (hclog.pow 2))
        (fun x hx => mul_ne_zero (pow_ne_zero 2 (hxn x hx)) (pow_ne_zero 2 (hln x hx)))
    · intro x hx
      exact (reciprocalLog_hasDerivAt (hx1 x hx)).deriv
  have hAbel := centered_partial_summation c α a b ha0.le hab reciprocalLog hf hdf
  rw [show (∫ t in a..b, reciprocalLog t) =
      Real.log (Real.log b) - Real.log (Real.log a) from
    integral_inv_div_log ha1 hb1] at hAbel
  have hg : IntervalIntegrable (fun x : ℝ => 2 * K * (x⁻¹ / Real.log x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc (h := hab)
    exact ((continuousOn_id.inv₀ hxn).div (hclog.pow 2)
      (fun x hx => pow_ne_zero 2 (hln x hx))).const_mul (2 * K)
  have hi : |∫ x in a..b, deriv reciprocalLog x * (partialCoefficientSum c x - α * x)| ≤
      2 * K / Real.log a := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]
        exact reciprocalLog_deriv_error_le K x _ hK (hx1 x ⟨hx.1.le, hx.2⟩)
          (hlx x ⟨hx.1.le, hx.2⟩) (hE x ⟨hx.1.le, hx.2⟩))) hg
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
      integral_inv_div_log_sq ha1 hb1] at hbound
    apply hbound.trans
    have hbnonneg : 0 ≤ (Real.log b)⁻¹ := inv_nonneg.mpr (Real.log_pos hb1).le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K) hbnonneg]
  have hA := reciprocalLog_error_le K a _ hK ha0 hla (hE a ⟨le_rfl, hab⟩)
  have hB := reciprocalLog_error_le K b _ hK (zero_lt_one.trans hb1)
    (hlx b ⟨hab, le_rfl⟩) (hE b ⟨hab, le_rfl⟩)
  have hBA : K / Real.log b ≤ K / Real.log a :=
    div_le_div_of_nonneg_left hK hlap (Real.log_le_log ha0 hab)
  rw [hAbel]
  calc
    _ ≤ |reciprocalLog b * (partialCoefficientSum c b - α * b)| +
        |reciprocalLog a * (partialCoefficientSum c a - α * a)| +
        |∫ t in a..b, deriv reciprocalLog t * (partialCoefficientSum c t - α * t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ K / Real.log a + K / Real.log a + 2 * K / Real.log a :=
      add_le_add (add_le_add (hB.trans hBA) hA) hi
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeBands
namespace OAI

/-! Concrete modulus-five supplies and their reciprocal masses. We use
half-open bands `(exp A, exp B]`; this harmless endpoint convention makes
adjacent supplies exactly disjoint and matches finite Abel summation. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma partialSum_deletedModFive (E : Finset ℕ) (one : Bool) (x : ℝ) :
    partialCoefficientSum (deletedModFiveLogWeight E one) x =
      deletedModFiveTheta E one x := by
  unfold partialCoefficientSum deletedModFiveTheta deletedModFivePrimes
    modFivePrimesUpTo deletedModFiveLogWeight
  rw [sdiff_eq_filter, sum_filter, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases h : ModFivePrime one p <;> by_cases he : p ∈ E <;> simp [h, he]



lemma modFivePrimeBand_sum (E : Finset ℕ) (one : Bool) (a b : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, 1 / (p : ℝ)) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, reciprocalLog p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    rw [if_pos hs]
    unfold deletedModFiveLogWeight
    rw [if_pos hs]
    unfold reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

/-- Both selected prime classes have their correct logarithmic-band mass,
uniformly over the upper endpoint and with any fixed finite exclusions. -/
theorem ModFiveThetaInput.band_error (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (one : Bool) (A B : ℝ), 1 ≤ A → A ≤ B →
      |(∑ p ∈ modFivePrimeBand E one (Real.exp A) (Real.exp B), 1 / (p : ℝ)) -
          modFiveDensity one * (Real.log B - Real.log A)| ≤ 4 * K / A := by
  obtain ⟨K, hK, h⟩ := hP.deleted_log_error E
  refine ⟨K, hK, fun one A B hA hAB => ?_⟩
  rw [modFivePrimeBand_sum]
  have hh := reciprocal_band_error (deletedModFiveLogWeight E one) (modFiveDensity one)
    K (Real.exp A) (Real.exp B) hK (Real.exp_le_exp.mpr hA)
      (Real.exp_le_exp.mpr hAB) (fun x hx => by
        rw [partialSum_deletedModFive]
        apply h one x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans ((Real.exp_le_exp.mpr hA).trans hx.1))
  simpa only [Real.log_exp] using hh


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinSquare
namespace OAI

/-! The actual bin-square padding average is bounded by the exact difference
small-ball probability, uniformly in a common translation of all bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

variable {α β : Type*} [Fintype α]

lemma average_finset_sum (μ : FiniteLaw α) (s : Finset β) (F : β → α → ℝ) :
    μ.average (fun x => ∑ b ∈ s, F b x) = ∑ b ∈ s, μ.average (F b) := by
  simp only [average, mul_sum]
  exact sum_comm


end FiniteLaw






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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLiteralBins
namespace OAI

/-! The bin mass is the literal normalized sum of padding-divisor weights.
Boolean selections are finite subsets, so no extra multiplicity is present. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma paddingTiltWeight_eq_five_pow (Q : Finset ℕ) (a : Q → Bool) :
    paddingTiltWeight Q a = (5 : ℝ) ^ (selectedCoordinates Q a).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingTiltWeight]

lemma paddingDivisorCoefficient_eq_four_pow (Q : Finset ℕ) (b : Q → Bool) :
    paddingDivisorCoefficient Q b = (4 : ℝ) ^ (selectedCoordinates Q b).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingDivisorCoefficient]





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

lemma padding_supported_iff_primeFactors_subset (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (a b : Q → Bool) :
    PaddingSelectionSupported Q a b ↔
      (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b]
  constructor
  · intro h p hp
    have hpQ := paddingAvailablePrimes_subset Q b hp
    exact (mem_paddingAvailablePrimes Q a ⟨p, hpQ⟩).mpr
      (h ⟨p, hpQ⟩ ((mem_paddingAvailablePrimes Q b ⟨p, hpQ⟩).mp hp))
  · intro h p hp
    exact (mem_paddingAvailablePrimes Q a p).mp
      (h ((mem_paddingAvailablePrimes Q b p).mpr hp))








lemma padding_divisor_weight_total (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (a : Q → Bool) :
    (∑ q ∈ retainedPrimeDivisors Q,
      if q.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.primeFactors.card else 0) =
        paddingTiltWeight Q a := by
  let F (q : retainedPrimeDivisors Q) : ℝ :=
    if q.val.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.val.primeFactors.card else 0
  have he (b : Q → Bool) : F (paddingDivisorEquiv Q hQ b) =
      (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a := by
    rw [padding_divisor_weight]
    change (if (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a
      then (4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card else 0) = _
    have hs := padding_supported_iff_primeFactors_subset Q hQ a b
    rw [paddingSelectedDivisor_primeFactors Q hQ b] at hs
    simp only [← hs,
      paddingSelectedDivisor_primeFactors Q hQ b, paddingAvailablePrimes_card,
      paddingDivisorCoefficient_eq_four_pow]
  calc
    _ = ∑ q : retainedPrimeDivisors Q, F q := (sum_coe_sort _ (fun q : ℕ =>
      if q.primeFactors ⊆ paddingAvailablePrimes Q a then (4 : ℝ) ^ q.primeFactors.card else 0)).symm
    _ = ∑ b : Q → Bool, F (paddingDivisorEquiv Q hQ b) :=
      ((paddingDivisorEquiv Q hQ).sum_comp F).symm
    _ = ∑ b : Q → Bool, (paddingDivisorLaw Q a).weight b * paddingTiltWeight Q a :=
      sum_congr rfl (fun b _ => he b)
    _ = paddingTiltWeight Q a := by
      rw [← sum_mul, (paddingDivisorLaw Q a).total, one_mul]

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

lemma paddingSelectedDivisor_dvd_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (n : ℤ) :
    (paddingSelectedDivisor Q b : ℤ) ∣ n ↔
      ∀ p : Q, b p = true → (p.val : ℤ) ∣ n := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun q : Q => (q.val : ℤ))
      (mem_filter.mpr ⟨mem_univ p, hp⟩)).trans h
  · intro h
    apply prod_dvd_of_coprime
    · intro p _ q _ hpq
      apply Nat.Coprime.cast
      apply (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      exact fun he => hpq (Subtype.ext he)
    · intro p hp
      exact h p (mem_filter.mp hp).2

lemma padding_literal_support_iff_dvd (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    q.primeFactors ⊆ paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) ↔
      (q : ℤ) ∣ n := by
  obtain ⟨b, rfl⟩ := exists_paddingSelection Q q hq
  rw [← padding_supported_iff_primeFactors_subset Q hQ,
    paddingSelectedDivisor_dvd_iff Q hQ b n]
  simp only [PaddingSelectionSupported, decide_eq_true_eq]

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



lemma padding_integer_weight_total (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℤ) :
    (∑ q ∈ retainedPrimeDivisors Q, if (q : ℤ) ∣ n then (4 : ℝ) ^ q.primeFactors.card else 0) =
      (5 : ℝ) ^ (Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n)).card := by
  have hh := padding_divisor_weight_total Q hQ (fun p => decide ((p.val : ℤ) ∣ n))
  rw [paddingTiltWeight_eq_five_pow, ← paddingAvailablePrimes_card,
    paddingAvailablePrimes_integer] at hh
  convert (preTransparency := .instances) hh using 1
  apply sum_congr rfl
  intro q hq
  have hd := padding_literal_support_iff_dvd Q hQ n q hq
  rw [paddingAvailablePrimes_integer] at hd
  simp only [hd]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuit
namespace OAI

/-! The actual deleted event is a finite depth-two DNF of prime tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit





end AC0Circuit














lemma squarefree_divisor_iff (d : ℕ) (hd : Squarefree d) (n : ℤ) :
    (d : ℤ) ∣ n ↔ ∀ p ∈ d.primeFactors, (p : ℤ) ∣ n := by
  constructor
  · intro hn p hp
    have hp' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    exact hp'.trans hn
  · intro hn
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    apply prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
        (Nat.mem_primeFactors.mp hq).1).mpr hpq).cast (R := ℤ)
    · exact hn








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability
namespace OAI

/-!
# Probability of one positive numerical word

The same residue coordinate is reused at every occurrence of a prime.
Selecting one occurrence per distinct prime therefore bounds the probability
by one reciprocal per distinct prime, including all padding factors. There
is no independence assumption between different sites of the word.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


/-- Every residue modulo the true modulus has precisely its uniform mass,
even though the common carrier `Fin B` also contains zero-weight points. -/
theorem uniformResidueLaw_mod_eq (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (r : ZMod p) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => (x.val : ZMod p) = r) = (p : ℝ)⁻¹ := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let : DecidableEq (ZMod p) := fun _ _ => Classical.propDecidable _
  let a : Fin B := ⟨r.val, r.val_lt.trans_le hpB⟩
  have ha : a.val < p := r.val_lt
  have har : (a.val : ZMod p) = r := ZMod.natCast_zmod_val r
  have hterm (x : Fin B) :
      (uniformResidueLaw B p hp hpB).weight x *
        (if (x.val : ZMod p) = r then (1 : ℝ) else 0) =
      if x = a then (p : ℝ)⁻¹ else 0 := by
    by_cases hx : x = a
    · subst x
      simp only [uniformResidueLaw_weight B p hp hpB a ha, har, ite_true, mul_one]
    · by_cases hxp : x.val < p
      · have hxr : (x.val : ZMod p) ≠ r := by
          intro he
          have hv := congrArg ZMod.val he
          rw [ZMod.val_natCast_of_lt hxp] at hv
          exact hx (Fin.ext hv)
        simp only [uniformResidueLaw_weight B p hp hpB x hxp, if_neg hxr,
          mul_zero, if_neg hx]
      · simp only [uniformResidueLaw, if_neg hxp, zero_mul, if_neg hx]
  unfold FiniteLaw.probability FiniteLaw.average
  dsimp only
  calc
    _ = ∑ x : Fin B, if x = a then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl (fun x _ => hterm x)
    _ = _ := by simp









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueTilt
namespace OAI

/-! At every translated site of the uniform residue model, divisibility
indicators give independent Bernoulli(1/p) variables. Thus the exact weighted
residue expectation is the tilted padding law used in the bin-square bound. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma padding_residue_single_law (B p : ℕ) (hp : 2 ≤ p) (hpB : p ≤ B)
    (n : ℤ) (b : Bool) :
    (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => decide ((p : ℤ) ∣ (z.val : ℤ) + n) = b) =
        (paddingOriginalPrimeLaw p hp).weight b := by
  have he (z : Fin B) : (p : ℤ) ∣ (z.val : ℤ) + n ↔
      (z.val : ZMod p) = -(n : ZMod p) :=
    residue_offset_divisibility (z.val : ZMod p) z.val n (by simp)
  have hh : (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n) = (p : ℝ)⁻¹ := by
    simpa only [he] using uniformResidueLaw_mod_eq B p (by omega) hpB (-(n : ZMod p))
  cases b
  · have hc := FiniteLaw.probability_complement (uniformResidueLaw B p (by omega) hpB)
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n)
    rw [hh] at hc
    simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hc
  · simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hh

lemma padding_residue_average (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, 2 ≤ p) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (F : (Q → Bool) → ℝ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))).average
        (fun z => F (paddingResidueAvailable Q B n z)) =
          (paddingOriginalLaw Q hQ).average F := by
  exact FiniteLaw.independent_average_map
    (fun p : Q => uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))
    (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))
    (fun p (z : Fin B) => decide ((p.val : ℤ) ∣ (z.val : ℤ) + n))
    (fun p b => padding_residue_single_law B p (hQ p p.property) (hQB p p.property) n b) F

lemma padding_residue_tilt (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, 2 ≤ p) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (F : (Q → Bool) → ℝ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))).average
        (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B n z) *
          F (paddingResidueAvailable Q B n z)) /
            paddingTiltNormalizer Q = (paddingAvailableLaw Q hQ).average F := by
  rw [padding_residue_average Q B hQ hQB n (fun a => paddingTiltWeight Q a * F a),
    padding_tilt_average Q hQ F]
  exact mul_div_cancel_left₀ _ (paddingTiltNormalizer_pos Q).ne'



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDegreeTail
namespace OAI

/-! The exact tilted padding law has mean at most `4 log L` eventually.
The finite exponential-moment bound gives the manuscript's `L^-100`
large-padding-degree error using the same fixed-modulus prime input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma paddingPrimeSupply_split (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    paddingPrimeSupply E L = paddingPrimeSupply E 1 ∪
      modFivePrimeBand E false (Real.exp 1) (Real.exp L) := by
  have hfloor : ⌊Real.exp 1⌋₊ ≤ ⌊Real.exp L⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hL)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    obtain ⟨hp0, hpL⟩ := mem_Icc.mp hp
    apply mem_union.mpr
    by_cases hsmall : p ≤ ⌊Real.exp 1⌋₊
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hsmall⟩, hprime⟩, he⟩)
    · exact Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hpL⟩, hprime, he⟩)
  · intro hp
    apply Finset.mem_sdiff.mpr
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨hp, he⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp, hprime⟩ := mem_filter.mp hp
      obtain ⟨hp0, hp1⟩ := mem_Icc.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hp0, hp1.trans hfloor⟩, hprime⟩, he⟩
    · obtain ⟨hp, hprime, he⟩ := mem_filter.mp hp
      exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le p, (mem_Ioc.mp hp).2⟩, hprime⟩, he⟩

lemma paddingPrimeSupply_split_disjoint (E : Finset ℕ) (L : ℝ) :
    Disjoint (paddingPrimeSupply E 1)
      (modFivePrimeBand E false (Real.exp 1) (Real.exp L)) := by
  apply disjoint_left.mpr
  intro p hp hb
  have hp1 := (mem_Icc.mp (mem_filter.mp (Finset.mem_sdiff.mp hp).1).1).2
  have hp2 := (mem_Ioc.mp (mem_filter.mp hb).1).1
  omega

theorem ModFiveThetaInput.padding_reciprocal_mass (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑ p ∈ paddingPrimeSupply E L, 1 / (p : ℝ)) ≤ (3 / 4 : ℝ) * Real.log L + C := by
  obtain ⟨K, hK, hband⟩ := hP.band_error E
  refine ⟨(∑ p ∈ paddingPrimeSupply E 1, 1 / (p : ℝ)) + 4 * K,
    add_nonneg (sum_nonneg (fun _ _ => by positivity)) (by positivity), fun L hL => ?_⟩
  rw [paddingPrimeSupply_split E L hL, sum_union (paddingPrimeSupply_split_disjoint E L)]
  have hb := (abs_le.mp (hband false 1 L le_rfl hL)).2
  norm_num [modFiveDensity] at hb
  simp only [one_div]
  linarith

lemma padding_mean_le_reciprocal (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (∑ p : Q, 5 / ((p.val : ℝ) + 4)) ≤ 5 * ∑ p ∈ Q, 1 / (p : ℝ) := by
  rw [← sum_coe_sort Q (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
  apply sum_le_sum
  intro p _
  have hp : (0 : ℝ) < p.val := by exact_mod_cast (by have := hQ p p.property; omega : 0 < p.val)
  calc
    5 / ((p.val : ℝ) + 4) ≤ 5 / (p.val : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
    _ = _ := by ring

theorem ModFiveThetaInput.eventually_padding_mean (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∑ p : paddingPrimeSupply E L, 5 / ((p.val : ℝ) + 4)) ≤ 4 * Real.log L := by
  obtain ⟨C, hC, hmass⟩ := hP.padding_reciprocal_mass E
  filter_upwards [eventually_ge_atTop (Real.exp (20 * C)), eventually_ge_atTop (1 : ℝ)]
    with L hLC hL
  have hlog : 20 * C ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLC
  have hh := padding_mean_le_reciprocal (paddingPrimeSupply E L)
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le)
  nlinarith [hmass L hL]

theorem ModFiveThetaInput.eventually_padding_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (paddingAvailableLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).probability
          (fun a => 400 * Real.log L < booleanCount a) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_mean E, eventually_ge_atTop (1 : ℝ)] with L hM hL
  let Q := paddingPrimeSupply E L
  have hQ : ∀ p ∈ Q, 2 ≤ p := fun _ hp => (paddingPrimeSupply_prime hp).two_le
  have hq0 (p : Q) : 0 ≤ 5 / ((p.val : ℝ) + 4) := by positivity
  have hq1 (p : Q) : 5 / ((p.val : ℝ) + 4) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hp : (2 : ℝ) ≤ p.val := by exact_mod_cast hQ p p.property
    linarith
  have hb := independent_boolean_tail (fun p : Q => 5 / ((p.val : ℝ) + 4)) hq0 hq1
    1 (4 * Real.log L) (400 * Real.log L) (by norm_num) hM
  change (paddingAvailableLaw Q hQ).probability _ ≤ _
  calc
    _ ≤ Real.exp ((Real.exp 1 - 1) * (4 * Real.log L) - 1 * (400 * Real.log L)) := hb
    _ ≤ Real.exp (-100 * Real.log L) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
      nlinarith [Real.exp_one_lt_three]
    _ = L ^ (-100 : ℝ) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hL)]
      congr 1
      ring

/-- The original uniform-residue expectation, with its literal padding
weight retained, has the same `L^-100` degree-deletion bound. -/
theorem ModFiveThetaInput.eventually_padding_residue_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (n : ℤ)
      (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B),
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            paddingTiltWeight _ (paddingResidueAvailable _ B n z) *
              if 400 * Real.log L < booleanCount (paddingResidueAvailable _ B n z)
              then 1 else 0) / paddingTiltNormalizer (paddingPrimeSupply E L) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_degree_tail E] with L hL
  intro B n hQB
  rw [padding_residue_tilt (paddingPrimeSupply E L) B
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le) hQB n
    (fun a => if 400 * Real.log L < booleanCount a then 1 else 0)]
  exact hL

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
namespace OAI

/-! Evaluate the actual padding-periodic weights at one common integer lift of the product-law sample. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical



lemma residueOrigin_spec {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :
    (data.residueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_residue_origin x).choose_spec p

lemma residueOrigin_divisibility {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) (offset : ℤ) :
    (p.val : ℤ) ∣ data.residueOrigin x + offset ↔
      (p.val : ℤ) ∣ (x p).val + offset := by
  exact (residue_offset_divisibility _ _ _ (data.residueOrigin_spec x p)).trans
    (residue_offset_divisibility ((x p).val : ZMod p.val) ((x p).val : ℤ) offset
      (by simp)).symm




end TwoPointCorrelations.ProhibitedPrimeFamily

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
namespace OAI

/-! Restriction of a product law to selected prime coordinates.  The
coordinate laws may depend on the prime; no common-modulus uniformity is
assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_reindex {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : ι ≃ κ) (μ : κ → FiniteLaw A) (f : (κ → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i => μ (e i))).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent μ).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent μ).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, (μ k).weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, (μ (e i)).weight (x i)) * f (fun k => x (e.symm k))
      congr 1
      simpa only [e.apply_symm_apply] using
        e.symm.prod_comp (fun i => (μ (e i)).weight (x i))

lemma independent_average_restrict {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι) (f : (S → A) → ℝ) :
    (independent μ).average (fun x => f (fun i : S => x i)) =
      (independent (fun i : S => μ i)).average f := by
  rw [independent_average_split μ S]
  simp only [joinCoordinates_mem, average_const]

/-- Independent coordinates retain their individual laws under an
injective change of the index set. -/
lemma independent_average_embedding {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : κ → ι) (he : Function.Injective e) (μ : ι → FiniteLaw A)
    (f : (κ → A) → ℝ) :
    (independent μ).average (fun x => f (fun k => x (e k))) =
      (independent (fun k => μ (e k))).average f := by
  let S : Finset ι := univ.image e
  let E : κ ≃ S := Equiv.ofBijective
    (fun k => ⟨e k, mem_image.mpr ⟨k, mem_univ _, rfl⟩⟩) (by
      constructor
      · intro x y hxy
        exact he (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨k, _, hk⟩ := mem_image.mp y.property
        exact ⟨k, Subtype.ext hk⟩)
  calc
    _ = (independent (fun i : S => μ i)).average
        (fun x => f (fun k => x (E k))) :=
      independent_average_restrict μ S (fun x => f (fun k => x (E k)))
    _ = _ := by
      rw [independent_average_reindex E]
      simp only [E.symm_apply_apply]
      rfl

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)




lemma residue_average_padding (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : (data.Q → Fin B) → ℝ) :
    (data.residueLaw B hB).average (fun x => f (data.paddingRestriction x)) =
      (data.paddingResidueLaw B hB).average f := by
  have hi : Function.Injective data.paddingCoordinate := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : ↥(data.P ∪ data.Q) => z.val) hpq
  exact FiniteLaw.independent_average_embedding data.paddingCoordinate hi
    (fun p => uniformResidueLaw B p.val (data.prime p).pos (hB _ p.property)) f



lemma paddingResidueOrigin_spec (x : data.Q → Fin B) (p : data.Q) :
    (data.paddingResidueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_padding_residue_origin x).choose_spec p

/-- Padding-periodic observables at the full CRT lift depend only on the
independent padding coordinates, including after a fixed integer shift. -/
lemma residue_average_padding_shift (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (site : ℤ) (f : ℤ → ℝ)
    (hf : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → f n = f m) :
    (data.residueLaw B hB).average (fun x => f (data.residueOrigin x + site)) =
      (data.paddingResidueLaw B hB).average (fun x =>
        f (data.paddingResidueOrigin x + site)) := by
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        f (data.paddingResidueOrigin (data.paddingRestriction x) + site)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply hf
      intro q hq
      let p : data.Q := ⟨q, hq⟩
      rw [Int.cast_add, Int.cast_add]
      exact congrArg (fun z : ZMod q => z + (site : ZMod q))
        ((data.residueOrigin_spec x (data.paddingCoordinate p)).trans
          (data.paddingResidueOrigin_spec (data.paddingRestriction x) p).symm)
    _ = _ := data.residue_average_padding hB
      (fun x => f (data.paddingResidueOrigin x + site))

end ProhibitedPrimeFamily

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeTupleDivisors_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, ∑ p ∈ P j, 1 / (p : ℝ) := by
  rw [primeTupleDivisors, sum_image]
  · calc
      _ = ∑ x : (j : Fin J) → P j, ∏ j, 1 / ((x j).val : ℝ) := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = ∏ j, ∑ p : P j, 1 / (p.val : ℝ) :=
        (Fintype.prod_sum (fun j (p : P j) => 1 / (p.val : ℝ))).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        exact sum_coe_sort (P j) (fun p : ℕ => 1 / (p : ℝ))
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
namespace OAI

/-! Arithmetic support of the actual one-prime-per-band tuple family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeHarmonicMass_eq_sum (S : Finset ℕ) :
    primeHarmonicMass S = ∑ p ∈ S, 1 / (p : ℝ) := by
  unfold primeHarmonicMass
  simpa only [one_div] using sum_coe_sort S (fun p : ℕ => 1 / (p : ℝ))








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightIndependence
namespace OAI

/-! The retained departure weight is independent of tuple-prime residue draws.
Only the padding-prime residues enter its divisibility, density and cutoff data. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma squarefree_divisor_congr (Qp : Finset ℕ) (q : ℕ) (hq : Squarefree q)
    (hpool : q.primeFactors ⊆ Qp) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    (q : ℤ) ∣ n ↔ (q : ℤ) ∣ m := by
  rw [squarefree_divisor_iff q hq n, squarefree_divisor_iff q hq m]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    hnm p (hpool hp)]

lemma paddingDensity_eq_of_prime_residues (Qp Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (n m : ℤ) (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) (hg : g n = g m) :
    paddingDensity Q u eligible g n = paddingDensity Q u eligible g m := by
  unfold paddingDensity
  rw [hg]
  congr 1
  apply sum_congr rfl
  intro q hq
  simp only [squarefree_divisor_congr Qp q (hsq q hq) (hpool q hq) n m hnm]




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




lemma actualPaddingVertex_sq (Q : Finset ℕ) (n : ℤ) :
    actualPaddingVertex Q n ^ 2 = actualPaddingWeight Q n :=
  Real.sq_sqrt (zero_le_one.trans (actualPaddingWeight_one_le Q n))

lemma actualPaddingDegree_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingDegree Q n = actualPaddingDegree Q m := by
  unfold actualPaddingDegree
  congr 1
  ext p
  simp only [mem_filter]
  apply and_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]

lemma actualPaddingWeight_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingWeight Q n = actualPaddingWeight Q m := by
  unfold actualPaddingWeight
  rw [actualPaddingDegree_residue_congr Q n m hnm]

lemma actualPaddingVertex_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingVertex Q n = actualPaddingVertex Q m := by
  unfold actualPaddingVertex
  rw [actualPaddingWeight_residue_congr Q n m hnm]


lemma actualPaddingDegreeCut_residue_congr (Q : Finset ℕ) (L : ℝ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingDegreeCut Q L n ↔ actualPaddingDegreeCut Q L m := by
  unfold actualPaddingDegreeCut
  rw [actualPaddingDegree_residue_congr Q n m hnm]

lemma actualPaddingDegree_eq_available (Q : Finset ℕ) (n : ℤ) :
    actualPaddingDegree Q n =
      (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card := by
  rw [paddingAvailablePrimes_integer]
  rfl

lemma actualPaddingWeight_eq_tilt (Q : Finset ℕ) (n : ℤ) :
    actualPaddingWeight Q n = paddingTiltWeight Q (fun p => decide ((p.val : ℤ) ∣ n)) := by
  rw [paddingTiltWeight_eq_five_pow, ← paddingAvailablePrimes_card,
    ← actualPaddingDegree_eq_available]
  rfl

lemma actualPaddingWeight_eq_divisor_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℤ) :
    actualPaddingWeight Q n = ∑ q ∈ retainedPrimeDivisors Q,
      if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
  simpa only [actualPaddingWeight, actualPaddingDegree, actualPaddingCoefficient] using
    (padding_integer_weight_total Q hQ n).symm



lemma actualPaddingDensity_nonneg (Q : Finset ℕ) (D : Finset ℕ)
    (eligible : ℕ → Prop) (n : ℤ) :
    0 ≤ paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n := by
  unfold paddingDensity
  apply div_nonneg _ (sq_nonneg _)
  apply sum_nonneg
  intro q _
  split_ifs
  · exact actualPaddingCoefficient_nonneg q
  · exact le_rfl



lemma actualPaddingDensity_residue_congr (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (eligible : ℕ → Prop)
    (n m : ℤ) (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n =
      paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) m :=
  paddingDensity_eq_of_prime_residues Q D actualPaddingCoefficient eligible (actualPaddingVertex Q)
    (fun _ hq => retainedPrimeDivisor_squarefree Q hQ (hD hq))
    (fun _ hq => retainedPrimeDivisor_factors Q hQ (hD hq)) n m hnm
    (actualPaddingVertex_residue_congr Q n m hnm)

lemma actualPaddingKeep_residue_congr (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (eligible : ℕ → Prop)
    (L K : ℝ) (n m : ℤ) (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    integerEdgeKeep D actualPaddingCoefficient eligible (actualPaddingVertex Q) L K
        (actualPaddingDegreeCut Q L) n ↔
      integerEdgeKeep D actualPaddingCoefficient eligible (actualPaddingVertex Q) L K
        (actualPaddingDegreeCut Q L) m := by
  unfold integerEdgeKeep
  rw [actualPaddingDensity_residue_congr Q hQ D hD eligible n m hnm,
    actualPaddingDegreeCut_residue_congr Q L n m hnm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingResidues
namespace OAI

/-! The proved padding laws applied to the graph's actual integer
normalization and bin density at any common lift of the prime residues. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma actualPaddingAvailability_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    (fun p : Q => decide ((p.val : ℤ) ∣ n)) = paddingResidueAvailable Q B site z := by
  funext p
  have hd : (p.val : ℤ) ∣ n ↔ (p.val : ℤ) ∣ ((z p).val : ℤ) + site := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_add, Int.cast_natCast, hn p]
  simp only [paddingResidueAvailable, hd]

lemma actualPaddingWeight_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    actualPaddingWeight Q n = paddingTiltWeight Q (paddingResidueAvailable Q B site z) := by
  rw [actualPaddingWeight_eq_tilt, actualPaddingAvailability_lift Q B site z n hn]

lemma actualPaddingDegree_lift (Q : Finset ℕ) (B : ℕ) (site : ℤ)
    (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) :
    (actualPaddingDegree Q n : ℝ) = booleanCount (paddingResidueAvailable Q B site z) := by
  rw [actualPaddingDegree_eq_available, actualPaddingAvailability_lift Q B site z n hn,
    paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl



/-- Deleting vertices with more than `400 log L` padding primes has the
proved weighted probability cost for the literal graph normalization. -/
theorem ModFiveThetaInput.eventually_actual_padding_degree_tail (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (site : ℤ)
      (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B)
      (N : (paddingPrimeSupply E L → Fin B) → ℤ),
      (∀ z (p : paddingPrimeSupply E L),
        (N z : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
              if ¬actualPaddingDegreeCut (paddingPrimeSupply E L) L (N z) then 1 else 0) /
                paddingTiltNormalizer (paddingPrimeSupply E L) ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_padding_residue_degree_tail E] with L hL
  intro B site hQB N hN
  have he (z : paddingPrimeSupply E L → Fin B) :
      (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
          (if ¬actualPaddingDegreeCut (paddingPrimeSupply E L) L (N z) then 1 else 0) =
        paddingTiltWeight _ (paddingResidueAvailable _ B site z) *
          (if 400 * Real.log L < booleanCount (paddingResidueAvailable _ B site z)
            then 1 else 0) := by
    rw [actualPaddingVertex_sq, actualPaddingWeight_lift _ B site z (N z) (hN z)]
    simp only [actualPaddingDegreeCut, actualPaddingDegree_lift _ B site z (N z) (hN z), not_le]
  simp_rw [he]
  exact hL B site hQB

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingMarginal
namespace OAI

/-! The actual padding estimates under the full tuple-and-padding residue
law.  All dependence on the tuple coordinates is removed by the proved
product-law restriction identity. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)


lemma residue_average_padding_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (L : ℝ) :
    (data.residueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
        if ¬actualPaddingDegreeCut data.Q L (data.residueOrigin x + site) then 1 else 0) =
    (data.paddingResidueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.paddingResidueOrigin x + site)) ^ 2 *
        if ¬actualPaddingDegreeCut data.Q L (data.paddingResidueOrigin x + site) then 1 else 0) := by
  apply data.residue_average_padding_shift hB site (fun n =>
    (actualPaddingVertex data.Q n) ^ 2 *
      if ¬actualPaddingDegreeCut data.Q L n then 1 else 0)
  intro n m hnm
  rw [actualPaddingVertex_residue_congr data.Q n m hnm,
    actualPaddingDegreeCut_residue_congr data.Q L n m hnm]

end ProhibitedPrimeFamily


theorem ModFiveThetaInput.eventually_actual_family_padding_degree_tail
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ),
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          if ¬actualPaddingDegreeCut data.Q L (data.residueOrigin x + site) then 1 else 0) /
            paddingTiltNormalizer data.Q ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_actual_padding_degree_tail E] with L hb
  intro h J M B data hQ hB site
  rw [data.residue_average_padding_degree_tail hB site L]
  have hbQ : ∀ (Q : Finset ℕ), Q = paddingPrimeSupply E L →
      ∀ (hprime : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B)
        (N : (Q → Fin B) → ℤ),
      (∀ z (p : Q), (N z : ZMod p.val) =
        ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : Q => uniformResidueLaw B p.val
        (hprime p p.property).pos (hQB p p.property))).average (fun z =>
          (actualPaddingVertex Q (N z)) ^ 2 *
            if ¬actualPaddingDegreeCut Q L (N z) then 1 else 0) /
              paddingTiltNormalizer Q ≤ L ^ (-100 : ℝ) := by
    intro Q hQ hprime hQB N hN
    subst Q
    exact hb B site hQB N hN
  apply hbQ data.Q hQ data.primeQ (fun p hp => hB p (mem_union_right _ hp))
    (fun z => data.paddingResidueOrigin z + site)
  intro z p
  rw [Int.cast_add, data.paddingResidueOrigin_spec z p]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingCuts
namespace OAI

/-! Loss of padding mass from the actual graph density and degree
cutoffs.  The second moment is applied before discarding the large bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



/-- The bin densities form a subprobability distribution even after
restricting the available padding divisors. -/
lemma actualPaddingDensity_sum_le_one (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ)
    (η c : ℝ) (hη : 0 < η) (bins : Finset ℤ) :
    (∑ j ∈ bins, paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) n) ≤ 1 := by
  unfold paddingDensity
  rw [← sum_div, sum_comm, actualPaddingVertex_sq]
  apply (div_le_one (zero_lt_one.trans_le (actualPaddingWeight_one_le Q n))).mpr
  calc
    _ ≤ ∑ q ∈ D, if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum
      intro q _
      have he (j : ℤ) : actualPaddingBin η c j q ↔ paddingBin η c (Real.log q) = j :=
        (paddingBin_eq_iff η c (Real.log q) j hη).symm
      simp only [he]
      by_cases hd : (q : ℤ) ∣ n
      · simp only [hd, and_true]
        simp only [sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact actualPaddingCoefficient_nonneg q
      · simp only [hd, and_false, ite_false, sum_const_zero, le_refl]
    _ ≤ ∑ q ∈ retainedPrimeDivisors Q,
        if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum_of_subset_of_nonneg hD
      intro q _ _
      split_ifs
      · exact actualPaddingCoefficient_nonneg q
      · exact le_rfl
    _ = _ := (actualPaddingWeight_eq_divisor_sum Q hQ n).symm

lemma actualPadding_keep_loss (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ)
    (L K η c : ℝ) (hη : 0 < η) (bins : Finset ℤ) :
    (∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then
        paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex Q) n else 0) ≤
      (∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
        (actualPaddingBin η c j) (actualPaddingVertex Q) n then
          paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex Q) n else 0) +
        if ¬actualPaddingDegreeCut Q L n then 1 else 0 := by
  by_cases hc : actualPaddingDegreeCut Q L n
  · simp only [integerEdgeKeep, hc, and_true, not_le, not_true_eq_false,
      ite_false, add_zero, le_refl]
  · have hs := actualPaddingDensity_sum_le_one Q hQ D hD n η c hη bins
    have hp : 0 ≤ ∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
        (actualPaddingBin η c j) (actualPaddingVertex Q) n then
          paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex Q) n else 0 := by
      apply sum_nonneg
      intro j _
      split_ifs
      · exact actualPaddingDensity_nonneg Q D _ n
      · exact le_rfl
    simp only [integerEdgeKeep, hc, and_false, not_false_eq_true, ite_true]
    linarith

/-- Both literal vertex cutoffs together remove only `O(1/K) + L⁻¹⁰⁰`
of the normalized, padding-weighted mass, summed over all selected bins. -/
theorem ModFiveThetaInput.eventually_actual_padding_keep_loss
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (η c K : ℝ) (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient
            (actualPaddingBin η c j) (actualPaddingVertex data.Q) L K
            (actualPaddingDegreeCut data.Q L) (data.residueOrigin x + site) then
              paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
                (actualPaddingVertex data.Q) (data.residueOrigin x + site) else 0) /
                  paddingTiltNormalizer data.Q ≤ C / K + L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := hP.actual_family_padding_large_bin_cut E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hP.eventually_actual_family_padding_degree_tail E,
    eventually_ge_atTop (1 : ℝ)] with L ht hL
  intro η c K h J M B data hQ site bins hη hηone hK hB D hD
  let μ := data.residueLaw B hB
  let ρ := fun (x : ↥(data.P ∪ data.Q) → Fin B) j => paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
    (actualPaddingVertex data.Q) (data.residueOrigin x + site)
  let w := fun (x : ↥(data.P ∪ data.Q) → Fin B) => (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2
  let bad := fun (x : ↥(data.P ∪ data.Q) → Fin B) => if ¬actualPaddingDegreeCut data.Q L
    (data.residueOrigin x + site) then (1 : ℝ) else 0
  have hp := fun (x : ↥(data.P ∪ data.Q) → Fin B) => actualPadding_keep_loss data.Q data.primeQ D hD
    (data.residueOrigin x + site) L K η c hη bins
  calc
    _ ≤ (μ.average (fun x => w x *
          ∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) +
        μ.average (fun x => w x * bad x)) / paddingTiltNormalizer data.Q := by
      apply div_le_div_of_nonneg_right _ (paddingTiltNormalizer_pos data.Q).le
      calc
        _ ≤ μ.average (fun x => w x *
            ((∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) + bad x)) := by
          apply μ.average_mono
          intro x
          exact mul_le_mul_of_nonneg_left (hp x) (sq_nonneg _)
        _ = _ := by simp only [FiniteLaw.average, mul_add, sum_add_distrib]
    _ = μ.average (fun x => w x *
          ∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) / paddingTiltNormalizer data.Q +
        μ.average (fun x => w x * bad x) / paddingTiltNormalizer data.Q := add_div _ _ _
    _ ≤ C / K + L ^ (-100 : ℝ) := add_le_add
      (hb L η c K h J M B data hQ site bins hL hη hηone hK hB D hD)
      (ht h J M B data hQ hB site)

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







lemma positivePrimeWeight_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) (n : ℤ) :
    positivePrimeWeight S n =
      positiveCenterWeight (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP)
        (fun p => decide ((p.val : ℤ) ∣ n)) := by
  rw [positiveCenterWeight_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeWeight, decide_eq_true_eq]
    exact (prod_attach S (fun p : ℕ =>
      (if (p : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ))).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)

lemma positivePrimeNormalizer_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) :
    positivePrimeNormalizer S =
      positiveCenterNormalizer (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP) := by
  rw [positiveCenterNormalizer_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeNormalizer, mul_one_div]
    exact (prod_attach S (fun p : ℕ => (2 : ℝ) / p)).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)

lemma positivePrimeNormalizer_squarefree (d : ℕ) (hd : Squarefree d) :
    positivePrimeNormalizer d.primeFactors = (2 : ℝ) ^ d.primeFactors.card / d := by
  unfold positivePrimeNormalizer
  rw [prod_div_distrib, prod_const]
  congr 1
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]


namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingFactorization
namespace OAI

/-! Exact independence of tuple-prime and padding-prime observables under
the actual union residue law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_sum_product {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq ι] [DecidableEq κ]
    (μ : ι → FiniteLaw A) (ν : κ → FiniteLaw A)
    (f : (ι → A) → ℝ) (g : (κ → A) → ℝ) :
    (independent (Sum.elim μ ν)).average
      (fun x => f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))) =
      (independent μ).average f * (independent ν).average g := by
  let e := Equiv.sumArrowEquivProdArrow ι κ A
  calc
    _ = ∑ xy : (ι → A) × (κ → A),
        (independent (Sum.elim μ ν)).weight (Sum.elim xy.1 xy.2) * (f xy.1 * g xy.2) :=
      (e.symm.sum_comp (fun x => (independent (Sum.elim μ ν)).weight x *
        (f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, independent, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, average]
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      ring

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)



lemma residue_average_tuple_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : (data.P → Fin B) → ℝ) (g : (data.Q → Fin B) → ℝ) :
    (data.residueLaw B hB).average (fun x =>
      f (data.tupleRestriction x) * g (data.paddingRestriction x)) =
      (data.tupleResidueLaw B hB).average f *
        (data.paddingResidueLaw B hB).average g := by
  let e : data.P ⊕ data.Q → ↥(data.P ∪ data.Q) := Sum.elim
    (fun p => ⟨p.val, mem_union_left _ p.property⟩)
    (fun p => ⟨p.val, mem_union_right _ p.property⟩)
  have he : Function.Injective e := by
    intro x y hxy
    have hv := congrArg (fun p : ↥(data.P ∪ data.Q) => p.val) hxy
    cases x with
    | inl p =>
      cases y with
      | inl q => exact congrArg Sum.inl (Subtype.ext hv)
      | inr q =>
        exact False.elim (disjoint_left.mp data.disjoint p.property (hv.symm ▸ q.property))
    | inr p =>
      cases y with
      | inl q =>
        exact False.elim (disjoint_left.mp data.disjoint q.property (hv ▸ p.property))
      | inr q => exact congrArg Sum.inr (Subtype.ext hv)
  let μ := fun p : ↥(data.P ∪ data.Q) =>
    uniformResidueLaw B p.val (data.prime p).pos (hB _ p.property)
  have hμ : (fun i => μ (e i)) = Sum.elim
      (fun p : data.P => uniformResidueLaw B p.val (data.primeP _ p.property).pos
        (hB _ (mem_union_left _ p.property)))
      (fun p : data.Q => uniformResidueLaw B p.val (data.primeQ _ p.property).pos
        (hB _ (mem_union_right _ p.property))) := by
    funext i
    cases i <;> rfl
  have ht := FiniteLaw.independent_average_embedding e he μ
    (fun x => f (fun p => x (Sum.inl p)) * g (fun p => x (Sum.inr p)))
  rw [hμ, FiniteLaw.independent_average_sum_product] at ht
  exact ht

/-- Prime divisibility observables and an arbitrary padding-periodic
integer weight are independent at the same translated CRT origin. -/
lemma residue_average_prime_boolean_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
    (F : (data.P → Bool) → ℝ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
        g (data.residueOrigin x + site)) =
      (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F *
        (data.paddingResidueLaw B hB).average (fun z =>
          g (data.paddingResidueOrigin z + site)) := by
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        F (paddingResidueAvailable data.P B site (data.tupleRestriction x)) *
          g (data.paddingResidueOrigin (data.paddingRestriction x) + site)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply congrArg₂ (fun a b : ℝ => a * b)
      · apply congrArg F
        funext p
        change decide ((p.val : ℤ) ∣ data.residueOrigin x + site) =
          decide ((p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site)
        have hdiv : (p.val : ℤ) ∣ data.residueOrigin x + site ↔
            (p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site :=
          data.residueOrigin_divisibility x ⟨p.val, mem_union_left _ p.property⟩ site
        simp only [hdiv]
      · apply hg
        intro q hq
        let p : data.Q := ⟨q, hq⟩
        rw [Int.cast_add, Int.cast_add]
        exact congrArg (fun a : ZMod q => a + (site : ZMod q))
          ((data.residueOrigin_spec x (data.paddingCoordinate p)).trans
            (data.paddingResidueOrigin_spec (data.paddingRestriction x) p).symm)
    _ = (data.tupleResidueLaw B hB).average
        (fun z => F (paddingResidueAvailable data.P B site z)) *
          (data.paddingResidueLaw B hB).average
            (fun z => g (data.paddingResidueOrigin z + site)) :=
      data.residue_average_tuple_padding hB
        (fun z : data.P → Fin B => F (paddingResidueAvailable data.P B site z))
        (fun z : data.Q → Fin B => g (data.paddingResidueOrigin z + site))
    _ = _ := by
      congr 1
      exact padding_residue_average data.P B (fun p hp => (data.primeP p hp).two_le)
        (fun p hp => hB p (mem_union_left _ hp)) site F

lemma positive_prime_padding_average
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) * g (data.residueOrigin x + site)) =
      positivePrimeNormalizer S * (data.paddingResidueLaw B hB).average
        (fun z => g (data.paddingResidueOrigin z + site)) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  have hq0 (p : data.P) : 0 ≤ q p := by dsimp [q]; positivity
  have hq1 (p : data.P) : q p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (data.primeP p p.property).pos)).mpr
    exact_mod_cast (data.primeP p p.property).one_lt.le
  simp_rw [positivePrimeWeight_eq_selection data.P S hSP]
  rw [data.residue_average_prime_boolean_padding hB site (positiveCenterWeight q T) g hg]
  have hm : (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average
      (positiveCenterWeight q T) = positivePrimeNormalizer S := by
    simpa only [paddingOriginalLaw, paddingOriginalPrimeLaw, q, T] using
      (positive_center_tilt_total q T hq0 hq1).trans
        (positivePrimeNormalizer_eq_selection data.P S hSP).symm
  rw [hm]


end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingCutCost
namespace OAI

/-! The two padding deletions with the positive tuple weight retained.
The literal rejection function depends only on Q residues. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma paddingRejectedMass_residue_congr (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q)
    (bins : Finset ℤ) (η c L K : ℝ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    paddingRejectedMass Q D bins η c L K n = paddingRejectedMass Q D bins η c L K m := by
  unfold paddingRejectedMass
  rw [actualPaddingVertex_residue_congr Q n m hnm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [actualPaddingKeep_residue_congr Q hQ D hD (actualPaddingBin η c j) L K n m hnm,
    actualPaddingDensity_residue_congr Q hQ D hD (actualPaddingBin η c j) n m hnm]

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma positive_prime_padding_factor (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) * g (data.residueOrigin x + site)) =
      positivePrimeNormalizer S *
        (data.residueLaw B hB).average (fun x => g (data.residueOrigin x + site)) := by
  rw [data.positive_prime_padding_average hB S hSP site g hg,
    data.residue_average_padding_shift hB site g hg]

end ProhibitedPrimeFamily

theorem ModFiveThetaInput.eventually_positive_padding_cut_cost
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (η c K : ℝ) (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (bins : Finset ℤ),
      0 < η → η ≤ 1 → 0 < K →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (S : Finset ℕ), S ⊆ data.P →
      (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight S (data.residueOrigin x + site) *
          paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
              positivePrimeNormalizer S * (C / K + L ^ (-100 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hP.eventually_actual_padding_keep_loss E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro η c K h J M B data hQ hB site bins hη hηone hK D hD S hSP
  have hg := paddingRejectedMass_residue_congr data.Q data.primeQ D hD bins η c L K
  have he := data.positive_prime_padding_factor hB S hSP site
    (paddingRejectedMass data.Q D bins η c L K) hg
  rw [he]
  calc
    _ = positivePrimeNormalizer S *
        ((data.residueLaw B hB).average (fun x =>
          paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hb η c K h J M B data hQ site bins hη hηone hK hB D hD)
      (by unfold positivePrimeNormalizer; positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleDeletionNormalizer
namespace OAI

/-! Exact normalizers for summing the deletion estimates over the
one-prime-per-band tuple family and retained padding divisors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tuple_normalizer_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, positivePrimeNormalizer d.primeFactors) =
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  calc
    _ = ∑ d ∈ primeTupleDivisors P, (2 : ℝ) ^ J / d := by
      apply sum_congr rfl
      intro d hd
      have ha := primeTupleDivisors_arithmetic P hprime hdisjoint hd
      rw [positivePrimeNormalizer_squarefree d ha.1, ha.2.1]
    _ = (2 : ℝ) ^ J * ∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = _ := by rw [primeTupleDivisors_mass P hprime hdisjoint]; simp only [primeHarmonicMass_eq_sum]


lemma tuple_normalizer_sum_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (D : Finset ℕ) (hD : D ⊆ primeTupleDivisors P) :
    (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) ≤
      (2 : ℝ) ^ J * ∏ j, primeHarmonicMass (P j) := by
  rw [← tuple_normalizer_sum P hprime hdisjoint]
  exact sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by
    unfold positivePrimeNormalizer
    positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.VariablePaddingDeletion
namespace OAI

/-! Padding deletion with the bin-dependent integer interval lengths
used in the manuscript. The product model is summed only after each
bin has been transferred separately. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem ModFiveThetaInput.eventually_model_tuple_padding_deletion
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K → ∀ site : ℤ,
      (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hP.eventually_positive_padding_cut_cost E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h J M B data hQ hB P hPeq hprime hdisjoint D hD Q hQsub bins η K c hη hηone hK site
  have heach (d : ℕ) (hmem : d ∈ D) :
      (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
      positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) := by
    have hd := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hmem)
    exact hb η (c d) K h J M B data hQ hB site bins hη hηone hK Q hQsub
      d.primeFactors (hd.2.2.trans_eq hPeq)
  rw [(data.residueLaw B hB).average_finset_sum, sum_div]
  calc
    _ ≤ ∑ d ∈ D, positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) :=
      sum_le_sum heach
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * (C / K + L ^ (-100 : ℝ)) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
      (add_nonneg (div_nonneg hC.le hK.le) (Real.rpow_nonneg (by linarith) _))

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_model_tuple_padding_deletion := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_model_tuple_padding_deletion
