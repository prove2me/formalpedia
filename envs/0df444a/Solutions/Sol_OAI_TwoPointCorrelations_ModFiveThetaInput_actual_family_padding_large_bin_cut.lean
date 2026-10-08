-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.actual_family_padding_large_bin_cut
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:55:57.83155+00:00
-- url     : https://prove2.me/submissions/08e156d0-75fa-469e-9d45-e4c8033fd4b1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_padding_small_ball

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




lemma square_average_eq (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.average f) ^ 2 = μ.average (fun x => μ.average (fun y => f x * f y)) := by
  simp only [average, pow_two, mul_sum, sum_mul]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingSelectionLaw
namespace OAI

/-! The padding experiment has tilted prime availability `5/(p+4)` and,
given availability, two independent selections of probability `4/5`.
Its exact difference pushforward is the manuscript's three-point law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingPairLocal_average (p : ℕ) (hp : 2 ≤ p) (F : Fin 3 → ℝ) :
    (paddingPairLocal p hp).average (fun x => F (paddingPairDifference x)) =
      (paddingStepLaw p hp).average F := by
  have hd : (p : ℝ) + 4 ≠ 0 := by positivity
  simp only [FiniteLaw.average, paddingPairLocal, FiniteLaw.dependentProduct,
    paddingAvailabilityLaw, paddingSelectionLaw, booleanLaw, FiniteLaw.product,
    Fintype.sum_prod_type, Fintype.sum_bool, paddingPairDifference,
    paddingStepLaw, paddingDifferenceAtom_zero, paddingDifferenceAtom_one,
    paddingDifferenceAtom_two, Fin.sum_univ_three]
  norm_num
  field_simp
  ring

lemma paddingPairLocal_fiber (p : ℕ) (hp : 2 ≤ p) (e : Fin 3) :
    (paddingPairLocal p hp).probability (fun x => paddingPairDifference x = e) =
      (paddingStepLaw p hp).weight e := by
  have hh := paddingPairLocal_average p hp (fun x => if x = e then 1 else 0)
  simpa [FiniteLaw.probability, FiniteLaw.average] using hh


lemma paddingPairLaw_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Fin 3) → ℝ) :
    (paddingPairLaw Q hQ).average (fun x => F (fun p => paddingPairDifference (x p))) =
      (paddingDifferenceLaw Q hQ).average F :=
  FiniteLaw.independent_average_map
    (fun p : Q => paddingPairLocal p (hQ p p.property))
    (fun p : Q => paddingStepLaw p (hQ p p.property))
    (fun _ => paddingPairDifference)
    (fun p => paddingPairLocal_fiber p (hQ p p.property)) F

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingPairSampling
namespace OAI

/-! The local three-boolean experiment agrees with first choosing all
available primes and then independently choosing two padding divisors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma paddingPairLaw_weight (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (a b c : Q → Bool) :
    (paddingPairLaw Q hQ).weight (fun p => (a p, b p, c p)) =
      (paddingAvailableLaw Q hQ).weight a *
        (paddingDivisorLaw Q a).weight b * (paddingDivisorLaw Q a).weight c := by
  simp only [paddingPairLaw, paddingPairLocal, paddingAvailableLaw, paddingDivisorLaw,
    FiniteLaw.independent, FiniteLaw.dependentProduct, FiniteLaw.product]
  rw [prod_mul_distrib, prod_mul_distrib]
  ring

lemma paddingPairLaw_average_nested (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Bool) → (Q → Bool) → (Q → Bool) → ℝ) :
    (paddingPairLaw Q hQ).average
        (fun x => F (fun p => (x p).1) (fun p => (x p).2.1) (fun p => (x p).2.2)) =
      (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).average (fun c => F a b c))) := by
  calc
    _ = ∑ y : (Q → Bool) × ((Q → Bool) × (Q → Bool)),
        (paddingPairLaw Q hQ).weight (fun p => (y.1 p, y.2.1 p, y.2.2 p)) *
          F y.1 y.2.1 y.2.2 := by
      exact ((paddingTripleEquiv Q).symm.sum_comp
        (fun x => (paddingPairLaw Q hQ).weight x *
          F (fun p => (x p).1) (fun p => (x p).2.1) (fun p => (x p).2.2))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, paddingPairLaw_weight, FiniteLaw.average, mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro c _
      ring

lemma paddingPairDifference_value (Q : Finset ℕ) (x : Q → Bool × (Bool × Bool)) :
    paddingDifferenceValue Q (fun p => paddingPairDifference (x p)) =
      paddingLog Q (fun p => (x p).2.1) - paddingLog Q (fun p => (x p).2.2) := by
  unfold paddingDifferenceValue paddingLog
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  cases hb : (x p).2.1 <;> cases hc : (x p).2.2 <;>
    simp [paddingPairDifference, paddingDifferenceStep, hb, hc]

/-- Exact law of the difference of two conditionally sampled padding divisors. -/
theorem padding_pair_difference_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : ℝ → ℝ) :
    (paddingAvailableLaw Q hQ).average (fun a =>
      (paddingDivisorLaw Q a).average (fun b =>
        (paddingDivisorLaw Q a).average (fun c => F (paddingLog Q b - paddingLog Q c)))) =
      (paddingDifferenceLaw Q hQ).average (fun x => F (paddingDifferenceValue Q x)) := by
  rw [← paddingPairLaw_average_nested]
  simpa only [paddingPairDifference_value] using
    paddingPairLaw_average Q hQ (fun x => F (paddingDifferenceValue Q x))

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





lemma paddingTiltWeight_pos (Q : Finset ℕ) (a : Q → Bool) : 0 < paddingTiltWeight Q a := by
  apply prod_pos
  intro p _
  cases a p <;> norm_num

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

lemma paddingDivisorLaw_weight_eq (Q : Finset ℕ) (a b : Q → Bool) :
    (paddingDivisorLaw Q a).weight b =
      if PaddingSelectionSupported Q a b then
        paddingDivisorCoefficient Q b / paddingTiltWeight Q a else 0 := by
  have hw := paddingTiltWeight_pos Q a
  have hh := padding_divisor_weight Q a b
  by_cases hs : PaddingSelectionSupported Q a b
  · rw [if_pos hs] at hh ⊢
    exact (eq_div_iff hw.ne').mpr hh
  · rw [if_neg hs] at hh ⊢
    exact (mul_eq_zero.mp hh).resolve_right hw.ne'

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

lemma partial_collision_bound (μ : FiniteLaw α) (bin : α → β) (B : Finset β) :
    (∑ b ∈ B, (μ.probability (fun x => bin x = b)) ^ 2) ≤
      μ.average (fun x => μ.probability (fun y => bin x = bin y)) := by
  calc
    _ = μ.average (fun x => μ.average (fun y =>
        ∑ b ∈ B, (if bin x = b then 1 else 0) * (if bin y = b then 1 else 0))) := by
      simp only [average_finset_sum]
      apply sum_congr rfl
      intro b _
      simpa only [probability] using square_average_eq μ (fun x => if bin x = b then 1 else 0)
    _ ≤ _ := by
      apply μ.average_mono
      intro x
      apply μ.average_mono
      intro y
      change (∑ b ∈ B, (if bin x = b then (1 : ℝ) else 0) *
        (if bin y = b then 1 else 0)) ≤ if bin x = bin y then 1 else 0
      by_cases h : bin x = bin y
      · have he (b : β) :
            (if bin x = b then (1 : ℝ) else 0) * (if bin y = b then 1 else 0) =
              (if bin x = b then 1 else 0) := by
          by_cases hx : bin x = b <;> simp [hx, ← h]
        simp_rw [he]
        rw [if_pos h]
        by_cases hx : bin x ∈ B <;> simp [hx]
      · rw [if_neg h]
        apply le_of_eq
        apply sum_eq_zero
        intro b _
        by_cases hx : bin x = b
        · have hy : bin y ≠ b := fun hy => h (hx.trans hy.symm)
          simp [hx, hy]
        · simp [hx]

end FiniteLaw


lemma paddingBin_difference {η c x y : ℝ} (hη : 0 < η)
    (h : paddingBin η c x = paddingBin η c y) : |x - y| < η := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  have he : (x + c) / η - (y + c) / η = (x - y) / η := by ring
  rw [he, abs_div, abs_of_pos hη] at hh
  exact (div_lt_one hη).mp hh


lemma padding_bin_square_small_ball (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (η c : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (B : Finset ℤ) :
    (paddingAvailableLaw Q hQ).average (fun a =>
      ∑ j ∈ B, (paddingBinMass Q a η c j) ^ 2) ≤
        (paddingDifferenceLaw Q hQ).probability
          (fun x => |paddingDifferenceValue Q x| ≤ 1) := by
  calc
    _ ≤ (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).probability (fun d =>
            paddingBin η c (paddingLog Q b) = paddingBin η c (paddingLog Q d)))) := by
      apply FiniteLaw.average_mono
      intro a
      exact FiniteLaw.partial_collision_bound _ _ _
    _ ≤ (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).probability (fun d => |paddingLog Q b - paddingLog Q d| ≤ 1))) := by
      apply FiniteLaw.average_mono
      intro a
      apply FiniteLaw.average_mono
      intro b
      apply FiniteLaw.average_mono
      intro d
      by_cases h : paddingBin η c (paddingLog Q b) = paddingBin η c (paddingLog Q d)
      · have hd := (paddingBin_difference hη h).le.trans hη1
        simp [h, hd]
      · simp [h]
        split_ifs <;> norm_num
    _ = _ := padding_pair_difference_average Q hQ (fun z => if |z| ≤ 1 then 1 else 0)


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


lemma paddingSelectedDivisor_log (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) : Real.log (paddingSelectedDivisor Q b) = paddingLog Q b := by
  rw [paddingSelectedDivisor, Nat.cast_prod, Real.log_prod]
  · simp only [selectedCoordinates, sum_filter, paddingLog]
  · intro p _
    exact_mod_cast (hQ p p.property).ne_zero

lemma paddingBinMass_normalized_sum (Q : Finset ℕ) (a : Q → Bool)
    (η c : ℝ) (j : ℤ) :
    paddingBinMass Q a η c j = (paddingTiltWeight Q a)⁻¹ *
      ∑ b : Q → Bool,
        if PaddingSelectionSupported Q a b ∧ paddingBin η c (paddingLog Q b) = j
        then paddingDivisorCoefficient Q b else 0 := by
  simp only [paddingBinMass, FiniteLaw.probability, FiniteLaw.average,
    paddingDivisorLaw_weight_eq, mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases hs : PaddingSelectionSupported Q a b <;>
    by_cases hb : paddingBin η c (paddingLog Q b) = j <;>
      simp [hs, hb, div_eq_mul_inv, mul_comm]


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






lemma paddingBinMass_eq_literal (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (a : Q → Bool) (η c : ℝ) (j : ℤ) :
    paddingBinMass Q a η c j = literalPaddingBinMass Q a η c j := by
  rw [paddingBinMass_normalized_sum, paddingTiltWeight_eq_five_pow]
  unfold literalPaddingBinMass
  rw [paddingAvailablePrimes_card, zpow_neg, zpow_natCast]
  congr 1
  let F (q : retainedPrimeDivisors Q) : ℝ :=
    if q.val.primeFactors ⊆ paddingAvailablePrimes Q a ∧
        paddingBin η c (Real.log q.val) = j
    then (4 : ℝ) ^ q.val.primeFactors.card else 0
  calc
    _ = ∑ b : Q → Bool, F (paddingDivisorEquiv Q hQ b) := by
      apply sum_congr rfl
      intro b _
      change _ = if (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a ∧
        paddingBin η c (Real.log (paddingSelectedDivisor Q b)) = j
        then (4 : ℝ) ^ (paddingSelectedDivisor Q b).primeFactors.card else 0
      have hs := padding_supported_iff_primeFactors_subset Q hQ a b
      rw [paddingSelectedDivisor_primeFactors Q hQ b] at hs
      simp only [← hs,
        paddingSelectedDivisor_log Q hQ b, paddingSelectedDivisor_primeFactors Q hQ b,
        paddingAvailablePrimes_card, paddingDivisorCoefficient_eq_four_pow]
    _ = ∑ q : retainedPrimeDivisors Q, F q := (paddingDivisorEquiv Q hQ).sum_comp F
    _ = _ := by
      unfold F
      exact sum_coe_sort (retainedPrimeDivisors Q) (fun q : ℕ =>
        if q.primeFactors ⊆ paddingAvailablePrimes Q a ∧ paddingBin η c (Real.log q) = j
        then (4 : ℝ) ^ q.primeFactors.card else 0)



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


lemma literalPaddingBinMass_integer (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (η c : ℝ) (j : ℤ) (hη : 0 < η) :
    literalPaddingBinMass Q (fun p => decide ((p.val : ℤ) ∣ n)) η c j =
      integerPaddingBinMass Q n η c j := by
  unfold literalPaddingBinMass integerPaddingBinMass
  rw [paddingAvailablePrimes_integer]
  congr 1
  apply sum_congr rfl
  intro q hq
  rw [← paddingAvailablePrimes_integer Q n]
  simp only [padding_literal_support_iff_dvd Q hQ n q hq,
    paddingBin_eq_iff η c (Real.log q) j hη]


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

lemma padding_residue_bin_square_le (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (η c : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (bins : Finset ℤ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (hQ p p.property).pos (hQB p p.property))).average
        (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B n z) *
          ∑ j ∈ bins, (literalPaddingBinMass Q (paddingResidueAvailable Q B n z) η c j) ^ 2) /
            paddingTiltNormalizer Q ≤
      (paddingDifferenceLaw Q (fun p hp => (hQ p hp).two_le)).probability
        (fun x => |paddingDifferenceValue Q x| ≤ 1) := by
  simp_rw [← paddingBinMass_eq_literal Q hQ]
  rw [padding_residue_tilt Q B (fun p hp => (hQ p hp).two_le) hQB n
    (fun a => ∑ j ∈ bins, (paddingBinMass Q a η c j) ^ 2)]
  exact padding_bin_square_small_ball Q _ η c hη hη1 bins

/-- Literal residue-model `rho_j`, weighted by `w/S`, satisfies the padding
anti-concentration estimate uniformly in site and bin translation. -/
theorem ModFiveThetaInput.padding_residue_bin_square (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (B : ℕ) (n : ℤ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 →
      ∀ hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B,
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            paddingTiltWeight _ (paddingResidueAvailable _ B n z) *
              ∑ j ∈ bins, (literalPaddingBinMass _ (paddingResidueAvailable _ B n z) η c j) ^ 2) /
                paddingTiltNormalizer (paddingPrimeSupply E L) ≤ C / L := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_small_ball E
  refine ⟨C, hC, fun L η c B n bins hL hη hη1 hQB => ?_⟩
  exact (padding_residue_bin_square_le (paddingPrimeSupply E L) B
    (fun _ hp => paddingPrimeSupply_prime hp) hQB n η c hη hη1 bins).trans (hbound L hL)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingLargeBinCut
namespace OAI

/-! The squared-bin estimate gives the exact `O(1/K)` cost of deleting
bins whose padding density exceeds `K/L`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma large_nonnegative_value (r K L : ℝ) (hr : 0 ≤ r) (hK : 0 < K) (hL : 0 < L) :
    (if K / L < r then r else 0) ≤ (L / K) * r ^ 2 := by
  by_cases h : K / L < r
  · rw [if_pos h, div_mul_eq_mul_div]
    apply (le_div_iff₀ hK).mpr
    have hh := (div_lt_iff₀ hL).mp h
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hh.le)]
  · rw [if_neg h]
    positivity





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





end TwoPointCorrelations.ProhibitedPrimeFamily

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



/-- With all squarefree padding divisors available, the graph density is
exactly the literal normalized bin mass. -/
lemma actualPaddingDensity_eq_integerBin (Q : Finset ℕ) (n : ℤ) (η c : ℝ) (j : ℤ) :
    paddingDensity (retainedPrimeDivisors Q) actualPaddingCoefficient
      (actualPaddingBin η c j) (actualPaddingVertex Q) n =
      integerPaddingBinMass Q n η c j := by
  unfold paddingDensity integerPaddingBinMass
  rw [actualPaddingVertex_sq]
  change (∑ q ∈ retainedPrimeDivisors Q,
      if actualPaddingBin η c j q ∧ (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) /
        (5 : ℝ) ^ (Q.filter (fun p : ℕ => (p : ℤ) ∣ n)).card = _
  have hs : (∑ q ∈ retainedPrimeDivisors Q,
      if actualPaddingBin η c j q ∧ (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) =
      ∑ q ∈ retainedPrimeDivisors Q,
        if (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
            Real.log q + c < ((j : ℝ) + 1) * η
        then (4 : ℝ) ^ q.primeFactors.card else 0 := by
    apply sum_congr rfl
    intro q _
    have he : actualPaddingBin η c j q ∧ (q : ℤ) ∣ n ↔
        (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
          Real.log q + c < ((j : ℝ) + 1) * η := by
      unfold actualPaddingBin
      tauto
    simp only [he, actualPaddingCoefficient]
  rw [hs, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]

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


lemma actualPaddingDensity_le_integerBin (Q : Finset ℕ) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ) (η c : ℝ) (j : ℤ) :
    paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) n ≤ integerPaddingBinMass Q n η c j := by
  rw [← actualPaddingDensity_eq_integerBin Q n η c j]
  unfold paddingDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg hD
  intro q _ _
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


lemma actualPaddingBin_lift (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (B : ℕ) (site : ℤ) (z : Q → Fin B) (n : ℤ)
    (hn : ∀ p : Q, (n : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val))
    (η c : ℝ) (j : ℤ) (hη : 0 < η) :
    integerPaddingBinMass Q n η c j =
      literalPaddingBinMass Q (paddingResidueAvailable Q B site z) η c j := by
  rw [← literalPaddingBinMass_integer Q hQ n η c j hη,
    actualPaddingAvailability_lift Q B site z n hn]

/-- The literal graph density, including an arbitrary restriction on the
padding-divisor set, has the same squared-bin bound at any residue lift. -/
theorem ModFiveThetaInput.actual_padding_residue_bin_square (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (B : ℕ) (site : ℤ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 →
      ∀ (hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors (paddingPrimeSupply E L) →
      ∀ N : (paddingPrimeSupply E L → Fin B) → ℤ,
      (∀ z (p : paddingPrimeSupply E L),
        (N z : ZMod p.val) = ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            (actualPaddingVertex (paddingPrimeSupply E L) (N z)) ^ 2 *
              ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
                (actualPaddingVertex (paddingPrimeSupply E L)) (N z)) ^ 2) /
                  paddingTiltNormalizer (paddingPrimeSupply E L) ≤ C / L := by
  obtain ⟨C, hC, hb⟩ := hP.padding_residue_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c B site bins hL hη hηone hQB D hD N hN
  let Q := paddingPrimeSupply E L
  let μ := FiniteLaw.independent (fun p : Q =>
    uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos (hQB p p.property))
  calc
    _ ≤ μ.average (fun z => paddingTiltWeight Q (paddingResidueAvailable Q B site z) *
        ∑ j ∈ bins, (literalPaddingBinMass Q (paddingResidueAvailable Q B site z) η c j) ^ 2) /
          paddingTiltNormalizer Q := by
      apply div_le_div_of_nonneg_right _ (paddingTiltNormalizer_pos Q).le
      apply μ.average_mono
      intro z
      rw [actualPaddingVertex_sq, actualPaddingWeight_lift Q B site z (N z) (hN z)]
      apply mul_le_mul_of_nonneg_left _ (paddingTiltWeight_pos Q _).le
      apply sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (actualPaddingDensity_nonneg Q D (actualPaddingBin η c j) (N z))
      exact (actualPaddingDensity_le_integerBin Q D hD (N z) η c j).trans_eq
        (actualPaddingBin_lift Q (fun _ hp => paddingPrimeSupply_prime hp)
          B site z (N z) (hN z) η c j hη)
    _ ≤ C / L := hb L η c B site bins hL hη hηone hQB


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

lemma residue_average_padding_squares
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors data.Q) (site : ℤ)
    (η c : ℝ) (bins : Finset ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
        ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex data.Q) (data.residueOrigin x + site)) ^ 2) =
    (data.paddingResidueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.paddingResidueOrigin x + site)) ^ 2 *
        ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex data.Q) (data.paddingResidueOrigin x + site)) ^ 2) := by
  apply data.residue_average_padding_shift hB site (fun n =>
    (actualPaddingVertex data.Q n) ^ 2 * ∑ j ∈ bins,
      (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
        (actualPaddingVertex data.Q) n) ^ 2)
  intro n m hnm
  rw [actualPaddingVertex_residue_congr data.Q n m hnm]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [actualPaddingDensity_residue_congr data.Q data.primeQ D hD _ n m hnm]


end ProhibitedPrimeFamily

theorem ModFiveThetaInput.actual_family_padding_bin_square (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (h J M B : ℕ)
      (data : ProhibitedPrimeFamily h J M), data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex data.Q) (data.residueOrigin x + site)) ^ 2) /
              paddingTiltNormalizer data.Q ≤ C / L := by
  obtain ⟨C, hC, hb⟩ := hP.actual_padding_residue_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c h J M B data hQ site bins hL hη hηone hB D hD
  rw [data.residue_average_padding_squares hB D hD site η c bins]
  have hbQ : ∀ (Q : Finset ℕ), Q = paddingPrimeSupply E L →
      ∀ (hprime : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B)
        (N : (Q → Fin B) → ℤ),
      (∀ z (p : Q), (N z : ZMod p.val) =
        ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      D ⊆ retainedPrimeDivisors Q →
      (FiniteLaw.independent (fun p : Q => uniformResidueLaw B p.val
        (hprime p p.property).pos (hQB p p.property))).average (fun z =>
          (actualPaddingVertex Q (N z)) ^ 2 * ∑ j ∈ bins,
            (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
              (actualPaddingVertex Q) (N z)) ^ 2) / paddingTiltNormalizer Q ≤ C / L := by
    intro Q hQ hprime hQB N hN hD
    subst Q
    exact hb L η c B site bins hL hη hηone hQB D hD N hN
  apply hbQ data.Q hQ data.primeQ (fun p hp => hB p (mem_union_right _ hp))
    (fun z => data.paddingResidueOrigin z + site) _ hD
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

lemma FiniteLaw.weighted_large_bin_cut {A I : Type*} [Fintype A]
    (μ : FiniteLaw A) (bins : Finset I) (weight : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a) (ρ : A → I → ℝ)
    (hρ : ∀ a j, 0 ≤ ρ a j) (K L : ℝ) (hK : 0 < K) (hL : 0 < L) :
    μ.average (fun a => weight a *
      ∑ j ∈ bins, if K / L < ρ a j then ρ a j else 0) ≤
      (L / K) * μ.average (fun a => weight a * ∑ j ∈ bins, (ρ a j) ^ 2) := by
  calc
    _ ≤ μ.average (fun a => weight a *
        ∑ j ∈ bins, (L / K) * (ρ a j) ^ 2) := by
      apply μ.average_mono
      intro a
      apply mul_le_mul_of_nonneg_left _ (hw a)
      exact sum_le_sum (fun j _ => large_nonnegative_value (ρ a j) K L (hρ a j) hK hL)
    _ = _ := by
      simp only [← mul_sum, FiniteLaw.average]
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring

theorem ModFiveThetaInput.actual_family_padding_large_bin_cut (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c K : ℝ) (h J M B : ℕ)
      (data : ProhibitedPrimeFamily h J M), data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 → 0 < K →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
            (actualPaddingBin η c j) (actualPaddingVertex data.Q) (data.residueOrigin x + site)
            then paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
              (actualPaddingVertex data.Q) (data.residueOrigin x + site) else 0) /
                paddingTiltNormalizer data.Q ≤ C / K := by
  obtain ⟨C, hC, hb⟩ := hP.actual_family_padding_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c K h J M B data hQ site bins hL hη hηone hK hB D hD
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let μ := data.residueLaw B hB
  let ρ := fun (x : ↥(data.P ∪ data.Q) → Fin B) j => paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
    (actualPaddingVertex data.Q) (data.residueOrigin x + site)
  let w := fun (x : ↥(data.P ∪ data.Q) → Fin B) => (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2
  have hs := μ.weighted_large_bin_cut bins w (fun x => sq_nonneg _) ρ
    (fun x j => actualPaddingDensity_nonneg data.Q D _ _) K L hK hLp
  calc
    _ ≤ ((L / K) * μ.average (fun x => w x * ∑ j ∈ bins, (ρ x j) ^ 2)) /
        paddingTiltNormalizer data.Q :=
      div_le_div_of_nonneg_right hs (paddingTiltNormalizer_pos data.Q).le
    _ = (L / K) * (μ.average (fun x => w x * ∑ j ∈ bins, (ρ x j) ^ 2) /
        paddingTiltNormalizer data.Q) := by ring
    _ ≤ (L / K) * (C / L) := mul_le_mul_of_nonneg_left
      (hb L η c h J M B data hQ site bins hL hη hηone hB D hD)
      (div_nonneg hLp.le hK.le)
    _ = C / K := by field_simp




end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.actual_family_padding_large_bin_cut := @OAI.TwoPointCorrelations.ModFiveThetaInput.actual_family_padding_large_bin_cut
