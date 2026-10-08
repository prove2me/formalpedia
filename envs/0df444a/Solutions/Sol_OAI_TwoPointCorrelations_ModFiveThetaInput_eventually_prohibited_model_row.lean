-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_prohibited_model_row
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:44:08.189548+00:00
-- url     : https://prove2.me/submissions/a6b035f7-1b89-4562-ac8a-e3a1d8518a7b

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

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

lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num



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


lemma dependentIndependent_average_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (μ : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → ℝ) :
    (dependentIndependent μ).average (fun x => ∏ i, f i (x i)) =
      ∏ i, (μ i).average (f i) := by
  simp only [average, dependentIndependent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm


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



lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ





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

/-- The concrete centered-prime supplies have reciprocal mass in `[W,2W]`
once their lower logarithmic endpoint exceeds one fixed threshold. -/
theorem ModFiveThetaInput.centered_band_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      W ≤ (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ∧
      (∑ p ∈ modFivePrimeBand E true (Real.exp A)
        (Real.exp (A * Real.exp (6 * W))), 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨K, hK, h⟩ := hP.band_error E
  refine ⟨max 1 (8 * K / W), le_max_left _ _, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hB : A ≤ A * Real.exp (6 * W) := by
    have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 6 * W)) hA0.le
    simpa only [mul_one] using hh
  have hmass := h true A (A * Real.exp (6 * W)) hA1 hB
  have he : Real.log (A * Real.exp (6 * W)) - Real.log A = 6 * W := by
    rw [Real.log_mul hA0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [he] at hmass
  have hsmall : 4 * K / A ≤ W / 2 := by
    have hh := (div_le_iff₀ hW).mp ((le_max_right 1 (8 * K / W)).trans hA)
    apply (div_le_iff₀ hA0).mpr
    nlinarith [hh]
  have hh := abs_le.mp hmass
  norm_num [modFiveDensity] at hh
  simp only [one_div]
  constructor <;> linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
namespace OAI

/-! Actual disjoint prime supplies at geometric logarithmic scales. Their
mass follows from the published fixed-modulus input through the proved
partial-summation chain, and all support assertions are finite identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma primeSupplyEndpoint_zero (A W : ℝ) : primeSupplyEndpoint A W 0 = A := by
  simp [primeSupplyEndpoint]

lemma primeSupplyEndpoint_succ (A W : ℝ) (i : ℕ) :
    primeSupplyEndpoint A W (i + 1) = primeSupplyEndpoint A W i * Real.exp (6 * W) := by
  unfold primeSupplyEndpoint
  rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
  ring








/-- Every centered supply is nonempty and has the required reciprocal mass.
The threshold is independent of the number of supplies and their indices. -/
theorem ModFiveThetaInput.centered_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ i : ℕ,
      (centeredPrimeSupply E A W i).Nonempty ∧
      W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W := by
  obtain ⟨A₀, hA₀, hmass⟩ := hP.centered_band_mass E W hW
  refine ⟨A₀, hA₀, fun A hA i => ?_⟩
  have hA0 : 0 ≤ A := (zero_le_one.trans hA₀).trans hA
  have hlower : A₀ ≤ primeSupplyEndpoint A W i := by
    calc
      A₀ ≤ A := hA
      _ = primeSupplyEndpoint A W 0 := (primeSupplyEndpoint_zero A W).symm
      _ ≤ _ := primeSupplyEndpoint_mono A W hA0 hW.le (Nat.zero_le _)
  have hh := hmass (primeSupplyEndpoint A W i) hlower
  rw [← primeSupplyEndpoint_succ] at hh
  change W ≤ (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ∧
      (∑ p ∈ centeredPrimeSupply E A W i, 1 / (p : ℝ)) ≤ 2 * W at hh
  refine ⟨?_, hh⟩
  by_contra he
  rw [not_nonempty_iff_eq_empty.mp he, sum_empty] at hh
  linarith [hh.1]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeSupplyScale_endpoint (W L : ℝ) (hW : 0 < W) (hL : 1 ≤ L) :
    primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (primeSupplyCount W L : ℝ) ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W) :=
    Nat.floor_le (by positivity)
  have hj' := (le_div_iff₀ (by positivity : 0 < 6 * W)).mp hj
  unfold primeSupplyEndpoint
  calc
    _ = Real.exp (Real.log L * (199 / 200 : ℝ) + 6 * W * primeSupplyCount W L) := by
      rw [Real.rpow_def_of_pos hLp, Real.exp_add]
    _ ≤ Real.exp (Real.log L) := Real.exp_le_exp.mpr (by nlinarith)
    _ = L := Real.exp_log hLp

lemma eventually_primeSupplyCount_pos (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (1200 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 1200 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : (0 : ℝ) ≤ 1200 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

theorem ModFiveThetaInput.eventually_actual_prime_supplies (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ primeSupplyCount W L ∧
      primeSupplyEndpoint (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) ≤ L ∧
      ∀ i : ℕ, (centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i).Nonempty ∧
        W ≤ (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ∧
        (∑ p ∈ centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W i, 1 / (p : ℝ)) ≤ 2 * W := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨A₀, _, hmass⟩ := hP.centered_supplies E W hWp
  have hlarge := (tendsto_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop A₀)
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_primeSupplyCount_pos W hWp,
    hlarge] with L hL hJ hA
  exact ⟨hJ, primeSupplyScale_endpoint W L hWp hL,
    hmass (L ^ (199 / 200 : ℝ)) hA⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical







lemma FiniteLaw.independent_average_coordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (μ : ι → FiniteLaw A) (i : ι) (f : A → ℝ) :
    (FiniteLaw.independent μ).average (fun x => f (x i)) = (μ i).average f := by
  have hh := FiniteLaw.independent_average_product μ (fun j x => if j = i then f x else 1)
  have he (j : ι) : (μ j).average (fun x => if j = i then f x else 1) =
      if j = i then (μ i).average f else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simpa only [he, prod_ite_eq', mem_univ, ite_true] using hh



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry
namespace OAI

/-! Perfect blocks use only the lit divisibilities at their actual positions. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem positiveWord_iff_departures (h : ℕ) (x : ℤ) (w : List SignedStep) :
    PositiveWord h x w ↔ ∀ i : Fin w.length,
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rw [positiveWord_cons, ih]
      constructor
      · rintro ⟨ha, hw⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
              wordDisplacement_cons, add_assoc] using hw ⟨i, by simpa using hi⟩
      · intro hw
        refine ⟨?_, ?_⟩
        · simpa using hw ⟨0, by simp⟩
        · intro i
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
            wordDisplacement_cons, add_assoc] using hw ⟨i.val + 1, by simp⟩



namespace ColumnWordPattern

variable {α : Type*} [Fintype α] [DecidableEq α]


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






lemma stepWord_covered (pairs : Finset (ℕ × ℕ)) (s : ℕ) (w : List SignedStep)
    (hlen : w.length ≤ s) (hpairs : ∀ a ∈ w, (a.tuple, a.padding) ∈ pairs) :
    ∃ c : BoundedStepWords pairs s, decodeStepWord c = w := by
  let f : Fin w.length → StepAlphabet pairs := fun i =>
    ⟨(w.get i).forward, ⟨((w.get i).tuple, (w.get i).padding), hpairs _ (List.get_mem _ _)⟩⟩
  refine ⟨⟨⟨w.length, by omega⟩, f⟩, ?_⟩
  change List.ofFn (fun i : Fin w.length => decodeStep (f i)) = w
  have he : (fun i : Fin w.length => decodeStep (f i)) = w.get := by
    funext i
    cases hw : w.get i
    simp only [f, decodeStep, hw]
  rw [he, List.ofFn_get]








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

lemma positiveWord_iff_prime_tests (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple)) :
    PositiveWord h n w ↔ ∀ i : Fin w.length,
      ∀ p ∈ ((w.get i).padding * (w.get i).tuple).primeFactors,
        (p : ℤ) ∣ n + wordDisplacement h (w.take i.val) := by
  rw [positiveWord_iff_departures]
  apply forall_congr'
  intro i
  simpa only [SignedStep.divisor, Nat.cast_mul] using
    squarefree_divisor_iff _ (hsq _ (List.get_mem _ _)) (n + wordDisplacement h (w.take i.val))







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


lemma mem_wordDivisorPrimeSupport (w : List SignedStep) (p : ℕ) :
    p ∈ wordDivisorPrimeSupport w ↔
      ∃ k : Fin w.length, p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors := by
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset]
  exact List.exists_mem_iff_get


/-- A residue test is exact arithmetic positivity at any common integer lift. -/
theorem residuePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    ResiduePositiveWord p h w r ↔ PositiveWord h n w := by
  rw [positiveWord_iff_prime_tests h n w hsq]
  constructor
  · intro hr k q hq
    have hmem : q ∈ wordDivisorPrimeSupport w :=
      (mem_wordDivisorPrimeSupport w q).mpr ⟨k, hq⟩
    obtain ⟨i, rfl⟩ := hcover q hmem
    exact (residue_offset_divisibility (r i) n _ (hn i)).mpr (hr k i hq)
  · intro hn' k i hi
    exact (residue_offset_divisibility (r i) n _ (hn i)).mp (hn' k (p i) hi)



/-- The finite catalog's modular event is exactly the deleted event at any
common integer lift. Minimality remains in the catalog, not in the random law. -/
theorem prohibited_residue_catalog_iff {ι : Type*} (p : ι → ℕ)
    (pairs : Finset (ℕ × ℕ)) (h s : ℕ) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ dq ∈ pairs, Squarefree (dq.2 * dq.1))
    (hcover : ∀ c : ProhibitedCatalog pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), ∃ i, p i = q) :
    (∃ c : ProhibitedCatalog pairs h s, ResiduePositiveWord p h (decodeStepWord c.val) r) ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ pairs) n := by
  have he (c : ProhibitedCatalog pairs h s) :
      ResiduePositiveWord p h (decodeStepWord c.val) r ↔
        PositiveWord h n (decodeStepWord c.val) :=
    residuePositiveWord_iff p h _ r n hn
      (fun a ha => hsq _ (c.property.1.2.2.1 a ha)) (hcover c)
  simp_rw [he]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨decodeStepWord c.val, hc, c.property⟩
  · rintro ⟨w, hw, hmin⟩
    obtain ⟨c, hc⟩ := stepWord_covered pairs s w hmin.1.2.1 hmin.1.2.2.1
    refine ⟨⟨c, ?_⟩, ?_⟩
    · simpa only [hc] using hmin
    · simpa only [hc] using hw


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
namespace OAI

/-! Density of the actual deleted event, with all finite catalog costs included. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace ProhibitedPrimeFamily

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)


lemma whole_squarefree (dq : ℕ × ℕ) (hdq : dq ∈ F.pairs) : Squarefree (dq.2 * dq.1) := by
  apply (Nat.squarefree_mul ?_).mpr
  · exact ⟨F.padding_squarefree _ hdq, F.tuple_squarefree _ hdq⟩
  · apply (Nat.disjoint_primeFactors (F.padding_squarefree _ hdq).ne_zero
      (F.tuple_squarefree _ hdq).ne_zero).mp
    exact F.disjoint.symm.mono (F.padding_pool _ hdq) (F.tuple_pool _ hdq)




/-- The finite-residue event is precisely the manuscript's prohibited-site
predicate at any common integer lift of those same coordinates. -/
lemma deletedEvent_iff (s B : ℕ) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    F.deletedEvent s B x ↔ ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs) n := by
  apply prohibited_residue_catalog_iff (fun p : ↥(F.P ∪ F.Q) => p.val) F.pairs h s _ n hn
    F.whole_squarefree
  intro c q hq
  exact ⟨⟨q, F.support_subset s c hq⟩, rfl⟩


end ProhibitedPrimeFamily

open _root_.Filter


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







lemma paddingResidueOrigin_spec (x : data.Q → Fin B) (p : data.Q) :
    (data.paddingResidueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_padding_residue_origin x).choose_spec p


end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidueTranslation
namespace OAI

/-! Translation invariance of the actual product law on the padded carrier. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma translateResidue_cast (B p : ℕ) [NeZero p] (hpB : p ≤ B)
    (c : ℤ) (x : Fin B) :
    ((translateResidue B p hpB c x).val : ZMod p) = (x.val : ZMod p) + (c : ZMod p) := by
  exact ZMod.natCast_zmod_val _

theorem uniformResidueLaw_translate (B p : ℕ) [NeZero p] (hp : 0 < p) (hpB : p ≤ B)
    (c : ℤ) (y : Fin B) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => translateResidue B p hpB c x = y) =
      (uniformResidueLaw B p hp hpB).weight y := by
  by_cases hy : y.val < p
  · have he (x : Fin B) : translateResidue B p hpB c x = y ↔
        (x.val : ZMod p) = (y.val : ZMod p) - (c : ZMod p) := by
      rw [eq_sub_iff_add_eq]
      constructor
      · intro hxy
        rw [← translateResidue_cast B p hpB c x, hxy]
      · intro hxy
        apply Fin.ext
        have hv := congrArg ZMod.val hxy
        simpa only [translateResidue, ZMod.val_natCast_of_lt hy] using hv
    have heq : (fun x => translateResidue B p hpB c x = y) =
        (fun x : Fin B => (x.val : ZMod p) = (y.val : ZMod p) - (c : ZMod p)) :=
      funext (fun x => propext (he x))
    rw [heq, uniformResidueLaw_mod_eq, uniformResidueLaw_weight B p hp hpB y hy]
  · have hn (x : Fin B) : translateResidue B p hpB c x ≠ y := by
      intro hxy
      have hx : (translateResidue B p hpB c x).val < p := ZMod.val_lt _
      exact hy (hxy ▸ hx)
    simp [FiniteLaw.probability, FiniteLaw.average, hn, uniformResidueLaw, hy]

theorem independent_residue_translate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B) (c : ℤ)
    (f : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => f (fun i => translateResidue B (p i) (hpB i) c (x i))) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average f := by
  exact FiniteLaw.independent_average_map _ _ _
    (fun i y => uniformResidueLaw_translate B (p i) (hp i) (hpB i) c y) f

theorem ProhibitedPrimeFamily.residue_average_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : ℤ → ℝ)
    (hf : ∀ n m, (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
      f n = f m) (c : ℤ) :
    (data.residueLaw B hB).average (fun x => f (data.residueOrigin x + c)) =
      (data.residueLaw B hB).average (fun x => f (data.residueOrigin x)) := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  let translate (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :=
    translateResidue B p.val (hB _ p.property) c (x p)
  calc
    _ = (data.residueLaw B hB).average (fun x => f (data.residueOrigin (translate x))) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply hf
      intro p
      rw [Int.cast_add, data.residueOrigin_spec, data.residueOrigin_spec]
      exact (translateResidue_cast B p.val (hB _ p.property) c (x p)).symm
    _ = _ := independent_residue_translate B (fun p : ↥(data.P ∪ data.Q) => p.val)
      (fun p => (data.prime p).pos) (fun p => hB _ p.property) c
      (fun x => f (data.residueOrigin x))

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeFamily
namespace OAI

/-! The prohibited-word data are constructed from the actual prime bands,
not assumed. Padding divisors have the requested degree cap, and the
finite pair catalog can impose any numerical eligibility condition. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical








lemma centeredPrimeBand_subset_pool (E : Finset ℕ) (A W : ℝ) (J : ℕ) (j : Fin J) :
    centeredPrimeBands E A W J j ⊆ centeredPrimePool E A W J := by
  intro p hp
  exact mem_primeTuplePool.mpr ⟨j, hp⟩






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

theorem ModFiveThetaInput.eventually_padding_pool_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop,
      primeHarmonicMass (paddingPrimeSupply E L) ≤ Real.log L := by
  obtain ⟨C, hC, hm⟩ := hP.padding_reciprocal_mass E
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp (4 * C))]
      with L hL hLC
  have hlog : 4 * C ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hLC
  rw [primeHarmonicMass_eq_sum]
  linarith [hm L hL]






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





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedWeightPeriodicity
namespace OAI

/-! The literal masked arithmetic weights depend only on the finite prime residues. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma ProhibitedPrimeFamily.prohibitedSite_congr {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) m := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  let x (p : ↥(data.P ∪ data.Q)) : Fin B :=
    ⟨(n : ZMod p.val).val, (ZMod.val_lt _).trans_le (hB _ p.property)⟩
  have hn (p : ↥(data.P ∪ data.Q)) : (n : ZMod p.val) = ((x p).val : ZMod p.val) :=
    (ZMod.natCast_zmod_val _).symm
  exact (data.deletedEvent_iff s B x n hn).symm.trans
    (data.deletedEvent_iff s B x m (fun p => (hnm p).symm.trans (hn p)))



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





lemma positivePrimeWeight_nonneg (S : Finset ℕ) (n : ℤ) :
    0 ≤ positivePrimeWeight S n := by
  apply prod_nonneg
  intro p _
  split_ifs <;> positivity





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



end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeRowSecondMoment
namespace OAI

/-! Finite second moments for the positive row majorant used to delete
rare sites. Independence is used only under the auxiliary product law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma average_add {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.average (fun x => f x + g x) = μ.average f + μ.average g := by
  simp only [average, mul_add, sum_add_distrib]

lemma independent_average_coordinate_mul {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (μ : ι → FiniteLaw α) (i j : ι) (hij : i ≠ j) (f g : α → ℝ) :
    (independent μ).average (fun x => f (x i) * g (x j)) =
      (μ i).average f * (μ j).average g := by
  let F : ι → α → ℝ := fun k a =>
    (if k = i then f a else 1) * (if k = j then g a else 1)
  have he (x : ι → α) : (∏ k, F k (x k)) = f (x i) * g (x j) := by
    simp only [F, prod_mul_distrib]
    simp
  have hm (k : ι) : (μ k).average (F k) =
      (if k = i then (μ i).average f else 1) *
        (if k = j then (μ j).average g else 1) := by
    by_cases hki : k = i
    · subst k
      simp [F, hij]
    · by_cases hkj : k = j
      · subst k
        simp [F, hki]
      · simp [F, hki, hkj]
  calc
    _ = (independent μ).average (fun x => ∏ k, F k (x k)) := by simp only [he]
    _ = ∏ k, (μ k).average (F k) := independent_average_product μ F
    _ = _ := by simp only [hm, prod_mul_distrib]; simp

end FiniteLaw

lemma booleanLaw_indicator_average (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => if b then (1 : ℝ) else 0) = q := by
  simp [booleanLaw, FiniteLaw.average]

lemma independent_boolean_count_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      booleanCount = ∑ i, q i := by
  rw [show booleanCount = (fun a : ι → Bool => ∑ i, if a i then (1 : ℝ) else 0) from rfl,
    FiniteLaw.average_sum]
  apply sum_congr rfl
  intro i _
  rw [FiniteLaw.independent_average_coordinate
    (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
    (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]

lemma independent_boolean_count_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  have hp (i j : ι) : μ.average (fun a =>
      (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0)) ≤
        q i * q j + if i = j then q i else 0 := by
    by_cases hij : i = j
    · subst j
      have he (a : ι → Bool) :
          (if a i then (1 : ℝ) else 0) * (if a i then 1 else 0) =
            if a i then 1 else 0 := by cases a i <;> norm_num
      simp only [he, ite_true]
      rw [FiniteLaw.independent_average_coordinate
        (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
        (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]
      nlinarith [sq_nonneg (q i)]
    · simp only [hij, ite_false, add_zero]
      exact le_of_eq ((FiniteLaw.independent_average_coordinate_mul
        (fun i => booleanLaw (q i) (hq0 i) (hq1 i)) i j hij
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0)).trans
          (by rw [booleanLaw_indicator_average, booleanLaw_indicator_average]))
  have he (a : ι → Bool) : (booleanCount a) ^ 2 =
      ∑ i, ∑ j, (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0) := by
    simp only [booleanCount, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
  change μ.average (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i
  simp_rw [he, μ.average_sum]
  calc
    _ ≤ ∑ i, ∑ j, (q i * q j + if i = j then q i else 0) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true, ← sum_mul]
      ring

lemma independent_boolean_shifted_count_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => (booleanCount a + ∑ i, q i) ^ 2) ≤
        4 * (∑ i, q i) ^ 2 + ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have he (a : ι → Bool) : (booleanCount a + V) ^ 2 =
      (booleanCount a) ^ 2 + booleanCount a * (2 * V) + V ^ 2 := by ring
  change μ.average (fun a => (booleanCount a + V) ^ 2) ≤ 4 * V ^ 2 + V
  simp_rw [he]
  rw [μ.average_add, μ.average_add, μ.average_mul_const, μ.average_const]
  have hm := independent_boolean_count_average q hq0 hq1
  have hs := independent_boolean_count_square q hq0 hq1
  change μ.average booleanCount = V at hm
  change μ.average (fun a => (booleanCount a) ^ 2) ≤ V ^ 2 + V at hs
  change μ.average (fun a => (booleanCount a) ^ 2) +
      μ.average booleanCount * (2 * V) + V ^ 2 ≤ 4 * V ^ 2 + V
  rw [hm]
  nlinarith

lemma padding_weight_square_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (paddingOriginalLaw Q hQ).average (fun a => (paddingTiltWeight Q a) ^ 2) =
      ∏ p : Q, (1 + 24 / (p.val : ℝ)) := by
  have he (a : Q → Bool) : (paddingTiltWeight Q a) ^ 2 =
      ∏ p : Q, if a p then (25 : ℝ) else 1 := by
    rw [paddingTiltWeight, ← prod_pow]
    apply prod_congr rfl
    intro p _
    cases a p <;> norm_num
  simp_rw [he]
  rw [paddingOriginalLaw, FiniteLaw.independent_average_product
    (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))
    (fun _ b => if b then (25 : ℝ) else 1)]
  apply prod_congr rfl
  intro p _
  simp [paddingOriginalPrimeLaw, booleanLaw, FiniteLaw.average]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeRowMoments
namespace OAI

/-! Group the disjoint prime bands before taking their row moments. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_grouped {ι A : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [Fintype A]
    (μ : (i : ι) → κ i → FiniteLaw A) (F : ((i : ι) → κ i → A) → ℝ) :
    (independent (fun p : Sigma κ => μ p.1 p.2)).average
      (fun x => F (fun i k => x ⟨i, k⟩)) =
        (dependentIndependent (fun i => independent (μ i))).average F := by
  let e := Equiv.piCurry (fun (i : ι) (_ : κ i) => A)
  calc
    _ = ∑ x : (i : ι) → κ i → A,
        (independent (fun p : Sigma κ => μ p.1 p.2)).weight (e.symm x) * F x :=
      (e.symm.sum_comp (fun x : Sigma κ → A =>
        (independent (fun p : Sigma κ => μ p.1 p.2)).weight x *
          F (fun i k => x ⟨i, k⟩))).symm
    _ = _ := by
      simp only [average, dependentIndependent, independent, Fintype.prod_sigma]
      rfl

lemma independent_average_disjoint_products {ι I A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    {κ : I → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [Fintype A]
    (μ : ι → FiniteLaw A) (e : (i : I) → κ i → ι)
    (he : Function.Injective (fun p : Sigma κ => e p.1 p.2))
    (f : (i : I) → (κ i → A) → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (fun k => x (e i k))) =
      ∏ i, (independent (fun k => μ (e i k))).average (f i) := by
  have hb := independent_average_embedding (fun p : Sigma κ => e p.1 p.2) he μ
    (fun x : Sigma κ → A => ∏ i, f i (fun k => x ⟨i, k⟩))
  rw [independent_average_grouped (fun i k => μ (e i k))
    (fun x => ∏ i, f i (x i)), dependentIndependent_average_product] at hb
  exact hb

end FiniteLaw

lemma prime_band_row_second_moment {J : ℕ} (P : Fin J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → 2 ≤ p) (ambient : Finset ℕ)
    (hambient : ∀ p ∈ ambient, 2 ≤ p) (hsub : ∀ j, P j ⊆ ambient)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (paddingOriginalLaw ambient hambient).average (fun x =>
      ∏ j : Fin J, (booleanCount (fun p : P j => x ⟨p.val, hsub j p.property⟩) +
        primeHarmonicMass (P j)) ^ 2) ≤
      ∏ j : Fin J, (4 * (primeHarmonicMass (P j)) ^ 2 + primeHarmonicMass (P j)) := by
  let e : (j : Fin J) → P j → ambient := fun j p => ⟨p.val, hsub j p.property⟩
  have he : Function.Injective (fun p : Sigma (fun j => P j) => e p.1 p.2) := by
    rintro ⟨j, p⟩ ⟨l, q⟩ hpq
    have hv : p.val = q.val := congrArg Subtype.val hpq
    have hjl : j = l := by
      by_contra hne
      exact disjoint_left.mp (hdisjoint j l (Ne.symm hne)) p.property (hv.symm ▸ q.property)
    subst l
    exact congrArg (Sigma.mk j) (Subtype.ext hv)
  rw [paddingOriginalLaw,
    FiniteLaw.independent_average_disjoint_products
      (fun p : ambient => paddingOriginalPrimeLaw p (hambient p p.property)) e he
      (fun j a => (booleanCount a + primeHarmonicMass (P j)) ^ 2)]
  apply Finset.prod_le_prod
  · intro j _
    exact FiniteLaw.average_nonneg _ (fun _ => sq_nonneg _)
  · intro j _
    have hm : (∑ p : P j, 1 / (p.val : ℝ)) = primeHarmonicMass (P j) := by
      simp only [primeHarmonicMass, one_div]
    simpa only [paddingOriginalPrimeLaw, e, hm] using
      independent_boolean_shifted_count_square
        (fun p : P j => 1 / (p.val : ℝ)) (fun _ => by positivity)
        (fun p => by
          apply (div_le_one (by exact_mod_cast (show 0 < p.val by have := hP j p p.property; omega))).mpr
          exact_mod_cast (show 1 ≤ p.val by have := hP j p p.property; omega))


namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

theorem prime_row_second_moment (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2) ≤
      (∏ q : data.Q, (1 + 24 / (q.val : ℝ))) *
        ∏ j : Fin J, (4 * (primeHarmonicMass (P j)) ^ 2 + primeHarmonicMass (P j)) := by
  let F := fun x : data.P → Bool =>
    ∏ j : Fin J, (booleanCount (fun p : P j => x ⟨p.val, hsub j p.property⟩) +
      primeHarmonicMass (P j)) ^ 2
  let g := fun n : ℤ => (actualPaddingWeight data.Q n) ^ 2
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2 =
        F (fun p => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
          g (data.residueOrigin x + site) := by
    simp only [primeRowMajorant, mul_pow, prod_pow, F, g, actualPrimeDegree_eq_count]
    ring
  simp_rw [he]
  rw [data.residue_average_prime_boolean_padding hB site F g
    (fun n m hnm => congrArg (fun t : ℝ => t ^ 2)
      (actualPaddingWeight_residue_congr data.Q n m hnm))]
  have hq : (data.paddingResidueLaw B hB).average
      (fun z => g (data.paddingResidueOrigin z + site)) =
        ∏ q : data.Q, (1 + 24 / (q.val : ℝ)) := by
    have hl (z : data.Q → Fin B) : g (data.paddingResidueOrigin z + site) =
        (paddingTiltWeight data.Q (paddingResidueAvailable data.Q B site z)) ^ 2 := by
      dsimp only [g]
      rw [actualPaddingWeight_lift data.Q B site z (data.paddingResidueOrigin z + site)
        (fun p => by rw [Int.cast_add, data.paddingResidueOrigin_spec])]
    simp_rw [hl]
    rw [paddingResidueLaw, padding_residue_average data.Q B
      (fun p hp => (data.primeQ p hp).two_le)
      (fun p hp => hB p (mem_union_right _ hp)) site
      (fun a => (paddingTiltWeight data.Q a) ^ 2)]
    exact padding_weight_square_average data.Q _
  rw [hq, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _ => by positivity))
  exact prime_band_row_second_moment P
    (fun j p hp => (data.primeP p (hsub j hp)).two_le) data.P
    (fun p hp => (data.primeP p hp).two_le) hsub hdisjoint

end ProhibitedPrimeFamily

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



lemma positive_tuple_padding_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors Q)
    (n : ℤ) :
    (∑ d ∈ D, ∑ q ∈ padding d,
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        if (q : ℤ) ∣ n then 1 else 0) ≤ primeRowMajorant P Q n := by
  calc
    _ ≤ ∑ d ∈ D, positivePrimeWeight d.primeFactors n * actualPaddingWeight Q n := by
      apply sum_le_sum
      intro d hd
      calc
        _ = positivePrimeWeight d.primeFactors n *
            (∑ q ∈ padding d, if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q _
          split_ifs <;> ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by
          rw [actualPaddingWeight_eq_divisor_sum Q hQ n]
          exact sum_le_sum_of_subset_of_nonneg (hpadding d hd) (by
            intro q _ _
            split_ifs
            · exact actualPaddingCoefficient_nonneg q
            · exact le_rfl)) (positivePrimeWeight_nonneg _ _)
    _ ≤ ∑ d ∈ primeTupleDivisors P,
        positivePrimeWeight d.primeFactors n * actualPaddingWeight Q n :=
      sum_le_sum_of_subset_of_nonneg hD (by
        intro d _ _
        exact mul_nonneg (positivePrimeWeight_nonneg _ _) (by
          exact zero_le_one.trans (actualPaddingWeight_one_le Q n)))
    _ = _ := by
      rw [← sum_mul, positivePrimeWeight_tuple_sum P hprime hdisjoint]
      exact mul_comm _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeRowMomentScale
namespace OAI

/-! The rare-site row majorant has a fixed polynomial second moment,
uniformly in the band-width parameter W. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma prime_row_moment_product_bound {J : ℕ} (Q : Finset ℕ) (V : Fin J → ℝ)
    (L W : ℝ) (hL : 1 ≤ L) (hW : 10 ≤ W)
    (hQ : (∑ p ∈ Q, 1 / (p : ℝ)) ≤ Real.log L)
    (hV0 : ∀ j, 0 ≤ V j) (hV : ∀ j, V j ≤ 2 * W)
    (hJ : (J : ℝ) * (6 * W) ≤ Real.log L) :
    (∏ q : Q, (1 + 24 / (q.val : ℝ))) *
      (∏ j : Fin J, (4 * (V j) ^ 2 + V j)) ≤ L ^ (25 : ℕ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hQprod : (∏ q : Q, (1 + 24 / (q.val : ℝ))) ≤ Real.exp (24 * Real.log L) := by
    calc
      _ ≤ ∏ q : Q, Real.exp (24 / (q.val : ℝ)) := by
        apply Finset.prod_le_prod
        · intro q _
          positivity
        · intro q _
          simpa only [add_comm] using Real.add_one_le_exp (24 / (q.val : ℝ))
      _ = Real.exp (24 * ∑ p ∈ Q, 1 / (p : ℝ)) := by
        rw [← Real.exp_sum, ← sum_coe_sort Q (fun p : ℕ => 1 / (p : ℝ)), mul_sum]
        congr 1
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hbase : 18 * W ^ 2 ≤ Real.exp (6 * W) := by
    have hE : W ≤ Real.exp W := by linarith [Real.add_one_le_exp W]
    have hE4 : (18 : ℝ) ≤ Real.exp (4 * W) := by
      linarith [Real.add_one_le_exp (4 * W)]
    calc
      _ ≤ Real.exp (4 * W) * (Real.exp W) ^ 2 :=
        mul_le_mul hE4 (pow_le_pow_left₀ (by linarith) hE 2)
          (sq_nonneg W) (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  have hVprod : (∏ j : Fin J, (4 * (V j) ^ 2 + V j)) ≤ Real.exp (Real.log L) := by
    calc
      _ ≤ ∏ _j : Fin J, Real.exp (6 * W) := by
        apply Finset.prod_le_prod
        · intro j _
          exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hV0 j)
        · intro j _
          have hv : 4 * (V j) ^ 2 + V j ≤ 18 * W ^ 2 := by
            have hs := mul_nonneg (hV0 j) (sub_nonneg.mpr (hV j))
            have ht := sq_nonneg (2 * W - V j)
            nlinarith [hV j, hV0 j]
          exact hv.trans hbase
      _ = Real.exp ((J : ℝ) * (6 * W)) := by
        simp only [prod_const, card_univ, Fintype.card_fin]
        rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hJ
  calc
    _ ≤ Real.exp (24 * Real.log L) * Real.exp (Real.log L) :=
      mul_le_mul hQprod hVprod (prod_nonneg (fun j _ =>
        add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hV0 j))) (Real.exp_pos _).le
    _ = L ^ (25 : ℕ) := by
      rw [← Real.exp_add]
      rw [show 24 * Real.log L + Real.log L = (25 : ℕ) * Real.log L by norm_num; ring]
      rw [Real.exp_nat_mul, Real.exp_log hLp]

namespace FiniteLaw

lemma square_event_average_le {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (f : α → ℝ) (E : α → Prop) :
    (μ.average (fun x => f x * if E x then 1 else 0)) ^ 2 ≤
      μ.average (fun x => (f x) ^ 2) * μ.probability E := by
  have hh := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := fun x => μ.weight x * (f x) ^ 2)
    (g := fun x => μ.weight x * if E x then 1 else 0)
    (r := fun x => μ.weight x * (f x * if E x then 1 else 0))
    (fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _))
    (fun x _ => mul_nonneg (μ.nonneg x) (by split_ifs <;> norm_num))
    (fun x _ => by split_ifs <;> ring_nf <;> exact le_rfl)
  exact hh

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

theorem prime_row_second_moment_polynomial (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (hsub : ∀ j, P j ⊆ data.P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (site : ℤ)
    (L W : ℝ) (hL : 1 ≤ L) (hW : 10 ≤ W)
    (hQ : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hJ : (J : ℝ) * (6 * W) ≤ Real.log L) :
    (data.residueLaw B hB).average (fun x =>
      (primeRowMajorant P data.Q (data.residueOrigin x + site)) ^ 2) ≤ L ^ (25 : ℕ) := by
  apply (data.prime_row_second_moment hB P hsub hdisjoint site).trans
  exact prime_row_moment_product_bound data.Q (fun j => primeHarmonicMass (P j)) L W
    hL hW hQ (fun j => by unfold primeHarmonicMass; positivity) hV hJ


end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RareRowDecay
namespace OAI

/-! Polynomially many rare-site row costs are absorbed by the
stretched-exponential forbidden-site probability. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_rare_row_exponent (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      (2 * C + 25) * Real.log L + 2 * L ^ (9 / 10 : ℝ) ≤
        (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) := by
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < 1 / (8 * (2 * C + 26)) by positivity)
  have hpower := (tendsto_rpow_atTop (y := (19 / 200 : ℝ)) (by norm_num)).eventually
    (eventually_ge_atTop (8 : ℝ))
  filter_upwards [hlog, hpower, eventually_ge_atTop (1 : ℝ)] with L hl hp hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hln : 0 ≤ Real.log L := Real.log_nonneg hL
  have hR : 0 ≤ L ^ (199 / 200 : ℝ) := Real.rpow_nonneg hLp.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hln, Real.norm_eq_abs, abs_of_nonneg hR] at hl
  have hc : (2 * C + 25) * Real.log L ≤ (1 / 8 : ℝ) * L ^ (199 / 200 : ℝ) := by
    calc
      _ ≤ (2 * C + 26) * Real.log L := by nlinarith
      _ ≤ (2 * C + 26) * ((1 / (8 * (2 * C + 26))) * L ^ (199 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by field_simp
  have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hLp.le (9 / 10 : ℝ))
  have he : L ^ (9 / 10 : ℝ) * L ^ (19 / 200 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  rw [he] at hh
  nlinarith

theorem eventually_rare_row_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ A x : ℝ, 0 ≤ A → 0 ≤ x →
      A ≤ Real.exp (C * Real.log L) →
      x ^ 2 ≤ L ^ (25 : ℕ) * Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      A * x ≤ Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [eventually_rare_row_exponent C hC, eventually_ge_atTop (1 : ℝ)]
      with L hscale hL
  intro A x hA hx hAbound hxbound
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA2 := pow_le_pow_left₀ hA hAbound 2
  have hh := mul_le_mul hA2 hxbound (sq_nonneg x)
    (sq_nonneg (Real.exp (C * Real.log L)))
  have hL25 : Real.exp ((25 : ℕ) * Real.log L) = L ^ (25 : ℕ) := by
    rw [Real.exp_nat_mul, Real.exp_log hLp]
  have he : (Real.exp (C * Real.log L)) ^ 2 *
      (L ^ (25 : ℕ) * Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ))) =
        Real.exp ((2 * C + 25) * Real.log L -
          (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
    rw [← Real.exp_nat_mul, ← hL25, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  have hexp := Real.exp_le_exp.mpr
    (show (2 * C + 25) * Real.log L - (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) ≤
      -(2 * L ^ (9 / 10 : ℝ)) by linarith)
  have hsq : (A * x) ^ 2 ≤ (Real.exp (-L ^ (9 / 10 : ℝ))) ^ 2 := by
    calc
      _ = A ^ 2 * x ^ 2 := mul_pow _ _ _
      _ ≤ Real.exp ((2 * C + 25) * Real.log L -
          (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := hh
      _ ≤ Real.exp (-(2 * L ^ (9 / 10 : ℝ))) := hexp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hAx : 0 ≤ A * x := mul_nonneg hA hx
  have hpos := Real.exp_pos (-L ^ (9 / 10 : ℝ))
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualRareRow
namespace OAI

/-! The row-moment and rare-site bounds for the literal centered prime
bands. All mass and scale assumptions are supplied by the fixed-modulus
prime theorem and the actual band-count definition. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma primeRowMajorant_nonneg {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ) (n : ℤ) :
    0 ≤ primeRowMajorant P Q n := by
  apply mul_nonneg (zero_le_one.trans (actualPaddingWeight_one_le Q n))
  apply prod_nonneg
  intro j _
  apply add_nonneg (Nat.cast_nonneg _)
  unfold primeHarmonicMass
  positivity

theorem ModFiveThetaInput.eventually_actual_row_second_moment (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 10 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ),
      (data.residueLaw B hB).average (fun x =>
        (primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site)) ^ 2) ≤ L ^ (25 : ℕ) := by
  filter_upwards [hP.eventually_actual_prime_supplies E W (by linarith),
    hP.eventually_padding_pool_mass E, eventually_ge_atTop (1 : ℝ)] with L hs hq hL
  intro h M B data hp hqeq hB site
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 ≤ A := Real.rpow_nonneg (by linarith) _
  have hsub (j : Fin J) : P j ⊆ data.P := by
    rw [hp]
    exact centeredPrimeBand_subset_pool E A W J j
  have hdisjoint (j l : Fin J) (hne : l ≠ j) : Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint E A W J hA (by linarith) j l hne
  have hV (j : Fin J) : primeHarmonicMass (P j) ≤ 2 * W := by
    simpa only [P, centeredPrimeBands, primeHarmonicMass_eq_sum, A] using (hs.2.2 j.val).2.2
  have hQ : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L := by
    rw [hqeq, ← primeHarmonicMass_eq_sum]
    exact hq
  have hJ : (J : ℝ) * (6 * W) ≤ Real.log L := by
    have hj := primeSupplyCount_mul_bound W L (by linarith) hL
    have hl := Real.log_nonneg hL
    change (J : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L at hj
    linarith
  exact data.prime_row_second_moment_polynomial hB P hsub hdisjoint site L W hL hW hQ hV hJ

theorem ModFiveThetaInput.eventually_actual_rare_row (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
        (bad : (↥(data.P ∪ data.Q) → Fin B) → Prop),
      (data.residueLaw B hB).probability bad ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      ∀ A : ℝ, 0 ≤ A → A ≤ Real.exp (C * Real.log L) →
      A * (data.residueLaw B hB).average (fun x =>
        primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site) * if bad x then 1 else 0) ≤
            Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [hP.eventually_actual_row_second_moment E W hW,
    eventually_rare_row_decay C hC, eventually_ge_atTop (1 : ℝ)] with L hm hd hL
  intro h M B data hp hq hB site bad hbad A hA hAcap
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  let F := fun x : ↥(data.P ∪ data.Q) → Fin B =>
    primeRowMajorant P data.Q (data.residueOrigin x + site)
  have hF : ∀ x, 0 ≤ F x := fun x => primeRowMajorant_nonneg P data.Q _
  have hs := (data.residueLaw B hB).square_event_average_le F bad
  have hL0 : 0 ≤ L := by linarith
  have hmoment : (data.residueLaw B hB).average (fun x => (F x) ^ 2) ≤ L ^ (25 : ℕ) :=
    hm h M B data hp hq hB site
  have hsq := hs.trans (mul_le_mul hmoment hbad
    ((data.residueLaw B hB).probability_nonneg bad) (by positivity))
  exact hd A _ hA ((data.residueLaw B hB).average_nonneg (fun x =>
    mul_nonneg (hF x) (by split_ifs <;> norm_num))) hAcap hsq

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RareRowSum
namespace OAI

/-! Sum the rare-site estimate over the polynomially many bins. The
row bound is applied in the product model before integer transfer. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma positive_rare_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors Q)
    (n : ℤ) (bad : Prop) :
    (∑ d ∈ D, ∑ q ∈ padding d,
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        if (q : ℤ) ∣ n ∧ bad then 1 else 0) ≤
      primeRowMajorant P Q n * if bad then 1 else 0 := by
  by_cases hb : bad
  · simp only [hb, and_true, ite_true, mul_one]
    exact positive_tuple_padding_row_bound P hprime hdisjoint Q D hQ hD padding hpadding n
  · simp only [hb, and_false, ite_false, mul_zero, sum_const_zero, le_refl]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedRowComparison
namespace OAI

/-! Sum the literal positive cost over tuple/padding choices. The
comparison error counts pairs, while the product-model cost is bounded
by the already proved row second moment and rare-event probability. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma ProhibitedPrimeFamily.prohibited_probability_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (site : ℤ) :
    (data.residueLaw B hB).probability (fun x =>
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)) =
      (data.residueLaw B hB).probability (data.deletedEvent s B) := by
  let f := fun n : ℤ => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
    then (1 : ℝ) else 0
  have hf (n m : ℤ)
      (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) : f n = f m := by
    simp only [f, data.prohibitedSite_congr hB s n m hnm]
  have ht := data.residue_average_translate hB f hf site
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x) ↔
        data.deletedEvent s B x :=
    (data.deletedEvent_iff s B x (data.residueOrigin x) (data.residueOrigin_spec x)).symm
  simpa [FiniteLaw.probability, f, he] using ht

lemma prohibitedPositiveRow_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (D : Finset ℕ) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q)
    (n : ℤ) :
    prohibitedPositiveRow data s D padding n ≤ primeRowMajorant P data.Q n *
      if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0 :=
  positive_rare_row_bound P hprime hdisjoint data.Q D data.primeQ hD padding hpadding n _


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualRareDeletion
namespace OAI

/-! The prohibited-site part of the deletion estimate. The rare-event
cost is controlled after summing the actual positive tuple/padding row;
only the finite-interval comparison error pays for individual pairs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem ModFiveThetaInput.eventually_prohibited_model_row (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B s : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      ∀ (A : ℝ), 0 ≤ A → A ≤ Real.exp (C * Real.log L) → ∀ site : ℤ,
      A * (data.residueLaw B hB).average (fun x =>
        prohibitedPositiveRow data s D padding (data.residueOrigin x + site)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [hP.eventually_actual_rare_row E W C hW hC,
    eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h M B s data hp hq hB hprob D hD padding hpadding A hA hAcap site
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  let bad := fun x : ↥(data.P ∪ data.Q) → Fin B =>
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)
  have hpbad : (data.residueLaw B hB).probability bad ≤
      Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
    rw [data.prohibited_probability_translate hB s site]
    exact hprob
  have hrow (x : ↥(data.P ∪ data.Q) → Fin B) :
      prohibitedPositiveRow data s D padding (data.residueOrigin x + site) ≤
        primeRowMajorant P data.Q (data.residueOrigin x + site) * if bad x then 1 else 0 := by
    apply prohibitedPositiveRow_le data s P (centeredPrimeBands_prime E _ W _)
      (centeredPrimeBands_disjoint E _ W _ (Real.rpow_nonneg (by linarith) _) (by linarith))
      D hD padding hpadding
  exact (mul_le_mul_of_nonneg_left ((data.residueLaw B hB).average_mono hrow) hA).trans
    (hb h M B data hp hq hB site bad hpbad A hA hAcap)


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_prohibited_model_row := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_prohibited_model_row
