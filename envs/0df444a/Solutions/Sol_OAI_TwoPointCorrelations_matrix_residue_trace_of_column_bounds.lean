-- Prove2me | solution 1 for OAI.TwoPointCorrelations.matrix_residue_trace_of_column_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:38:56.996418+00:00
-- url     : https://prove2.me/submissions/8e5193b1-1789-404a-9ecc-b68a30555cab

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






lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixClosedWords
namespace OAI

/-! Signed closed-word expansion of the actual matrix power moment. -/

namespace TwoPointCorrelations

open _root_.Finset

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V]








omit [DecidableEq V] in
lemma sum_fin_cons {k : ℕ} (f : (Fin (k + 1) → V) → ℝ) :
    ∑ v, f v = ∑ a, ∑ v : Fin k → V, f (Fin.cons a v) := by
  have he := (Fin.consEquiv (fun _ : Fin (k + 1) => V)).sum_comp f
  change (∑ p : V × (Fin k → V), f (Fin.cons p.1 p.2)) = ∑ v, f v at he
  simpa only [Fintype.sum_prod_type] using he.symm







end Paths

section Nonbacktracking

variable {D V : Type*} [DecidableEq D]



variable [DecidableEq V]



end Nonbacktracking

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixWords
namespace OAI

/-! Expand finite shift matrices using step labels, without enumerating intermediate sites. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V E S : Type*} [Fintype V] [DecidableEq V] [Fintype E]







omit [DecidableEq V] [Fintype E] in
lemma sum_at_injective_site (embed : V → S) (hinj : Function.Injective embed)
    (z : S) (f : S → ℝ) :
    (∑ j, if z = embed j then f (embed j) else 0) =
      if z ∈ Set.range embed then f z else 0 := by
  classical
  by_cases hz : z ∈ Set.range embed
  · obtain ⟨j, rfl⟩ := hz
    have he (i : V) : embed j = embed i ↔ j = i := hinj.eq_iff
    simp [he]
  · have he (j : V) : z ≠ embed j := fun h => hz ⟨j, h.symm⟩
    simp [he, hz]

omit [DecidableEq V] in
lemma shiftMatrix_action (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (i : V) (f : S → ℝ) :
    (∑ j, shiftMatrix embed next weight i j * f (embed j)) =
      ∑ e, retainedShiftWeight embed next weight e (embed i) * f (next e (embed i)) := by
  classical
  simp only [shiftMatrix, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  have he (j : V) :
      (if next e (embed i) = embed j then weight e (embed i) else 0) * f (embed j) =
        if next e (embed i) = embed j then weight e (embed i) * f (embed j) else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [sum_at_injective_site embed hinj (next e (embed i))
    (fun z => weight e (embed i) * f z)]
  unfold retainedShiftWeight
  split_ifs <;> simp

omit [DecidableEq V] [Fintype E] in
lemma shiftWordTerm_cons (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x y : S) (e : E) (w : Fin k → E) :
    shiftWordTerm embed next weight x y (Fin.cons e w) =
      retainedShiftWeight embed next weight e x *
        shiftWordTerm embed next weight (next e x) y w := by
  classical
  simp only [shiftWordTerm, shiftWordEnd, shiftWordWeight, Fin.cons_zero, Fin.tail_cons]
  split_ifs <;> simp

/-- Only the initial site and the step labels are summed. Intermediate sites
are forced by the integer shifts and killed when they leave the finite domain. -/
theorem shiftMatrix_pow_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) (i j : V) :
    (shiftMatrix embed next weight ^ k) i j =
      ∑ w : Fin k → E, shiftWordTerm embed next weight (embed i) (embed j) w := by
  classical
  induction k generalizing i with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, shiftWordTerm, shiftWordEnd, shiftWordWeight,
        hinj.eq_iff, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        pow_zero, one_smul]
  | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp_rw [ih]
      rw [shiftMatrix_action embed hinj next weight i
        (fun x => ∑ w : Fin k → E, shiftWordTerm embed next weight x (embed j) w)]
      rw [sum_fin_cons]
      simp_rw [mul_sum, shiftWordTerm_cons]

theorem shiftMatrix_power_closed_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) :
    matrixFrobeniusSq (shiftMatrix embed next weight ^ k) =
      ∑ i, ∑ j, ∑ u : Fin k → E, ∑ v : Fin k → E,
        shiftWordTerm embed next weight (embed i) (embed j) u *
          shiftWordTerm embed next weight (embed i) (embed j) v := by
  unfold matrixFrobeniusSq
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [shiftMatrix_pow_words embed hinj, pow_two, sum_mul]
  simp_rw [mul_sum]

omit [DecidableEq V] [Fintype E] in
lemma shiftWordWeight_support (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) {k : ℕ} (x : S) (w : Fin k → E)
    (hx : x ∈ Set.range embed) (hw : shiftWordWeight embed next weight x w ≠ 0) :
    shiftWordEnd next x w ∈ Set.range embed := by
  classical
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have hn : next (w 0) x ∈ Set.range embed := by
        by_contra hn
        exact hp.1 (by simp [retainedShiftWeight, hn])
      exact ih (next (w 0) x) (Fin.tail w) hn hp.2

omit [DecidableEq V] [Fintype E] in
/-- The common endpoint is forced by the first word, and hence contributes
no additional factor equal to the number of sites. -/
lemma sum_shiftWordTerm_pair (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) {k : ℕ} (i : V)
    (u v : Fin k → E) :
    (∑ j, shiftWordTerm embed next weight (embed i) (embed j) u *
      shiftWordTerm embed next weight (embed i) (embed j) v) =
      if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
        shiftWordWeight embed next weight (embed i) u *
          shiftWordWeight embed next weight (embed i) v else 0 := by
  classical
  by_cases he : shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v
  · have ht (j : V) : shiftWordTerm embed next weight (embed i) (embed j) u *
        shiftWordTerm embed next weight (embed i) (embed j) v =
        if shiftWordEnd next (embed i) u = embed j then
          shiftWordWeight embed next weight (embed i) u *
            shiftWordWeight embed next weight (embed i) v else 0 := by
      simp only [shiftWordTerm, ← he]
      split_ifs <;> simp
    simp_rw [ht]
    rw [sum_at_injective_site embed hinj _ (fun _ =>
      shiftWordWeight embed next weight (embed i) u *
        shiftWordWeight embed next weight (embed i) v)]
    by_cases hm : shiftWordEnd next (embed i) u ∈ Set.range embed
    · rw [if_pos hm, if_pos he]
    · have hz : shiftWordWeight embed next weight (embed i) u = 0 := by
        by_contra hz
        exact hm (shiftWordWeight_support embed next weight (embed i) u ⟨i, rfl⟩ hz)
      rw [if_neg hm, if_pos he, hz, zero_mul]
  · have ht (j : V) : shiftWordTerm embed next weight (embed i) (embed j) u *
        shiftWordTerm embed next weight (embed i) (embed j) v = 0 := by
      unfold shiftWordTerm
      split_ifs with hu hv
      · exact (he (hu.trans hv.symm)).elim
      all_goals simp
    simp [ht, he]

theorem shiftMatrix_moment_forced_words (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : E → S → ℝ) (k : ℕ) :
    matrixFrobeniusSq (shiftMatrix embed next weight ^ k) =
      ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        if shiftWordEnd next (embed i) u = shiftWordEnd next (embed i) v then
          shiftWordWeight embed next weight (embed i) u *
            shiftWordWeight embed next weight (embed i) v else 0 := by
  classical
  rw [shiftMatrix_power_closed_words embed hinj]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  exact sum_shiftWordTerm_pair embed hinj next weight i u v

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftTraceComparison
namespace OAI

/-! Signed expectation and comparison of the forced-word trace expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V E S Ω Ω' : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [Fintype Ω] [Fintype Ω']


theorem average_shiftMatrix_moment (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : Ω → E → S → ℝ) (μ : FiniteLaw Ω) (k : ℕ) :
    μ.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight ω) ^ k)) =
      ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) := by
  simp only [shiftMatrix_moment_forced_words embed hinj, shiftClosedWeight,
    FiniteLaw.average, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]


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


lemma centeredTuple_add (P : Finset ℕ) (n t : ℤ)
    (ht : ∀ p ∈ P, (p : ℤ) ∣ t) : centeredTuple P (n + t) = centeredTuple P n := by
  unfold centeredTuple
  apply prod_congr rfl
  intro p hp
  simp only [dvd_add_left (ht p hp)]








/-- Divisibility by a padding divisor is unchanged along its integer edge. -/
lemma padding_dvd_along_edge (h q d : ℕ) (n m : ℤ)
    (hm : m = n + (h * q * d : ℕ)) : (q : ℤ) ∣ m ↔ (q : ℤ) ∣ n := by
  rw [hm]
  apply dvd_add_left
  norm_cast
  exact dvd_mul_of_dvd_left (dvd_mul_left q h) d




lemma centeredTuple_padding_periodic (P : Finset ℕ) (h d : ℕ)
    (hd : ∀ p ∈ P, p ∣ d) (q : ℕ) (n : ℤ) :
    centeredTuple P (n + (h * q * d : ℕ)) = centeredTuple P n := by
  apply centeredTuple_add
  intro p hp
  exact_mod_cast dvd_mul_of_dvd_right (hd p hp) (h * q)


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftWords
namespace OAI

/-! The actual centered integer-edge matrix as a matrix of forced signed shifts. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma signedIntegerWeight_nonzero (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ)
    (ha : signedIntegerWeight Q u eligible g center L K extra h a n ≠ 0) :
    a.padding ∈ Q ∧ eligible a.padding ∧ (a.padding : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧
      integerEdgeKeep Q u eligible g L K extra (n + a.displacement h) := by
  classical
  rcases a with ⟨b, d, q⟩
  cases b
  · simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte] at ha
    unfold directedIntegerEdge at ha
    split_ifs at ha with he
    · refine ⟨he.1, he.2.2.1, ?_, he.2.2.2.2.2, he.2.2.2.2.1⟩
      exact (padding_dvd_along_edge h q d _ _ he.2.1).mpr he.2.2.2.1
    · contradiction
  · simp only [signedIntegerWeight, ↓reduceIte] at ha
    unfold directedIntegerEdge at ha
    split_ifs at ha with he
    · exact ⟨he.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2⟩
    · contradiction


variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerShiftGeometry
namespace OAI

/-! Numerical words attached to the forced paths in the actual trace expansion. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}


lemma integerShiftEnd_site (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    (shiftWordEnd (integerShiftNext Q tuple h) x w).2 =
      x.2 + wordDisplacement h (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordEnd, integerStepWord]
  | succ k ih =>
      rw [shiftWordEnd, ih]
      simp only [integerStepWord, List.ofFn_succ, List.map_cons, wordDisplacement_cons,
        integerShiftNext, Fin.tail_def]
      ring

lemma integer_closed_word_displacement (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) {k : ℕ}
    (x : D × ℤ) (u v : Fin k → D × (Q × Bool))
    (he : shiftWordEnd (integerShiftNext Q tuple h) x u =
      shiftWordEnd (integerShiftNext Q tuple h) x v) :
    wordDisplacement h (integerStepWord Q tuple u ++ reverseWord (integerStepWord Q tuple v)) = 0 := by
  have hs := congrArg Prod.snd he
  rw [integerShiftEnd_site, integerShiftEnd_site] at hs
  rw [wordDisplacement_append, wordDisplacement_reverseWord]
  omega

lemma signedIntegerWeight_flip (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ) :
    signedIntegerWeight Q u eligible g center L K extra h a.flip (n + a.displacement h) =
      signedIntegerWeight Q u eligible g center L K extra h a n := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [signedIntegerWeight, SignedStep.flip, SignedStep.displacement]

/-- Periodicity permits using the departure center in both orientations.
All surviving cutoffs remain literal indicator conditions. -/
lemma signedIntegerWeight_departure (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h : ℕ) (a : SignedStep) (n : ℤ)
    (hperiod : ∀ q ∈ Q, ∀ z, center (z + (h * q * a.tuple : ℕ)) = center z) :
    signedIntegerWeight Q u eligible g center L K extra h a n =
      if a.padding ∈ Q ∧ eligible a.padding ∧ (a.padding : ℤ) ∣ n ∧
        integerEdgeKeep Q u eligible g L K extra n ∧
        integerEdgeKeep Q u eligible g L K extra (n + a.displacement h) then
        L * u a.padding * center n / (g n * g (n + a.displacement h)) else 0 := by
  classical
  rcases a with ⟨b, d, q⟩
  by_cases hq : q ∈ Q
  · cases b
    · have hd : (SignedStep.mk false d q).displacement h = -(h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      have hn : n + -(h * q * d : ℕ) + (h * q * d : ℕ) = n := by ring
      have hc : center (n + -(h * q * d : ℕ)) = center n := by
        have hh := hperiod q hq (n + -(h * q * d : ℕ))
        rw [hn] at hh
        exact hh.symm
      have hqd : (q : ℤ) ∣ n + -(h * q * d : ℕ) ↔ (q : ℤ) ∣ n := by
        apply dvd_add_left
        apply dvd_neg.mpr
        exact_mod_cast dvd_mul_of_dvd_left (dvd_mul_left q h) d
      simp only [signedIntegerWeight, Bool.false_eq_true, ↓reduceIte, hd, directedIntegerEdge,
        hq, hn, true_and, hqd, hc]
      rw [mul_comm (g (n + -(h * q * d : ℕ))) (g n)]
      congr 1
      apply propext
      tauto
    · have hd : (SignedStep.mk true d q).displacement h = (h * q * d : ℕ) := by
        simp [SignedStep.displacement, Nat.cast_mul]
      simp [signedIntegerWeight, directedIntegerEdge, hd]
  · cases b <;> simp [signedIntegerWeight, directedIntegerEdge, hq]

variable [DecidableEq D]


variable [Fintype V]


variable [Fintype D] [DecidableEq V]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerClosedCatalog
namespace OAI

/-! A fixed-length numerical closed word remembers both forced matrix paths.
Only their starting site and external copy indices remain outside this code. -/

namespace TwoPointCorrelations

variable {D : Type*}

theorem integerStepWord_injective (Q : Finset ℕ) (tuple : D → ℕ)
    (hinj : Function.Injective tuple) (k : ℕ) :
    Function.Injective (integerStepWord (D := D) Q tuple (k := k)) := by
  intro a b hab
  have hs : (fun i => SignedStep.mk (a i).2.2 (tuple (a i).1) (a i).2.1.val) =
      (fun i => SignedStep.mk (b i).2.2 (tuple (b i).1) (b i).2.1.val) := by
    apply List.ofFn_injective
    simpa only [integerStepWord, List.map_ofFn, Function.comp_def] using hab
  funext i
  apply Prod.ext
  · exact hinj (congrArg SignedStep.tuple (congrFun hs i))
  · apply Prod.ext
    · exact Subtype.ext (congrArg SignedStep.padding (congrFun hs i))
    · exact congrArg SignedStep.forward (congrFun hs i)


theorem integerClosedWordCode_injective (Q : Finset ℕ) (tuple : D → ℕ)
    (hinj : Function.Injective tuple) (k : ℕ) :
    Function.Injective (integerClosedWordCode (D := D) Q tuple (k := k)) := by
  intro a b hab
  have hlen (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).length = k := by
    simp only [integerStepWord, List.length_map, List.length_ofFn]
  have htake (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).take k =
      integerStepWord Q tuple w := by
    simpa only [hlen] using (List.take_length (l := integerStepWord Q tuple w))
  have hdrop (w : Fin k → D × (Q × Bool)) : (integerStepWord Q tuple w).drop k = [] := by
    simpa only [hlen] using (List.drop_length (l := integerStepWord Q tuple w))
  apply Prod.ext
  · apply integerStepWord_injective Q tuple hinj k
    have he := congrArg (List.take k) hab
    simpa only [integerClosedWordCode, List.take_append, hlen, Nat.sub_self,
      List.take_zero, List.append_nil, htake] using he
  · apply integerStepWord_injective Q tuple hinj k
    have he := congrArg (List.drop k) hab
    have hr : reverseWord (integerStepWord Q tuple a.2) =
        reverseWord (integerStepWord Q tuple b.2) := by
      simpa only [integerClosedWordCode, List.drop_append, hlen, Nat.sub_self,
        List.drop_zero, hdrop, List.nil_append] using he
    simpa only [reverseWord_reverseWord] using congrArg reverseWord hr

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWalkNormalization
namespace OAI

/-! Exact normalization of a closed numerical word, counting repeated visits. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma scalarWalkProduct_mul (h : ℕ) (a b : SignedStep → ℤ → ℝ)
    (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x * b t x) n w =
      scalarWalkProduct h a n w * scalarWalkProduct h b n w := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t w ih => simp only [scalarWalkProduct, ih]; ring

lemma scalarWalkProduct_congr (h : ℕ) {a b : SignedStep → ℤ → ℝ}
    (hab : ∀ t x, a t x = b t x) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h a n w = scalarWalkProduct h b n w := by
  have he : a = b := funext (fun t => funext (hab t))
  rw [he]

/-- Each visit contributes its denominator once at departure and once
at arrival; the only uncancelled factors lie at the two endpoints. -/
theorem scalarWalkProduct_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w *
        g n / g (n + wordDisplacement h w) := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct, hg]
  | cons t w ih =>
      rw [scalarWalkProduct, ih, scalarWalkProduct, wordDisplacement_cons]
      rw [← add_assoc]
      field_simp [hg n, hg (n + t.displacement h),
        hg (n + t.displacement h + wordDisplacement h w)]

/-- On a closed word, the exact original edge denominators become the
product of departure weights. Repeated sites remain repeated factors. -/
theorem scalarWalkProduct_closed_normalize (h : ℕ) (a : SignedStep → ℤ → ℝ)
    (g : ℤ → ℝ) (hg : ∀ n, g n ≠ 0) (n : ℤ) (w : List SignedStep)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w =
      scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w := by
  rw [scalarWalkProduct_normalize h a g hg, hclosed, add_zero, mul_div_cancel_right₀ _ (hg n)]

/-- Keep every arithmetic, vertex, and orientation condition while moving
the exact matrix denominator to the departure site. -/
theorem signedIntegerWeight_closed_normalize (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h w = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n w =
      scalarWalkProduct h (fun t x =>
        if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
          integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
        then L * u t.padding * center t x / (g x) ^ 2 else 0) n w := by
  let a : SignedStep → ℤ → ℝ := fun t x =>
    if t.padding ∈ Q ∧ eligible t t.padding ∧ (t.padding : ℤ) ∣ x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) x ∧
      integerEdgeKeep Q u (eligible t) g L K (extra t) (x + t.displacement h)
    then L * u t.padding * center t x else 0
  calc
    _ = scalarWalkProduct h (fun t x => a t x / (g x * g (x + t.displacement h))) n w := by
      apply scalarWalkProduct_congr
      intro t x
      rw [signedIntegerWeight_departure Q u (eligible t) g (center t) L K (extra t) h t x
        (hperiod t)]
      dsimp only [a]
      split_ifs <;> simp
    _ = scalarWalkProduct h (fun t x => a t x / (g x) ^ 2) n w :=
      scalarWalkProduct_closed_normalize h a g hg n w hclosed
    _ = _ := by
      apply scalarWalkProduct_congr
      intro t x
      dsimp only [a]
      split_ifs <;> simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedPathProduct
namespace OAI

/-! Join two paths with common endpoints into the literal closed signed word. -/

namespace TwoPointCorrelations

lemma scalarWalkProduct_append (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (n : ℤ) (u v : List SignedStep) :
    scalarWalkProduct h weight n (u ++ v) =
      scalarWalkProduct h weight n u *
        scalarWalkProduct h weight (n + wordDisplacement h u) v := by
  induction u generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t u ih =>
      simp only [List.cons_append, scalarWalkProduct, ih, wordDisplacement_cons]
      rw [← add_assoc]
      ring

lemma scalarWalkProduct_reverse (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h weight (n + wordDisplacement h w) (reverseWord w) =
      scalarWalkProduct h weight n w := by
  induction w generalizing n with
  | nil => simp [scalarWalkProduct]
  | cons t w ih =>
      rw [wordDisplacement_cons, reverseWord_cons, scalarWalkProduct_append]
      rw [show n + (t.displacement h + wordDisplacement h w) =
        (n + t.displacement h) + wordDisplacement h w by ring, ih]
      rw [wordDisplacement_reverseWord]
      have he : n + t.displacement h + wordDisplacement h w + -wordDisplacement h w =
          n + t.displacement h := by ring
      rw [he]
      simp only [scalarWalkProduct, hflip, mul_one]
      ring

theorem scalarWalkProduct_closed_pair (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (n : ℤ) (u v : List SignedStep)
    (hend : wordDisplacement h u = wordDisplacement h v) :
    scalarWalkProduct h weight n u * scalarWalkProduct h weight n v =
      scalarWalkProduct h weight n (u ++ reverseWord v) := by
  rw [scalarWalkProduct_append, hend, scalarWalkProduct_reverse h weight hflip]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerPathProduct
namespace OAI

/-! Separate the copy, block, and endpoint gates from the signed arithmetic
edge product along an actual forced matrix path. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}



lemma integerPathMask_zero_or_one (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    {k : ℕ} (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    integerPathMask embed Q tuple h gate x w = 0 ∨
      integerPathMask embed Q tuple h gate x w = 1 := by
  induction k generalizing x with
  | zero => exact Or.inr rfl
  | succ k ih =>
      simp only [integerPathMask, integerStepMask]
      split_ifs
      · simpa only [one_mul] using ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w)
      · exact Or.inl (zero_mul _)

variable [Fintype V] [DecidableEq D]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
namespace OAI

/-! Arithmetic translation leaves the physical copy and block gates fixed. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}

lemma scalarWalkProduct_translate (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (c n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun t z => weight t (z + c)) n w =
      scalarWalkProduct h weight (n + c) w := by
  induction w generalizing n with
  | nil => rfl
  | cons t w ih =>
      simp only [scalarWalkProduct, ih]
      rw [show n + t.displacement h + c = n + c + t.displacement h by ring]


variable [Fintype V] [DecidableEq D]

lemma retained_physicalShiftWeight (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) (e : D × (Q × Bool)) (x : D × ℤ) :
    retainedShiftWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) e x =
      integerStepMask embed Q tuple h gate e x *
        weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 := by
  by_cases hc : x.1 ≠ e.1
  · by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2
    · by_cases hr : integerShiftNext Q tuple h e x ∈ Set.range embed
      · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg, hr]
      · simp [retainedShiftWeight, integerStepMask, hr]
    · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg]
  · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc]

theorem physicalShiftWord_product (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w =
      integerPathMask embed Q tuple h gate x w *
        scalarWalkProduct h weight x.2 (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordWeight, integerPathMask, integerStepWord, scalarWalkProduct]
  | succ k ih =>
      rw [shiftWordWeight, retained_physicalShiftWeight, ih]
      simp only [integerPathMask, integerStepWord, List.ofFn_succ, List.map_cons, scalarWalkProduct]
      dsimp only [integerShiftNext, Fin.tail_def]
      ring

theorem physicalShiftWord_closed_pair (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (c : ℤ) {k : ℕ} (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + c))) x b =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        scalarWalkProduct h weight (x.2 + c) (integerClosedWordCode Q tuple (a, b)) := by
  have he := congrArg (fun y : D × ℤ => y.2) hend
  rw [integerShiftEnd_site, integerShiftEnd_site] at he
  have hd : wordDisplacement h (integerStepWord Q tuple a) =
      wordDisplacement h (integerStepWord Q tuple b) := by omega
  rw [physicalShiftWord_product, physicalShiftWord_product,
    scalarWalkProduct_translate, scalarWalkProduct_translate]
  unfold integerClosedWordCode
  rw [← scalarWalkProduct_closed_pair h weight hflip (x.2 + c) _ _ hd]
  ring


lemma maskedSignedIntegerWeight_flip (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (t : SignedStep) (n : ℤ) :
    maskedSignedIntegerWeight Q u eligible g center L K extra h keep
      t.flip (n + t.displacement h) =
      maskedSignedIntegerWeight Q u eligible g center L K extra h keep t n := by
  unfold maskedSignedIntegerWeight
  rw [signedIntegerWeight_flip, SignedStep.displacement_flip]
  rw [show n + t.displacement h + -t.displacement h = n by ring]
  dsimp only [SignedStep.flip]
  ring


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

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring











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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingProduct
namespace OAI

/-! Identify recursive padding weights with the literal product at the numerical departures. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma wordDisplacement_take_succ (h : ℕ) (word : List SignedStep) (t : ℕ) :
    wordDisplacement h (word.take (t + 1)) =
      wordDisplacement h (word.take t) + wordStepDisplacement h word t := by
  simp only [wordDisplacement_take, sum_range_succ]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWordPadding
namespace OAI

/-! Separate the actual closed matrix word into centered factors and its retained padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




theorem closed_signed_word_factorization (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (center : SignedStep → ℤ → ℝ)
    (L K : ℝ) (extra : SignedStep → ℤ → Prop) (h : ℕ) (n : ℤ) (word : List SignedStep)
    (hg : ∀ n, g n ≠ 0)
    (hperiod : ∀ t, ∀ q ∈ Q, ∀ z, center t (z + (h * q * t.tuple : ℕ)) = center t z)
    (hclosed : wordDisplacement h word = 0) :
    scalarWalkProduct h (fun t x =>
      signedIntegerWeight Q u (eligible t) g (center t) L K (extra t) h t x) n word =
      scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n word *
        scalarWalkProduct h center n word := by
  rw [signedIntegerWeight_closed_normalize Q u eligible g center L K extra h n word
    hg hperiod hclosed]
  rw [← scalarWalkProduct_mul]
  apply scalarWalkProduct_congr
  intro t x
  unfold retainedEdgeDeparture
  split_ifs <;> ring




theorem scalarWalkProduct_ofFn {m : ℕ} (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (step : Fin m → SignedStep) (n : ℤ) :
    scalarWalkProduct h weight n (List.ofFn step) =
      ∏ i : Fin m, weight (step i) (n + wordDisplacement h ((List.ofFn step).take i.val)) := by
  induction m generalizing n with
  | zero => simp [scalarWalkProduct]
  | succ m ih =>
      rw [List.ofFn_succ, scalarWalkProduct, ih, Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, wordDisplacement_nil, add_zero]
      congr 1
      apply prod_congr rfl
      intro i _
      simp only [Fin.val_succ, List.take_succ_cons, wordDisplacement_cons,
        add_assoc]

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


lemma columnTuple_primeFactors {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (columnTuple w i).primeFactors = univ.image (fun j => (w j i).val) := by
  exact familyTuple_primeFactors (fun _ p => p.val)
    (fun j p => hprime j _ p.property) (fun j => w j i)
    (selectedPrimeValues_injective (fun j => w j i) hdisjoint)



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnClosedEncoding
namespace OAI

/-! Recover the column data of the actual joined matrix paths. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ofFn_rev_eq_reverse {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega


lemma closedColumnRows_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    integerStepWord Q (fun d => ∏ j, (d j).val) (closedColumnRows Q a b) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  unfold integerStepWord closedColumnRows integerClosedWordCode
  rw [List.ofFn_fin_append, List.map_append]
  congr 1
  rw [reverseWord]
  simp only [integerStepWord, List.map_reverse, List.map_ofFn, Function.comp_def]
  rw [← ofFn_rev_eq_reverse]
  simp only [SignedStep.flip]




theorem closedColumn_encoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    columnTupleWord (closedColumnAssignment Q a b) (closedColumnForward Q a b)
      (fun i => (closedColumnPadding Q a b i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  rw [← closedColumnRows_word]
  simp only [columnTupleWord, columnTuple, closedColumnAssignment, closedColumnForward,
    closedColumnPadding, integerStepWord, List.map_ofFn, Function.comp_def]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedTraceEncoding
namespace OAI

/-! The actual closed-pair catalog has length `2*k`, as in the trace bounds. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma columnTupleWord_reindex {J R S : ℕ} {P : Fin J → Finset ℕ}
    (he : R = S) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) :
    columnTupleWord (fun j i => w j (Fin.cast he.symm i))
      (fun i => forward (Fin.cast he.symm i)) (fun i => padding (Fin.cast he.symm i)) =
      columnTupleWord w forward padding := by
  subst S
  rfl


theorem closedTraceEncoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (p : (Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))) :
    columnTupleWord (closedTraceEncoding Q p).2.1 (closedTraceEncoding Q p).1
      (fun i => ((closedTraceEncoding Q p).2.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  dsimp only [closedTraceEncoding]
  exact (columnTupleWord_reindex (show k + k = 2 * k by omega)
    (closedColumnAssignment Q p.1 p.2) (closedColumnForward Q p.1 p.2)
    (fun i => (closedColumnPadding Q p.1 p.2 i).val)).trans
      (closedColumn_encoding_word Q p.1 p.2)

theorem closedTraceEncoding_injective {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (closedTraceEncoding (k := k) (P := P) Q) := by
  intro a b hab
  apply integerClosedWordCode_injective Q _ (primeTuple_injective hprime hdisjoint) k
  rw [← closedTraceEncoding_word Q a, ← closedTraceEncoding_word Q b, hab]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedTraceSummation
namespace OAI

/-! Partition the actual path-pair catalog by its signs without multiplicity loss. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mem_closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :
    a ∈ closedTraceFiber Q F forward ↔
      ∃ p ∈ F, (closedTraceEncoding Q p).1 = forward ∧ (closedTraceEncoding Q p).2 = a := by
  simp only [closedTraceFiber, mem_image, mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hf⟩, ha⟩
    exact ⟨p, hp, hf, ha⟩
  · rintro ⟨p, hp, hf, ha⟩
    exact ⟨p, ⟨hp, hf⟩, ha⟩

lemma closedTraceFiber_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q F forward) :
    ∃ p ∈ F, columnTupleWord a.1 forward (fun i => (a.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  obtain ⟨p, hp, hf, he⟩ := (mem_closedTraceFiber Q F forward a).mp ha
  refine ⟨p, hp, ?_⟩
  simpa only [hf, he] using closedTraceEncoding_word Q p

theorem sum_closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))))
    (term : (Fin (2 * k) → Bool) →
      (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → ℝ) :
    (∑ p ∈ F, term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2) =
      ∑ forward, ∑ a ∈ closedTraceFiber Q F forward, term forward a := by
  symm
  calc
    _ = ∑ forward, ∑ p ∈ F.filter (fun p => (closedTraceEncoding Q p).1 = forward),
        term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2 := by
      apply sum_congr rfl
      intro forward _
      unfold closedTraceFiber
      rw [sum_image]
      · apply sum_congr rfl
        intro p hp
        rw [(mem_filter.mp hp).2]
      · intro a ha b hb hab
        apply closedTraceEncoding_injective Q hprime hdisjoint
        exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab
    _ = _ := sum_fiberwise F (fun p => (closedTraceEncoding Q p).1)
      (fun p => term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedFamilyWitnesses
namespace OAI

/-! The literal minimal-word catalog discharges the numerical witness-family hypotheses. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)

lemma catalog_pairs (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : (t.tuple, t.padding) ∈ F.pairs :=
  c.property.1.2.2.1 t ht


lemma catalog_whole_squarefree (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : Squarefree (t.padding * t.tuple) :=
  F.whole_squarefree _ (F.catalog_pairs s c t ht)




end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.AttachedCatalogAvoidance
namespace OAI

/-! The attached minimal-word catalog is the actual vertex-deletion indicator. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma attachedResiduePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h B : ℕ)
    (w : List SignedStep) (a n : ℤ) (x : ι → Fin B)
    (hn : ∀ i, (n : ZMod (p i)) = ((x i).val : ZMod (p i)))
    (hsq : ∀ t ∈ w, Squarefree (t.padding * t.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    AttachedResiduePositiveWord p h w a B x ↔ PositiveWord h (n + a) w := by
  let r (i : ι) : ZMod (p i) := ((x i).val : ZMod (p i)) + (a : ZMod (p i))
  have hr : ∀ i, ((n + a : ℤ) : ZMod (p i)) = r i := by
    intro i
    simp only [Int.cast_add, hn, r]
  rw [← residuePositiveWord_iff p h w r (n + a) hr hsq hcover]
  constructor
  · intro ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _
    rw [ht k i hi, Int.cast_add]
    ring
  · intro ht k i hi
    have he := ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _ at he
    change ((x i).val : ZMod (p i)) = _
    rw [Int.cast_add]
    calc
      _ = (((x i).val : ZMod (p i)) + (a : ZMod (p i))) - a := by ring
      _ = _ := by rw [he]; ring


theorem attachedCatalogAvoidance_ne_zero_iff {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v)) := by
  have htest (a : Fin (D + 1) × ProhibitedCatalog F.pairs h s) :
      AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
        (decodeStepWord a.2.val) (wordDisplacement h (main.take (min a.1.val main.length))) B x ↔
      PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
        (decodeStepWord a.2.val) := by
    apply attachedResiduePositiveWord_iff _ h B _ _ n x hn
    · exact F.catalog_whole_squarefree s a.2
    · intro q hq
      exact ⟨⟨q, F.support_subset s a.2 hq⟩, rfl⟩
  have hne : attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ a : Fin (D + 1) × ProhibitedCatalog F.pairs h s,
        ¬PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
          (decodeStepWord a.2.val) := by
    unfold attachedCatalogAvoidance witnessAvoidance
    rw [prod_ne_zero_iff]
    constructor
    · intro hx a ha
      have hz := hx a (mem_univ a)
      have ht := (htest a).mpr ha
      simp [ht] at hz
    · intro hx a _
      have ht : ¬AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
          (decodeStepWord a.2.val)
          (wordDisplacement h (main.take (min a.1.val main.length))) B x :=
        fun hp => hx a ((htest a).mp hp)
      simp [ht]
  rw [hne]
  constructor
  · intro ha v hv ⟨w, hw, hm⟩
    obtain ⟨c, hc⟩ := stepWord_covered F.pairs s w hm.1.2.1 hm.1.2.2.1
    have hcm : MinimalWord (ForwardProhibited h s (fun d q => (d, q) ∈ F.pairs))
        (decodeStepWord c) := by rw [hc]; exact hm
    have hh := ha (⟨v, by omega⟩, ⟨c, hcm⟩)
    rw [min_eq_left hv, hc] at hh
    exact hh hw
  · intro ha a hw
    exact ha (min a.1.val main.length) (Nat.min_le_right _ _)
      ⟨decodeStepWord a.2.val, hw, a.2.property⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CatalogVertexIndicator
namespace OAI

/-! Equality of the finite residue-catalog indicator with the actual integer vertex mask. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma witnessAvoidance_eq_indicator {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) :
    witnessAvoidance I x = if ∀ w, I w x = false then 1 else 0 := by
  unfold witnessAvoidance
  split_ifs with hI
  · apply prod_eq_one
    intro w _
    simp only [hI w, Bool.false_eq_true, ite_false, sub_zero]
  · obtain ⟨w, hw⟩ := not_forall.mp hI
    have ht : I w x = true := Bool.eq_true_of_not_eq_false hw
    apply prod_eq_zero (mem_univ w)
    simp [ht]

lemma witnessAvoidance_eq_one_of_ne_zero {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) (hx : witnessAvoidance I x ≠ 0) :
    witnessAvoidance I x = 1 := by
  rw [witnessAvoidance_eq_indicator] at hx ⊢
  split_ifs with hI
  · rfl
  · simp [hI] at hx

theorem attachedCatalogAvoidance_eq_indicator {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x =
      if ∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v)) then 1 else 0 := by
  split_ifs with hkeep
  · exact witnessAvoidance_eq_one_of_ne_zero _ x
      ((attachedCatalogAvoidance_ne_zero_iff F s B D main hD x n hn).mpr hkeep)
  · by_contra hne
    exact hkeep ((attachedCatalogAvoidance_ne_zero_iff F s B D main hD x n hn).mp hne)


theorem attachedCatalogAvoidance_eq_departure_product {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (hlen : 0 < main.length) (hclosed : wordDisplacement h main = 0)
    (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x =
      ∏ v : Fin main.length,
        if ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
          (n + wordDisplacement h (main.take v.val)) then (0 : ℝ) else 1 := by
  have he : (∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v))) ↔
      (∀ v < main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v))) := by
    constructor
    · exact fun hh v hv => hh v hv.le
    · intro hh v hv
      rcases lt_or_eq_of_le hv with hv | rfl
      · exact hh v hv
      · simpa only [List.take_length, hclosed, add_zero, List.take_zero,
          wordDisplacement_nil] using hh 0 hlen
  rw [attachedCatalogAvoidance_eq_indicator F s B D main hD x n hn]
  simp only [he]
  split_ifs with hkeep
  · symm
    apply prod_eq_one
    intro v _
    exact if_neg (hkeep v.val v.isLt)
  · push Not at hkeep
    obtain ⟨v, hv, hbad⟩ := hkeep
    symm
    exact prod_eq_zero (mem_univ (⟨v, hv⟩ : Fin main.length)) (if_pos hbad)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedVertexMask
namespace OAI

/-! A closed nonempty word counts a binary vertex mask once per departure, despite the two edge endpoints. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma closed_binary_mask_product {m : ℕ} (hm : 0 < m)
    (site : Fin (m + 1) → ℤ) (hclosed : site (Fin.last m) = site 0)
    (mask : ℤ → ℝ) (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    (∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ)) =
      ∏ i : Fin m, mask (site i.castSucc) := by
  by_cases hz : ∃ i : Fin m, mask (site i.castSucc) = 0
  · obtain ⟨i, hi⟩ := hz
    rw [prod_mul_distrib, prod_eq_zero (mem_univ i) hi, zero_mul]
  · have hd (i : Fin m) : mask (site i.castSucc) = 1 :=
      (hmask _).resolve_left (fun hi => hz ⟨i, hi⟩)
    have ha (i : Fin m) : mask (site i.succ) = 1 := by
      by_cases hi : i.val + 1 < m
      · have he : i.succ = (⟨i.val + 1, hi⟩ : Fin m).castSucc := Fin.ext rfl
        rw [he, hd]
      · have he : i.succ = Fin.last m := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        have he0 : (⟨0, hm⟩ : Fin m).castSucc = (0 : Fin (m + 1)) := Fin.ext rfl
        rw [he, hclosed, ← he0, hd]
    simp only [hd, ha, mul_one, prod_const_one]

theorem closed_masked_scalar_word {m : ℕ} (hm : 0 < m)
    (h : ℕ) (step : Fin m → SignedStep) (n : ℤ)
    (hclosed : wordDisplacement h (List.ofFn step) = 0)
    (weight : SignedStep → ℤ → ℝ) (mask : ℤ → ℝ)
    (hmask : ∀ z, mask z = 0 ∨ mask z = 1) :
    scalarWalkProduct h (fun t z => mask z * weight t z * mask (z + t.displacement h))
      n (List.ofFn step) =
      scalarWalkProduct h weight n (List.ofFn step) *
        scalarWalkProduct h (fun _ z => mask z) n (List.ofFn step) := by
  let site (i : Fin (m + 1)) := n + wordDisplacement h ((List.ofFn step).take i.val)
  have hsite : site (Fin.last m) = site 0 := by
    have ht : (List.ofFn step).take m = List.ofFn step :=
      List.take_of_length_le (by simp)
    simp only [site, Fin.val_last, ht, hclosed, add_zero, Fin.val_zero,
      List.take_zero, wordDisplacement_nil]
  have hs (i : Fin m) : site i.castSucc + (step i).displacement h = site i.succ := by
    have ht : wordStepDisplacement h (List.ofFn step) i.val = (step i).displacement h := by
      simp only [wordStepDisplacement, List.getElem?_ofFn, i.isLt, dite_true, Fin.eta,
        Option.map_some, Option.getD_some]
    simp only [site, Fin.val_castSucc, Fin.val_succ, wordDisplacement_take_succ, ht, add_assoc]
  simp only [scalarWalkProduct_ofFn]
  change (∏ i : Fin m, mask (site i.castSucc) * weight (step i) (site i.castSucc) *
      mask (site i.castSucc + (step i).displacement h)) =
    (∏ i : Fin m, weight (step i) (site i.castSucc)) * ∏ i : Fin m, mask (site i.castSucc)
  calc
    _ = (∏ i : Fin m, weight (step i) (site i.castSucc)) *
        ∏ i : Fin m, mask (site i.castSucc) * mask (site i.succ) := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [hs]
      ring
    _ = _ := by rw [closed_binary_mask_product hm site hsite mask hmask]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWordIdentity
namespace OAI

/-! Exact identification of a masked closed matrix word with the literal
centered word average.  No arithmetic or probabilistic estimate is assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma centeredTuple_column {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    centeredTuple (columnTuple w i).primeFactors n =
      ∏ j, ((if ((w j i).val : ℤ) ∣ n then (1 : ℝ) else 0) - ((w j i).val : ℝ)⁻¹) := by
  unfold centeredTuple
  rw [columnTuple_primeFactors w i hprime hdisjoint, prod_image]
  exact fun _ _ _ _ he => selectedPrimeValues_injective (fun j => w j i) hdisjoint he

theorem lifted_tuple_center_product {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n)
      (data.residueOrigin x) (columnTupleWord w forward padding) =
      ∏ t : Fin R × Fin J,
        ((if ((label t).val : ℤ) ∣ (x (label t)).val +
            wordDisplacement h ((columnTupleWord w forward padding).take t.1.val)
          then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹) := by
  simp only [columnTupleWord]
  rw [scalarWalkProduct_ofFn, Fintype.prod_prod_type]
  apply prod_congr rfl
  intro i _
  rw [centeredTuple_column w i hprime hdisjoint]
  apply prod_congr rfl
  intro j _
  rw [← hlabel i j]
  simp only [data.residueOrigin_divisibility]
  rfl

theorem lifted_catalog_mask_product {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s D : ℕ) (step : Fin R → SignedStep)
    (hR : 0 < R) (hRD : R ≤ D) (hclosed : wordDisplacement h (List.ofFn step) = 0)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    scalarWalkProduct h (fun _ n =>
      if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then (0 : ℝ) else 1)
      (data.residueOrigin x) (List.ofFn step) =
      attachedCatalogAvoidance data s B D (List.ofFn step) x := by
  rw [scalarWalkProduct_ofFn]
  have hc := attachedCatalogAvoidance_eq_departure_product data s B D (List.ofFn step)
    (by simpa only [List.length_ofFn] using hRD)
    (by simpa only [List.length_ofFn] using hR) hclosed x (data.residueOrigin x)
    (data.residueOrigin_spec x)
  apply Eq.trans _ hc.symm
  apply Fintype.prod_equiv (finCongr (List.length_ofFn (f := step))).symm
  intro i
  rfl

theorem closed_masked_word_eq_centered_product {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s D : ℕ) (hR : 0 < R) (hRD : R ≤ D)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (hg : ∀ n, g n ≠ 0) (x : ↥(data.P ∪ data.Q) → Fin B) :
    let mask := fun n => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
      then (0 : ℝ) else 1
    scalarWalkProduct h (fun t n => mask n *
      signedIntegerWeight Q u (eligible t) g (centeredTuple t.tuple.primeFactors)
        L K (extra t) h t n * mask (n + t.displacement h))
      (data.residueOrigin x) (columnTupleWord w forward padding) =
      data.residueValue
        (fun n => scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h)
          n (columnTupleWord w forward padding)) x *
      (∏ t : Fin R × Fin J,
        ((if ((label t).val : ℤ) ∣ (x (label t)).val +
            wordDisplacement h ((columnTupleWord w forward padding).take t.1.val)
          then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹)) *
      attachedCatalogAvoidance data s B D (columnTupleWord w forward padding) x := by
  dsimp only
  unfold columnTupleWord
  rw [closed_masked_scalar_word hR h _ (data.residueOrigin x) hclosed _ _
    (fun n => by split_ifs <;> simp)]
  rw [closed_signed_word_factorization Q u eligible g
    (fun t n => centeredTuple t.tuple.primeFactors n) L K extra h (data.residueOrigin x)
    (List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i))) hg
    (fun t q _ n => centeredTuple_padding_periodic t.tuple.primeFactors h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q n) hclosed]
  have hc := lifted_tuple_center_product data w forward padding hprime hdisjoint label hlabel x
  unfold columnTupleWord at hc
  rw [hc]
  rw [lifted_catalog_mask_product data s D _ hR hRD hclosed x]
  rfl

theorem closed_masked_word_average {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s D : ℕ) (hR : 0 < R) (hRD : R ≤ D)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop) (hg : ∀ n, g n ≠ 0) :
    let mask := fun n => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
      then (0 : ℝ) else 1
    (data.residueLaw B hB).average (fun x => scalarWalkProduct h (fun t n => mask n *
      signedIntegerWeight Q u (eligible t) g (centeredTuple t.tuple.primeFactors)
        L K (extra t) h t n * mask (n + t.displacement h))
      (data.residueOrigin x) (columnTupleWord w forward padding)) =
    prohibitedCenteredAverage data hB s D (columnTupleWord w forward padding) label
      (data.residueValue (fun n => scalarWalkProduct h
        (retainedEdgeDeparture Q u eligible g L K extra h) n (columnTupleWord w forward padding))) := by
  dsimp only
  unfold prohibitedCenteredAverage
  apply congrArg (data.residueLaw B hB).average
  funext x
  exact closed_masked_word_eq_centered_product data w forward padding hprime hdisjoint
    label hlabel s D hR hRD hclosed Q u eligible g L K extra hg x

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedClosedWordAverage
namespace OAI

/-! Identify the scalar word expectations appearing in the matrix bound. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

theorem maskedClosedWord_residue_average {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s budget : ℕ) (hR : 0 < R) (hRD : R ≤ budget)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (hg : ∀ n, g n ≠ 0) :
    (data.residueLaw B hB).average (fun x => scalarWalkProduct h
      (maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
        L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n))
      (data.residueOrigin x) (columnTupleWord w forward padding)) =
      prohibitedCenteredAverage data hB s budget (columnTupleWord w forward padding) label
        (data.residueValue (fun n => scalarWalkProduct h
          (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K
            (fun t => extra t.tuple) h) n (columnTupleWord w forward padding))) := by
  have hw : maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n) =
      fun t n =>
        (if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then (0 : ℝ) else 1) *
          signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
            L K (extra t.tuple) h t n *
          (if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + t.displacement h)
            then (0 : ℝ) else 1) := by
    funext t n
    by_cases hn : ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n <;>
      by_cases hm : ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
        (n + t.displacement h) <;>
      simp [maskedSignedIntegerWeight, vertexIndicator, hn, hm]
  rw [hw]
  exact closed_masked_word_average data hB w forward padding hprime hdisjoint label hlabel
    s budget hR hRD hclosed Q u (fun t => eligible t.tuple) g L K
    (fun t => extra t.tuple) hg

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MaskedWeightPeriodicity
namespace OAI

/-! The literal masked arithmetic weights depend only on the finite prime residues. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma centeredTuple_eq_of_prime_residues (P : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) :
    centeredTuple P n = centeredTuple P m := by
  unfold centeredTuple
  apply prod_congr rfl
  intro p hp
  have he : (p : ℤ) ∣ n ↔ (p : ℤ) ∣ m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]
  simp only [he]

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

lemma maskedSignedIntegerWeight_residue_congr {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (t : SignedStep) (htuple : t.tuple.primeFactors ⊆ data.P) (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t n =
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t m := by
  have hQ : ∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p) :=
    fun p hp => hnm ⟨p, mem_union_right _ hp⟩
  have hshift : ∀ p : ↥(data.P ∪ data.Q),
      ((n + t.displacement h : ℤ) : ZMod p.val) =
        ((m + t.displacement h : ℤ) : ZMod p.val) := by
    intro p
    simp only [Int.cast_add, hnm p]
  have hkeep (a b : ℤ) (hab : ∀ p ∈ data.Q, (a : ZMod p) = (b : ZMod p)) :
      integerEdgeKeep Q u (eligible t.tuple) g L K (extra t.tuple) a ↔
        integerEdgeKeep Q u (eligible t.tuple) g L K (extra t.tuple) b := by
    unfold integerEdgeKeep
    rw [paddingDensity_eq_of_prime_residues data.Q Q u (eligible t.tuple) g hsq hpool a b hab
      (hg a b hab), hextra t.tuple a b hab]
  have hcenter : centeredTuple t.tuple.primeFactors n = centeredTuple t.tuple.primeFactors m :=
    centeredTuple_eq_of_prime_residues _ n m
      (fun p hp => hnm ⟨p, mem_union_left _ (htuple hp)⟩)
  have hperiod : ∀ q ∈ Q, ∀ z,
      centeredTuple t.tuple.primeFactors (z + (h * q * t.tuple : ℕ)) =
        centeredTuple t.tuple.primeFactors z :=
    fun q _ z => centeredTuple_padding_periodic _ h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q z
  have hedge : signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
      L K (extra t.tuple) h t n =
      signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
        L K (extra t.tuple) h t m := by
    rw [signedIntegerWeight_departure Q u _ g _ L K _ h t n hperiod,
      signedIntegerWeight_departure Q u _ g _ L K _ h t m hperiod]
    by_cases hq : t.padding ∈ Q
    · have hd := squarefree_divisor_congr data.Q t.padding (hsq _ hq) (hpool _ hq) n m hQ
      have hQs : ∀ p ∈ data.Q,
          ((n + t.displacement h : ℤ) : ZMod p) =
            ((m + t.displacement h : ℤ) : ZMod p) :=
        fun p hp => hshift ⟨p, mem_union_right _ hp⟩
      simp only [hq, true_and, hd, hkeep n m hQ, hkeep _ _ hQs, hcenter,
        hg n m hQ, hg _ _ hQs]
    · simp only [hq, false_and, ite_false]
  dsimp only [maskedSignedIntegerWeight, vertexIndicator]
  simp only [data.prohibitedSite_congr hB s n m hnm,
    data.prohibitedSite_congr hB s _ _ hshift, hedge]
  split_ifs <;> rfl

lemma scalarWalkProduct_residue_congr (P : Finset ℕ) (h : ℕ)
    (weight : SignedStep → ℤ → ℝ) (w : List SignedStep)
    (hw : ∀ t ∈ w, ∀ n m : ℤ, (∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) →
      weight t n = weight t m) (n m : ℤ)
    (hnm : ∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) :
    scalarWalkProduct h weight n w = scalarWalkProduct h weight m w := by
  induction w generalizing n m with
  | nil => rfl
  | cons t w ih =>
      rw [scalarWalkProduct, scalarWalkProduct, hw t (List.mem_cons_self ..) n m hnm,
        ih (fun a ha => hw a (List.mem_cons_of_mem t ha))]
      intro p hp
      simp only [Int.cast_add, hnm p hp]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueMatrixMoment
namespace OAI

/-! Reduce the actual translated matrix moment to signed closed-word expectations. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [DecidableEq D] [Fintype V]

theorem physicalClosedPair_average_abs_le {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    {k : ℕ} (x : D × ℤ) (a b : Fin k → D × (Q × Bool))
    (hend : shiftWordEnd (integerShiftNext Q tuple h) x a =
      shiftWordEnd (integerShiftNext Q tuple h) x b)
    (hperiod : ∀ t ∈ integerClosedWordCode Q tuple (a, b), ∀ n m : ℤ,
      (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
        weight t n = weight t m) :
    |(data.residueLaw B hB).average (fun r =>
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x b)| ≤
      |(data.residueLaw B hB).average (fun r =>
        scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| := by
  have htrans := data.residue_average_translate hB
    (fun n => scalarWalkProduct h weight n (integerClosedWordCode Q tuple (a, b)))
    (fun n m hnm => scalarWalkProduct_residue_congr (data.P ∪ data.Q) h weight _
      (fun t ht z z' hz => hperiod t ht z z' (fun p => hz p.val p.property)) n m
      (fun p hp => hnm ⟨p, hp⟩)) x.2
  have hpair : (data.residueLaw B hB).average (fun r =>
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x a *
      shiftWordWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) x b) =
      (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
        (data.residueLaw B hB).average (fun r =>
          scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b))) := by
    calc
      _ = (data.residueLaw B hB).average (fun r =>
          (integerPathMask embed Q tuple h gate x a * integerPathMask embed Q tuple h gate x b) *
            scalarWalkProduct h weight (data.residueOrigin r + x.2)
              (integerClosedWordCode Q tuple (a, b))) := by
        apply congrArg (data.residueLaw B hB).average
        funext r
        rw [physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ x a b hend,
          add_comm x.2]
      _ = _ := by
        rw [← htrans]
        simp only [FiniteLaw.average, mul_sum]
        apply sum_congr rfl
        intro r _
        ring
  rw [hpair]
  rcases integerPathMask_zero_or_one embed Q tuple h gate x a with ha | ha <;>
    rcases integerPathMask_zero_or_one embed Q tuple h gate x b with hb | hb <;>
    simp [ha, hb]

variable [Fintype D] [DecidableEq V]

theorem physicalResidueMatrix_moment_le {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (tuple : D → ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n) (k : ℕ)
    (hperiod : ∀ (a b : Fin k → D × (Q × Bool)),
      ∀ t ∈ integerClosedWordCode Q tuple (a, b), ∀ n m : ℤ,
        (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
          weight t n = weight t m) :
    (data.residueLaw B hB).average (fun r =>
      matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤
      ∑ i : V, ∑ a : Fin k → D × (Q × Bool), ∑ b : Fin k → D × (Q × Bool),
        if shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
          shiftWordEnd (integerShiftNext Q tuple h) (embed i) b ∧
            integerPathMask embed Q tuple h gate (embed i) a ≠ 0 ∧
            integerPathMask embed Q tuple h gate (embed i) b ≠ 0 then
          |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
            (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0 := by
  rw [average_shiftMatrix_moment embed hinj]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro a _
  apply sum_le_sum
  intro b _
  by_cases hend : shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) b
  · by_cases ha : integerPathMask embed Q tuple h gate (embed i) a = 0
    · simp only [shiftClosedWeight, hend, ite_true, physicalShiftWord_product, ha,
        zero_mul, ne_eq, not_true_eq_false, false_and, and_false, ite_false,
        FiniteLaw.average_const, le_refl]
    · by_cases hb : integerPathMask embed Q tuple h gate (embed i) b = 0
      · simp only [shiftClosedWeight, hend, ite_true, physicalShiftWord_product, hb,
          zero_mul, mul_zero, ne_eq, not_true_eq_false, and_false, ite_false,
          FiniteLaw.average_const, le_refl]
      · simp only [shiftClosedWeight, hend, ha, hb, ne_eq, not_false_eq_true,
          and_self, ite_true]
        exact (le_abs_self _).trans
          (physicalClosedPair_average_abs_le data hB embed Q tuple gate weight hflip
            (embed i) a b hend (hperiod a b))
  · simp [shiftClosedWeight, hend]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeMatrixResidues
namespace OAI

/-! Discharge residue periodicity for the literal prime-family matrix weights. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem primeClosedPair_residue_congr {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool))
    (t : SignedStep)
    (ht : t ∈ integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b))
    (n m : ℤ) (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t n =
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t m := by
  rw [← closedTraceEncoding_word Q (a, b)] at ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  apply maskedSignedIntegerWeight_residue_congr data hB s Q u eligible g L K extra
    hsq hpool hg hextra _ _ n m hnm
  rw [columnTuple_primeFactors _ i hprime hdisjoint]
  intro p hp
  obtain ⟨j, _, rfl⟩ := mem_image.mp hp
  exact hP j ((closedTraceEncoding Q (a, b)).2.1 j i).property

lemma maskedSignedIntegerWeight_pairs (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (center : ℕ → ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (keep : ℤ → Prop)
    (pairs : Finset (ℕ × ℕ)) (hallowed : ∀ d q, eligible d q → (d, q) ∈ pairs)
    (t : SignedStep) (n : ℤ)
    (hw : maskedSignedIntegerWeight Q u eligible g center L K extra h keep t n ≠ 0) :
    (t.tuple, t.padding) ∈ pairs := by
  have hs := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
  exact hallowed _ _ (signedIntegerWeight_nonzero Q u (eligible t.tuple) g
    (center t.tuple) L K (extra t.tuple) h t n hs).2.1

lemma scalarWalkProduct_pairs (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (pairs : Finset (ℕ × ℕ))
    (hsupport : ∀ t n, weight t n ≠ 0 → (t.tuple, t.padding) ∈ pairs)
    (w : List SignedStep) (n : ℤ) (hw : scalarWalkProduct h weight n w ≠ 0) :
    ∀ t ∈ w, (t.tuple, t.padding) ∈ pairs := by
  induction w generalizing n with
  | nil => simp
  | cons t w ih =>
      have hp := mul_ne_zero_iff.mp hw
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hsupport _ _ hp.1
      · exact ih _ hp.2 a ha

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualClosedPairCatalog
namespace OAI

/-! The actual trace catalog retains the numerical masks and allowed pair support. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [DecidableEq D] [Fintype D] [Fintype V]



omit [DecidableEq D] [Fintype V] in
theorem actualClosedPairCatalog_sum {h J M B k : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (hsupport : ∀ t n, weight t n ≠ 0 → (t.tuple, t.padding) ∈ data.pairs)
    (x : D × ℤ) :
    (∑ a : Fin k → D × (Q × Bool), ∑ b : Fin k → D × (Q × Bool),
      if closedPairNumericalTest embed Q tuple h gate x (a, b) then
        |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
          (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0) =
      ∑ p ∈ actualClosedPairCatalog embed Q tuple h gate data.pairs k x,
        |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
          (data.residueOrigin r) (integerClosedWordCode Q tuple p))| := by
  simp only [actualClosedPairCatalog, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hv : closedPairNumericalTest embed Q tuple h gate x (a, b)
  · by_cases hp : ∀ t ∈ integerClosedWordCode Q tuple (a, b), (t.tuple, t.padding) ∈ data.pairs
    · rw [if_pos hv, if_pos ⟨hv, hp⟩]
    · have hz (r : ↥(data.P ∪ data.Q) → Fin B) :
          scalarWalkProduct h weight (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)) = 0 := by
        by_contra hne
        exact hp (scalarWalkProduct_pairs h weight data.pairs hsupport _ _ hne)
      simp only [hv, hp, and_false, ite_true, ite_false, hz, FiniteLaw.average_const, abs_zero]
  · simp only [hv, false_and, ite_false]

omit [DecidableEq D] [Fintype V] in
theorem actualClosedPairCatalog_closed {h k : ℕ}
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ)
    (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ)) (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool)))
    (hp : p ∈ actualClosedPairCatalog embed Q tuple h gate pairs k x) :
    wordDisplacement h (integerClosedWordCode Q tuple p) = 0 := by
  exact integer_closed_word_displacement Q tuple h x p.1 p.2 (mem_filter.mp hp).2.1.1


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnMatrixTrace
namespace OAI

/-! The actual residue-model matrix is bounded by the same literal column
catalog to which the four trace estimates apply. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem columnMatrix_residue_trace_le {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s budget : ℕ) (hk : 0 < 2 * k) (hbudget : 2 * k ≤ budget)
    (embed : V → ((j : Fin J) → P j) × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n, g n ≠ 0)
    (hgdep : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (hallowed : ∀ d q, eligible d q → (d, q) ∈ data.pairs) :
    let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
    let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
    (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
      (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
        (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤
      ∑ i : V, ∑ forward, ∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q tuple h gate data.pairs k (embed i)) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun j => (a.2 j).val)) (actualColumnLabel data hP a.1)
          (data.residueValue (fun n => scalarWalkProduct h
            (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K
              (fun t => extra t.tuple) h) n (columnTupleWord a.1 forward (fun j => (a.2 j).val))))| := by
  dsimp only
  let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
  let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
    L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
  let F (i : V) := actualClosedPairCatalog embed Q tuple h gate data.pairs k (embed i)
  have hbound := physicalResidueMatrix_moment_le data hB embed hinj Q tuple gate weight
    (maskedSignedIntegerWeight_flip Q u eligible g _ L K extra h _) k
    (fun a b t ht n m hnm => primeClosedPair_residue_congr data hB hP hprime hdisjoint
      s Q u eligible g L K extra hsq hpool hgdep hextra a b t ht n m hnm)
  refine hbound.trans_eq ?_
  apply sum_congr rfl
  intro i _
  trans (∑ a : Fin k → ((j : Fin J) → P j) × (Q × Bool),
    ∑ b : Fin k → ((j : Fin J) → P j) × (Q × Bool),
    if closedPairNumericalTest embed Q tuple h gate (embed i) (a, b) then
      |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
        (data.residueOrigin r) (integerClosedWordCode Q tuple (a, b)))| else 0)
  · apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    unfold closedPairNumericalTest
    split_ifs <;> rfl
  rw [actualClosedPairCatalog_sum data hB embed Q tuple gate weight
    (maskedSignedIntegerWeight_pairs Q u eligible g _ L K extra h _ data.pairs hallowed)]
  let term (forward : Fin (2 * k) → Bool)
      (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    |(data.residueLaw B hB).average (fun r => scalarWalkProduct h weight
      (data.residueOrigin r) (columnTupleWord a.1 forward (fun j => (a.2 j).val)))|
  calc
    _ = ∑ p ∈ F i, term (closedTraceEncoding Q p).1 (closedTraceEncoding Q p).2 := by
      apply sum_congr rfl
      intro p _
      simp only [term, closedTraceEncoding_word]
      rfl
    _ = ∑ forward, ∑ a ∈ closedTraceFiber Q (F i) forward, term forward a :=
      sum_closedTraceFiber Q hprime hdisjoint (F i) term
    _ = _ := by
      apply sum_congr rfl
      intro forward _
      apply sum_congr rfl
      intro a ha
      obtain ⟨p, hp, hword⟩ := closedTraceFiber_word Q (F i) forward a ha
      have hc : wordDisplacement h (columnTupleWord a.1 forward (fun j => (a.2 j).val)) = 0 := by
        rw [hword]
        exact actualClosedPairCatalog_closed embed Q tuple gate data.pairs (embed i) p hp
      dsimp only [term]
      apply congrArg abs
      exact maskedClosedWord_residue_average data hB a.1 forward (fun j => (a.2 j).val)
        hprime hdisjoint (actualColumnLabel data hP a.1) (fun _ _ => rfl)
        s budget hk hbudget hc Q u eligible g L K extra hg

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixTraceSummation
namespace OAI

/-! Sum the actual column bounds over signs and starting vertices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem matrix_residue_trace_of_column_bounds {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s budget : ℕ) (hk : 0 < 2 * k) (hbudget : 2 * k ≤ budget)
    (embed : V → ((j : Fin J) → P j) × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K T : ℝ) (extra : ℕ → ℤ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n, g n ≠ 0)
    (hgdep : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (hallowed : ∀ d q, eligible d q → (d, q) ∈ data.pairs)
    (hT : 0 ≤ T)
    (hdim : (Fintype.card V : ℝ) * (2 : ℝ) ^ (2 * k) ≤ Real.exp (108 * L))
    (hcolumn : ∀ (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool),
      Real.exp (108 * L) * (∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) ≤ T) :
    let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
    let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
    (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
      (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
        (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤ T := by
  dsimp only
  have hb := columnMatrix_residue_trace_le data hB hP hprime hdisjoint s budget hk hbudget
    embed hinj Q u eligible g L K extra gate hsq hpool hg hgdep hextra hallowed
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (108 * L))).mp
  calc
    _ ≤ Real.exp (108 * L) * (∑ i : V, ∑ forward, ∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k (embed i)) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun j => (a.2 j).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ ∑ _i : V, ∑ _forward : Fin (2 * k) → Bool, T := by
      simp only [mul_sum]
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro forward _
      simpa only [mul_sum] using hcolumn (embed i) forward
    _ = ((Fintype.card V : ℝ) * (2 : ℝ) ^ (2 * k)) * T := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ Real.exp (108 * L) * T := mul_le_mul_of_nonneg_right hdim hT

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.matrix_residue_trace_of_column_bounds := @OAI.TwoPointCorrelations.matrix_residue_trace_of_column_bounds
