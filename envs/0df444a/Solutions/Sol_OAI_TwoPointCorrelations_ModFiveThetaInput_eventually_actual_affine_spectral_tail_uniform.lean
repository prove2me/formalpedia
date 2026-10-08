-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:24:06.884416+00:00
-- url     : https://prove2.me/submissions/0bc41da5-da4c-4ce2-b817-788dfd1e5e85

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_actual_affine_word_comparison
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_actual_matrix_trace

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset



end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst


/-- Special case of Mathlib d13f23b's `spectralRadius_le_nnnorm` (which dropped the
`NormOneClass` assumption of the older `spectrum.spectralRadius_le_nnnorm`) for operators. -/
theorem spectralRadius_le_nnnorm_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) : spectralRadius ℂ T ≤ ‖T‖₊ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (E →L[ℂ] E) := inferInstance
    simp [spectralRadius, spectrum.of_subsingleton T]
  · exact spectrum.spectralRadius_le_nnnorm T

end

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




omit [DecidableEq V] in
lemma matrixFrobeniusSq_nonneg (A : Matrix V V ℝ) : 0 ≤ matrixFrobeniusSq A :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))



end Paths

section Nonbacktracking

variable {D V : Type*} [DecidableEq D]



variable [DecidableEq V]



end Nonbacktracking

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

/-- The signed expectations are compared before taking absolute values.
There is one initial-site factor, and no intermediate-site factor. -/
theorem shiftMatrix_moment_comparison (embed : V → S) (hinj : Function.Injective embed)
    (next : E → S → S) (weight : Ω → E → S → ℝ) (weight' : Ω' → E → S → ℝ)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ω') (k : ℕ) (ε : ℝ)
    (hcompare : ∀ i u v,
      |μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) -
        ν.average (fun ω => shiftClosedWeight embed next (weight' ω) k i u v)| ≤ ε) :
    |μ.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight ω) ^ k)) -
      ν.average (fun ω => matrixFrobeniusSq (shiftMatrix embed next (weight' ω) ^ k))| ≤
      (Fintype.card V : ℝ) * (Fintype.card E : ℝ) ^ (2 * k) * ε := by
  classical
  rw [average_shiftMatrix_moment embed hinj, average_shiftMatrix_moment embed hinj,
    ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ u : Fin k → E, ∑ v : Fin k → E,
        |μ.average (fun ω => shiftClosedWeight embed next (weight ω) k i u v) -
          ν.average (fun ω => shiftClosedWeight embed next (weight' ω) k i u v)| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro u _
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : V, ∑ _u : Fin k → E, ∑ _v : Fin k → E, ε :=
      sum_le_sum (fun i _ => sum_le_sum (fun u _ => sum_le_sum (fun v _ => hcompare i u v)))
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
        Nat.cast_pow]
      rw [show 2 * k = k + k by omega, pow_add]
      ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixMomentNorm
namespace OAI

/-! The unnormalized matrix moment controls the operator norm used in the spectral step. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma real_matrix_row_square (A : Matrix V V ℝ) (v : V → ℂ) (i : V) :
    ‖∑ j, (A i j : ℂ) * v j‖ ^ 2 ≤
      (∑ j, (A i j) ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
  have htri : ‖∑ j, (A i j : ℂ) * v j‖ ≤ ∑ j, |A i j| * ‖v j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sum_le univ (fun j => (A i j : ℂ) * v j)
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun j => |A i j|) (fun j => ‖v j‖)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)))).mpr htri
  exact hsq.trans (by simpa only [sq_abs] using hcs)

theorem real_matrix_operator_norm_le (A : Matrix V V ℝ) :
    ‖matrixOperator (fun i j => (A i j : ℂ))‖ ≤ Real.sqrt (matrixFrobeniusSq A) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hsum : ‖matrixOperator (fun i j => (A i j : ℂ)) v‖ ^ 2 ≤
      matrixFrobeniusSq A * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [matrixOperator_apply]
    calc
      _ ≤ ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, ‖v j‖ ^ 2 :=
        sum_le_sum (fun i _ => real_matrix_row_square A (fun j => v j) i)
      _ = _ := by rw [← sum_mul]; rfl
  have hroot := Real.sq_sqrt (matrixFrobeniusSq_nonneg A)
  have hn := norm_nonneg (matrixOperator (fun i j => (A i j : ℂ)) v)
  have hprod : 0 ≤ Real.sqrt (matrixFrobeniusSq A) * ‖v‖ := by positivity
  nlinarith

lemma matrixOperator_mul (A B : Matrix V V ℂ) :
    matrixOperator (A * B) = matrixOperator A * matrixOperator B := by
  ext v i
  change (∑ j, (A * B) i j * v j) =
    ∑ j, A i j * (∑ k, B j k * v k)
  simp only [Matrix.mul_apply]
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma matrixOperator_one : matrixOperator (1 : Matrix V V ℂ) = 1 := by
  ext v i
  change (∑ j, (1 : Matrix V V ℂ) i j * v j) = v i
  simp [Matrix.one_apply]

lemma matrixOperator_pow (A : Matrix V V ℂ) (k : ℕ) :
    matrixOperator (A ^ k) = matrixOperator A ^ k := by
  induction k with
  | zero => simp only [pow_zero, matrixOperator_one]
  | succ k ih => rw [pow_succ, matrixOperator_mul, ih, pow_succ]


omit [DecidableEq V] in
lemma real_matrix_cast_mul (A B : Matrix V V ℝ) :
    complexifyMatrix (A * B) = complexifyMatrix A * complexifyMatrix B := by
  ext i j
  change ((∑ x, A i x * B x j : ℝ) : ℂ) = ∑ x, (A i x : ℂ) * (B x j : ℂ)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]

lemma real_matrix_cast_pow (A : Matrix V V ℝ) (k : ℕ) :
    complexifyMatrix (A ^ k) = complexifyMatrix A ^ k := by
  induction k with
  | zero =>
      ext i j
      change (((1 : Matrix V V ℝ) i j : ℝ) : ℂ) = (1 : Matrix V V ℂ) i j
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  | succ k ih => rw [pow_succ, real_matrix_cast_mul, ih, pow_succ]

/-- The precise moment-to-operator inequality used by spectral transfer. -/
theorem real_matrix_operator_power_norm_le (A : Matrix V V ℝ) (k : ℕ) :
    ‖matrixOperator (fun i j => (A i j : ℂ)) ^ k‖ ≤
      Real.sqrt (matrixFrobeniusSq (A ^ k)) := by
  have hpow := matrixOperator_pow (complexifyMatrix A) k
  have hcast := congrArg matrixOperator (real_matrix_cast_pow A k)
  calc
    _ = ‖matrixOperator (fun i j => ((A ^ k) i j : ℂ))‖ :=
      congrArg norm (hpow.symm.trans hcast.symm)
    _ ≤ _ := real_matrix_operator_norm_le (A ^ k)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixSpectralTail
namespace OAI

/-! The exact unnormalized moment controls the exceptional block origins.
No self-adjointness of the nonbacktracking matrix is needed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma real_matrix_spectral_power_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (k : ℕ) (hk : 0 < k) :
    realMatrixSpectralRadius A ^ (2 * k) ≤ matrixFrobeniusSq (A ^ k) := by
  let T := matrixOperator (fun i j => (A i j : ℂ))
  have hp := (spectrum.spectralRadius_pow_le (𝕜 := ℂ) T k (by omega)).trans
    (spectralRadius_le_nnnorm_clm (T ^ k))
  have hr : realMatrixSpectralRadius A ^ k ≤ ‖T ^ k‖ := by
    have ht := ENNReal.toReal_mono (by exact ENNReal.coe_ne_top) hp
    simpa only [realMatrixSpectralRadius, ENNReal.toReal_pow, ENNReal.coe_toReal,
      coe_nnnorm] using ht
  have hm := hr.trans (real_matrix_operator_power_norm_le A k)
  have hnonneg : 0 ≤ realMatrixSpectralRadius A ^ k := pow_nonneg ENNReal.toReal_nonneg _
  have hs := (sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).mpr hm
  rw [Real.sq_sqrt (matrixFrobeniusSq_nonneg _)] at hs
  simpa only [Nat.mul_comm 2 k, pow_mul] using hs

theorem FiniteLaw.matrix_spectral_tail {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix V V ℝ) (k : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B)
    (hmoment : μ.average (fun x => matrixFrobeniusSq (A x ^ k)) ≤ B ^ (2 * k)) :
    μ.probability (fun x => Real.exp 1 * B < realMatrixSpectralRadius (A x)) ≤
      Real.exp (-(2 * k : ℕ)) := by
  have hden : 0 < (Real.exp 1 * B) ^ (2 * k) := pow_pos (mul_pos (Real.exp_pos _) hB) _
  calc
    _ ≤ μ.average (fun x => matrixFrobeniusSq (A x ^ k) / (Real.exp 1 * B) ^ (2 * k)) := by
      apply μ.average_mono
      intro x
      by_cases hx : Real.exp 1 * B < realMatrixSpectralRadius (A x)
      · rw [if_pos hx]
        apply (one_le_div hden).mpr
        exact (pow_le_pow_left₀ (by positivity) hx.le _).trans
          (real_matrix_spectral_power_le (A x) k hk)
      · rw [if_neg hx]
        exact div_nonneg (matrixFrobeniusSq_nonneg _) hden.le
    _ = μ.average (fun x => matrixFrobeniusSq (A x ^ k)) / (Real.exp 1 * B) ^ (2 * k) := by
      simp only [div_eq_mul_inv, μ.average_mul_const]
    _ ≤ B ^ (2 * k) / (Real.exp 1 * B) ^ (2 * k) :=
      div_le_div_of_nonneg_right hmoment hden.le
    _ = ((Real.exp 1) ^ (2 * k))⁻¹ := by
      rw [mul_pow]
      field_simp
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      simp

lemma trace_moment_add_one_le (B : ℝ) (hB : 1 ≤ B) (n : ℕ) (hn : 0 < n) :
    B ^ n + 1 ≤ (2 * B) ^ n := by
  have hb : 1 ≤ B ^ n := one_le_pow₀ hB
  have ht : (2 : ℝ) ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    nlinarith [(one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ m)]
  rw [mul_pow]
  nlinarith

theorem FiniteLaw.matrix_spectral_tail_add_one {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Matrix V V ℝ) (k : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 1 ≤ B)
    (hmoment : μ.average (fun x => matrixFrobeniusSq (A x ^ k)) ≤ B ^ (2 * k) + 1) :
    μ.probability (fun x => Real.exp 1 * (2 * B) < realMatrixSpectralRadius (A x)) ≤
      Real.exp (-(2 * k : ℕ)) := by
  exact μ.matrix_spectral_tail A k hk (2 * B) (by linarith)
    (hmoment.trans (trace_moment_add_one_le B hB (2 * k) (by omega)))

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











lemma modFivePrimesUpTo_le {one : Bool} {x : ℝ} (hx : 0 ≤ x) {p : ℕ}
    (hp : p ∈ modFivePrimesUpTo one x) : (p : ℝ) ≤ x :=
  (Nat.le_floor_iff hx).mp (mem_Icc.mp (mem_filter.mp hp).1).2



lemma log_nat_nonneg (p : ℕ) : 0 ≤ Real.log (p : ℝ) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)



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





lemma centeredPrimeSupply_global_bounds {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 ≤ A) (hW : 0 ≤ W) {J i p : ℕ} (hi : i < J)
    (hL : primeSupplyEndpoint A W J ≤ L) (hp : p ∈ centeredPrimeSupply E A W i) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  have hh := centeredPrimeSupply_mem hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
  have hlo : A < Real.log p := by
    have hmono := primeSupplyEndpoint_mono A W hA hW (Nat.zero_le i)
    rw [primeSupplyEndpoint_zero] at hmono
    exact hmono.trans_lt hh.2.2.2.1
  have hhi : Real.log p ≤ L := hh.2.2.2.2.trans
    ((primeSupplyEndpoint_mono A W hA hW (Nat.succ_le_of_lt hi)).trans hL)
  constructor
  · simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hlo
  · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hhi

lemma primeSupplyEndpoint_sum_lt (A W : ℝ) (hA : 0 < A) (hW : 1 ≤ W) (J : ℕ) :
    (∑ i ∈ range J, primeSupplyEndpoint A W (i + 1)) < 2 * primeSupplyEndpoint A W J := by
  have hratio : 2 ≤ Real.exp (6 * W) := by
    linarith [Real.add_one_le_exp (6 * W)]
  induction J with
  | zero => simp [primeSupplyEndpoint, hA]
  | succ J ih =>
    have he : 0 ≤ primeSupplyEndpoint A W J := by unfold primeSupplyEndpoint; positivity
    have hstep : 2 * primeSupplyEndpoint A W J ≤ primeSupplyEndpoint A W (J + 1) := by
      rw [primeSupplyEndpoint_succ]
      nlinarith [mul_le_mul_of_nonneg_right hratio he]
    rw [sum_range_succ]
    linarith

lemma centeredPrimeSupply_tuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    (p : Fin J → ℕ) (hp : ∀ i : Fin J, p i ∈ centeredPrimeSupply E A W i.val) :
    Real.log ((∏ i, p i : ℕ) : ℝ) < 2 * L := by
  have hlog : Real.log ((∏ i, p i : ℕ) : ℝ) = ∑ i, Real.log (p i : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (centeredPrimeSupply_mem (hp i)).1.ne_zero
  rw [hlog]
  calc
    _ ≤ ∑ i : Fin J, primeSupplyEndpoint A W (i.val + 1) :=
      sum_le_sum (fun i _ => (centeredPrimeSupply_mem (hp i)).2.2.2.2)
    _ = ∑ i ∈ range J, primeSupplyEndpoint A W (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => primeSupplyEndpoint A W (i + 1)) J
    _ < 2 * primeSupplyEndpoint A W J := primeSupplyEndpoint_sum_lt A W hA hW J
    _ ≤ 2 * L := by linarith


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PhysicalMatrixComparison
namespace OAI

/-! Compare physical matrix moments by their signed closed scalar words.
Copy gates remain fixed while only the arithmetic origin is averaged. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma FiniteLaw.uniform_average {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (FiniteLaw.uniform α).average f = uniformAverage f := by
  simp only [FiniteLaw.average, FiniteLaw.uniform, uniformAverage, ← mul_sum, div_eq_mul_inv]
  ring

theorem physicalMatrix_moment_comparison {D V α β : Type*}
    [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype α] [Fintype β]
    (embed : V → D × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ)
    (hflip : ∀ t n, weight t.flip (n + t.displacement h) = weight t n)
    (μ : FiniteLaw α) (ν : FiniteLaw β) (origin : α → ℤ) (origin' : β → ℤ)
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcompare : ∀ (i : V) (a b : Fin k → D × (Q × Bool)),
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
        shiftWordEnd (integerShiftNext Q tuple h) (embed i) b →
      |μ.average (fun x => scalarWalkProduct h weight ((embed i).2 + origin x)
          (integerClosedWordCode Q tuple (a, b))) -
        ν.average (fun x => scalarWalkProduct h weight ((embed i).2 + origin' x)
          (integerClosedWordCode Q tuple (a, b)))| ≤ ε) :
    |μ.average (fun x => matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin x))) ^ k)) -
      ν.average (fun x => matrixFrobeniusSq (shiftMatrix embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin' x))) ^ k))| ≤
      (Fintype.card V : ℝ) * (Fintype.card (D × (Q × Bool)) : ℝ) ^ (2 * k) * ε := by
  apply shiftMatrix_moment_comparison embed hinj
  intro i a b
  by_cases hend : shiftWordEnd (integerShiftNext Q tuple h) (embed i) a =
      shiftWordEnd (integerShiftNext Q tuple h) (embed i) b
  · have ha (x : α) : shiftClosedWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin x))) k i a b =
        (integerPathMask embed Q tuple h gate (embed i) a *
          integerPathMask embed Q tuple h gate (embed i) b) *
          scalarWalkProduct h weight ((embed i).2 + origin x) (integerClosedWordCode Q tuple (a, b)) := by
      rw [shiftClosedWeight, if_pos hend]
      exact physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ _ a b hend
    have hb (x : β) : shiftClosedWeight embed (integerShiftNext Q tuple h)
        (physicalShiftWeight Q tuple h gate (fun t n => weight t (n + origin' x))) k i a b =
        (integerPathMask embed Q tuple h gate (embed i) a *
          integerPathMask embed Q tuple h gate (embed i) b) *
          scalarWalkProduct h weight ((embed i).2 + origin' x) (integerClosedWordCode Q tuple (a, b)) := by
      rw [shiftClosedWeight, if_pos hend]
      exact physicalShiftWord_closed_pair embed Q tuple h gate weight hflip _ _ a b hend
    simp_rw [ha, hb]
    rcases integerPathMask_zero_or_one embed Q tuple h gate (embed i) a with hma | hma <;>
      rcases integerPathMask_zero_or_one embed Q tuple h gate (embed i) b with hmb | hmb
    all_goals simp only [hma, hmb, zero_mul, mul_zero, one_mul, FiniteLaw.average_const,
      sub_self, abs_zero]
    all_goals first | exact hε | exact hcompare i a b hend
  · simpa only [shiftClosedWeight, hend, ite_false, FiniteLaw.average_const, sub_self, abs_zero] using hε

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceIntervalError
namespace OAI

/-! The finite word-comparison error absorbs the full physical trace
catalog, including every initial vertex and both words of the pair. -/

namespace TwoPointCorrelations

lemma trace_interval_error_le_one (L : ℝ) (k : ℕ) (v e : ℝ)
    (hL : 4800 ≤ L) (hk : (k : ℝ) ≤ L) (he0 : 0 ≤ e)
    (hv : v ≤ Real.exp (106 * L)) (he : e ≤ Real.exp (L ^ 4)) :
    v * e ^ (2 * k) * Real.exp (-(L ^ 9)) ≤ 1 := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL2 : 106 ≤ L ^ 2 := by nlinarith
  have hL4 : 106 ≤ L ^ 4 := hL2.trans (pow_le_pow_right₀ hL1 (by norm_num))
  have h15 : 106 * L ≤ L ^ 5 := by
    have hh := mul_le_mul_of_nonneg_right hL4 hL0
    nlinarith
  have h59 : 3 * L ^ 5 ≤ L ^ 9 := by
    have hh := mul_le_mul_of_nonneg_right (show 3 ≤ L ^ 4 by linarith) (pow_nonneg hL0 5)
    nlinarith
  calc
    _ ≤ Real.exp (106 * L) * (Real.exp (L ^ 4)) ^ (2 * k) * Real.exp (-(L ^ 9)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hv (pow_le_pow_left₀ he0 he _) (pow_nonneg he0 _) (Real.exp_pos _).le
    _ = Real.exp (106 * L + (2 * k : ℕ) * L ^ 4 - L ^ 9) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp (106 * L + 2 * L ^ 5 - L ^ 9) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hk (pow_nonneg hL0 4)
      push_cast
      nlinarith
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
namespace OAI

/-! The literal finite retained-divisor set and its Euler-product mass.
Distinct prime subsets produce distinct integers, so the divisor sum does
not contain hidden multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma retainedPrimeDivisor_pos (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    {u : ℕ} (hu : u ∈ retainedPrimeDivisors S) : 0 < u := by
  obtain ⟨U, hU, rfl⟩ := mem_image.mp hu
  exact prod_pos (fun p hp => (hS p ((mem_powerset.mp hU) hp)).pos)




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTupleMass
namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma centeredPrimeTuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j)) :
    0 < d ∧ Real.log d ≤ 2 * L := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  constructor
  · exact prod_pos fun j _ => (centeredPrimeSupply_mem (x j).property).1.pos
  · exact (centeredPrimeSupply_tuple_log_bound hA hW hL
      (fun j => (x j).val) (fun j => (x j).property)).le




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

lemma centeredPrimeBand_subset_pool (E : Finset ℕ) (A W : ℝ) (J : ℕ) (j : Fin J) :
    centeredPrimeBands E A W J j ⊆ centeredPrimePool E A W J := by
  intro p hp
  exact mem_primeTuplePool.mpr ⟨j, hp⟩

lemma centeredPrimePool_bounds (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) :
    Real.exp A < (p : ℝ) ∧ (p : ℝ) ≤ Real.exp L := by
  obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
  exact centeredPrimeSupply_global_bounds hA hW j.isLt hL hj

lemma paddingPrimeSupply_bounds (E : Finset ℕ) (L : ℝ) {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : (p : ℝ) ≤ Real.exp L :=
  modFivePrimesUpTo_le (Real.exp_pos _).le (Finset.mem_sdiff.mp hp).1

lemma actualProhibitedPrimeFamily_residue_bound (h J M : ℕ) (E : Finset ℕ)
    (A W L : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ}
    (hp : p ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).P ∪
      (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).Q) :
    p ≤ ⌊Real.exp L⌋₊ := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  rcases mem_union.mp hp with hp | hp
  · exact (centeredPrimePool_bounds E A W L J hA hW hL hp).2
  · exact paddingPrimeSupply_bounds E L hp

lemma centeredPrimePool_lower_nat (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {p : ℕ} (hp : p ∈ centeredPrimePool E A W J) : ⌈Real.exp A⌉₊ ≤ p :=
  Nat.ceil_le.mpr (centeredPrimePool_bounds E A W L J hA hW hL hp).1.le


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



lemma centeredPrimeTuple_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (centeredPrimeBands E A W J)) :
    d ≤ ⌊Real.exp (2 * L)⌋₊ := by
  have hb := centeredPrimeTuple_log_bound hA hW hL hd
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hb.1
  simpa only [Real.exp_log hdpos] using Real.exp_le_exp.mpr hb.2

/-- Removing one prime from an actual tuple only reduces its value. -/
lemma centeredPrimeTuple_complement_upper (E : Finset ℕ) (A W L : ℝ) (J : ℕ)
    (hA : 0 < A) (hW : 1 ≤ W) (hL : primeSupplyEndpoint A W J ≤ L)
    (x : (j : Fin J) → centeredPrimeBands E A W J j) (j : Fin J) :
    (∏ i ∈ univ.erase j, (x i).val) ≤ ⌊Real.exp (2 * L)⌋₊ := by
  apply le_trans _ (centeredPrimeTuple_upper E A W L J hA hW hL
    (mem_image.mpr ⟨x, mem_univ _, rfl⟩))
  exact Nat.le_of_dvd (prod_pos (fun i _ => (centeredPrimeSupply_mem (x i).property).1.pos))
    (prod_dvd_prod_of_subset (univ.erase j) univ (fun i => (x i).val) (erase_subset _ _))

lemma paddingPairEligible_padding_upper {L η : ℝ} {d q : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hd : 0 < d)
    (he : PaddingPairEligible L η d q) : q ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  by_cases hq : q = 0
  · simp [hq]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  let j := paddingBin η 0 (Real.log (d * q : ℕ))
  have hj := (mem_paddingBinIndices_iff L η j hη).mp he.2
  have hx := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp rfl
  simp only [add_zero] at hx
  have hxupper : Real.log (d * q : ℕ) ≤ 100 * L + 1 := by
    nlinarith [hj.2, hx.2]
  have hqlog : Real.log q ≤ Real.log (d * q : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul hd0 hq0]
    linarith [log_nat_nonneg d]
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  have hqp : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  simpa only [Real.exp_log hqp] using Real.exp_le_exp.mpr (hqlog.trans hxupper)

lemma actualProhibitedPrimeFamily_padding_upper (h J M : ℕ) (E : Finset ℕ)
    (A W L η : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hη : 0 < η) (hηone : η ≤ 1)
    (he : ∀ d q, eligible d q → PaddingPairEligible L η d q)
    {dq : ℕ × ℕ}
    (hdq : dq ∈ (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs) :
    dq.2 ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
  have hm := (actualProhibitedPrimeFamily_pairs h J M E A W L eligible hA hW hE
    dq.1 dq.2).mp hdq
  have hs := (actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).tuple_squarefree dq hdq
  exact paddingPairEligible_padding_upper hη hηone (Nat.pos_of_ne_zero hs.ne_zero)
    (he dq.1 dq.2 hm.2.2.2)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeBlockDimension
namespace OAI

/-! The actual tuple copies and the length-exp(103L) block fit the
exp(106L) starting-vertex allowance in the matrix trace. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma primeTuple_card_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (Dmax : ℕ)
    (hmax : ∀ d : (j : Fin J) → P j, (∏ j, (d j).val) ≤ Dmax) :
    Fintype.card ((j : Fin J) → P j) ≤ Dmax := by
  have hp (d : (j : Fin J) → P j) : 0 < ∏ j, (d j).val :=
    prod_pos (fun j _ => (hprime j _ (d j).property).pos)
  let f : ((j : Fin J) → P j) → Fin Dmax := fun d =>
    ⟨(∏ j, (d j).val) - 1, by have := hmax d; have := hp d; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply primeTuple_injective hprime hdisjoint
    have he := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    change (∏ j, (a j).val) - 1 = (∏ j, (b j).val) - 1 at he
    change (∏ j, (a j).val) = (∏ j, (b j).val)
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem actual_prime_block_dimension (E : Finset ℕ) (W L : ℝ)
    (hW : 1 ≤ W) (hL : 1 ≤ L) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    (Fintype.card (((j : Fin J) → P j) × Fin ⌈Real.exp (103 * L)⌉₊) : ℝ) ≤
      Real.exp (106 * L) := by
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
  have hend : primeSupplyEndpoint A W J ≤ L :=
    primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL
  have hd : Fintype.card ((j : Fin J) → P j) ≤ ⌊Real.exp (2 * L)⌋₊ := by
    apply primeTuple_card_le P (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA.le (zero_le_one.trans hW))
    intro d
    exact centeredPrimeTuple_upper E A W L J hA hW hend (mem_image.mpr ⟨d, mem_univ _, rfl⟩)
  have hdc : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) := by
    exact_mod_cast hd
  have hd' : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    hdc.trans (Nat.floor_le (Real.exp_pos _).le)
  have hm : (⌈Real.exp (103 * L)⌉₊ : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have he := Real.one_le_exp (show 0 ≤ 103 * L by linarith)
    have hc : (⌈Real.exp (103 * L)⌉₊ : ℝ) ≤ Real.exp (103 * L) + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ Real.exp (103 * L) from (Real.exp_pos _).le)).le
    linarith
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    _ ≤ Real.exp (2 * L) * (2 * Real.exp (103 * L)) :=
      mul_le_mul hd' hm (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = 2 * (Real.exp (2 * L) * Real.exp (103 * L)) := by ring
    _ = 2 * Real.exp (105 * L) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp L * Real.exp (105 * L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp L]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeAlphabetSize
namespace OAI

/-! The full forced-step alphabet includes all bounded padding divisors.
Its size still fits the polynomial exponential budget of finite-law
comparison; no eligibility restriction is needed for this count. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma boundedPaddingDivisor_real_upper (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (q : ℝ) ≤ Real.exp (100 * L ^ 2) := by
  have hr := (mem_filter.mp hq).1
  have hsq := retainedPrimeDivisor_squarefree (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hpool := retainedPrimeDivisor_factors (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hdeg : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    (show (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) by
      exact_mod_cast (mem_filter.mp hq).2).trans
        (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg hL)))
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    _ ≤ ∏ _p ∈ q.primeFactors, Real.exp L :=
      Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
        (fun p hp => paddingPrimeSupply_bounds E L (hpool hp))
    _ = Real.exp ((q.primeFactors.card : ℝ) * L) := by
      rw [prod_const, Real.exp_nat_mul]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

lemma boundedPaddingDivisors_card (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ((boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊).card : ℝ) ≤
      Real.exp (100 * L ^ 2) := by
  let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  let N := ⌊Real.exp (100 * L ^ 2)⌋₊
  have hp (q : Q) : 0 < q.val := retainedPrimeDivisor_pos (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp q.property).1
  have hq (q : Q) : q.val ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr (boundedPaddingDivisor_real_upper E L hL _ q.property)
  let f : Q → Fin N := fun q => ⟨q.val - 1, by have := hp q; have := hq q; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he : a.val - 1 = b.val - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  have hc : Q.card ≤ N := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact (show (Q.card : ℝ) ≤ N by exact_mod_cast hc).trans (Nat.floor_le (Real.exp_pos _).le)

lemma actual_prime_alphabet_size (E : Finset ℕ) (W L : ℝ) (hW : 1 ≤ W) (hL : 4800 ≤ L) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
    (Fintype.card (((j : Fin J) → P j) × (Q × Bool)) : ℝ) ≤ Real.exp (L ^ 4) := by
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hend : primeSupplyEndpoint A W J ≤ L := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  have hd : Fintype.card ((j : Fin J) → P j) ≤ ⌊Real.exp (2 * L)⌋₊ := by
    apply primeTuple_card_le P (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA.le (by linarith))
    intro d
    exact centeredPrimeTuple_upper E A W L J hA hW hend (mem_image.mpr ⟨d, mem_univ _, rfl⟩)
  have hd' : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    (show (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by exact_mod_cast hd).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hq := boundedPaddingDivisors_card E L (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (2 * L) * (Real.exp (100 * L ^ 2) * Real.exp L) := by gcongr
    _ = Real.exp (100 * L ^ 2 + 3 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hL2 : 103 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 103 by linarith) (sq_nonneg L)]

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

lemma ProhibitedPrimeFamily.pair_cross_coprime {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (a b : data.pairs) : a.val.1.Coprime b.val.2 := by
  apply (Nat.disjoint_primeFactors (data.tuple_squarefree _ a.property).ne_zero
    (data.padding_squarefree _ b.property).ne_zero).mp
  exact data.disjoint.mono (data.tuple_pool _ a.property) (data.padding_pool _ b.property)

lemma ProhibitedPrimeFamily.pair_product_injective {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) :
    Function.Injective (fun a : data.pairs => a.val.1 * a.val.2) := by
  intro a b hab
  change a.val.1 * a.val.2 = b.val.1 * b.val.2 at hab
  have hdab : a.val.1 ∣ b.val.1 := (data.pair_cross_coprime a b).dvd_of_dvd_mul_right
    (hab ▸ dvd_mul_right a.val.1 a.val.2)
  have hdba : b.val.1 ∣ a.val.1 := (data.pair_cross_coprime b a).dvd_of_dvd_mul_right
    (hab.symm ▸ dvd_mul_right b.val.1 b.val.2)
  have hd : a.val.1 = b.val.1 := Nat.dvd_antisymm hdab hdba
  have hq : a.val.2 = b.val.2 := by
    rw [← hd] at hab
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero) hab
  exact Subtype.ext (Prod.ext hd hq)

lemma ProhibitedPrimeFamily.pairs_card_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (B : ℕ)
    (hB : ∀ dq ∈ data.pairs, dq.1 * dq.2 ≤ B) : data.pairs.card ≤ B := by
  have hp (a : data.pairs) : 0 < a.val.1 * a.val.2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (data.tuple_squarefree _ a.property).ne_zero)
      (Nat.pos_of_ne_zero (data.padding_squarefree _ a.property).ne_zero)
  let f : data.pairs → Fin B := fun a =>
    ⟨a.val.1 * a.val.2 - 1, by have := hp a; have := hB _ a.property; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply data.pair_product_injective
    change a.val.1 * a.val.2 = b.val.1 * b.val.2
    have he : a.val.1 * a.val.2 - 1 = b.val.1 * b.val.2 - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf

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

lemma actualProhibitedPrimeFamily_pairs_card (h J M : ℕ) (E : Finset ℕ)
    (A W L η : ℝ) (eligible : ℕ → ℕ → Prop) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1)
    (he : ∀ d q, eligible d q → PaddingPairEligible L η d q) :
    ((actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE).pairs.card : ℝ) ≤
      Real.exp (101 * L) := by
  let data := actualProhibitedPrimeFamily h J M E A W L eligible hA hW hE
  have hb : data.pairs.card ≤ ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply data.pairs_card_le
    intro dq hdq
    have hm := (actualProhibitedPrimeFamily_pairs h J M E A W L eligible hA hW hE
      dq.1 dq.2).mp hdq
    exact paddingPairEligible_product_upper hη hηone (he _ _ hm.2.2.2)
  have hbr : (data.pairs.card : ℝ) ≤ (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) := by exact_mod_cast hb
  exact (hbr.trans (Nat.floor_le (Real.exp_pos _).le)).trans
    (Real.exp_le_exp.mpr (by linarith))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeTraceParameters
namespace OAI

/-! The canonical prime count and padding degree cap satisfy the numerical
budgets of the trace theorem with an absolute coefficient. -/

namespace TwoPointCorrelations

lemma prime_trace_degree_budget (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    ((primeSupplyCount W L + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ 101 * Real.log L ∧
      (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hcount := primeSupplyCount_mul_bound W L (by linarith) hL
  have hprod : (primeSupplyCount W L : ℝ) ≤ primeSupplyCount W L * (6 * W) := by
    have hb := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ primeSupplyCount W L by positivity)
    nlinarith
  have hj : (primeSupplyCount W L : ℝ) ≤ Real.log L := by
    nlinarith
  have hm : (⌊100 * Real.log L⌋₊ : ℝ) ≤ 100 * Real.log L := Nat.floor_le (by positivity)
  refine ⟨?_, hm⟩
  push_cast
  linarith

lemma prime_trace_endpoints (L : ℝ) (hL : 1 ≤ L) :
    1 ≤ ⌊Real.exp L⌋₊ ∧
      (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L ∧
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ ⌈Real.exp (L ^ (199 / 200 : ℝ))⌉₊ ∧
      (⌊Real.exp (100 * L + 1)⌋₊ : ℝ) ≤ Real.exp (100 * L + 1) ∧
      (⌊Real.exp (2 * L)⌋₊ : ℝ) ≤ Real.exp (2 * L) := by
  refine ⟨?_, Nat.floor_le (Real.exp_pos _).le, Nat.le_ceil _,
    Nat.floor_le (Real.exp_pos _).le, Nat.floor_le (Real.exp_pos _).le⟩
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa only [Nat.cast_one] using Real.one_le_exp (by linarith : 0 ≤ L)

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



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeMatrix
namespace OAI

/-! The residue-model trace bound for the actual prime supplies and padding
normalization. Its only analytic input is the cited fixed-modulus prime theorem. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma canonicalTraceFamily_residue_bound (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) :
    ∀ p ∈ (canonicalTraceFamily h E W L eligible hL hW hE).P ∪
      (canonicalTraceFamily h E W L eligible hL hW hE).Q, p ≤ ⌊Real.exp L⌋₊ :=
  fun _ hp => actualProhibitedPrimeFamily_residue_bound h _ _ E _ W L eligible _ _ hE
    (primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL) hp

theorem ModFiveThetaInput.eventually_actual_prime_matrix_trace (hprime : ModFiveThetaInput)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let g := actualPaddingVertex Qp
      let keep := fun n => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) n
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) g (fun d => centeredTuple d.primeFactors)
        L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L) h keep
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
      (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix embed (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_actual_matrix_trace h 101 W hh (by norm_num) hW,
    hprime.eventually_actual_pool_masses E W hW] with L htrace hmasses
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hA : 0 < A := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
  have hend : primeSupplyEndpoint A W J ≤ L :=
    primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL
  have hP (j : Fin J) : P j ⊆ data.P := centeredPrimeBand_subset_pool E A W J j
  have hdegree := prime_trace_degree_budget W L hW hL
  have hep := prime_trace_endpoints L hL
  have hq (q : ℕ) (hq : q ∈ Q) : q ∈ retainedPrimeDivisors Qp := (mem_filter.mp hq).1
  intro V _ _ embed hinj hdim gate
  apply htrace J ⌊100 * Real.log L⌋₊ ⌊Real.exp L⌋₊ ⌈Real.exp A⌉₊
    ⌊Real.exp L⌋₊ ⌊Real.exp (100 * L + 1)⌋₊ ⌊Real.exp (2 * L)⌋₊ data hB P Q hP
    hmasses.1 hdegree.1
    (fun j => (hmasses.2.1 j).1) (fun j => (hmasses.2.1 j).2.1)
    (fun j => (hmasses.2.1 j).2.2)
    hmasses.2.2.1 hmasses.2.2.2.2.1 hmasses.2.2.2.2.2 hdegree.2
    (centeredPrimeBands_prime E A W J) (centeredPrimeBands_disjoint E A W J hA.le (by linarith))
    (fun _ hp => centeredPrimePool_lower_nat E A W L J hA.le (by linarith) hend hp)
    (fun p hp => hB p (mem_union_left _ hp))
    hep.1 hep.2.1 hep.2.2.1 hep.2.2.2.1 hep.2.2.2.2
    (fun dq hdq => actualProhibitedPrimeFamily_padding_upper h J ⌊100 * Real.log L⌋₊
      E A W L η eligible hA.le (by linarith) hE hη hηone he hdq)
    (fun w j => centeredPrimeTuple_complement_upper E A W L J hA hW hend w j)
    (fun q hqQ => retainedPrimeDivisor_squarefree Qp (fun _ hp => paddingPrimeSupply_prime hp) (hq q hqQ))
    (fun q hqQ => retainedPrimeDivisor_factors Qp (fun _ hp => paddingPrimeSupply_prime hp) (hq q hqQ))
    actualPaddingCoefficient (actualPaddingVertex Qp) (Real.exp (4 * J))
    (fun d q => (d, q) ∈ data.pairs) (fun _ => actualPaddingDegreeCut Qp L)
    actualPaddingCoefficient_nonneg (fun _ => le_rfl)
    (fun n => by rw [actualPaddingVertex_sq]; exact actualPaddingWeight_one_le Qp n)
    (Real.one_le_exp (by positivity))
    (actualPaddingVertex_residue_congr Qp)
    (fun _ n m hnm => actualPaddingDegreeCut_residue_congr Qp L n m hnm)
    V embed hinj hdim gate (fun _ _ hp => hp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualBlockTrace
namespace OAI

/-! The actual finite block has the dimension required by the residue trace bound. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeBlockEmbedding_injective {J : ℕ} {P : Fin J → Finset ℕ} (N : ℕ) :
    Function.Injective (primeBlockEmbedding (P := P) N) := by
  intro a b hab
  apply Prod.ext
  · exact congrArg (fun z : ((j : Fin J) → P j) × ℤ => z.1) hab
  · apply Fin.ext
    have he : (a.2.val : ℤ) = (b.2.val : ℤ) := congrArg Prod.snd hab
    exact_mod_cast he

theorem ModFiveThetaInput.eventually_actual_block_trace (hprime : ModFiveThetaInput)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let g := actualPaddingVertex Qp
      let keep := fun n => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) n
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) g (fun d => centeredTuple d.primeFactors)
        L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L) h keep
      let N := ⌈Real.exp (103 * L)⌉₊
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix (primeBlockEmbedding (P := P) N)
          (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [hprime.eventually_actual_prime_matrix_trace h hh E hE W hW] with L htrace
  intro hL η hη hηone eligible he
  dsimp only
  intro gate
  exact htrace hL η hη hηone eligible he _ (primeBlockEmbedding _)
    (primeBlockEmbedding_injective _) (actual_prime_block_dimension E W L hW hL) gate

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeAffineWordComparison
namespace OAI

/-! Canonical prime bands exclude every prime factor of the progression
modulus, so the affine-origin word comparison has no additional premise. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma canonicalTraceFamily_coprime (h l : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) :
    ∀ p ∈ (canonicalTraceFamily h E W L eligible hL hW hE).P ∪
      (canonicalTraceFamily h E W L eligible hL hW hE).Q, l.Coprime p := by
  intro p hp
  have hprime := (canonicalTraceFamily h E W L eligible hL hW hE).prime ⟨p, hp⟩
  have hnot : p ∉ E := by
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨j, hj⟩ := mem_primeTuplePool.mp hp
      exact (centeredPrimeSupply_mem hj).2.2.1
    · exact (mem_sdiff.mp hp).2
  exact (hprime.coprime_iff_not_dvd.mpr (fun hd => hnot (hEl p hprime hd))).symm

theorem ModFiveThetaInput.eventually_actual_prime_affine_word_comparison_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (E : Finset ℕ) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E)
    (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ (w : ColumnPrimeAssignment J (2 * ⌊L⌋₊) P) (forward : Fin (2 * ⌊L⌋₊) → Bool)
        (padding : Fin (2 * ⌊L⌋₊) → Q),
      wordDisplacement h (columnTupleWord w forward (fun i => (padding i).val)) = 0 →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N => scalarWalkProduct h weight (a + l * x.val)
          (columnTupleWord w forward (fun i => (padding i).val))) -
        (data.residueLaw B hB).average (fun r => scalarWalkProduct h weight (data.residueOrigin r)
          (columnTupleWord w forward (fun i => (padding i).val)))| ≤ Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcompare⟩ := hBr.eventually_actual_affine_word_comparison
  refine ⟨A, hA, ?_⟩
  intro h l E hE hEl W hW
  filter_upwards [hcompare, hprime.eventually_actual_pool_masses E W hW,
    eventually_ge_atTop (4800 : ℝ)] with L hcompare hmasses hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hpool : (data.P ∪ data.Q).Nonempty := by
    by_contra hn
    have hempty : data.P = ∅ := not_nonempty_iff_eq_empty.mp
      (fun hp => hn (hp.mono subset_union_left))
    have hp := hmasses.2.2.1
    change 1 ≤ primeHarmonicMass data.P at hp
    rw [hempty] at hp
    norm_num [primeHarmonicMass] at hp
  have hdegree := prime_trace_degree_budget W L hW hL
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hJM : ((J + ⌊100 * Real.log L⌋₊ : ℕ) : ℝ) ≤ L ^ 2 :=
    hdegree.1.trans (by nlinarith)
  have hs : (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hk : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hkpos : 0 < ⌊L⌋₊ := by
    apply (Nat.le_floor_iff (by linarith : 0 ≤ L)).mpr
    simpa using hL
  have hRL : ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ 4 * L := by push_cast; linarith
  have hJ : (J : ℝ) ≤ L / 2 := by
    have hc := primeSupplyCount_mul_bound W L (by linarith) hL
    change (J : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L at hc
    have hj : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hRJ : ((2 * ⌊L⌋₊ * J : ℕ) : ℝ) ≤ L ^ 2 := by
    push_cast
    nlinarith [mul_le_mul hk hJ (Nat.cast_nonneg J) (by linarith : 0 ≤ L)]
  have hpair : (data.pairs.card : ℝ) ≤ Real.exp (101 * L) :=
    actualProhibitedPrimeFamily_pairs_card h J ⌊100 * Real.log L⌋₊ E
      (L ^ (199 / 200 : ℝ)) W L η eligible (Real.rpow_nonneg (by linarith) _)
      (by linarith) hE hL hη hηone he
  intro w forward padding hclosed a N hN
  have hq : Q ⊆ retainedPrimeDivisors data.Q := fun q hq => (mem_filter.mp hq).1
  exact hcompare h J ⌊100 * Real.log L⌋₊ (2 * ⌊L⌋₊) ⌊L ^ (1 / 10 : ℝ)⌋₊
    ⌊Real.exp L⌋₊ data hB hpool (Nat.floor_le (Real.exp_pos _).le) hs hJM hpair
    (by omega) hRL hRJ Q hq P w forward (fun i => (padding i).val)
    (centeredPrimeBands_prime E _ W J)
    (centeredPrimeBands_disjoint E _ W J (Real.rpow_nonneg (by linarith) _) (by linarith))
    (fun i => (show (((padding i).val.primeFactors.card : ℕ) : ℝ) ≤
      (⌊100 * Real.log L⌋₊ : ℝ) by exact_mod_cast (mem_filter.mp (padding i).property).2).trans hdegree.2)
    (actualColumnLabel data (fun j => centeredPrimeBand_subset_pool E _ W J j) w)
    (fun _ _ => rfl) hclosed (fun d q => (d, q) ∈ data.pairs) (Real.exp (4 * J)) a l N
    (canonicalTraceFamily_coprime h l E W L eligible hL hW hE hEl) hN


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualAffineIntervalMatrix
namespace OAI

/-! The finite-block moment on a fixed progression of origins. This
allows the progression gate to be frozen before applying the trace bound. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_actual_affine_interval_matrix_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
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
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => matrixFrobeniusSq
        (shiftMatrix (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
          (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + (a + l * x.val : ℕ)))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) + 1 := by
  obtain ⟨A, hA, hword⟩ := hprime.eventually_actual_prime_affine_word_comparison_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh E hE hEl W hW
  have hword := hword h l E hE hEl W hW
  filter_upwards [hword, hprime.eventually_actual_block_trace h hh E hE W hW,
    eventually_ge_atTop (4800 : ℝ)] with L hword htrace hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
    (fun _ => actualPaddingDegreeCut Qp L) h
    (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
  let D := (j : Fin J) → P j
  let M := ⌈Real.exp (103 * L)⌉₊
  let V := D × Fin M
  let embed : V → D × ℤ := primeBlockEmbedding M
  let tuple : D → ℕ := fun d => ∏ j, (d j).val
  have hprimeP := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hdisjoint := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hP (j : Fin J) : P j ⊆ data.P := centeredPrimeBand_subset_pool E _ W J j
  have hsq (q : ℕ) (hq : q ∈ Q) : Squarefree q :=
    retainedPrimeDivisor_squarefree Qp (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp hq).1
  have hpool (q : ℕ) (hq : q ∈ Q) : q.primeFactors ⊆ data.Q :=
    retainedPrimeDivisor_factors Qp (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp hq).1
  intro gate a N hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast this
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hcompare := physicalMatrix_moment_comparison embed
    (primeBlockEmbedding_injective M) Q tuple h gate weight
    (maskedSignedIntegerWeight_flip Q actualPaddingCoefficient _ _ _ _ _ _ h _)
    (FiniteLaw.uniform (Fin N)) (data.residueLaw ⌊Real.exp L⌋₊ hB)
    (fun x => (a + l * x.val : ℕ)) data.residueOrigin ⌊L⌋₊ (Real.exp (-(L ^ 9)))
    (Real.exp_pos _).le ?_
  · rw [FiniteLaw.uniform_average] at hcompare
    have herr := trace_interval_error_le_one L ⌊L⌋₊ (Fintype.card V)
      (Fintype.card (D × (Q × Bool))) hlarge (Nat.floor_le (by linarith))
      (Nat.cast_nonneg _) (actual_prime_block_dimension E W L hW hL)
      (actual_prime_alphabet_size E W L hW hlarge)
    have hupper := htrace hL η hη hηone eligible he gate
    have hdiff := (le_abs_self _).trans (hcompare.trans herr)
    dsimp only [embed, V, D, tuple, M, weight, data, Q, Qp, P, J] at hdiff
    linarith
  · intro i b c hend
    let enc := closedTraceEncoding Q (b, c)
    have hclosed : wordDisplacement h (columnTupleWord enc.2.1 enc.1 (fun j => (enc.2.2 j).val)) = 0 := by
      rw [closedTraceEncoding_word]
      exact integer_closed_word_displacement Q tuple h (embed i) b c hend
    have hw := hword hL η hη hηone eligible he enc.2.1 enc.1 enc.2.2 hclosed
      (a + i.2.val) N hN
    rw [closedTraceEncoding_word] at hw
    have ht := data.residue_average_translate hB
      (fun n => scalarWalkProduct h weight n (integerClosedWordCode Q tuple (b, c)))
      (fun n m hnm => scalarWalkProduct_residue_congr (data.P ∪ data.Q) h weight _
        (fun t ht z z' hz => primeClosedPair_residue_congr data hB hP hprimeP hdisjoint
          ⌊L ^ (1 / 10 : ℝ)⌋₊ Q actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs)
          (actualPaddingVertex Qp) L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L)
          hsq hpool (actualPaddingVertex_residue_congr Qp)
          (fun _ n m hnm => actualPaddingDegreeCut_residue_congr Qp L n m hnm)
          b c t ht z z' (fun p => hz p.val p.property)) n m (fun p hp => hnm ⟨p, hp⟩))
      (embed i).2
    have havg : (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
        scalarWalkProduct h weight ((embed i).2 + data.residueOrigin r)
          (integerClosedWordCode Q tuple (b, c))) =
        (data.residueLaw ⌊Real.exp L⌋₊ hB).average (fun r =>
          scalarWalkProduct h weight (data.residueOrigin r)
            (integerClosedWordCode Q tuple (b, c))) := by
      simpa only [add_comm (embed i).2] using ht
    rw [FiniteLaw.uniform_average]
    rw [havg]
    simpa only [embed, primeBlockEmbedding, Nat.cast_add, Nat.cast_mul,
      add_assoc, add_left_comm (a : ℤ)] using hw


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualAffineSpectralTail
namespace OAI

/-! Exceptional origins along a fixed progression for the actual finite block. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform_oai
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
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
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      let matrix := fun c : ℤ => shiftMatrix
        (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
          (fun t n => weight t (n + c)))
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J)) <
          realMatrixSpectralRadius (matrix (a + l * x.val : ℕ)) then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, htrace⟩ := hprime.eventually_actual_affine_interval_matrix_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh E hE hEl W hW
  have htrace := htrace h l hh E hE hEl W hW
  filter_upwards [htrace] with L htrace
  intro hL η hη hηone eligible he
  dsimp only
  intro gate a N hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast this
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hk : 0 < ⌊L⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ L)).mpr (by simpa using hL)
  have hsqrt : 1 ≤ Real.sqrt W := by simpa using Real.sqrt_le_sqrt hW
  have hbase : 1 ≤ Real.exp (4 * (primeSupplyCount W L : ℝ)) *
      (2 * Real.exp 150 * Real.sqrt W) ^ primeSupplyCount W L := by
    have hinner : 1 ≤ 2 * Real.exp 150 * Real.sqrt W := by
      have hx : 1 ≤ 2 * Real.exp 150 := by linarith [Real.one_le_exp (show (0 : ℝ) ≤ 150 by norm_num)]
      simpa only [one_mul] using mul_le_mul hx hsqrt zero_le_one (by positivity)
    simpa only [one_mul] using mul_le_mul
      (Real.one_le_exp (show 0 ≤ 4 * (primeSupplyCount W L : ℝ) by positivity))
      (one_le_pow₀ hinner) zero_le_one (Real.exp_pos _).le
  have hm := htrace hL η hη hηone eligible he gate a N hN
  rw [← FiniteLaw.uniform_average] at hm
  have ht := (FiniteLaw.uniform (Fin N)).matrix_spectral_tail_add_one _ ⌊L⌋₊ hk _ hbase hm
  simpa only [FiniteLaw.probability, FiniteLaw.uniform_average] using ht


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform_oai := @OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform_oai
