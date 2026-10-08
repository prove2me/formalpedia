-- Prove2me | solution 1 for OAI.TwoPointCorrelations.affineCorrectedElliott_of_mrt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:52:18.028995+00:00
-- url     : https://prove2.me/submissions/74aeee30-f893-44c4-bc55-1e4d04983654

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_AC0Circuit_dyadic_approximation
import Theorems.Thm_OAI_TwoPointCorrelations_AC0Circuit_fourier_tail_polynomial_degree
import Theorems.Thm_OAI_TwoPointCorrelations_conditional_binaryCorrectedElliott
import Theorems.Thm_OAI_TwoPointCorrelations_modFiveThetaInput

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





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AffineTransfer
namespace OAI

/-!
# Exact progression and affine endpoint identities

These finite identities implement the endpoint step of §8 of the manuscript.
They include nonunit residue classes and do not assume any cancellation theorem.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations


lemma progression_interval_image (l b N : ℕ) (hl : 0 < l) :
    (Finset.Icc 1 N).image (fun n => l * n + b) =
      (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨hn, hnN⟩, rfl⟩
    constructor
    · constructor
      · have : 0 < l * n := Nat.mul_pos hl hn
        omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left l hnN) b
    · simp
  · rintro ⟨⟨hbm, hmN⟩, hmod⟩
    have hdvd : l ∣ m - b := Nat.ModEq.dvd' hmod.symm
    obtain ⟨n, hn⟩ := hdvd
    have heq : l * n + b = m := by omega
    refine ⟨n, ⟨?_, ?_⟩, heq⟩
    · by_contra h
      have hn0 : n = 0 := by omega
      subst n
      simp only [Nat.mul_zero, zero_add] at heq
      omega
    · exact Nat.le_of_mul_le_mul_left (by omega : l * n ≤ l * N) hl

/-- Exact extraction of an affine subsequence from two progression prefixes. -/
theorem affine_sum_eq_residue_prefix (u : ℕ → ℂ) (l b N : ℕ) (hl : 0 < l) :
    (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      residuePrefix u l b (l * N + b) - residuePrefix u l b b := by
  have hinj : Set.InjOn (fun n : ℕ => l * n + b) (Finset.Icc 1 N) := by
    intro n hn m hm hnm
    exact Nat.eq_of_mul_eq_mul_left hl (Nat.add_right_cancel hnm)
  have hsum : (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) =
      ∑ m ∈ (Finset.Ioc b (l * N + b)).filter (fun m => m % l = b % l), u m := by
    rw [← progression_interval_image l b N hl, Finset.sum_image hinj]
  have hsplit := Finset.sum_Ioc_consecutive
    (fun m => if m % l = b % l then u m else 0)
    (Nat.zero_le b) (Nat.le_add_left b (l * N))
  unfold residuePrefix
  rw [hsum, Finset.sum_filter]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsplit)


/-- Swapping the two factors does not alter an affine correlation. -/
theorem affineSum_swap (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) :
    affineSum f g a₁ a₂ b₁ b₂ N = affineSum g f a₂ a₁ b₂ b₁ N := by
  unfold affineSum
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _


/-- Passage from a vanishing progression mean to its affine subsequence. -/
theorem affine_mean_tendsto_zero (u : ℕ → ℂ) (l b : ℕ) (hl : 0 < l)
    (hp : Filter.Tendsto (fun M : ℕ => residuePrefix u l b M / (M : ℂ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, u (l * n + b)) / (N : ℂ))
      Filter.atTop (nhds 0) := by
  have ht : Filter.Tendsto (fun N : ℕ => l * N + b) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro k
    filter_upwards [Filter.eventually_ge_atTop k] with N hN
    have : N ≤ l * N := by nlinarith
    omega
  have hsample := hp.comp ht
  have hratio : Filter.Tendsto (fun N : ℕ => ((l * N + b : ℕ) : ℂ) / (N : ℂ))
      Filter.atTop (nhds (l : ℂ)) := by
    have h := Filter.Tendsto.add (tendsto_const_nhds (x := (l : ℂ)))
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (b : ℂ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    push_cast
    field_simp
  have hboundary := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (residuePrefix u l b b)
  have hresult := (hratio.mul hsample).sub hboundary
  simp only [mul_zero, sub_zero] at hresult
  apply hresult.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmNat : 0 < l * N + b := by nlinarith
  have hm : ((l * N + b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hmNat.ne'
  rw [affine_sum_eq_residue_prefix u l b N hl]
  dsimp only [Function.comp_apply]
  field_simp

end TwoPointCorrelations

end OAI

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



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))













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






end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalFactors
namespace OAI

/-!
# Multiplicative functions from local prime-power factors

The finite local expansions in Part III of the manuscript replace values at
primes dividing a fixed dilation. The resulting functions are ordinary
multiplicative functions; complete multiplicativity is not required.
-/

namespace TwoPointCorrelations


@[simp] theorem fromPrimePowers_one (F : ℕ → ℕ → ℂ) : fromPrimePowers F 1 = 1 := by
  simp [fromPrimePowers]

/-- Coprime arguments have disjoint prime support, so arbitrary prime-power
values give an ordinary multiplicative function. -/
theorem fromPrimePowers_multiplicative (F : ℕ → ℕ → ℂ) :
    Multiplicative (fromPrimePowers F) := by
  intro m n hm hn hcop
  unfold fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors

theorem fromPrimePowers_oneBounded (F : ℕ → ℕ → ℂ)
    (hF : ∀ p k, Nat.Prime p → 0 < k → ‖F p k‖ ≤ 1) :
    OneBounded (fromPrimePowers F) := by
  intro n hn
  unfold fromPrimePowers Finsupp.prod
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    exact hF p _ hprime hk

@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]


/-- The local construction recovers a normalized multiplicative function on
positive integers, without replacing its prime-power values by powers. -/
theorem fromPrimePowers_reconstruct (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) {n : ℕ} (hn : 0 < n) :
    fromPrimePowers (fun p k => f (p ^ k)) n = f n := by
  symm
  apply Nat.multiplicative_factorization f _ h1 hn.ne'
  intro a b hab
  by_cases ha : a = 0
  · subst a
    have hb : b = 1 := by simpa using hab
    subst b
    simp [h1]
  by_cases hb : b = 0
  · subst b
    have ha : a = 1 := by simpa using hab
    subst a
    simp [h1]
  exact hf a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab

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




lemma cubeAverage_sub {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x - g x) = cubeAverage f - cubeAverage g := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]



lemma cubeAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → BooleanCube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, Finset.sum_div]
  rw [Finset.sum_comm]

lemma cubeAverage_mono {n : ℕ} {f g : BooleanCube n → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage f ≤ cubeAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)


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


lemma walsh_flipBit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : BooleanCube n) :
    walsh S (flipBit i x) = if i ∈ S then -walsh S x else walsh S x := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hrest : (∏ j ∈ S.erase i, booleanSign ((flipBit i x) j)) =
        ∏ j ∈ S.erase i, booleanSign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flipBit, Function.update_of_ne (mem_erase.mp hj).1]
    unfold walsh
    rw [← Finset.prod_erase_mul _ _ hi, hrest,
      ← Finset.prod_erase_mul _ (fun j => booleanSign (x j)) hi]
    simp [flipBit]
  · rw [if_neg hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [flipBit, Function.update_of_ne hji]

lemma cubeAverage_eq_zero_of_flip {n : ℕ} (f : BooleanCube n → ℝ) (i : Fin n)
    (hf : ∀ x, f (flipBit i x) = -f x) : cubeAverage f = 0 := by
  have hsum : (∑ x, f (flipBit i x)) = ∑ x, f x :=
    (flipBit i).sum_comp f
  simp_rw [hf] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  have hz : (∑ x, f x) = 0 := by linarith
  simp [cubeAverage, hz]

lemma cubeAverage_walsh {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    cubeAverage (walsh S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply cubeAverage_eq_zero_of_flip _ i
  intro x
  simp [walsh_flipBit, hi]















/-- Finite Walsh inversion of a cylinder indicator. -/
lemma cubePattern_walsh_expansion {n : ℕ} (S : Finset (Fin n))
    (z x : BooleanCube n) :
    (2 : ℝ) ^ S.card * cubePattern S z x =
      ∑ T ∈ S.powerset, walsh T z * walsh T x := by
  have hcoord (i : Fin n) : 1 + booleanSign (z i) * booleanSign (x i) =
      if x i = z i then (2 : ℝ) else 0 := by
    cases hx : x i <;> cases hz : z i <;> norm_num [booleanSign, hx, hz]
  have hprod : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
      (2 : ℝ) ^ S.card * cubePattern S z x := by
    by_cases h : ∀ i ∈ S, x i = z i
    · calc
        (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
            ∏ _i ∈ S, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hcoord, if_pos (h i hi)]
        _ = (2 : ℝ) ^ S.card * cubePattern S z x := by
          rw [cubePattern, if_pos h]
          simp
    · have hex : ∃ i ∈ S, x i ≠ z i := by
        push Not at h
        exact h
      obtain ⟨i, hi, hneq⟩ := hex
      have hz : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) = 0 := by
        apply Finset.prod_eq_zero hi
        rw [hcoord, if_neg hneq]
      simp [hz, cubePattern, h]
  rw [← hprod, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_mul_distrib]
  rfl

/-- Vanishing of all nonconstant Walsh coefficients on a coordinate set makes
that marginal exactly uniform. -/
lemma cubeAverage_pattern_of_walsh {n : ℕ} (g : BooleanCube n → ℝ)
    (S : Finset (Fin n)) (z : BooleanCube n) (hmean : cubeAverage g = 1)
    (hcoeff : ∀ T ⊆ S, T.Nonempty → walshCoefficient g T = 0) :
    cubeAverage (fun x => g x * cubePattern S z x) = 1 / (2 : ℝ) ^ S.card := by
  have hsum : (∑ T ∈ S.powerset, walsh T z * walshCoefficient g T) = 1 := by
    rw [Finset.sum_eq_single ∅]
    · simpa [walshCoefficient] using hmean
    · intro T hT hne
      rw [hcoeff T (mem_powerset.mp hT) (Finset.nonempty_iff_ne_empty.mpr hne), mul_zero]
    · simp
  have hscale : (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) = 1 := by
    calc
      (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) =
          cubeAverage (fun x => (2 : ℝ) ^ S.card * (g x * cubePattern S z x)) :=
        (cubeAverage_mul_const _ _).symm
      _ = cubeAverage (fun x => ∑ T ∈ S.powerset,
          walsh T z * (g x * walsh T x)) := by
        congr 1
        funext x
        rw [mul_left_comm, cubePattern_walsh_expansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ T ∈ S.powerset, walsh T z * walshCoefficient g T := by
        rw [cubeAverage_sum]
        apply Finset.sum_congr rfl
        intro T hT
        exact cubeAverage_mul_const _ _
      _ = 1 := hsum
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  nlinarith only [hscale]




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
namespace OAI

/-!
# Bounded-independence circuit comparison after Fourier correction

The comparison uses the fixed-depth specialization of Mark Braverman,
*Polylogarithmic independence fools AC⁰ circuits*, J. ACM 57 (2010), Article 28,
Corollary 2 in the author's version. We use depth 22, with absolute constants
and natural logarithms. Circuits below have actual finite syntax: literals
and arbitrary finite-fan-in AND/OR gates. They are tree circuits, a subclass
of the circuits covered by Braverman's theorem. The size counts both input
occurrences and gates; the depth counts AND/OR levels.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace AC0Circuit




lemma size_pos {n : ℕ} (c : AC0Circuit n) : 0 < c.size := by
  cases c <;> simp [size]



end AC0Circuit





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitClauseIndependence
namespace OAI

/-! The first gate case of bounded-independence circuit fooling. A clause is
the complement of a Boolean cylinder. Restricting a wide clause to t distinct
coordinates makes both its exceptional probabilities at most 2⁻ᵗ. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {n : ℕ}

lemma cubeAverage_pattern (S : Finset (Fin n)) (z : BooleanCube n) :
    cubeAverage (cubePattern S z) = 1 / (2 : ℝ) ^ S.card := by
  have hm : cubeAverage (fun _ : BooleanCube n => (1 : ℝ)) = 1 := cubeAverage_const 1
  have hc : ∀ T ⊆ S, T.Nonempty → walshCoefficient (fun _ => (1 : ℝ)) T = 0 := by
    intro T _ hT
    simpa only [walshCoefficient, one_mul] using cubeAverage_walsh hT
  simpa only [one_mul] using cubeAverage_pattern_of_walsh (fun _ => 1) S z hm hc





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialMean
namespace OAI

/-! The polynomial-expectation step in Braverman's proof (Proposition 6,
author version https://www.cs.toronto.edu/~mbraverm/FoolAC0v7.pdf).
On the Boolean cube, multilinear degree is represented by Walsh support.
Preservation of low-degree expectations gives a sandwich criterion for
bounded-independence comparison. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {n : ℕ}



lemma cubePattern_extend (S : Finset (Fin n)) (z : S → Bool) (x : BooleanCube n) :
    cubePattern S (cubeExtend S z) x = if cubeRestrict S x = z then 1 else 0 := by
  have heq : (∀ i ∈ S, x i = cubeExtend S z i) ↔ cubeRestrict S x = z := by
    constructor
    · intro h
      funext i
      simpa only [cubeRestrict, cubeExtend, dif_pos i.property] using h i i.property
    · intro h i hi
      have hh := congrFun h ⟨i, hi⟩
      simpa only [cubeRestrict, cubeExtend, dif_pos hi] using hh
  simp only [cubePattern, heq]

lemma cube_function_partition (S : Finset (Fin n)) (φ : (S → Bool) → ℝ)
    (x : BooleanCube n) :
    φ (cubeRestrict S x) = ∑ z : S → Bool, φ z * cubePattern S (cubeExtend S z) x := by
  simp only [cubePattern_extend]
  simp

lemma TWiseUniformDensity.restricted_mean {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t)
    (φ : (S → Bool) → ℝ) :
    cubeAverage (fun x => g x * φ (cubeRestrict S x)) =
      (∑ z : S → Bool, φ z) / (2 : ℝ) ^ S.card := by
  have heq : (fun x => g x * φ (cubeRestrict S x)) =
      fun x => ∑ z : S → Bool, φ z * (g x * cubePattern S (cubeExtend S z) x) := by
    funext x
    rw [cube_function_partition S φ x, mul_sum]
    apply sum_congr rfl
    intro z _
    ring
  rw [heq, cubeAverage_sum]
  simp_rw [cubeAverage_mul_const, hg S hS]
  simp only [div_eq_mul_inv, sum_mul, one_mul]

lemma uniformDensity_tWise (t : ℕ) :
    TWiseUniformDensity (fun _ : BooleanCube n => (1 : ℝ)) t := by
  intro S _ z
  simpa only [one_mul] using cubeAverage_pattern S z

lemma TWiseUniformDensity.restricted_expectation {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t)
    (φ : (S → Bool) → ℝ) :
    cubeAverage (fun x => g x * φ (cubeRestrict S x)) =
      cubeAverage (fun x => φ (cubeRestrict S x)) := by
  rw [hg.restricted_mean S hS φ]
  simpa only [one_mul] using ((uniformDensity_tWise t).restricted_mean S hS φ).symm

lemma TWiseUniformDensity.walsh_expectation {t : ℕ} {g : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (S : Finset (Fin n)) (hS : S.card ≤ t) :
    cubeAverage (fun x => g x * walsh S x) = cubeAverage (walsh S) := by
  have heq (x : BooleanCube n) :
      walsh S x = ∏ i : S, booleanSign (cubeRestrict S x i) := by
    simp only [walsh, cubeRestrict]
    exact (Finset.prod_attach S (fun i => booleanSign (x i))).symm
  have hfun : walsh S = fun x => ∏ i : S, booleanSign (cubeRestrict S x i) := funext heq
  rw [hfun]
  exact hg.restricted_expectation S hS (fun z => ∏ i : S, booleanSign (z i))


lemma TWiseUniformDensity.polynomial_expectation {t : ℕ} {g F : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hF : WalshDegreeLE F t) :
    cubeAverage (fun x => g x * F x) = cubeAverage F := by
  obtain ⟨a, ha⟩ := hF
  have hfun : F = fun x => ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => S.card ≤ t), a S * walsh S x := funext ha
  rw [hfun]
  simp_rw [mul_sum]
  rw [cubeAverage_sum, cubeAverage_sum]
  apply sum_congr rfl
  intro S hS
  have hs : S.card ≤ t := (mem_filter.mp hS).2
  have heq : (fun x => g x * (a S * walsh S x)) =
      fun x => a S * (g x * walsh S x) := by funext x; ring
  rw [heq, cubeAverage_mul_const, cubeAverage_mul_const, hg.walsh_expectation S hs]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.PretentiousDistance
namespace OAI

/-!
# The pretentious distance used in ordinary two-point correlations

These definitions use the prime cutoff and the twist-height cutoff at the same
integer scale.  The finite-prime perturbation estimate below is Lemma
`lem:finite-prime-stability` of *Ordinary two-point correlations of
multiplicative functions* (24 September 2026).  It is elementary and does not
assume any analytic input.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter _root_.Finset





lemma characterTwist_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ‖characterTwist χ t n‖ ≤ 1 := by
  simpa only [characterTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
    χ.norm_le_one (n : ZMod q)





/-- Altering a fixed finite set of prime values changes the square of the
pretentious distance by at most twice their reciprocal sum. -/
lemma squaredDistance_finite_prime_change (f b g : ℕ → ℂ) (N : ℕ)
    (P : Finset ℕ) (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hb : ∀ n, 0 < n → ‖b n‖ ≤ 1)
    (hg : ∀ n, 0 < n → ‖g n‖ ≤ 1)
    (heq : ∀ p, Nat.Prime p → p ∉ P → b p = f p) :
    |squaredDistance b g N - squaredDistance f g N| ≤
      2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  let S := primesUpTo N
  have hterm (p : ℕ) (hp : 0 < p) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤ 2 / (p : ℝ) := by
    have hdiff : ‖f p - b p‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith [hf p hp, hb p hp])
    have hprod : ‖(f p - b p) * conj (g p)‖ ≤ 2 := by
      calc
        ‖(f p - b p) * conj (g p)‖ = ‖f p - b p‖ * ‖g p‖ := by simp
        _ ≤ 2 * 1 := mul_le_mul hdiff (hg p hp) (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hre : |(f p * conj (g p)).re - (b p * conj (g p)).re| ≤ 2 := by
      calc
        |(f p * conj (g p)).re - (b p * conj (g p)).re| =
          |((f p - b p) * conj (g p)).re| := by rw [sub_mul, Complex.sub_re]
        _ ≤ ‖(f p - b p) * conj (g p)‖ := Complex.abs_re_le_norm _
        _ ≤ 2 := hprod
    rw [← sub_div, show (1 - (b p * conj (g p)).re) -
      (1 - (f p * conj (g p)).re) =
        (f p * conj (g p)).re - (b p * conj (g p)).re by ring,
      abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
    exact div_le_div_of_nonneg_right hre (Nat.cast_nonneg p)
  have htermP (p : ℕ) (hp : p ∈ S) :
      |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| ≤
      if p ∈ P then 2 / (p : ℝ) else 0 := by
    split_ifs with hP
    · exact hterm p ((Finset.mem_filter.mp hp).2.pos)
    · have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      rw [heq p hprime hP, sub_self, abs_zero]
  calc
    |squaredDistance b g N - squaredDistance f g N| =
      |∑ p ∈ S, ((1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ))| := by
          rw [Finset.sum_sub_distrib]
          rfl
    _ ≤ ∑ p ∈ S, |(1 - (b p * conj (g p)).re) / (p : ℝ) -
        (1 - (f p * conj (g p)).re) / (p : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, if p ∈ P then 2 / (p : ℝ) else 0 := Finset.sum_le_sum htermP
    _ = ∑ p ∈ S.filter (fun p => p ∈ P), 2 / (p : ℝ) := by rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hnot
        positivity
    _ = 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The bound is uniform over the changing twist and finite modifications. -/
lemma UniformlyNonpretentious.finite_prime_change {f b : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (P : Finset ℕ)
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1) (hb : ∀ n, 0 < n → ‖b n‖ ≤ 1)
    (heq : ∀ p, Nat.Prime p → p ∉ P → b p = f p) :
    UniformlyNonpretentious b := by
  intro q hq χ K
  filter_upwards [hfnp q hq χ (K + 2 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ))] with N hN
  intro t ht
  have hdist := squaredDistance_finite_prime_change f b (characterTwist χ t) N
    P hf hb (fun n _ => characterTwist_norm_le_one χ t n) heq
  have hlow := hN t ht
  have := (abs_le.mp hdist).1
  linarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CharacterTwists
namespace OAI

/-!
# Dirichlet character twists preserve uniform nonpretentiousness

Characters with different moduli are multiplied after changing both levels
to the product modulus. The resulting character equals the pointwise product
on every natural number, including the nonunit classes. This gives an exact
identity of pretentious distances and preserves the original height cutoff.
-/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate
open _root_.Filter



@[simp] lemma conjugateCharacter_apply {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    conjugateCharacter χ n = conj (χ n) := rfl

/-- Changing both character levels to their product preserves their pointwise
product, even when the argument is not a unit modulo the product. -/
lemma productCharacters_apply_nat {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    productCharacters χ ψ (n : ZMod (q * r)) = χ (n : ZMod q) * ψ (n : ZMod r) := by
  unfold productCharacters
  simp only [MulChar.coeToFun_mul, Pi.mul_apply]
  by_cases hcop : n.Coprime (q * r)
  · have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q r) hcop.isCoprime
    have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ
      (Nat.dvd_mul_left r q) hcop.isCoprime
    simpa only [Int.cast_natCast] using congrArg₂ (· * ·) hχ hψ
  · have hunit : ¬IsUnit (n : ZMod (q * r)) := by
      simpa only [ZMod.isUnit_iff_coprime] using hcop
    rw [MulChar.map_nonunit _ hunit, zero_mul]
    by_cases hnq : n.Coprime q
    · have hnr : ¬n.Coprime r := by
        intro hnr
        exact hcop (hnq.mul_right hnr)
      have hunitr : ¬IsUnit (n : ZMod r) := by
        simpa only [ZMod.isUnit_iff_coprime] using hnr
      rw [MulChar.map_nonunit ψ hunitr, mul_zero]
    · have hunitq : ¬IsUnit (n : ZMod q) := by
        simpa only [ZMod.isUnit_iff_coprime] using hnq
      rw [MulChar.map_nonunit χ hunitq, zero_mul]


lemma characterTwist_productCharacters {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) (t : ℝ) (n : ℕ) :
    characterTwist (productCharacters χ ψ) t n =
      characterTwist χ t n * ψ (n : ZMod r) := by
  unfold characterTwist
  rw [productCharacters_apply_nat]
  ring

/-- The same real twist height appears on both sides, including at primes
dividing either character modulus. -/
lemma squaredDistance_twistByCharacter {q r : ℕ} (f : ℕ → ℂ)
    (ψ : DirichletCharacter ℂ r) (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) :
    squaredDistance (TwoPointCorrelations.twistByCharacter f ψ) (characterTwist χ t) N =
      squaredDistance f (characterTwist (productCharacters χ (conjugateCharacter ψ)) t) N := by
  unfold squaredDistance
  apply Finset.sum_congr rfl
  intro p hp
  rw [characterTwist_productCharacters]
  simp only [TwoPointCorrelations.twistByCharacter, map_mul, conjugateCharacter_apply, Complex.conj_conj]
  congr 2
  congr 1
  ring

lemma UniformlyNonpretentious.twistByCharacter {r : ℕ} {f : ℕ → ℂ}
    (hf : UniformlyNonpretentious f) (ψ : DirichletCharacter ℂ r) (hr : 0 < r) :
    UniformlyNonpretentious (TwoPointCorrelations.twistByCharacter f ψ) := by
  intro q hq χ K
  filter_upwards [hf (q * r) (Nat.mul_pos hq hr)
    (productCharacters χ (conjugateCharacter ψ)) K] with N hN
  intro t ht
  rw [squaredDistance_twistByCharacter]
  exact hN t ht

lemma OneBounded.twistByCharacter {q : ℕ} {f : ℕ → ℂ}
    (hf : OneBounded f) (χ : DirichletCharacter ℂ q) : OneBounded (TwoPointCorrelations.twistByCharacter f χ) := by
  intro n hn
  unfold TwoPointCorrelations.twistByCharacter
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LocalExpansion
namespace OAI

/-!
# Finite local expansions

The local sequences in manuscript Lemma `lem:affine-dilation` have value zero
at exponent zero. A difference of two normalized local sequences represents
such a sequence. Expansion over subsets then produces ordinary multiplicative
components that retain the original prime values outside the fixed finite set.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations


theorem localComponent_multiplicative (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) : Multiplicative (localComponent f B C P E) :=
  fromPrimePowers_multiplicative _

theorem localComponent_oneBounded (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hf : OneBounded f)
    (hB : ∀ p k, p ∈ P → 0 < k → ‖B p k‖ ≤ 1)
    (hC : ∀ p k, p ∈ P → 0 < k → ‖C p k‖ ≤ 1) :
    OneBounded (localComponent f B C P E) := by
  apply fromPrimePowers_oneBounded
  intro p k hp hk
  split_ifs with hpP hpE
  · exact hC p k hpP hk
  · exact hB p k hpP hk
  · exact hf _ (pow_pos hp.pos _)

theorem localComponent_prime (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) :
    localComponent f B C P E p = f p := by
  simp [localComponent, fromPrimePowers_prime _ hp, hpP]

/-- Expanding the support of a prime-power product is valid when the additional
local factors have value one at exponent zero. -/
theorem fromPrimePowers_split (F : ℕ → ℕ → ℂ) (P : Finset ℕ)
    (hF : ∀ p, F p 0 = 1) (n : ℕ) :
    fromPrimePowers F n =
      (∏ p ∈ P, F p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ P, F p (n.factorization p) := by
  unfold fromPrimePowers
  rw [Finsupp.prod_of_support_subset _ (s := P ∪ n.primeFactors)
    (by simp) F (fun p _ => hF p)]
  rw [← Finset.union_sdiff_self_eq_union (s := P) (t := n.primeFactors),
    Finset.prod_union disjoint_sdiff_self_left.symm]

theorem localComponent_split (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hE : E ⊆ P) (hf : f 1 = 1)
    (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1) (n : ℕ) :
    localComponent f B C P E n =
      ((∏ p ∈ P \ E, B p (n.factorization p)) * ∏ p ∈ E, C p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p) := by
  unfold localComponent
  rw [fromPrimePowers_split _ P (by intro p; simp [hB, hC, hf])]
  congr 1
  · rw [← Finset.sdiff_union_of_subset hE, Finset.prod_union Finset.sdiff_disjoint]
    congr 1
    · simp only [Finset.union_sdiff_cancel_right (Finset.sdiff_disjoint)]
      apply Finset.prod_congr rfl
      intro p hp
      have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
      have hpE : p ∉ E := (Finset.mem_sdiff.mp hp).2
      simp [hpP, hpE]
    · apply Finset.prod_congr rfl
      intro p hp
      simp [hp, hE hp]
  · apply Finset.prod_congr rfl
    intro p hp
    simp [(Finset.mem_sdiff.mp hp).2]

/-- Exact finite expansion with one normalized multiplicative component for
each subset of the exceptional primes. -/
theorem local_difference_expansion (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P : Finset ℕ) (hf : f 1 = 1)
    (hB : ∀ p, B p 0 = 1) (hC : ∀ p, C p 0 = 1) (n : ℕ) :
    (∏ p ∈ P, (B p (n.factorization p) - C p (n.factorization p))) *
        (∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p)) =
      ∑ E ∈ P.powerset, (-1 : ℂ) ^ E.card * localComponent f B C P E n := by
  rw [Finset.prod_sub, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  rw [localComponent_split f B C P E (Finset.mem_powerset.mp hE) hf hB hC n]
  ring

/-- Every bounded component inherits nonpretentiousness from the original
factor. This uses only changes at the fixed finite prime set. -/
theorem localComponent_nonpretentious (f : ℕ → ℂ) (B C : ℕ → ℕ → ℂ)
    (P E : Finset ℕ) (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (hB : ∀ p k, p ∈ P → 0 < k → ‖B p k‖ ≤ 1)
    (hC : ∀ p k, p ∈ P → 0 < k → ‖C p k‖ ≤ 1) :
    UniformlyNonpretentious (localComponent f B C P E) := by
  apply hfnp.finite_prime_change P hf (localComponent_oneBounded f B C P E hf hB hC)
  intro p hp hpP
  exact localComponent_prime f B C P E hp hpP

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.Dilation
namespace OAI

/-!
# Finite multiplicative expansion of a dilation

This is the arithmetic content of manuscript Lemma `lem:affine-dilation`.
The equality is asserted for positive arguments, the domain relevant to
ordinary multiplicative functions. No complete multiplicativity is used.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations






theorem dilationLocal_eq_sub (a : ℕ) (f : ℕ → ℂ) {p : ℕ}
    (hp : p ∈ a.primeFactors) (k : ℕ) :
    dilationLocal a f p k = dilationB a f p k - dilationC a f p k := by
  have hpos : 0 < a.factorization p := by
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  by_cases hk : k = 0
  · subst k
    simp [dilationLocal, dilationB, dilationC, hpos]
  · simp [dilationB, dilationC, hk]

theorem dilate_eq_local_product (a : ℕ) (f : ℕ → ℂ)
    (ha : 0 < a) (hf : Multiplicative f) (h1 : f 1 = 1)
    {n : ℕ} (hn : 0 < n) :
    dilate a f n =
      (∏ p ∈ a.primeFactors, dilationLocal a f p (n.factorization p)) *
        ∏ p ∈ n.primeFactors \ a.primeFactors, f (p ^ n.factorization p) := by
  classical
  by_cases hd : a ∣ n
  · have hle : a.factorization ≤ n.factorization :=
      (Nat.factorization_le_iff_dvd ha.ne' hn.ne').mpr hd
    have hsupport : (n / a).factorization.support ⊆ a.primeFactors ∪ n.primeFactors := by
      intro p hp
      apply Finset.mem_union.mpr
      right
      change p ∈ n.factorization.support
      apply Finsupp.mem_support_iff.mpr
      have hp' := Finsupp.mem_support_iff.mp hp
      simp only [Nat.factorization_div hd, Finsupp.tsub_apply] at hp'
      omega
    have hprod := fromPrimePowers_reconstruct f hf h1
      (Nat.div_pos (Nat.le_of_dvd hn hd) ha)
    rw [dilate, ite_eq_left_iff.mpr (fun h => (h hd).elim), ← hprod]
    unfold fromPrimePowers
    rw [Finsupp.prod_of_support_subset _ hsupport _ (by intro p _; simp [h1])]
    rw [← Finset.union_sdiff_self_eq_union (s := a.primeFactors) (t := n.primeFactors),
      Finset.prod_union disjoint_sdiff_self_left.symm]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp [dilationLocal, Nat.not_lt.mpr (hle p), Nat.factorization_div hd,
        Finsupp.tsub_apply]
    · apply Finset.prod_congr rfl
      intro p hp
      have hp0 : a.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hp).2
      simp [Nat.factorization_div hd, Finsupp.tsub_apply, hp0]
  · have hex : ∃ p, n.factorization p < a.factorization p := by
      by_contra! h
      apply hd
      exact (Nat.factorization_le_iff_dvd ha.ne' hn.ne').mp (Finsupp.le_def.mpr h)
    obtain ⟨p, hp⟩ := hex
    have hpP : p ∈ a.primeFactors := by
      change p ∈ a.factorization.support
      apply Finsupp.mem_support_iff.mpr
      omega
    simp only [dilate, hd, ite_false]
    rw [Finset.prod_eq_zero hpP (by simp [dilationLocal, hp])]
    simp

/-- A fixed dilation is a finite signed sum of normalized ordinary
multiplicative functions, even at arguments with nonunit residue classes. -/
theorem dilate_eq_sum_components (a : ℕ) (f : ℕ → ℂ)
    (ha : 0 < a) (hf : Multiplicative f) (h1 : f 1 = 1)
    {n : ℕ} (hn : 0 < n) :
    dilate a f n = ∑ E ∈ a.primeFactors.powerset,
      (-1 : ℂ) ^ E.card * dilationComponent a f E n := by
  rw [dilate_eq_local_product a f ha hf h1 hn]
  rw [show (∏ p ∈ a.primeFactors, dilationLocal a f p (n.factorization p)) =
    ∏ p ∈ a.primeFactors, (dilationB a f p (n.factorization p) -
      dilationC a f p (n.factorization p)) from
    Finset.prod_congr rfl (fun p hp => dilationLocal_eq_sub a f hp _)]
  exact local_difference_expansion f (dilationB a f) (dilationC a f) a.primeFactors h1
    (by intro p; simp [dilationB]) (by intro p; simp [dilationC]) n

theorem dilationComponent_multiplicative (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    Multiplicative (dilationComponent a f E) :=
  localComponent_multiplicative _ _ _ _ _

@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]

theorem dilationB_bound (a : ℕ) (f : ℕ → ℂ) (hf : OneBounded f)
    {p k : ℕ} (hp : p ∈ a.primeFactors) : ‖dilationB a f p k‖ ≤ 1 := by
  have hpos := (Nat.prime_of_mem_primeFactors hp).pos
  unfold dilationB dilationLocal
  split_ifs
  · simp
  · simp
  · exact hf _ (pow_pos hpos _)

theorem dilationComponent_oneBounded (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (hf : OneBounded f) : OneBounded (dilationComponent a f E) := by
  apply localComponent_oneBounded _ _ _ _ _ hf
  · intro p k hp _
    exact dilationB_bound a f hf hp
  · intro p k _ hk
    simp [dilationC, Nat.ne_of_gt hk]

theorem dilationComponent_nonpretentious (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (hf : OneBounded f) (hfnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (dilationComponent a f E) := by
  apply localComponent_nonpretentious _ _ _ _ _ hfnp hf
  · intro p k hp _
    exact dilationB_bound a f hf hp
  · intro p k _ hk
    simp [dilationC, Nat.ne_of_gt hk]

/-- Outside the dilation primes, the components keep the full prime-power
sequence of the original function. -/
theorem dilationComponent_prime_pow (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ)
    (h1 : f 1 = 1) {p : ℕ} (hp : p.Prime) (hpA : p ∉ a.primeFactors) (k : ℕ) :
    dilationComponent a f E (p ^ k) = f (p ^ k) := by
  unfold dilationComponent localComponent fromPrimePowers
  rw [hp.factorization_pow, Finsupp.prod_single_index]
  · simp [hpA]
  · simp [hpA, h1]

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
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function



variable {𝕂 : Type*} [RCLike 𝕂]








@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

















local notation (name := mellintransform) "𝓜" => mellin















@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le


























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi
namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem
namespace OAI

/-! The fixed modulus-five prime number theorem follows from the three
nonprincipal contour estimates, the zeta prime number theorem, and finite
character orthogonality. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.Finset
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
namespace OAI

/-! Relabel, complement and conjoin the residue circuits used in a
closed-word expansion without increasing their internal depth. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset


lemma negate_eval {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.eval x = true ↔ c.eval x ≠ true := by
  induction c with
  | literal i b => cases b <;> cases hx : x i <;> simp [negate, eval, hx]
  | andGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_forall]
  | orGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_exists]

lemma negate_depth {n : ℕ} (c : AC0Circuit n) : c.negate.depth = c.depth := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, depth, ih]
  | orGate c ih => simp only [negate, depth, ih]

lemma negate_size {n : ℕ} (c : AC0Circuit n) : c.negate.size = c.size := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, size, ih]
  | orGate c ih => simp only [negate, size, ih]









end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end











theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind



theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply Real.log_pos; norm_num
        linarith [E₁.nonneg]




























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩

/-- Mertens' second theorem implies the reciprocal-prime estimate. -/
theorem primeReciprocalInput : PrimeReciprocalInput := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun x hx => ?_⟩
  rw [sievePrimesUpTo_eq_Ioc]
  exact hC x hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialAlgebra
namespace OAI

/-! Algebra of the low-degree functions used in the circuit approximation.
Multiplication adds degrees, including after Boolean multilinearization. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.symmDiff

variable {n : ℕ}

lemma walsh_mul (S T : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh T x = walsh (S ∆ T) x := by
  have hd : Disjoint (S ∆ T) (S ∩ T) := by
    rw [disjoint_left]
    intro i hi hi'
    simp only [mem_symmDiff, mem_inter] at hi hi'
    tauto
  have hu : (S ∆ T) ∪ (S ∩ T) = S ∪ T := by
    ext i
    simp only [mem_union, mem_symmDiff, mem_inter]
    tauto
  have he : walsh (S ∪ T) x * walsh (S ∩ T) x = walsh S x * walsh T x :=
    prod_union_inter
  have hh : walsh (S ∪ T) x = walsh (S ∆ T) x * walsh (S ∩ T) x := by
    simpa only [walsh, hu] using
      (prod_union hd : (∏ i ∈ (S ∆ T) ∪ (S ∩ T), booleanSign (x i)) = _)
  rw [hh, mul_assoc, walsh_mul_self, mul_one] at he
  exact he.symm





lemma WalshDegreeLE.sum {ι : Type*} (I : Finset ι) (F : ι → BooleanCube n → ℝ)
    {t : ℕ} (hF : ∀ i ∈ I, WalshDegreeLE (F i) t) :
    WalshDegreeLE (fun x => ∑ i ∈ I, F i x) t := by
  choose a ha using fun i : I => hF i i.property
  refine ⟨fun S => ∑ i : I, a i S, ?_⟩
  intro x
  dsimp only
  rw [← sum_coe_sort I]
  simp_rw [ha]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  exact (sum_mul _ _ _).symm

lemma WalshDegreeLE.mul {F G : BooleanCube n → ℝ} {p q : ℕ}
    (hF : WalshDegreeLE F p) (hG : WalshDegreeLE G q) :
    WalshDegreeLE (fun x => F x * G x) (p + q) := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  let A := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ p)
  let B := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ q)
  have heq : (fun x => F x * G x) = fun x =>
      ∑ S ∈ A, ∑ T ∈ B, (a S * b T) * walsh (S ∆ T) x := by
    funext x
    rw [ha, hb, sum_mul]
    apply sum_congr rfl
    intro S _
    rw [mul_sum]
    apply sum_congr rfl
    intro T _
    rw [← walsh_mul]
    ring
  rw [heq]
  apply WalshDegreeLE.sum A
  intro S hS
  apply WalshDegreeLE.sum B
  intro T hT
  apply WalshDegreeLE.smul
  apply WalshDegreeLE.of_walsh
  calc
    (S ∆ T).card ≤ (S ∪ T).card := card_le_card symmDiff_subset_union
    _ ≤ S.card + T.card := card_union_le S T
    _ ≤ p + q := add_le_add (mem_filter.mp hS).2 (mem_filter.mp hT).2

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSemiExact
namespace OAI

/-! The finite algebraic steps of Braverman's Lemmas 11–12. A polynomial
that vanishes off a Boolean event gives a pointwise minorant after applying
`p ↦ 1 - (1-p)^2`; the uniform squared error is exactly the minorant gap.
Only the approximation construction, not this expectation argument, needs
the circuit-depth estimates. -/

namespace TwoPointCorrelations

variable {n : ℕ}


lemma semiExactMinorant_le {F P : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (hzero : ∀ x, F x = 0 → P x = 0) :
    ∀ x, semiExactMinorant P x ≤ F x := by
  intro x
  rcases hF x with hx | hx
  · simp [semiExactMinorant, hzero x hx, hx]
  · rw [hx]
    unfold semiExactMinorant
    nlinarith [sq_nonneg (1 - P x)]

lemma semiExactMinorant_gap {F P : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (hzero : ∀ x, F x = 0 → P x = 0) :
    ∀ x, F x - semiExactMinorant P x = (F x - P x) ^ 2 := by
  intro x
  rcases hF x with hx | hx
  · simp [semiExactMinorant, hzero x hx, hx]
  · simp only [semiExactMinorant, hx]
    ring

lemma WalshDegreeLE.minorant {P : BooleanCube n → ℝ} {d : ℕ}
    (hP : WalshDegreeLE P d) : WalshDegreeLE (semiExactMinorant P) (d + d) := by
  have hp := (WalshDegreeLE.const (n := n) 1 d).sub hP
  have hs := hp.mul hp
  have hq := (WalshDegreeLE.const (n := n) 1 (d + d)).sub hs
  change WalshDegreeLE (fun x => 1 - (1 - P x) ^ 2) (d + d)
  simpa only [pow_two] using hq

/-- A small exceptional set and a semi-exact low-degree approximation give
the required one-sided comparison of the original Boolean expectation. -/
theorem TWiseUniformDensity.semiExact_lower {t : ℕ}
    {g F F₀ P : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hn : ∀ x, 0 ≤ g x)
    (hF₀ : ∀ x, F₀ x = 0 ∨ F₀ x = 1)
    (hzero : ∀ x, F₀ x = 0 → P x = 0)
    (hdeg : WalshDegreeLE (semiExactMinorant P) t)
    {δu δg ε : ℝ}
    (hu : cubeAverage (fun x => |F x - F₀ x|) ≤ δu)
    (hmu : cubeAverage (fun x => g x * |F x - F₀ x|) ≤ δg)
    (herr : cubeAverage (fun x => (F₀ x - P x) ^ 2) ≤ ε) :
    cubeAverage F - (δu + δg + ε) ≤ cubeAverage (fun x => g x * F x) := by
  have hu' : cubeAverage F ≤ cubeAverage F₀ + δu := by
    have hb : ∀ x, F x ≤ F₀ x + |F x - F₀ x| := by
      intro x
      linarith [le_abs_self (F x - F₀ x)]
    have h := cubeAverage_mono hb
    rw [cubeAverage_add] at h
    linarith
  have hgap : cubeAverage F₀ - cubeAverage (semiExactMinorant P) ≤ ε := by
    rw [← cubeAverage_sub]
    simpa only [semiExactMinorant_gap hF₀ hzero] using herr
  have hlow : cubeAverage (semiExactMinorant P) ≤
      cubeAverage (fun x => g x * F₀ x) := by
    have h := cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left
      (semiExactMinorant_le hF₀ hzero x) (hn x))
    rw [hg.polynomial_expectation hdeg] at h
    exact h
  have hmu' : cubeAverage (fun x => g x * F₀ x) ≤
      cubeAverage (fun x => g x * F x) + δg := by
    have hb : ∀ x, g x * F₀ x ≤ g x * F x + g x * |F x - F₀ x| := by
      intro x
      have h : F₀ x ≤ F x + |F x - F₀ x| := by
        have ha := le_abs_self (F₀ x - F x)
        rw [abs_sub_comm] at ha
        linarith
      have h' := mul_le_mul_of_nonneg_left h (hn x)
      nlinarith only [h']
    have h := cubeAverage_mono hb
    rw [cubeAverage_add] at h
    linarith
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitErrorCutoff
namespace OAI

/-! The algebraic error-cutoff step of Braverman's Lemma 10. A Fourier
approximation of the exceptional event suppresses the large polynomial
values on that event while preserving exact zeros. -/

namespace TwoPointCorrelations

open scoped _root_.Classical



lemma exceptionalExtension_boolean {n : ℕ} {F : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (E : BooleanCube n → Bool) (x : BooleanCube n) :
    exceptionalExtension F E x = 0 ∨ exceptionalExtension F E x = 1 := by
  unfold exceptionalExtension
  split_ifs
  · exact Or.inr rfl
  · exact hF x

lemma errorCutoffPolynomial_zero {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (he : ∀ x, E x = false → P x = F x)
    (x : BooleanCube n) (hx : exceptionalExtension F E x = 0) :
    errorCutoffPolynomial P T x = 0 := by
  have hE : E x = false := by
    cases h : E x <;> simp_all [exceptionalExtension]
  have hF : F x = 0 := by simpa [exceptionalExtension, hE] using hx
  simp [errorCutoffPolynomial, he x hE, hF]

lemma errorCutoffPolynomial_degree {n p q : ℕ} {P T : BooleanCube n → ℝ}
    (hP : WalshDegreeLE P p) (hT : WalshDegreeLE T q) :
    WalshDegreeLE (errorCutoffPolynomial P T) (p + q) :=
  hP.mul ((WalshDegreeLE.const 1 q).sub hT)

lemma errorCutoffPolynomial_sq_bound {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (hF : ∀ x, F x = 0 ∨ F x = 1)
    (he : ∀ x, E x = false → P x = F x) {B : ℝ} (hB : 1 ≤ B)
    (hP : ∀ x, |P x| ≤ B) (x : BooleanCube n) :
    (exceptionalExtension F E x - errorCutoffPolynomial P T x) ^ 2 ≤
      2 * (if E x then (1 : ℝ) else 0) +
        2 * B ^ 2 * ((if E x then (1 : ℝ) else 0) - T x) ^ 2 := by
  have hp : (P x) ^ 2 ≤ B ^ 2 := by
    have ha := abs_le.mp (hP x)
    nlinarith
  have hBsq : 1 ≤ B ^ 2 := by nlinarith
  cases hE : E x
  · have heq := he x hE
    rcases hF x with hf | hf
    · simp [exceptionalExtension, errorCutoffPolynomial, hE, heq, hf]
      positivity
    · simp only [exceptionalExtension, errorCutoffPolynomial, hE,
        Bool.false_eq_true, ite_false, heq, hf, one_mul, mul_zero, zero_add]
      have hh := mul_le_mul_of_nonneg_right hBsq (sq_nonneg (T x))
      nlinarith only [hh, sq_nonneg (T x)]
  · simp only [exceptionalExtension, errorCutoffPolynomial, hE, ite_true]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg (1 - T x))
    nlinarith only [hh, sq_nonneg (1 + P x * (1 - T x))]

theorem errorCutoffPolynomial_mean_sq {n : ℕ} {F P T : BooleanCube n → ℝ}
    {E : BooleanCube n → Bool} (hF : ∀ x, F x = 0 ∨ F x = 1)
    (he : ∀ x, E x = false → P x = F x) {B δ ε : ℝ} (hB : 1 ≤ B)
    (hP : ∀ x, |P x| ≤ B)
    (hE : cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ δ)
    (hT : cubeAverage (fun x => ((if E x then (1 : ℝ) else 0) - T x) ^ 2) ≤ ε) :
    cubeAverage (fun x =>
      (exceptionalExtension F E x - errorCutoffPolynomial P T x) ^ 2) ≤
        2 * δ + 2 * B ^ 2 * ε := by
  have hh := cubeAverage_mono (errorCutoffPolynomial_sq_bound (T := T) hF he hB hP)
  rw [cubeAverage_add, cubeAverage_mul_const, cubeAverage_mul_const] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hE (by norm_num))
    (mul_le_mul_of_nonneg_left hT (by positivity)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree
namespace OAI

/-! Degree bookkeeping for the random polynomial construction. The recursive
degree uses the largest child degree, rather than the number of leaves. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma WalshDegreeLE.mono {n p q : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F p) (hpq : p ≤ q) : WalshDegreeLE F q := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun S => if S.card ≤ p then a S else 0, ?_⟩
  intro x
  rw [ha]
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ p
  · simp [hS, hS.trans hpq]
  · simp [hS]


namespace AC0Circuit


end AC0Circuit

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitMixedLaw
namespace OAI

/-! The half-uniform input law in Braverman's proof. Small exceptional
probability for this law bounds both the uniform and supplied probabilities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma cubeDensityLaw_average {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (f : BooleanCube n → ℝ) :
    (cubeDensityLaw g hg hmean).average f = cubeAverage (fun x => g x * f x) := by
  unfold FiniteLaw.average cubeDensityLaw cubeAverage
  rw [sum_div]
  apply sum_congr rfl
  intro x _
  ring



lemma mixedCubeLaw_probability {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (E : BooleanCube n → Prop) :
    (mixedCubeLaw g hg hmean).probability E =
      ((cubeDensityLaw g hg hmean).probability E +
        cubeAverage (fun x => if E x then (1 : ℝ) else 0)) / 2 := by
  unfold mixedCubeLaw FiniteLaw.probability
  rw [cubeDensityLaw_average, cubeDensityLaw_average]
  have heq : (fun x => (g x + 1) / 2 * (if E x then (1 : ℝ) else 0)) =
      fun x => (1 / 2 : ℝ) *
        (g x * (if E x then (1 : ℝ) else 0) + (if E x then (1 : ℝ) else 0)) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add]
  ring

theorem mixedCubeLaw_exception_bounds {n : ℕ} (g : BooleanCube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1) (E : BooleanCube n → Prop)
    {δ : ℝ} (hE : (mixedCubeLaw g hg hmean).probability E ≤ δ) :
    (cubeDensityLaw g hg hmean).probability E ≤ 2 * δ ∧
      cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ 2 * δ := by
  rw [mixedCubeLaw_probability] at hE
  have hμ := (cubeDensityLaw g hg hmean).probability_nonneg E
  have hU : 0 ≤ cubeAverage (fun x => if E x then (1 : ℝ) else 0) := by
    calc
      0 = cubeAverage (fun _ : BooleanCube n => (0 : ℝ)) := by simp
      _ ≤ _ := cubeAverage_mono (fun x => by split_ifs <;> norm_num)
  constructor <;> linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationComparison
namespace OAI

/-! Braverman's final finite expectation argument. The combinatorial
approximation and an L² approximation to its small error event imply a
one-sided bounded-independence comparison. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma exceptionalExtension_gap {n : ℕ} {F : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (E : BooleanCube n → Bool) (x : BooleanCube n) :
    |F x - exceptionalExtension F E x| ≤ if E x then (1 : ℝ) else 0 := by
  cases hE : E x
  · simp [exceptionalExtension, hE]
  · rcases hF x with h | h <;> simp [exceptionalExtension, hE, h]

theorem TWiseUniformDensity.approximation_lower {n p q t : ℕ}
    {g F P T : BooleanCube n → ℝ} {E : BooleanCube n → Bool}
    (hwise : TWiseUniformDensity g t) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hF : ∀ x, F x = 0 ∨ F x = 1)
    (hP : WalshDegreeLE P p) (hT : WalshDegreeLE T q) (ht : (p + q) + (p + q) ≤ t)
    (houtside : ∀ x, E x = false → P x = F x)
    {B δ ε : ℝ} (hB : 1 ≤ B) (hbound : ∀ x, |P x| ≤ B)
    (hE : (mixedCubeLaw g hg hmean).probability (fun x => E x = true) ≤ δ)
    (herror : cubeAverage (fun x => ((if E x then (1 : ℝ) else 0) - T x) ^ 2) ≤ ε) :
    cubeAverage F - (8 * δ + 2 * B ^ 2 * ε) ≤ cubeAverage (fun x => g x * F x) := by
  have hmix := mixedCubeLaw_exception_bounds g hg hmean (fun x => E x = true) hE
  have hU : cubeAverage (fun x => if E x then (1 : ℝ) else 0) ≤ 2 * δ := by
    convert (preTransparency := .instances) hmix.2 using 1
    congr 1
    funext x
    by_cases h : E x = true <;> simp [h]
  have hG : cubeAverage (fun x => g x * (if E x then (1 : ℝ) else 0)) ≤ 2 * δ := by
    have hm := hmix.1
    rw [FiniteLaw.probability, cubeDensityLaw_average] at hm
    convert (preTransparency := .instances) hm using 1
    congr 1
    funext x
    by_cases h : E x = true <;> simp [h]
  have hu : cubeAverage (fun x => |F x - exceptionalExtension F E x|) ≤ 2 * δ :=
    (cubeAverage_mono (exceptionalExtension_gap hF E)).trans hU
  have hm : cubeAverage (fun x => g x * |F x - exceptionalExtension F E x|) ≤ 2 * δ :=
    (cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left
      (exceptionalExtension_gap hF E x) (hg x))).trans hG
  have hs := errorCutoffPolynomial_mean_sq hF houtside hB hbound hU herror
  have hdeg := ((errorCutoffPolynomial_degree hP hT).minorant).mono ht
  have hh := hwise.semiExact_lower hg (exceptionalExtension_boolean hF E)
    (errorCutoffPolynomial_zero houtside) hdeg hu hm hs
  convert (preTransparency := .instances) hh using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitCertificateBounds
namespace OAI

/-! Numerical bounds carried by the recursive polynomial/error-circuit
construction. They retain explicit circuit dependence until the final
size and depth estimates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit




lemma negate_indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.indicator x = 1 - c.indicator x := by
  have he : c.negate.eval x = !(c.eval x) := by
    apply Bool.eq_iff_iff.mpr
    rw [negate_eval]
    simp
  simp only [indicator, he]
  cases c.eval x <;> norm_num

end AC0Circuit



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierTruncation
namespace OAI

/-! The canonical low-degree approximation and its exact Fourier-tail error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma walshTruncation_degree {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    WalshDegreeLE (walshTruncation f t) t := ⟨walshCoefficient f, fun _ => rfl⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
namespace OAI

/-! Partial assignments and the consistent terms used in the canonical
decision tree of a DNF. Each term contains at most one literal per variable. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PartialAssignment





@[simp] lemma assign_empty {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) :
    ρ.assign ∅ x = ρ := by funext i; simp [assign]





end PartialAssignment


namespace CubeTerm










end CubeTerm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionDNF
namespace OAI

/-! A decision tree of depth r is a DNF of width at most r. Both Boolean
polarities have such a representation, so gates can be switched without
counting the number of clauses produced by earlier switches. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] lemma negate_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    T.negate.eval x = !(T.eval x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hx : x i <;> simp [negate, eval, hx, hl, hh]

@[simp] lemma negate_depth {n : ℕ} (T : BooleanDecisionTree n) : T.negate.depth = T.depth := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh => simp [negate, depth, hl, hh]

end BooleanDecisionTree







namespace BooleanDecisionTree




end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionRestriction
namespace OAI

/-! Decision-tree certificates are preserved by fixing additional coordinates.
We also package the two Boolean polarities of a certificate. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] theorem restrict_eval {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (T.restrict ρ).eval x = T.eval (ρ.apply x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none =>
      cases hx : x i <;> simp [restrict, eval, PartialAssignment.apply, hρ, hx, hl, hh]
    | some b =>
      cases b <;> simp [restrict, eval, PartialAssignment.apply, hρ, hl, hh]


end BooleanDecisionTree






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicBudgets
namespace OAI

/-! Natural-number budgets for the fixed depth twenty-two application.
Using powers of two keeps the exponential error calculation elementary. -/

namespace TwoPointCorrelations

open scoped _root_.Classical




lemma bravermanSwitches_pos (j : ℕ) : 1 ≤ bravermanSwitches j := by
  unfold bravermanSwitches
  omega



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicErrors
namespace OAI

/-! The two losses in Braverman's comparison fit a common dyadic error
budget. These are scalar inequalities, independent of the circuit. -/

namespace TwoPointCorrelations

lemma dyadic_cancel (a b : ℕ) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (a + b) = (1 / 2 : ℝ) ^ b := by
  rw [pow_add]
  calc
    _ = (2 * (1 / 2) : ℝ) ^ a * (1 / 2 : ℝ) ^ b := by rw [mul_pow]; ring
    _ = _ := by norm_num

lemma braverman_exception_loss (j : ℕ) :
    8 * ((2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
  have hsmall : (7 / 8 : ℝ) ^ bravermanSamples j ≤ (1 / 2 : ℝ) ^ (2 * j + 4) := by
    calc
      _ = ((7 / 8 : ℝ) ^ 40) ^ (j + 1) := by rw [← pow_mul]; rfl
      _ ≤ ((1 / 2 : ℝ) ^ 5) ^ (j + 1) :=
        pow_le_pow_left₀ (by positivity) (by norm_num) _
      _ = (1 / 2 : ℝ) ^ (5 * (j + 1)) := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    _ ≤ 8 * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (2 * j + 4)) := by gcongr
    _ = (2 : ℝ) ^ (j + 3) * (1 / 2 : ℝ) ^ ((j + 3) + (j + 1)) := by
      have hcoef : 8 * (2 : ℝ) ^ j = (2 : ℝ) ^ (j + 3) := by rw [pow_add]; ring
      rw [← mul_assoc, hcoef]
      congr 2
      omega
    _ = _ := dyadic_cancel _ _

lemma braverman_spectral_loss (j : ℕ) :
    2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
      (4 * (2 : ℝ) ^ bravermanErrorExponent j *
        (1 / 2 : ℝ) ^ (bravermanSwitches j + 1)) ≤
      (1 / 2 : ℝ) ^ (j + 1) := by
  let a := 2 * bravermanNormExponent j + bravermanErrorExponent j + 3
  have he : bravermanSwitches j + 1 = a + (j + 8) := by
    dsimp [bravermanSwitches, a]
    omega
  have hcoef : 2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
      (4 * (2 : ℝ) ^ bravermanErrorExponent j) = (2 : ℝ) ^ a := by
    dsimp [a]
    rw [pow_add, pow_add, show 2 * bravermanNormExponent j =
      bravermanNormExponent j * 2 by omega, pow_mul]
    ring
  calc
    _ = (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (a + (j + 8)) := by
      rw [he]
      rw [← mul_assoc, hcoef]
    _ = (1 / 2 : ℝ) ^ (j + 8) := dyadic_cancel _ _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma braverman_total_loss (j : ℕ) :
    8 * ((2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j) +
      2 * ((2 : ℝ) ^ bravermanNormExponent j) ^ 2 *
        (4 * (2 : ℝ) ^ bravermanErrorExponent j *
          (1 / 2 : ℝ) ^ (bravermanSwitches j + 1)) ≤ (1 / 2 : ℝ) ^ j := by
  have h₁ := braverman_exception_loss j
  have h₂ := braverman_spectral_loss j
  have he : (1 / 2 : ℝ) ^ (j + 1) + (1 / 2 : ℝ) ^ (j + 1) =
      (1 / 2 : ℝ) ^ j := by rw [pow_succ]; ring
  exact (add_le_add h₁ h₂).trans_eq he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicComparison
namespace OAI

/-! The fixed-depth bounded-independence theorem with a completely
explicit polynomial budget, stated first at dyadic accuracy. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

theorem AC0Circuit.dyadic_comparison_lower {n j t : ℕ} (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) (ht : bravermanDegree j ≤ t)
    (g : BooleanCube n → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hwise : TWiseUniformDensity g t) :
    cubeAverage c.indicator - (1 / 2 : ℝ) ^ j ≤
      cubeAverage (fun x => g x * c.indicator x) := by
  obtain ⟨P, E, hP, hdepth, hsize, hprob, hexact, hnorm⟩ :=
    c.dyadic_approximation (mixedCubeLaw g hg hmean) hc hm
  let D := switchingDegree 89 (bravermanSwitches j)
  have herror : cubeAverage (fun x => (E.indicator x - walshTruncation E.indicator D x) ^ 2) ≤
      4 * (2 : ℝ) ^ bravermanErrorExponent j *
        (1 / 2 : ℝ) ^ (bravermanSwitches j + 1) := by
    apply (E.fourier_tail_polynomial_degree 89 (bravermanSwitches j) hdepth
      (bravermanSwitches_pos j)).trans
    have hreal : (E.size : ℝ) ≤ (2 : ℝ) ^ bravermanErrorExponent j := by
      exact_mod_cast hsize
    gcongr
  have hF (x) : c.indicator x = 0 ∨ c.indicator x = 1 := by
    cases he : c.eval x <;> simp [AC0Circuit.indicator, he]
  have hbound : 1 ≤ (2 : ℝ) ^ bravermanNormExponent j := one_le_pow₀ (by norm_num)
  have hdegree : (bravermanBase j ^ 22 + D) + (bravermanBase j ^ 22 + D) ≤ t := by
    dsimp [bravermanDegree] at ht
    dsimp [D]
    omega
  have hh := hwise.approximation_lower hg hmean hF hP
    (walshTruncation_degree E.indicator D) hdegree
    (fun x hx => hexact x (by simp [hx])) hbound hnorm hprob herror
  have hloss := braverman_total_loss j
  linarith

theorem AC0Circuit.dyadic_comparison {n j t : ℕ} (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) (ht : bravermanDegree j ≤ t)
    (g : BooleanCube n → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hwise : TWiseUniformDensity g t) :
    |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| ≤
      (1 / 2 : ℝ) ^ j := by
  have hlo := c.dyadic_comparison_lower hc hm ht g hg hmean hwise
  have hhi := c.negate.dyadic_comparison_lower (by simpa [AC0Circuit.negate_depth] using hc)
    (by simpa [AC0Circuit.negate_size] using hm) ht g hg hmean hwise
  have hu : cubeAverage c.negate.indicator = 1 - cubeAverage c.indicator := by
    change cubeAverage (fun x => c.negate.indicator x) = _
    simp_rw [AC0Circuit.negate_indicator]
    rw [cubeAverage_sub, cubeAverage_const]
  have hgneg : cubeAverage (fun x => g x * c.negate.indicator x) =
      1 - cubeAverage (fun x => g x * c.indicator x) := by
    simp_rw [AC0Circuit.negate_indicator, mul_sub, mul_one]
    rw [cubeAverage_sub, hmean]
  rw [hu, hgneg] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialGrowth
namespace OAI

/-! The explicit dyadic independence budget is polynomial in its accuracy
parameter. The closure argument avoids expanding enormous fixed constants. -/

namespace TwoPointCorrelations


namespace NatPolynomialGrowth

theorem const (a : ℕ) : NatPolynomialGrowth (fun _ => a) :=
  ⟨a, 0, fun _ => by simp⟩

theorem id : NatPolynomialGrowth (fun j => j) :=
  ⟨1, 1, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : NatPolynomialGrowth f) (hg : NatPolynomialGrowth g) :
    NatPolynomialGrowth (fun j => f j + g j) := by
  obtain ⟨K, C, hK⟩ := hf
  obtain ⟨L, D, hL⟩ := hg
  refine ⟨K + L, C + D, fun j => ?_⟩
  calc
    _ ≤ K * (j + 1) ^ C + L * (j + 1) ^ D := Nat.add_le_add (hK j) (hL j)
    _ ≤ K * (j + 1) ^ (C + D) + L * (j + 1) ^ (C + D) := by
      gcongr <;> omega
    _ = _ := by ring

theorem mul {f g : ℕ → ℕ} (hf : NatPolynomialGrowth f) (hg : NatPolynomialGrowth g) :
    NatPolynomialGrowth (fun j => f j * g j) := by
  obtain ⟨K, C, hK⟩ := hf
  obtain ⟨L, D, hL⟩ := hg
  refine ⟨K * L, C + D, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) * (L * (j + 1) ^ D) := Nat.mul_le_mul (hK j) (hL j)
    _ = _ := by rw [pow_add]; ring

theorem pow {f : ℕ → ℕ} (hf : NatPolynomialGrowth f) (k : ℕ) :
    NatPolynomialGrowth (fun j => f j ^ k) := by
  obtain ⟨K, C, hK⟩ := hf
  refine ⟨K ^ k, C * k, fun j => ?_⟩
  calc
    _ ≤ (K * (j + 1) ^ C) ^ k := Nat.pow_le_pow_left (hK j) k
    _ = _ := by rw [mul_pow, pow_mul]

end NatPolynomialGrowth

theorem bravermanDegree_polynomial : NatPolynomialGrowth bravermanDegree := by
  have hid := NatPolynomialGrowth.id
  have hbase : NatPolynomialGrowth bravermanBase :=
    ((NatPolynomialGrowth.const 40).mul (hid.add (NatPolynomialGrowth.const 1))).mul
      (hid.add (NatPolynomialGrowth.const 3))
  have hnorm : NatPolynomialGrowth bravermanNormExponent :=
    ((NatPolynomialGrowth.const 2).mul hid |>.add (NatPolynomialGrowth.const 3)).mul
      (((NatPolynomialGrowth.const 2).mul hbase |>.add (NatPolynomialGrowth.const 2)).pow 22)
  have herror : NatPolynomialGrowth bravermanErrorExponent :=
    (NatPolynomialGrowth.const 20).mul (hid.add (NatPolynomialGrowth.const 3))
  have hr : NatPolynomialGrowth bravermanSwitches :=
    ((((NatPolynomialGrowth.const 2).mul hnorm).add herror).add hid).add
      (NatPolynomialGrowth.const 10)
  have hden : NatPolynomialGrowth (fun j => switchingDenominator (bravermanSwitches j)) :=
    (NatPolynomialGrowth.const 24).mul
      ((((NatPolynomialGrowth.const 2).mul hr).add (NatPolynomialGrowth.const 3)).pow 2)
  have hD : NatPolynomialGrowth (fun j => switchingDegree 89 (bravermanSwitches j)) :=
    (((NatPolynomialGrowth.const 8).mul (hr.add (NatPolynomialGrowth.const 1))).mul
      (hden.pow 89))
  exact (NatPolynomialGrowth.const 2).mul ((hbase.pow 22).add hD)

theorem bravermanDegree_polynomial_positive :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ j, bravermanDegree j ≤ K * (j + 1) ^ C := by
  obtain ⟨K, C, h⟩ := bravermanDegree_polynomial
  refine ⟨K + 1, C + 1, by omega, by omega, fun j => (h j).trans ?_⟩
  exact Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_right (by omega) (Nat.le_succ C))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitLogarithmicBudget
namespace OAI

/-! Convert a dyadic accuracy index to the natural logarithm used in the
published fixed-depth bounded-independence input. -/

namespace TwoPointCorrelations

lemma dyadic_index_of_ratio (m : ℕ) (hm : 1 ≤ m) (ε : ℝ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ j : ℕ, m ≤ 2 ^ j ∧ (1 / 2 : ℝ) ^ j ≤ ε ∧
      (j : ℝ) + 1 ≤ 6 * Real.log ((m : ℝ) / ε) := by
  let L := Real.log ((m : ℝ) / ε)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio : (2 : ℝ) ≤ (m : ℝ) / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hL : 1 / 2 ≤ L := hlogtwo.trans (Real.log_le_log (by norm_num) hratio)
  let j := ⌈2 * L⌉₊
  have hjlo : 2 * L ≤ (j : ℝ) := Nat.le_ceil _
  have hjhi : (j : ℝ) < 2 * L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlogbound : L ≤ (j : ℝ) * Real.log 2 := by
    nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]
  have hx : (m : ℝ) / ε ≤ (2 : ℝ) ^ j := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simpa only [Real.log_pow] using hlogbound
  have hmul : (m : ℝ) ≤ (2 : ℝ) ^ j * ε := (div_le_iff₀ hε).mp hx
  have hmle : (m : ℝ) ≤ (2 : ℝ) ^ j := by nlinarith [show (0 : ℝ) < 2 ^ j by positivity]
  have heps : (1 / 2 : ℝ) ^ j ≤ ε := by
    have hh : (1 : ℝ) / (2 : ℝ) ^ j ≤ ε :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    simpa only [div_pow, one_pow] using hh
  exact ⟨j, by exact_mod_cast hmle, heps, by linarith⟩

theorem bravermanDegree_logarithmic_budget :
    ∃ K C : ℕ, 0 < K ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ t : ℕ,
        (K : ℝ) * (Real.log ((m : ℝ) / ε)) ^ C ≤ (t : ℝ) →
        ∃ j : ℕ, m ≤ 2 ^ j ∧ (1 / 2 : ℝ) ^ j ≤ ε ∧ bravermanDegree j ≤ t := by
  obtain ⟨K, C, hK, hC, hbound⟩ := bravermanDegree_polynomial_positive
  refine ⟨K * 6 ^ C, C, by positivity, hC, ?_⟩
  intro m hm ε hε hεhalf t ht
  obtain ⟨j, hmj, hjε, hjlog⟩ := dyadic_index_of_ratio m hm ε hε hεhalf
  refine ⟨j, hmj, hjε, ?_⟩
  have hj : (bravermanDegree j : ℝ) ≤ (K : ℝ) * ((j : ℝ) + 1) ^ C := by
    exact_mod_cast hbound j
  have hdeg : (bravermanDegree j : ℝ) ≤ (t : ℝ) := by
    calc
      _ ≤ _ := hj
      _ ≤ (K : ℝ) * (6 * Real.log ((m : ℝ) / ε)) ^ C := by gcongr
      _ = ((K * 6 ^ C : ℕ) : ℝ) * (Real.log ((m : ℝ) / ε)) ^ C := by
        push_cast
        rw [mul_pow]
        ring
      _ ≤ _ := ht
  exact_mod_cast hdeg

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BravermanDepth22Theorem
namespace OAI

/-! Braverman’s bounded-independence theorem at depth twenty-two follows
from finite circuit approximation and switching estimates. -/

namespace TwoPointCorrelations

theorem bravermanDepth22Input : BravermanDepth22Input := by
  obtain ⟨K, C, hK, hC, hbudget⟩ := bravermanDegree_logarithmic_budget
  refine ⟨K, C, hK, hC, ?_⟩
  intro n c hc ε hε hεhalf t ht g hg hmean hwise
  obtain ⟨j, hmj, hεj, htj⟩ := hbudget c.size c.size_pos ε hε hεhalf t ht
  exact (c.dyadic_comparison hc hmj htj g hg hmean hwise).trans hεj

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
namespace OAI

/-!
# Residue classes as finite multiplicative expansions

The character identity in manuscript Lemma `lem:affine-residue` includes
nonunit residue classes. Dividing by the gcd reduces to a unit class, so the
standard character orthogonality relation applies even when the reduced
modulus is one. Each resulting dilation has the finite expansion already
proved in `Dilation`.
-/

open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations


lemma naturalCharacter_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Multiplicative (naturalCharacter χ) := by
  intro m n _ _ _
  simp [naturalCharacter, map_mul]

lemma naturalCharacter_oneBounded {q : ℕ} (χ : DirichletCharacter ℂ q) :
    OneBounded (naturalCharacter χ) := by
  intro n _
  exact χ.norm_le_one _

@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]

/-- The inverse-value form of conjugation on a unit residue. -/
lemma character_conj_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : conj (χ a) = χ a⁻¹ := by
  rw [show conj (χ a) = χ⁻¹ a from MulChar.star_apply' χ a, MulChar.inv_apply]
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit, ZMod.inv_coe_unit]

lemma residue_character_orthogonality {q c k : ℕ} (hq : 0 < q)
    (hc : c.Coprime q) :
    (if k % q = c % q then (1 : ℂ) else 0) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, conj (naturalCharacter χ c) * naturalCharacter χ k := by
  let : NeZero q := ⟨hq.ne'⟩
  have hcunit : IsUnit (c : ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hc
  have hs := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hcunit (k : ZMod q)
  have htot : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have heq : ((c : ZMod q) = (k : ZMod q)) ↔ k % q = c % q := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact eq_comm
  simp_rw [naturalCharacter, character_conj_unit _ hcunit]
  simp only [hs, heq]
  split_ifs <;> simp_all

lemma scaled_residue_iff {d q c n : ℕ} (hd : 0 < d) (hn : d ∣ n) :
    n % (d * q) = (d * c) % (d * q) ↔ (n / d) % q = c % q := by
  obtain ⟨k, rfl⟩ := hn
  rw [Nat.mul_div_cancel_left k hd, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact Nat.mul_left_cancel_iff hd

lemma dvd_of_scaled_residue {d q c n : ℕ}
    (h : n % (d * q) = (d * c) % (d * q)) : d ∣ n := by
  have hr : d ∣ n % (d * q) := by
    rw [h, Nat.mul_mod_mul_left]
    exact dvd_mul_right d _
  have ht : d ∣ (d * q) * (n / (d * q)) := dvd_mul_of_dvd_left (dvd_mul_right d q) _
  simpa only [Nat.mod_add_div] using dvd_add hr ht

/-- Gcd reduction followed by character orthogonality, valid also for `b = 0`
and for reduced modulus one. No assumption that the original class is a unit
is present. -/
theorem residue_indicator_eq_character_dilations (l b n : ℕ) (hl : 0 < l) :
    (if n % l = b % l then (1 : ℂ) else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          conj (naturalCharacter χ (b / b.gcd l)) *
            dilate (b.gcd l) (naturalCharacter χ) n := by
  let d := b.gcd l
  let q := l / d
  let c := b / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hl
  have hdl : d ∣ l := Nat.gcd_dvd_right b l
  have hdb : d ∣ b := Nat.gcd_dvd_left b l
  have hlq : l = d * q := (Nat.mul_div_cancel' hdl).symm
  have hbc : b = d * c := (Nat.mul_div_cancel' hdb).symm
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl hdl) hd
  have hc : c.Coprime q := Nat.coprime_div_gcd_div_gcd hd
  change (if n % l = b % l then (1 : ℂ) else 0) =
    (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      conj (naturalCharacter χ c) * dilate d (naturalCharacter χ) n
  by_cases hn : d ∣ n
  · simp only [dilate, if_pos hn]
    rw [hlq, hbc]
    simp only [scaled_residue_iff hd hn]
    exact residue_character_orthogonality hq hc
  · have hnres : n % l ≠ b % l := by
      intro h
      apply hn
      apply dvd_of_scaled_residue (q := q) (c := c)
      simpa only [← hlq, ← hbc] using h
    simp [hnres, dilate, hn]

/-- Every residue indicator is an explicit finite sum of bounded normalized
multiplicative functions. -/
theorem residue_indicator_eq_components (l b n : ℕ) (hl : 0 < l) (hn : 0 < n) :
    (if n % l = b % l then (1 : ℂ) else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              dilationComponent (b.gcd l) (naturalCharacter χ) E n := by
  rw [residue_indicator_eq_character_dilations l b n hl]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [dilate_eq_sum_components (b.gcd l) (naturalCharacter χ)
    (Nat.gcd_pos_of_pos_right b hl) (naturalCharacter_multiplicative χ)
    (naturalCharacter_one χ) hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E _
  ring

lemma Multiplicative.mul {f g : ℕ → ℂ} (hf : Multiplicative f) (hg : Multiplicative g) :
    Multiplicative (fun n => f n * g n) := by
  intro m n hm hn hcop
  dsimp only
  rw [hf m n hm hn hcop, hg m n hm hn hcop]
  ring

lemma OneBounded.mul {f g : ℕ → ℂ} (hf : OneBounded f) (hg : OneBounded g) :
    OneBounded (fun n => f n * g n) := by
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (hg n hn) (norm_nonneg _) zero_le_one).trans_eq
    (by norm_num)


lemma residueComponent_multiplicative {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hf : Multiplicative f) :
    Multiplicative (residueComponent f d χ E) :=
  hf.mul (dilationComponent_multiplicative d (naturalCharacter χ) E)

lemma residueComponent_oneBounded {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hf : OneBounded f) :
    OneBounded (residueComponent f d χ E) :=
  hf.mul (dilationComponent_oneBounded d (naturalCharacter χ) E
    (naturalCharacter_oneBounded χ))

/-- Restriction to a nonunit progression modifies the character twist only at
primes dividing the fixed gcd. Hence every multiplicative piece preserves the
original uniformly nonpretentious factor. -/
lemma residueComponent_nonpretentious {q : ℕ} (f : ℕ → ℂ) (d : ℕ)
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (hq : 0 < q)
    (hf : OneBounded f) (hfnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious (residueComponent f d χ E) := by
  apply (hfnp.twistByCharacter χ hq).finite_prime_change d.primeFactors
    (hf.twistByCharacter χ) (residueComponent_oneBounded f d χ E hf)
  intro p hp hpD
  unfold residueComponent TwoPointCorrelations.twistByCharacter
  congr 1
  simpa only [pow_one, naturalCharacter] using
    dilationComponent_prime_pow d (naturalCharacter χ) E (naturalCharacter_one χ) hp hpD 1

/-- An explicit expansion after multiplication by the original first factor. -/
theorem residue_weight_eq_components (f : ℕ → ℂ) (l b n : ℕ)
    (hl : 0 < l) (hn : 0 < n) :
    (if n % l = b % l then f n else 0) =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              residueComponent f (b.gcd l) χ E n := by
  calc
    _ = f n * (if n % l = b % l then (1 : ℂ) else 0) := by split_ifs <;> simp
    _ = _ := by
      rw [residue_indicator_eq_components l b n hl hn, mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      unfold residueComponent
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.AffineDeduction
namespace OAI

open _root_.Filter
open scoped _root_.BigOperators

namespace TwoPointCorrelations


theorem Multiplicative.one_eq_zero_or_one {f : ℕ → ℂ} (hf : Multiplicative f) :
    f 1 = 0 ∨ f 1 = 1 := by
  have heq := hf 1 1 (by decide) (by decide) (by decide)
  have hprod : f 1 * (f 1 - 1) = 0 := by
    calc
      f 1 * (f 1 - 1) = f 1 * f 1 - f 1 := by ring
      _ = 0 := by simpa using congrArg (fun z : ℂ => z - f 1) heq.symm
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem Multiplicative.zero_of_one_eq_zero {f : ℕ → ℂ} (hf : Multiplicative f)
    (h0 : f 1 = 0) {n : ℕ} (hn : 0 < n) : f n = 0 := by
  simpa [h0] using hf 1 n (by decide) hn (Nat.coprime_one_left n)

lemma residuePrefix_congr {u v : ℕ → ℂ} (h : ∀ n, 0 < n → u n = v n)
    (l b N : ℕ) : residuePrefix u l b N = residuePrefix v l b N := by
  unfold residuePrefix
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n (Finset.mem_Ioc.mp hn).1]

lemma residuePrefix_sum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℂ) (l b N : ℕ) :
    residuePrefix (fun n => ∑ i ∈ s, u i n) l b N =
      ∑ i ∈ s, residuePrefix (u i) l b N := by
  unfold residuePrefix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

lemma residuePrefix_const_mul (c : ℂ) (u : ℕ → ℂ) (l b N : ℕ) :
    residuePrefix (fun n => c * u n) l b N = c * residuePrefix u l b N := by
  unfold residuePrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- Finite signed local expansions preserve an established progression limit. -/
theorem finite_expansion_progression_zero {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (F : ι → ℕ → ℂ) (G : κ → ℕ → ℂ) (u v : ℕ → ℂ)
    (hu : ∀ n, 0 < n → u n = ∑ i ∈ s, c i * F i n)
    (hv : ∀ n, 0 < n → v n = ∑ j ∈ t, d j * G j n)
    (h l b : ℕ)
    (hz : ∀ i ∈ s, ∀ j ∈ t,
      Tendsto (fun N : ℕ => residuePrefix (fun n => F i n * G j (n + h)) l b N /
        (N : ℂ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => residuePrefix (fun n => u n * v (n + h)) l b N /
      (N : ℂ)) atTop (nhds 0) := by
  have heq (N : ℕ) : residuePrefix (fun n => u n * v (n + h)) l b N / (N : ℂ) =
      ∑ i ∈ s, ∑ j ∈ t, (c i * d j) *
        (residuePrefix (fun n => F i n * G j (n + h)) l b N / (N : ℂ)) := by
    rw [residuePrefix_congr (v := fun n => ∑ i ∈ s, ∑ j ∈ t,
      (c i * d j) * (F i n * G j (n + h))) (by
        intro n hn
        rw [hu n hn, hv (n + h) (by omega)]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring)]
    simp only [residuePrefix_sum, residuePrefix_const_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  have hout := tendsto_finsetSum s (fun i hi =>
    tendsto_finsetSum t (fun j hj =>
      (tendsto_const_nhds (x := c i * d j)).mul (hz i hi j hj)))
  simpa using hout

theorem ProgressionCorrectedElliott.dilations
    (hprog : ProgressionCorrectedElliott) (f g : ℕ → ℂ)
    (hf : Multiplicative f) (hg : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hfb : OneBounded f) (hgb : OneBounded g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (a a' h l b : ℕ) (ha : 0 < a) (ha' : 0 < a') (hh : 0 < h) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      residuePrefix (fun n => dilate a f n * dilate a' g (n + h)) l b N / (N : ℂ))
      atTop (nhds 0) := by
  apply finite_expansion_progression_zero a.primeFactors.powerset a'.primeFactors.powerset
    (fun E => (-1 : ℂ) ^ E.card) (fun E => (-1 : ℂ) ^ E.card)
    (dilationComponent a f) (dilationComponent a' g)
    (dilate a f) (dilate a' g)
    (fun n hn => dilate_eq_sum_components a f ha hf hf1 hn)
    (fun n hn => dilate_eq_sum_components a' g ha' hg hg1 hn)
  intro E _ E' _
  apply hprog _ _ (dilationComponent_multiplicative a f E)
    (dilationComponent_multiplicative a' g E')
    (dilationComponent_oneBounded _ _ _ hfb) (dilationComponent_oneBounded _ _ _ hgb)
    _ h l b hh hl
  exact hnp.imp (dilationComponent_nonpretentious a f E hfb)
    (dilationComponent_nonpretentious a' g E' hgb)

private theorem affine_ordered_zero (hprog : ProgressionCorrectedElliott)
    (f g : ℕ → ℂ) (hf : Multiplicative f) (hg : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hfb : OneBounded f) (hgb : OneBounded g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (horder : a₂ * b₁ < a₁ * b₂) :
    Tendsto (fun N : ℕ => affineSum f g a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0) := by
  have hp := hprog.dilations f g hf hg hf1 hg1 hfb hgb hnp a₂ a₁
    (a₁ * b₂ - a₂ * b₁) (a₁ * a₂) (a₂ * b₁) ha₂ ha₁
    (Nat.sub_pos_of_lt horder) (Nat.mul_pos ha₁ ha₂)
  have ht := affine_mean_tendsto_zero
    (fun m => dilate a₂ f m * dilate a₁ g (m + (a₁ * b₂ - a₂ * b₁)))
    (a₁ * a₂) (a₂ * b₁) (Nat.mul_pos ha₁ ha₂) hp
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only
  congr 1
  unfold affineSum
  apply Finset.sum_congr rfl
  intro n hn
  have hl : a₁ * a₂ * n + a₂ * b₁ = a₂ * (a₁ * n + b₁) := by ring
  have hr : a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁) =
      a₁ * (a₂ * n + b₂) := by
    calc
      _ = a₁ * a₂ * n + a₁ * b₂ := by omega
      _ = _ := by ring
  rw [hr, hl]
  simp [dilate, ha₁.ne', ha₂.ne']

/-- The manuscript's affine reduction, conditional here on its internal
progression theorem. This is not the published-input conditional main result. -/
theorem ProgressionCorrectedElliott.affine (hprog : ProgressionCorrectedElliott) :
    AffineCorrectedElliott := by
  intro f g hf hg hfb hgb hnp a₁ a₂ b₁ b₂ ha₁ ha₂ hneq
  rcases hf.one_eq_zero_or_one with hf0 | hf1
  · have hz (N : ℕ) : affineSum f g a₁ a₂ b₁ b₂ N = 0 := by
      unfold affineSum
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos := (Finset.mem_Icc.mp hn).1
      rw [hf.zero_of_one_eq_zero hf0 (by nlinarith : 0 < a₁ * n + b₁), zero_mul]
    simpa only [hz, zero_div] using (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
  rcases hg.one_eq_zero_or_one with hg0 | hg1
  · have hz (N : ℕ) : affineSum f g a₁ a₂ b₁ b₂ N = 0 := by
      unfold affineSum
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos := (Finset.mem_Icc.mp hn).1
      rw [hg.zero_of_one_eq_zero hg0 (by nlinarith : 0 < a₂ * n + b₂), mul_zero]
    simpa only [hz, zero_div] using (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have h := affine_ordered_zero hprog g f hg hf hg1 hf1 hgb hfb hnp.symm
      a₂ a₁ b₂ b₁ ha₂ ha₁ hlt
    simpa only [affineSum_swap f g] using h
  · exact affine_ordered_zero hprog f g hf hg hf1 hg1 hfb hgb hnp
      a₁ a₂ b₁ b₂ ha₁ ha₂ hgt

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ProgressionDeduction
namespace OAI

/-!
# From binary cancellation to every progression and affine forms

The character expansion treats all residue classes, while
finite-prime stability preserves nonpretentiousness of an original factor.
-/

open _root_.Filter
open scoped _root_.BigOperators _root_.ComplexConjugate

namespace TwoPointCorrelations

/-- The progression sum is a fixed finite linear combination of ordinary
binary sums, with no coprimality condition on the residue class. -/
theorem residuePrefix_eq_component_correlations (f g : ℕ → ℂ) (h l b N : ℕ)
    (hl : 0 < l) :
    residuePrefix (fun n => f n * g (n + h)) l b N =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              correlationSum (residueComponent f (b.gcd l) χ E) g 0 h N := by
  have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  unfold residuePrefix
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N,
        ((l / b.gcd l).totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
            ∑ E ∈ (b.gcd l).primeFactors.powerset,
              (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
                (residueComponent f (b.gcd l) χ E n * g (n + h)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos := (Finset.mem_Ioc.mp hn).1
      rw [show (if n % l = b % l then f n * g (n + h) else 0) =
          (if n % l = b % l then f n else 0) * g (n + h) by split_ifs <;> simp]
      rw [residue_weight_eq_components f l b n hl hnpos, mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      rw [← Finset.mul_sum]
      simp only [correlationSum, hI, Nat.add_zero]

/-- Every-residue progression cancellation follows from the
binary corrected Elliott statement by finite character expansion. -/
theorem BinaryCorrectedElliott.progression (hbinary : BinaryCorrectedElliott) :
    ProgressionCorrectedElliott := by
  intro f g hf hg hfb hgb hnp h l b hh hl
  let d := b.gcd l
  let q := l / d
  let c := b / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hl
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_right b l)) hd
  have hpiece (χ : DirichletCharacter ℂ q) (E : Finset ℕ) :
      Tendsto (fun N : ℕ => correlationSum (residueComponent f d χ E) g 0 h N /
        (N : ℂ)) atTop (nhds 0) := by
    apply hbinary _ _ (residueComponent_multiplicative f d χ E hf) hg
      (residueComponent_oneBounded f d χ E hfb) hgb _ 0 h hh.ne
    exact hnp.imp (residueComponent_nonpretentious f d χ E hq hfb) id
  have hsum := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ _ => tendsto_finsetSum d.primeFactors.powerset (fun E _ =>
      (tendsto_const_nhds (x := conj (naturalCharacter χ c) * (-1 : ℂ) ^ E.card)).mul
        (hpiece χ E)))
  have hlimit := (tendsto_const_nhds (x := (q.totient : ℂ)⁻¹)).mul hsum
  have heq (N : ℕ) :
      residuePrefix (fun n => f n * g (n + h)) l b N / (N : ℂ) =
        (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, ∑ E ∈ d.primeFactors.powerset,
            (conj (naturalCharacter χ c) * (-1 : ℂ) ^ E.card) *
              (correlationSum (residueComponent f d χ E) g 0 h N / (N : ℂ)) := by
    rw [residuePrefix_eq_component_correlations f g h l b N hl]
    simp only [d, q, c, mul_div_assoc, Finset.sum_div]
  simp_rw [heq]
  simpa using hlimit

/-- The complete qualitative affine reduction, including nonunit slopes and
either original nonpretentious factor, assuming binary cancellation. -/
theorem BinaryCorrectedElliott.affine (hbinary : BinaryCorrectedElliott) :
    AffineCorrectedElliott := hbinary.progression.affine

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ConditionalElliott
namespace OAI

/-! Theorem 1.2 and Corollary 1.3 of the manuscript, conditionally on the
explicit published short-sum, prime-distribution and circuit inputs. -/

namespace TwoPointCorrelations



theorem conditional_affineCorrectedElliott (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  (conditional_binaryCorrectedElliott hP hBr hM hMRT).affine

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.PartiallyDischargedMain
namespace OAI

/-! All three main statements with the two proved prime-distribution inputs
discharged. Only the circuit and MRT inputs remain parameters. -/

namespace TwoPointCorrelations



theorem affineCorrectedElliott_of_circuit_mrt (hBr : BravermanDepth22Input)
    (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  conditional_affineCorrectedElliott modFiveThetaInput hBr primeReciprocalInput hMRT

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.MainWithMRTInputs
namespace OAI

/-! The three manuscript main results after discharging both prime inputs
and the fixed-depth Braverman input. Only the published MRT inputs remain. -/

namespace TwoPointCorrelations



theorem affineCorrectedElliott_of_mrt_oai (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  affineCorrectedElliott_of_circuit_mrt bravermanDepth22Input hMRT

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.affineCorrectedElliott_of_mrt_oai := @OAI.TwoPointCorrelations.affineCorrectedElliott_of_mrt_oai
