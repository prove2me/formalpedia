-- Prove2me | solution 1 for OAI.TwoPointCorrelations.conditional_binaryCorrectedElliott
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:43:08.452358+00:00
-- url     : https://prove2.me/submissions/9fc1b4fd-8097-4458-acce-890412b3edaf

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_canonical_shifted_source_deletion_uniform
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_complex_bin
import Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_retained_mass
import Theorems.Thm_OAI_TwoPointCorrelations_canonical_raw_pair_selection
import Theorems.Thm_OAI_TwoPointCorrelations_qualitative_canonical_nonraw_total

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueCounts
namespace OAI

/-!
# Residue counts on arbitrary finite consecutive intervals

An interval is represented by its starting residue `A` and its length `N`.
Thus this includes arbitrary translates, including intervals starting at
negative integers. We prove the exact quotient-and-remainder count, the
one-count discrepancy, and the total-variation estimate used by the finite
residue comparison in the manuscript.
-/

namespace TwoPointCorrelations

open _root_.Finset


lemma residueCount_add {D : ℕ} [NeZero D] (A : ZMod D) (M N : ℕ) (r : ZMod D) :
    residueCount A (M + N) r = residueCount A M r + residueCount (A + (M : ZMod D)) N r := by
  unfold residueCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_add, add_assoc]

lemma residueCount_period {D : ℕ} [NeZero D] (A r : ZMod D) :
    residueCount A D r = 1 := by
  unfold residueCount
  rw [← Fin.sum_univ_eq_sum_range]
  let e : Fin D ≃ ZMod D :=
    { toFun := fun i => (i.val : ZMod D)
      invFun := fun z => ⟨z.val, z.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun z => ZMod.natCast_zmod_val z }
  change (∑ i : Fin D, (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0) (e i)) = 1
  rw [e.sum_comp (fun z : ZMod D => if A + z = r then (1 : ℕ) else 0)]
  have htest (j : ZMod D) : A + j = r ↔ j = r - A := by
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using h
    · intro h
      rw [h]
      ring
  simp_rw [htest]
  simp

lemma residueCount_multiple {D : ℕ} [NeZero D] (A r : ZMod D) (k : ℕ) :
    residueCount A (D * k) r = k := by
  induction k with
  | zero => simp [residueCount]
  | succ k ih =>
      rw [Nat.mul_succ, residueCount_add, ih, residueCount_period]

lemma residueCount_short {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ)
    (hN : N ≤ D) : residueCount A N r = if (r - A).val < N then 1 else 0 := by
  unfold residueCount
  have htest (j : ℕ) (hj : j ∈ Finset.range N) :
      A + (j : ZMod D) = r ↔ j = (r - A).val := by
    have hjD : j < D := (Finset.mem_range.mp hj).trans_le hN
    constructor
    · intro h
      have heq : (j : ZMod D) = r - A := by
        apply eq_sub_iff_add_eq.mpr
        simpa [add_comm] using h
      have hv := congrArg ZMod.val heq
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hjD] using hv
    · intro h
      rw [h, ZMod.natCast_zmod_val]
      ring
  calc
    (∑ j ∈ Finset.range N, if A + (j : ZMod D) = r then 1 else 0) =
        ∑ j ∈ Finset.range N, if j = (r - A).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [htest j hj]
    _ = if (r - A).val < N then 1 else 0 := by simp

/-- Exact residue count on an arbitrary translated interval. -/
theorem residueCount_exact {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    residueCount A N r = N / D + if (r - A).val < N % D then 1 else 0 := by
  have hsplit := residueCount_add A (D * (N / D)) (N % D) r
  have hN : D * (N / D) + N % D = N := Nat.div_add_mod N D
  rw [hN, residueCount_multiple] at hsplit
  simpa only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    residueCount_short A r (N % D) (Nat.le_of_lt (Nat.mod_lt N (NeZero.pos D)))] using hsplit

/-- The count differs from interval length divided by modulus by at most one. -/
theorem residueCount_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D) (N : ℕ) :
    |(residueCount A N r : ℝ) - (N : ℝ) / D| ≤ 1 := by
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  have hrem₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) := by positivity
  have hrem₁ : ((N % D : ℕ) : ℝ) < D := by exact_mod_cast Nat.mod_lt N (NeZero.pos D)
  have hdiv₀ : (0 : ℝ) ≤ ((N % D : ℕ) : ℝ) / D := div_nonneg hrem₀ hD.le
  have hdiv₁ : ((N % D : ℕ) : ℝ) / D < 1 := (div_lt_one hD).mpr hrem₁
  have hquot : (N : ℝ) / D = (N / D : ℕ) + ((N % D : ℕ) : ℝ) / D := by
    have hN : (N : ℝ) = (D : ℝ) * (N / D : ℕ) + (N % D : ℕ) := by
      exact_mod_cast (Nat.div_add_mod N D).symm
    apply (div_eq_iff hD.ne').mpr
    field_simp
    nlinarith [hN]
  rw [residueCount_exact, Nat.cast_add, hquot]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> rw [abs_le] <;>
    constructor <;> linarith




lemma residueProbability_discrepancy {D : ℕ} [NeZero D] (A r : ZMod D)
    (N : ℕ) (hN : 0 < N) : |residueProbability A N r - 1 / (D : ℝ)| ≤ 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have heq : residueProbability A N r - 1 / (D : ℝ) =
      ((residueCount A N r : ℝ) - (N : ℝ) / D) / N := by
    unfold residueProbability
    field_simp
  rw [heq, abs_div, abs_of_pos hN']
  exact div_le_div_of_nonneg_right (residueCount_discrepancy A r N) hN'.le


/-- The stronger `D/(2N)` bound implies the `D/N` estimate used in the paper. -/
theorem residueTotalVariation_le {D : ℕ} [NeZero D] (A : ZMod D)
    (N : ℕ) (hN : 0 < N) : residueTotalVariation A N ≤ (D : ℝ) / (2 * N) := by
  unfold residueTotalVariation
  have hsum : (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
      (D : ℝ) / N := by
    calc
      (∑ r : ZMod D, |residueProbability A N r - 1 / (D : ℝ)|) ≤
          ∑ _r : ZMod D, 1 / (N : ℝ) :=
        Finset.sum_le_sum (fun r _ => residueProbability_discrepancy A r N hN)
      _ = (D : ℝ) / N := by simp [ZMod.card, nsmul_eq_mul, div_eq_mul_inv]
  have := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
  convert (preTransparency := .instances) this using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
namespace OAI

/-!
# Finite CRT marginals and contraction under independent randomization

A selected finite set of pairwise coprime residue coordinates has the law
of one residue modulo their product. The exact interval count from
`ResidueCounts` gives total variation at most `D / (2N)`. Applying any
finite stochastic kernel preserves this bound; in particular one may add
independent finite randomness and project to any selected encoded bits.
These are the finite arithmetic and data-processing steps in `q:crt-bits`.
-/

open _root_.Finset

namespace TwoPointCorrelations






/-- A bounded observable has expectation difference at most twice TV. -/
lemma finite_observable_difference {α : Type*} [Fintype α]
    (f g u : α → ℝ) (hu : ∀ x, |u x| ≤ 1) :
    |(∑ x, f x * u x) - ∑ x, g x * u x| ≤ 2 * finiteTotalVariation f g := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (f x * u x - g x * u x)| = |∑ x, (f x - g x) * u x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ x, |(f x - g x) * u x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu x)
    _ = 2 * finiteTotalVariation f g := by unfold finiteTotalVariation; ring








/-- This CRT-transported mass is the actual empirical joint residue law. -/
lemma crtJointProbability_eq_count {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (r : ∀ i, ZMod (s i)) :
    crtJointProbability s hcop A N r =
      (∑ j ∈ Finset.range N,
        if ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r
          then (1 : ℝ) else 0) / N := by
  unfold crtJointProbability residueProbability residueCount
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have heq : A + (j : ZMod (∏ i, s i)) = (ZMod.prodEquivPi s hcop).symm r ↔
      ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))) = r :=
    (ZMod.prodEquivPi s hcop).toEquiv.eq_symm_apply
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, heq]




lemma crtJointProbability_totalVariation {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℕ)
    [∀ i, NeZero (s i)] (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) :
    finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) =
      residueTotalVariation A N := by
  unfold finiteTotalVariation crtJointProbability crtUniform residueTotalVariation
  congr 1
  exact (ZMod.prodEquivPi s hcop).symm.toEquiv.sum_comp
    (fun z => |residueProbability A N z - 1 / (∏ i, s i : ℕ)|)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CoprimeExceptionDensity
namespace OAI

/-! The finite coprimality-exception count used when extracting a fixed
divisor from two multiplicative functions. No independence between the
two residue conditions is assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma shiftedDivisorCount_eq_residueCount (p a Y : ℕ) [NeZero p] :
    shiftedDivisorCount p a Y = residueCount (a : ZMod p) Y 0 := by
  unfold shiftedDivisorCount residueCount
  simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]

lemma shiftedDivisorCount_le (p a Y : ℕ) (hp : 0 < p) :
    (shiftedDivisorCount p a Y : ℝ) ≤ (Y : ℝ) / p + 1 := by
  let _ : NeZero p := ⟨hp.ne'⟩
  rw [shiftedDivisorCount_eq_residueCount]
  have hb := (abs_le.mp (residueCount_discrepancy (a : ZMod p) 0 Y)).2
  linarith


lemma coprimeExceptionCount_le_divisorCounts (u d Y : ℕ) (P : Finset ℕ)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    coprimeExceptionCount u d Y ≤
      ∑ p ∈ P, (shiftedDivisorCount p 1 Y + shiftedDivisorCount p (1 + d) Y) := by
  unfold coprimeExceptionCount shiftedDivisorCount
  calc
    _ ≤ ∑ v ∈ range Y, ∑ p ∈ P,
        ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0)) := by
      apply sum_le_sum
      intro v _
      by_cases hv : u.Coprime ((v + 1) * (v + 1 + d))
      · calc
          _ = 0 := if_neg (fun hnot => hnot hv)
          _ ≤ _ := Nat.zero_le _
      · simp only [hv, not_false_eq_true, ite_true]
        obtain ⟨p, hp, hpu, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hv
        have hpP := hcover p hp hpu
        have hsingle :
            ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0)) ≤
              ∑ p ∈ P, ((if p ∣ 1 + v then 1 else 0) +
                (if p ∣ 1 + d + v then 1 else 0)) :=
          single_le_sum (f := fun p : ℕ =>
            ((if p ∣ 1 + v then 1 else 0) + (if p ∣ 1 + d + v then 1 else 0) : ℕ))
            (fun _ _ => Nat.zero_le _) hpP
        apply le_trans _ hsingle
        rcases hp.dvd_mul.mp hpn with hpn | hpn
        · have ht : p ∣ 1 + v := by simpa only [Nat.add_comm] using hpn
          simp only [ht, ite_true]
          omega
        · have ht : p ∣ 1 + d + v := by
            convert (preTransparency := .instances) hpn using 1
            omega
          simp only [ht, ite_true]
          omega
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      exact sum_add_distrib

theorem coprimeExceptionCount_bound (u d Y : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    (coprimeExceptionCount u d Y : ℝ) ≤
      2 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 2 * P.card := by
  have hnat := coprimeExceptionCount_le_divisorCounts u d Y P hcover
  calc
    _ ≤ ∑ p ∈ P, ((shiftedDivisorCount p 1 Y : ℝ) +
        (shiftedDivisorCount p (1 + d) Y : ℝ)) := by exact_mod_cast hnat
    _ ≤ ∑ p ∈ P, (2 * (Y : ℝ) * (1 / (p : ℝ)) + 2) := by
      apply sum_le_sum
      intro p hp
      have h₁ := shiftedDivisorCount_le p 1 Y (hP p hp).pos
      have h₂ := shiftedDivisorCount_le p (1 + d) Y (hP p hp).pos
      calc
        _ ≤ ((Y : ℝ) / p + 1) + ((Y : ℝ) / p + 1) := add_le_add h₁ h₂
        _ = _ := by ring
    _ = _ := by rw [sum_add_distrib, mul_sum]; simp [mul_comm]


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





/-- Grouping an interval average by its actual CRT residue vector. -/
lemma crtJointProbability_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtJointProbability s hcop A N r * F r) =
      uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) := by
  simp_rw [crtJointProbability_eq_count, div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold uniformAverage
  rw [Fintype.card_fin]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => F (ZMod.prodEquivPi s hcop (A + (j : ZMod (∏ i, s i))))) N).symm

lemma crtUniform_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (F : (∀ i, ZMod (s i)) → ℝ) :
    (∑ r, crtUniform s r * F r) = uniformAverage F := by
  unfold crtUniform uniformAverage
  rw [← Finset.mul_sum]
  simp only [Fintype.card_pi, ZMod.card, Nat.cast_prod]
  ring

/-- Uniform translated interval averages of any bounded observable of the
selected residue coordinates differ from the product law by at most `D/N`. -/
theorem crt_observable_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N)
    (F : (∀ i, ZMod (s i)) → ℝ) (hF : ∀ r, |F r| ≤ 1) :
    |uniformAverage (fun j : Fin N =>
        F (ZMod.prodEquivPi s hcop (A + (j.val : ZMod (∏ i, s i))))) -
      uniformAverage F| ≤ (∏ i, s i : ℕ) / (N : ℝ) := by
  have h := finite_observable_difference (crtJointProbability s hcop A N) (crtUniform s) F hF
  rw [crtJointProbability_expectation, crtUniform_expectation] at h
  calc
    _ ≤ 2 * finiteTotalVariation (crtJointProbability s hcop A N) (crtUniform s) := h
    _ = 2 * residueTotalVariation A N := by rw [crtJointProbability_totalVariation]
    _ ≤ 2 * ((∏ i, s i : ℕ) / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (residueTotalVariation_le A N hN) (by norm_num)
    _ = _ := by ring

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




theorem norm_positivePrefix_le (u : ℕ → ℂ) (Y : ℕ) (B : ℝ)
    (hu : ∀ n, 0 < n → ‖u n‖ ≤ B) : ‖positivePrefix u Y‖ ≤ Y * B := by
  calc
    _ ≤ ∑ v ∈ Finset.range Y, ‖u (v + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.range Y, B :=
      Finset.sum_le_sum (fun v _ => hu (v + 1) (by omega))
    _ = _ := by simp







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MultiplicativeExtraction
namespace OAI

/-! Extracting a fixed divisor from two ordinary multiplicative functions.
The failure of coprimality is counted explicitly, including its finite
interval boundary term. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma multiplicativeExtractionGap_eq_zero {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (u d n : ℕ) (hu : 0 < u) (hn : 0 < n)
    (hcop : u.Coprime (n * (n + d))) :
    multiplicativeExtractionGap f g u d n = 0 := by
  obtain ⟨h₁, h₂⟩ := Nat.coprime_mul_iff_right.mp hcop
  unfold multiplicativeExtractionGap
  rw [hfm u n hu hn h₁, hgm u (n + d) hu (by omega) h₂]
  ring

lemma norm_multiplicativeExtractionGap_le {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d n : ℕ) (hu : 0 < u) (hn : 0 < n) :
    ‖multiplicativeExtractionGap f g u d n‖ ≤
      2 * (if ¬u.Coprime (n * (n + d)) then (1 : ℝ) else 0) := by
  by_cases hcop : u.Coprime (n * (n + d))
  · rw [multiplicativeExtractionGap_eq_zero hfm hgm u d n hu hn hcop]
    simp [hcop]
  · simp only [hcop, not_false_eq_true, ite_true, mul_one]
    have hn' : 0 < n + d := by omega
    have h₁ : ‖f (u * n) * g (u * (n + d))‖ ≤ 1 := by
      rw [norm_mul]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (hf _ (Nat.mul_pos hu hn))
          (hg _ (Nat.mul_pos hu hn')) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h₂ : ‖f u * g u * f n * g (n + d)‖ ≤ 1 := by
      simp only [norm_mul]
      calc
        _ ≤ ((1 : ℝ) * 1) * 1 * 1 := by gcongr <;> first | exact hf _ hu | exact hg _ hu | exact hf _ hn | exact hg _ hn'
        _ = _ := by norm_num
    exact (norm_sub_le _ _).trans (by linarith)

theorem multiplicativeExtraction_sum_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d Y : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    ‖positivePrefix (multiplicativeExtractionGap f g u d) Y‖ ≤
      4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card := by
  have hb : ‖positivePrefix (multiplicativeExtractionGap f g u d) Y‖ ≤
      2 * (coprimeExceptionCount u d Y : ℝ) := by
    unfold positivePrefix
    calc
      _ ≤ ∑ v ∈ range Y, ‖multiplicativeExtractionGap f g u d (v + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ range Y,
          2 * (if ¬u.Coprime ((v + 1) * (v + 1 + d)) then (1 : ℝ) else 0) := by
        apply sum_le_sum
        intro v _
        exact norm_multiplicativeExtractionGap_le hfm hgm hf hg u d (v + 1) hu (by omega)
      _ = _ := by simp [coprimeExceptionCount, mul_sum]
  have hc := coprimeExceptionCount_bound u d Y P hP hcover
  nlinarith only [hb, hc]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NearbyCutoffs
namespace OAI

/-! A bounded positive-prefix mean changes little when the real cutoff
is moved within one logarithmic bin. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma positivePrefix_sub_norm_le (f : ℕ → ℂ) (hf : OneBounded f)
    (N M : ℕ) (hNM : N ≤ M) :
    ‖positivePrefix f M - positivePrefix f N‖ ≤ (M - N : ℕ) := by
  have he : positivePrefix f M = positivePrefix f N +
      positivePrefix (fun n => f (N + n)) (M - N) := by
    unfold positivePrefix
    have hs := sum_range_add (fun n => f (n + 1)) N (M - N)
    rw [Nat.add_sub_of_le hNM] at hs
    simpa only [Nat.add_assoc] using hs
  rw [he, add_sub_cancel_left]
  simpa only [mul_one] using norm_positivePrefix_le (fun n => f (N + n)) (M - N) 1
    (fun n hn => hf _ (by omega))

lemma real_prefix_nearby (f : ℕ → ℂ) (hf : OneBounded f) (X Y : ℝ)
    (hY : 0 < Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * (X - Y) / X + 1 / X := by
  have hX : 0 < X := hY.trans_le hYX
  have hNM : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_mono hYX
  have hN : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le hY.le
  have hM : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX.le
  have hlow := Nat.lt_floor_add_one Y
  have hdiff : ((⌊X⌋₊ - ⌊Y⌋₊ : ℕ) : ℝ) ≤ X - Y + 1 := by
    rw [Nat.cast_sub hNM]
    linarith
  have hnormN : ‖positivePrefix f ⌊Y⌋₊‖ ≤ (⌊Y⌋₊ : ℝ) := by
    simpa only [mul_one] using norm_positivePrefix_le f ⌊Y⌋₊ 1 hf
  have hnorm : ‖positivePrefix f ⌊Y⌋₊‖ ≤ Y := hnormN.trans hN
  have hinv : 0 ≤ 1 / Y - 1 / X := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hY hYX)
  have he : positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ) =
      positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ)) -
        (positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖positivePrefix f ⌊Y⌋₊ * (((1 / Y - 1 / X : ℝ) : ℂ))‖ +
        ‖(positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊) / (X : ℂ)‖ := norm_sub_le _ _
    _ = ‖positivePrefix f ⌊Y⌋₊‖ * (1 / Y - 1 / X) +
        ‖positivePrefix f ⌊X⌋₊ - positivePrefix f ⌊Y⌋₊‖ / X := by
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hinv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    _ ≤ Y * (1 / Y - 1 / X) + (X - Y + 1) / X := by
      exact add_le_add (mul_le_mul_of_nonneg_right hnorm hinv)
        (div_le_div_of_nonneg_right
          ((positivePrefix_sub_norm_le f hf _ _ hNM).trans hdiff) hX.le)
    _ = _ := by field_simp; ring

lemma real_prefix_log_bin (f : ℕ → ℂ) (hf : OneBounded f) (X Y η : ℝ)
    (hX : 0 < X) (_hη : 0 ≤ η) (hYlow : X * Real.exp (-η) ≤ Y) (hYX : Y ≤ X) :
    ‖positivePrefix f ⌊Y⌋₊ / (Y : ℂ) - positivePrefix f ⌊X⌋₊ / (X : ℂ)‖ ≤
      2 * η + 1 / X := by
  have hY : 0 < Y := (mul_pos hX (Real.exp_pos _)).trans_le hYlow
  apply (real_prefix_nearby f hf X Y hY hYX).trans
  have hexp : 1 - η ≤ Real.exp (-η) := by
    have he := Real.add_one_le_exp (-η)
    linarith
  have hy : X - Y ≤ X * η := by nlinarith
  have hd : (X - Y) / X ≤ η := (div_le_iff₀ hX).mpr (by nlinarith)
  calc
    _ = 2 * ((X - Y) / X) + 1 / X := by ring
    _ ≤ _ := by linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
namespace OAI

/-! The literal scale choice of the manuscript satisfies all prime-supply
mass and support hypotheses; no prime-family existence premise remains. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



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










@[simp] theorem dilationComponent_one (a : ℕ) (f : ℕ → ℂ) (E : Finset ℕ) :
    dilationComponent a f E 1 = 1 := by
  simp [dilationComponent, localComponent]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectMajorant
namespace OAI

/-! The elementary p²-periodic majorant from the qualitative analytic
transfer. Prime powers of exponent at least two are left unrestricted. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma primeDefectLocal_nonneg (f : ℕ → ℂ) (p n : ℕ) : 0 ≤ primeDefectLocal f p n := by
  unfold primeDefectLocal
  split_ifs <;> positivity

lemma primeDefectLocal_le_one {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) (n : ℕ) : primeDefectLocal f p n ≤ 1 := by
  unfold primeDefectLocal
  split_ifs
  · exact hf p hp.pos
  · exact le_rfl



lemma prime_valuation_one_iff {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (p ∣ n ∧ ¬p ^ 2 ∣ n) ↔ n.factorization p = 1 := by
  rw [hp.dvd_iff_one_le_factorization hn.ne', hp.pow_dvd_iff_le_factorization hn.ne']
  omega

lemma norm_le_primeDefectMajorant {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf1 : f 1 = 1) (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (hn : 0 < n) :
    ‖f n‖ ≤ primeDefectMajorant f P n := by
  have he : f n = (∏ p ∈ P, f (p ^ n.factorization p)) *
      ∏ p ∈ n.primeFactors \ P, f (p ^ n.factorization p) := by
    rw [← fromPrimePowers_reconstruct f hfm hf1 hn]
    exact fromPrimePowers_split _ P (by intro p; simp [hf1]) n
  have hout : (∏ p ∈ n.primeFactors \ P, ‖f (p ^ n.factorization p)‖) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
    exact hf _ (pow_pos hprime.pos _)
  rw [he, norm_mul, norm_prod, norm_prod]
  calc
    _ ≤ (∏ p ∈ P, ‖f (p ^ n.factorization p)‖) * 1 :=
      mul_le_mul_of_nonneg_left hout (prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ∏ p ∈ P, ‖f (p ^ n.factorization p)‖ := mul_one _
    _ ≤ primeDefectMajorant f P n := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      unfold primeDefectLocal
      split_ifs with hv
      · rw [(prime_valuation_one_iff (hP p hp) hn).mp hv, pow_one]
      · exact hf _ (pow_pos (hP p hp).pos _)

lemma primeDefectLocal_formula (f : ℕ → ℂ) (p n : ℕ) :
    primeDefectLocal f p n = 1 - (1 - ‖f p‖) *
      ((if p ∣ n then (1 : ℝ) else 0) - (if p ^ 2 ∣ n then (1 : ℝ) else 0)) := by
  have hp : p ∣ p ^ 2 := by simp [pow_two]
  by_cases hpn : p ∣ n
  · by_cases hp2n : p ^ 2 ∣ n <;> simp [primeDefectLocal, hpn, hp2n]
  · have hp2n : ¬p ^ 2 ∣ n := fun hh => hpn (hp.trans hh)
    simp [primeDefectLocal, hpn, hp2n]

lemma primeDefectLocal_mod (f : ℕ → ℂ) (p n : ℕ) :
    primeDefectLocal f p (n % p ^ 2) = primeDefectLocal f p n := by
  unfold primeDefectLocal
  have hp : p ∣ p ^ 2 := by simp [pow_two]
  simp only [Nat.dvd_mod_iff hp, Nat.dvd_mod_iff (dvd_refl (p ^ 2))]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectMean
namespace OAI

/-! Exact one-prime p² averages of the elementary modulus majorant. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sum_zero_multiples_of_dvd (a N : ℕ) (haN : a ∣ N) :
    (∑ v ∈ range N, if a ∣ v then (1 : ℝ) else 0) = (N / a : ℕ) := by
  let F : ℕ → ℝ := fun v => if a ∣ v then 1 else 0
  have hpos : (∑ v ∈ range N, F (v + 1)) = (N / a : ℕ) := by
    have hh := congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_multiples N a)
    simpa only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hh
  have h1 := sum_range_succ F N
  have h2 := sum_range_succ' F N
  have hF0 : F 0 = 1 := by simp [F]
  have hFN : F N = 1 := by simp [F, haN]
  change (∑ v ∈ range N, F v) = _
  linarith

lemma primeDefectLocal_sum (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ range (p ^ 2), primeDefectLocal f p n) =
      (p : ℝ) ^ 2 - (1 - ‖f p‖) * ((p : ℝ) - 1) := by
  simp_rw [primeDefectLocal_formula]
  rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib,
    sum_zero_multiples_of_dvd p (p ^ 2) (by simp [pow_two]),
    sum_zero_multiples_of_dvd (p ^ 2) (p ^ 2) (dvd_refl _)]
  have hpp : p ^ 2 / p = p := by rw [pow_two, Nat.mul_div_cancel_left _ hp.pos]
  rw [hpp, Nat.div_self (pow_pos hp.pos 2)]
  simp

lemma primeDefectLocal_average (f : ℕ → ℂ) {p : ℕ} [NeZero (p ^ 2)] (hp : p.Prime) :
    uniformAverage (fun r : ZMod (p ^ 2) => primeDefectLocal f p r.val) =
      1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  let e : Fin (p ^ 2) ≃ ZMod (p ^ 2) :=
    { toFun := fun i => (i.val : ZMod (p ^ 2))
      invFun := fun r => ⟨r.val, r.val_lt⟩
      left_inv := fun i => Fin.ext (ZMod.val_natCast_of_lt i.isLt)
      right_inv := fun r => ZMod.natCast_zmod_val r }
  have hsum : (∑ r : ZMod (p ^ 2), primeDefectLocal f p r.val) =
      ∑ n ∈ range (p ^ 2), primeDefectLocal f p n := by
    rw [← e.sum_comp (fun r => primeDefectLocal f p r.val)]
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    exact congrArg (primeDefectLocal f p) (ZMod.val_natCast_of_lt i.isLt)
  unfold uniformAverage
  rw [hsum, ZMod.card, primeDefectLocal_sum f hp, Nat.cast_pow]
  field_simp [hp0]

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




@[simp] lemma naturalCharacter_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    naturalCharacter χ 1 = 1 := by simp [naturalCharacter]














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortSumSampling
namespace OAI

/-!
# Sampling the published short-interval estimate

For integral short lengths, a moving short sum is constant on each unit
cell of its origin. Thus its published integral controls the actual finite
sum of integer origins, with outer cutoff `Y+1`. The progression restriction
is an average of fixed frequencies and has total coefficient mass one.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical






lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NonrawPrefix
namespace OAI

/-! Exact finite-prefix assembly of the nonraw expansion at the retained
divisor scale. No endpoint terms are discarded. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma positivePrefix_const_mul (c : ℂ) (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => c * F n) X = c * positivePrefix F X := by
  simp only [positivePrefix, mul_sum]


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


lemma paddingBinIndices_card (L η : ℝ) (hL : 0 ≤ L) (hη : 0 < η) :
    ((paddingBinIndices L η).card : ℝ) ≤ 100 * L / η + 1 := by
  have hf : 0 ≤ ⌊100 * L / η⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc : ((paddingBinIndices L η).card : ℝ) = (⌊100 * L / η⌋ : ℝ) + 1 := by
    have hh := Int.card_Icc_of_le 0 ⌊100 * L / η⌋
      (show (0 : ℤ) ≤ ⌊100 * L / η⌋ + 1 by omega)
    simp only [sub_zero] at hh
    change ((Icc (0 : ℤ) ⌊100 * L / η⌋).card : ℝ) = _
    exact_mod_cast hh
  rw [hc]
  linarith [Int.floor_le (100 * L / η)]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal
namespace OAI

/-! The actual finite harmonic mass in the manuscript's half-open bins.
Its lower bound follows from the proved reciprocal padding law and its
upper bound simply removes the two restrictions. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical



lemma padding_bin_weight_sum (L η : ℝ) (d q : ℕ) (hη : 0 < η) :
    (∑ j ∈ paddingBinIndices L η,
      if (q.primeFactors.card : ℝ) ≤ 100 * Real.log L ∧
          (j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
          Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η
      then (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0) =
      if PaddingPairEligible L η d q then
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) else 0 := by
  have hi (j : ℤ) :
      ((j : ℝ) * η ≤ Real.log (d * q : ℕ) ∧
        Real.log (d * q : ℕ) < ((j : ℝ) + 1) * η) ↔
        paddingBin η 0 (Real.log (d * q : ℕ)) = j := by
    simpa only [add_zero] using
      (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).symm
  simp only [hi, PaddingPairEligible]
  by_cases hc : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L
  · simp [hc]
  · simp [hc]

lemma totalPaddingBinMass_eq (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    totalPaddingBinMass D Q L η = ∑ d ∈ D, paddingPairHarmonicMass Q L η d := by
  unfold totalPaddingBinMass paddingPairHarmonicMass
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  exact padding_bin_weight_sum L η d q hη





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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount
namespace OAI

/-! Bounds for the actual finite bin set at eta = exp(-J). -/

namespace TwoPointCorrelations

open _root_.Filter

lemma paddingBinIndices_card_linear (L η : ℝ) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1) :
    ((paddingBinIndices L η).card : ℝ) ≤ 101 * L / η := by
  have hb := paddingBinIndices_card L η (by linarith) hη
  have hratio : 1 ≤ L / η := (one_le_div hη).mpr (by linarith)
  have he : 101 * L / η = 100 * L / η + L / η := by ring
  rw [he]
  linarith

lemma paddingBinIndices_card_polynomial (L W : ℝ) (hL : 101 ≤ L) (hW : 1 ≤ W) :
    ((paddingBinIndices L (Real.exp (-(primeSupplyCount W L : ℝ)))).card : ℝ) ≤
      Real.exp (3 * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hJ := primeSupplyCount_le_log W L hW hLone
  have he : Real.exp (primeSupplyCount W L) ≤ L := by
    simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJ
  have hη : Real.exp (-(primeSupplyCount W L : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hb := paddingBinIndices_card_linear L (Real.exp (-(primeSupplyCount W L : ℝ)))
    hLone (Real.exp_pos _) hη
  calc
    _ ≤ 101 * L / Real.exp (-(primeSupplyCount W L : ℝ)) := hb
    _ = 101 * L * Real.exp (primeSupplyCount W L) := by rw [Real.exp_neg]; field_simp
    _ ≤ 101 * L * L := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ L ^ 3 := by
      have hx := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
      nlinarith
    _ = _ := by
      rw [show 3 * Real.log L = (3 : ℕ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hLp]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeParameterChoice
namespace OAI

/-! The manuscript's final exponential savings at eta = exp(-J),
K = exp(4J), and a fixed sufficiently large W. -/

namespace TwoPointCorrelations

lemma two_pow_eq_exp (J : ℕ) : (2 : ℝ) ^ J = Real.exp ((J : ℝ) * Real.log 2) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

lemma quantitative_small_terms (L W : ℝ) (J : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hJ : 60 * (J : ℝ) ≤ Real.log L) :
    Real.exp J * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ)) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * L ^ (-100 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-2 * W * J) ≤ Real.exp (-(J : ℝ)) := by
  have hLp : 0 < L := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogtwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have htwo : (J : ℝ) * Real.log 2 ≤ J := by nlinarith
  have hWJ : (J : ℝ) ≤ W * J := by nlinarith
  rw [two_pow_eq_exp]
  simp only [Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Real.exp_le_exp.mpr <;> nlinarith

lemma quantitative_spectral_term (C W : ℝ) (J : ℕ) (hC : 0 ≤ C) (hW : 0 < W)
    (hchoice : Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1)) :
    Real.exp (5 * (J : ℝ)) * (C / Real.sqrt W) ^ J ≤ Real.exp (-(J : ℝ)) := by
  have he : Real.exp (5 * (J : ℝ)) = (Real.exp 5) ^ J := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [he, ← mul_pow]
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (by positivity)) hchoice J
  calc
    _ ≤ (Real.exp (-1)) ^ J := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma primeSupplyCount_final_budget (L W : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W) :
    60 * (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hj := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ0 : (0 : ℝ) ≤ primeSupplyCount W L := Nat.cast_nonneg _
  nlinarith

lemma primeSupplyCount_saving (L W : ℝ) (hL : 1 ≤ L) (_hW : 0 < W) :
    Real.exp (-(primeSupplyCount W L : ℝ)) ≤
      Real.exp 1 * L ^ (-(1 / (1200 * W)) : ℝ) := by
  have hLp : 0 < L := by linarith
  have hf := Nat.lt_floor_add_one (((1 / 200 : ℝ) * Real.log L) / (6 * W))
  have he : ((1 / 200 : ℝ) * Real.log L) / (6 * W) = Real.log L / (1200 * W) := by ring
  change ((1 / 200 : ℝ) * Real.log L) / (6 * W) < (primeSupplyCount W L : ℝ) + 1 at hf
  rw [he] at hf
  rw [Real.rpow_def_of_pos hLp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hz : Real.log L * (-(1 / (1200 * W))) = -(Real.log L / (1200 * W)) := by ring
  rw [hz]
  linarith

lemma exists_fixed_spectral_parameter (C : ℝ) (hC : 0 ≤ C) :
    ∃ W : ℝ, 10 ≤ W ∧ Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1) := by
  let a := Real.exp 6 * C + 4
  have ha : 4 ≤ a := by
    have hp := mul_nonneg (Real.exp_pos (6 : ℝ)).le hC
    dsimp only [a]
    linarith
  have hap : 0 < a := by linarith
  refine ⟨a ^ 2, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hap.le, ← mul_div_assoc]
  apply (div_le_iff₀ hap).mpr
  have he : Real.exp (-1) * Real.exp 6 = Real.exp 5 := by
    rw [← Real.exp_add]
    norm_num
  dsimp [a]
  rw [mul_add, ← mul_assoc, he]
  linarith [Real.exp_pos (-1)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FinalErrorScale
namespace OAI

/-! The residual rare-site and summed block-boundary errors are below
the same exp(-J) saving as the principal terms. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_rare_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, Real.exp (-L ^ (9 / 10 : ℝ)) ≤
      Real.exp (-(primeSupplyCount W L : ℝ)) := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 9 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hs] with L hL hs
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith : 0 < L) _), one_mul] at hs
  apply Real.exp_le_exp.mpr
  have hj := primeSupplyCount_le_log W L hW hL
  linarith

lemma eventually_bin_error_saving (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      (L / Real.exp (-(primeSupplyCount W L : ℝ))) * Real.exp (-L) ≤
        Real.exp (-(primeSupplyCount W L : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_sublinear_log_cost 0 3 (by norm_num) (by norm_num)] with L hL hs
  simp only [Real.rpow_zero, mul_one] at hs
  have hLp : 0 < L := by linarith
  have hj := primeSupplyCount_le_log W L hW hL
  have he : L / Real.exp (-(primeSupplyCount W L : ℝ)) =
      Real.exp (Real.log L + (primeSupplyCount W L : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hLp, Real.exp_neg, div_inv_eq_mul]
  rw [he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PartialCenteringSum
namespace OAI

/-! Exact finite summation of partial-centering errors. Each removed
supply subset costs its retained reciprocal mass, never its number of primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_sum_finite {α : Type*} (S : Finset α) (F : α → ℕ → ℂ) (X : ℕ) :
    positivePrefix (fun n => ∑ a ∈ S, F a n) X =
      ∑ a ∈ S, positivePrefix (F a) X := by
  unfold positivePrefix
  exact sum_comm




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftTransfer
namespace OAI

/-!
# Transfer from a positive gap to two arbitrary shifts

Cancellation for a positive gap gives cancellation for any two
distinct nonnegative shifts.
-/

open _root_.Filter

namespace TwoPointCorrelations


lemma residuePrefix_one (u : ℕ → ℂ) (b N : ℕ) :
    residuePrefix u 1 b N = ∑ n ∈ Finset.Icc 1 N, u n := by
  have hs : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [residuePrefix, hs, Nat.mod_one, ite_true]

theorem correlation_shift_zero (f g : ℕ → ℂ) (h b : ℕ)
    (hzero : Tendsto (fun N : ℕ => correlationSum f g 0 h N / (N : ℂ))
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => correlationSum f g b (b + h) N / (N : ℂ))
      atTop (nhds 0) := by
  have hp : Tendsto (fun N : ℕ =>
      residuePrefix (fun n => f n * g (n + h)) 1 b N / (N : ℂ)) atTop (nhds 0) := by
    simpa only [residuePrefix_one, correlationSum, Nat.add_zero] using hzero
  have ht := affine_mean_tendsto_zero (fun n => f n * g (n + h)) 1 b (by decide) hp
  simpa only [correlationSum, one_mul, Nat.add_assoc] using ht

theorem UnshiftedCorrectedElliott.binary (hcore : UnshiftedCorrectedElliott) :
    BinaryCorrectedElliott := by
  intro f g hf hg hfb hgb hnp h₁ h₂ hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := correlation_shift_zero f g (h₂ - h₁) h₁
      (hcore f g hf hg hfb hgb hnp _ (Nat.sub_pos_of_lt hlt))
    simpa only [Nat.add_sub_of_le hlt.le] using h
  · have h := correlation_shift_zero g f (h₁ - h₂) h₂
      (hcore g f hg hf hgb hfb hnp.symm _ (Nat.sub_pos_of_lt hgt))
    simpa only [Nat.add_sub_of_le hgt.le, correlationSum, mul_comm] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveNormalization
namespace OAI

/-! Setting the unused value at zero to zero permits globally bounded graph
test vectors without changing any of the theorem's positive correlations. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma positiveNormalization_eq {f : ℕ → ℂ} {n : ℕ} (hn : 0 < n) :
    positiveNormalization f n = f n := by
  simp only [positiveNormalization, ne_of_gt hn, ite_false]

lemma positiveNormalization_norm {f : ℕ → ℂ} (hf : OneBounded f) (n : ℕ) :
    ‖positiveNormalization f n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [positiveNormalization, hn]
  · rw [positiveNormalization_eq (Nat.pos_of_ne_zero hn)]
    exact hf n (Nat.pos_of_ne_zero hn)

lemma Multiplicative.positiveNormalization {f : ℕ → ℂ} (hf : Multiplicative f) :
    Multiplicative (positiveNormalization f) := by
  intro m n hm hn hcop
  rw [positiveNormalization_eq (Nat.mul_pos hm hn), positiveNormalization_eq hm,
    positiveNormalization_eq hn]
  exact hf m n hm hn hcop

lemma UniformlyNonpretentious.positiveNormalization {f : ℕ → ℂ}
    (hnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    UniformlyNonpretentious (positiveNormalization f) := by
  apply hnp.finite_prime_change ∅ hf (fun n _ => positiveNormalization_norm hf n)
  intro p hp _
  exact positiveNormalization_eq hp.pos

lemma positiveNormalization_prefix (f g : ℕ → ℂ) (h N : ℕ) :
    positivePrefix (fun n => positiveNormalization f n * positiveNormalization g (n + h)) N =
      positivePrefix (fun n => f n * g (n + h)) N := by
  unfold positivePrefix
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [positiveNormalization_eq (by omega), positiveNormalization_eq (by omega)]

lemma correlationSum_eq_positivePrefix (f g : ℕ → ℂ) (h N : ℕ) :
    correlationSum f g 0 h N = positivePrefix (fun n => f n * g (n + h)) N := by
  unfold correlationSum positivePrefix
  simp only [Nat.add_zero]
  rw [← Ico_add_one_right_eq_Icc, ← zero_add 1,
    ← sum_Ico_add' (fun n => f n * g (n + h)) 0 N 1, range_eq_Ico]

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





















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BinCutoffGeometry
namespace OAI

/-! The literal logarithmic bin places T/(dq) between X exp(-eta)
and X. Floor normalization introduces a scalar of norm at most one. -/

namespace TwoPointCorrelations

lemma actualPaddingBin_cutoff (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (η X : ℝ) (hX : 0 < X) (j : ℤ)
    (hb : actualPaddingBin η (Real.log d) j q) :
    X * Real.exp (-η) ≤ (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ∧
      (X * Real.exp ((j : ℝ) * η)) / (d * q : ℕ) ≤ X := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hu : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']
    ring
  have hl : Real.exp ((j : ℝ) * η) ≤ (d * q : ℕ) := by
    calc
      _ ≤ Real.exp (Real.log (d * q : ℕ)) := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.1)
      _ = _ := Real.exp_log hu
  have hh : (d * q : ℕ) ≤ Real.exp (((j : ℝ) + 1) * η) := by
    calc
      _ = Real.exp (Real.log (d * q : ℕ)) := (Real.exp_log hu).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [hlog]; exact hb.2.le)
  constructor
  · apply (le_div_iff₀ hu).mpr
    have he : Real.exp (-η) * Real.exp (((j : ℝ) + 1) * η) =
        Real.exp ((j : ℝ) * η) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ (X * Real.exp (-η)) * Real.exp (((j : ℝ) + 1) * η) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by rw [mul_assoc, he]
  · apply (div_le_iff₀ hu).mpr
    exact mul_le_mul_of_nonneg_left hl hX.le

lemma floor_cutoff_weight_norm_le (T : ℝ) (hT : 0 < T) :
    ‖(⌊T⌋₊ : ℂ) / (T : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact (div_le_one hT).mpr (Nat.floor_le hT.le)

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





namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)





end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisorEndpointSymmetry
namespace OAI

/-! Positive tuple/padding edge weights are unchanged when the origin
is moved to the other endpoint. Both signs of the shift are included. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma positivePrimeWeight_add_multiple (d : ℕ) (n c : ℤ) :
    positivePrimeWeight d.primeFactors (n + (d : ℤ) * c) =
      positivePrimeWeight d.primeFactors n := by
  unfold positivePrimeWeight
  apply prod_congr rfl
  intro p hp
  have hpd : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
  have hc : (p : ℤ) ∣ (d : ℤ) * c := dvd_mul_of_dvd_left hpd c
  have he : (p : ℤ) ∣ n + (d : ℤ) * c ↔ (p : ℤ) ∣ n := by
    constructor
    · intro hn
      simpa only [add_sub_cancel_right] using dvd_sub hn hc
    · intro hn
      exact dvd_add hn hc
  simp only [he]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalCenteringBins
namespace OAI

/-! Sum the actual partial-centering errors over the logarithmic bins.
The interval exponent remains the absolute value 1000. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma bin_cutoff_ge (L η X : ℝ) (hη : 0 < η) (hX : 0 ≤ X)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    X ≤ X * Real.exp ((j : ℝ) * η) := by
  have hj0 : (0 : ℝ) ≤ j := by
    exact_mod_cast ((mem_paddingBinIndices_iff L η j hη).mp hj).1
  have he : 1 ≤ Real.exp ((j : ℝ) * η) := Real.one_le_exp (mul_nonneg hj0 hη.le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hX



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFinalWindows
namespace OAI

/-! The final logarithmic bins meet both the analytic and spectral
long-window hypotheses, uniformly in the absolute exponent A. -/

namespace TwoPointCorrelations

open _root_.Filter


lemma floor_exp_half_bound (Y T : ℝ) (hY : 2 ≤ Y) (hT : Real.exp Y ≤ T) :
    Real.exp (Y / 2) ≤ (⌊T⌋₊ : ℝ) := by
  let E := Real.exp (Y / 2)
  have hE : 2 ≤ E := by
    have he := Real.add_one_le_exp (Y / 2)
    dsimp only [E]
    linarith
  have hsq : E * E ≤ T := by
    calc
      _ = Real.exp Y := by
        dsimp only [E]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ T := hT
  have hf := Nat.lt_floor_add_one T
  change E ≤ _
  nlinarith

lemma final_bin_windows (L X η : ℝ) (A : ℕ) (hL : 2 ≤ L)
    (hA : 1000 ≤ A) (hX : Real.exp (L ^ A) ≤ X) (hη : 0 < η)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    Real.exp (L ^ (1000 : ℝ)) ≤ X ∧
      Real.exp (L ^ A / 2) ≤ (⌊X * Real.exp ((j : ℝ) * η)⌋₊ : ℝ) := by
  have hLone : 1 ≤ L := by linarith
  have hAp : A ≠ 0 := by omega
  have hpow : L ^ (1000 : ℝ) ≤ L ^ A := by
    rw [Real.rpow_ofNat]
    exact pow_le_pow_right₀ hLone hA
  have hY : 2 ≤ L ^ A := hL.trans (le_self_pow₀ hLone hAp)
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  exact ⟨(Real.exp_le_exp.mpr hpow).trans hX,
    floor_exp_half_bound _ _ hY
      (hX.trans (bin_cutoff_ge L η X hη hXp.le j hj))⟩




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SourceDeletionTerms
namespace OAI

/-! The three source deletions at the actual, possibly bin-dependent,
integer sampling sites. Extra pair eligibility is retained in the rare
term and may be discarded in the two nonnegative numerical terms. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma uniformAverage_finset_sum {α ι : Type*} [Fintype α]
    (S : Finset ι) (f : ι → α → ℝ) :
    uniformAverage (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, uniformAverage (f i) := by
  unfold uniformAverage
  rw [sum_comm, sum_div]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingIntegerBounds
namespace OAI

/-! Truncated padding weights on actual integer intervals.  The finite
active-state comparison is used only after the degree restriction. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma uniformAverage_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (f : (i : ι) → β i → ℝ) :
    uniformAverage (fun x : ∀ i, β i => ∏ i, f i (x i)) =
      ∏ i, uniformAverage (f i) := by
  simp only [uniformAverage, Fintype.card_pi, Nat.cast_prod]
  rw [← Fintype.prod_sum, prod_div_distrib]









lemma paddingTiltNormalizer_one_le (Q : Finset ℕ) : 1 ≤ paddingTiltNormalizer Q := by
  calc
    1 = ∏ _p : Q, (1 : ℝ) := by simp
    _ ≤ paddingTiltNormalizer Q := by
      apply Finset.prod_le_prod
      · intro p _
        exact zero_le_one
      · intro p _
        exact le_add_of_nonneg_right (by positivity)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectCRT
namespace OAI

/-! The ordinary mean of the finite prime-defect majorant is computed by
CRT modulo the squared primes. Only the finite interval boundary remains. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma uniformAverage_pi_product_crt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] (F : ∀ i, β i → ℝ) :
    uniformAverage (fun r : ∀ i, β i => ∏ i, F i (r i)) =
      ∏ i, uniformAverage (F i) := by
  unfold uniformAverage
  rw [Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum, prod_div_distrib]

lemma primeDefectMajorant_crt_bound {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf1 : f 1 = 1) (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) ≤
      (∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) +
        (∏ p ∈ P, (p : ℝ) ^ 2) / N := by
  let s : P → ℕ := fun p => p.val ^ 2
  let : ∀ p : P, NeZero (s p) := fun p => ⟨pow_ne_zero _ (hP p.val p.property).ne_zero⟩
  let F : (∀ p : P, ZMod (s p)) → ℝ := fun r =>
    ∏ p : P, primeDefectLocal f p.val (r p).val
  have hcop : Pairwise (fun p q : P => (s p).Coprime (s q)) := by
    intro p q hpq
    have hp : p.val.Coprime q.val := (Nat.coprime_primes
      (hP p.val p.property) (hP q.val q.property)).mpr (by
        intro h
        exact hpq (Subtype.ext h))
    exact (hp.pow_left 2).pow_right 2
  have hF : ∀ r, |F r| ≤ 1 := by
    intro r
    have hn : 0 ≤ F r := prod_nonneg (fun p _ => primeDefectLocal_nonneg f _ _)
    rw [abs_of_nonneg hn]
    exact Finset.prod_le_one (fun p _ => primeDefectLocal_nonneg f _ _)
      (fun p _ => primeDefectLocal_le_one hf (hP p.val p.property) _)
  have hmodel : uniformAverage F =
      ∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)) := by
    change uniformAverage (fun r : ∀ p : P, ZMod (s p) =>
      ∏ p : P, primeDefectLocal f p.val (r p).val) = _
    rw [uniformAverage_pi_product_crt (fun p : P => ZMod (s p))
      (fun p r => primeDefectLocal f p.val r.val)]
    calc
      _ = ∏ p : P, (1 - (1 - ‖f p.val‖) *
          (1 / (p.val : ℝ) - 1 / (p.val : ℝ) ^ 2)) := by
        apply prod_congr rfl
        intro p _
        exact primeDefectLocal_average f (hP p.val p.property)
      _ = _ := prod_coe_sort P (fun p : ℕ =>
        1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))
  have hpoint (n : ℕ) :
      F (ZMod.prodEquivPi s hcop (n : ZMod (∏ p : P, s p))) =
        primeDefectMajorant f P n := by
    have he : ZMod.prodEquivPi s hcop (n : ZMod (∏ p : P, s p)) =
        fun p => (n : ZMod (s p)) := by
      funext p
      simp only [ZMod.prodEquivPi_apply]
      exact ZMod.cast_natCast (dvd_prod_of_mem s (mem_univ p)) n
    rw [he]
    change (∏ p : P, primeDefectLocal f p.val (n : ZMod (s p)).val) = _
    simp only [ZMod.val_natCast, s, primeDefectLocal_mod]
    exact prod_coe_sort P (fun p => primeDefectLocal f p n)
  have he := crt_observable_difference s hcop (1 : ZMod (∏ p : P, s p)) N hN F hF
  have hreal : uniformAverage (fun j : Fin N =>
      F (ZMod.prodEquivPi s hcop (1 + (j.val : ZMod (∏ p : P, s p))))) =
      (∑ n ∈ range N, primeDefectMajorant f P (n + 1)) / (N : ℝ) := by
    unfold uniformAverage
    rw [Fintype.card_fin, ← Fin.sum_univ_eq_sum_range]
    congr 1
    apply sum_congr rfl
    intro j _
    change F (ZMod.prodEquivPi s hcop (1 + (j.val : ZMod (∏ p : P, s p)))) = _
    rw [show (1 : ZMod (∏ p : P, s p)) + (j.val : ZMod (∏ p : P, s p)) =
      ((j.val + 1 : ℕ) : ZMod (∏ p : P, s p)) by push_cast; ring, hpoint]
  rw [hreal, hmodel] at he
  have hprod : ((∏ p : P, s p : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) ^ 2 := by
    simp only [Nat.cast_prod, s, Nat.cast_pow]
    exact prod_coe_sort P (fun p : ℕ => (p : ℝ) ^ 2)
  rw [hprod] at he
  apply (div_le_div_of_nonneg_right
    (sum_le_sum (fun n _ => norm_le_primeDefectMajorant hfm hf1 hf P hP (n + 1) (by omega)))
    (Nat.cast_nonneg N)).trans
  have hb := le_trans (le_abs_self _) he
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeModulusDefect
namespace OAI

/-! The exact modulus-defect series used in the qualitative reduction. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma primeModulusDefect_nonneg {f : ℕ → ℂ} (hf : OneBounded f) (p : ℕ) :
    0 ≤ primeModulusDefect f p := by
  unfold primeModulusDefect
  split_ifs with hp
  · exact div_nonneg (sub_nonneg.mpr (hf p hp.pos)) (Nat.cast_nonneg p)
  · exact le_rfl

lemma prime_square_density_lower {p : ℕ} (hp : p.Prime) :
    (1 / (p : ℝ)) / 2 ≤ 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ = ((p : ℝ) / 2) / (p : ℝ) ^ 2 := by field_simp [hp0.ne']
    _ ≤ ((p : ℝ) - 1) / (p : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp [hp0.ne']

lemma prime_square_defect_factor_nonneg {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
  have hi : 1 / (p : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).mpr hp1
  have hc : 0 ≤ 1 - ‖f p‖ := sub_nonneg.mpr (hf p hp.pos)
  have hd : 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 ≤ 1 := by
    have hh : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    linarith
  have hb := mul_le_mul_of_nonneg_left hd hc
  have hn := norm_nonneg (f p)
  nlinarith

lemma prime_square_defect_factor_le_exp {f : ℕ → ℂ} (hf : OneBounded f)
    {p : ℕ} (hp : p.Prime) :
    1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) ≤
      Real.exp (-primeModulusDefect f p / 2) := by
  have hc : 0 ≤ 1 - ‖f p‖ := sub_nonneg.mpr (hf p hp.pos)
  have hd := mul_le_mul_of_nonneg_left (prime_square_density_lower hp) hc
  have hd' : primeModulusDefect f p / 2 ≤
      (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) := by
    simpa only [primeModulusDefect, if_pos hp, div_eq_mul_inv, one_mul,
      mul_assoc] using hd
  have he := Real.add_one_le_exp (-primeModulusDefect f p / 2)
  linarith

lemma prime_square_defect_product_le_exp {f : ℕ → ℂ} (hf : OneBounded f)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (1 - ‖f p‖) * (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) ≤
      Real.exp (-(∑ p ∈ P, primeModulusDefect f p) / 2) := by
  calc
    _ ≤ ∏ p ∈ P, Real.exp (-primeModulusDefect f p / 2) :=
      Finset.prod_le_prod (fun p hp => prime_square_defect_factor_nonneg hf (hP p hp))
        (fun p hp => prime_square_defect_factor_le_exp hf (hP p hp))
    _ = _ := by rw [← Real.exp_sum, ← sum_div, sum_neg_distrib]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectLimit
namespace OAI

/-! Divergent reciprocal prime-modulus defect forces vanishing ordinary
mean modulus, using only the finite p² CRT majorants. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

lemma Multiplicative.eq_zero_of_one_ne {f : ℕ → ℂ}
    (hf : Multiplicative f) (h1 : f 1 ≠ 1) (n : ℕ) (hn : 0 < n) : f n = 0 := by
  have he : f n = f 1 * f n := by
    simpa only [one_mul] using hf 1 n (by omega) hn (Nat.coprime_one_left n)
  have hm : (1 - f 1) * f n = 0 := by linear_combination he
  rcases mul_eq_zero.mp hm with h | h
  · exact False.elim (h1 (sub_eq_zero.mp h).symm)
  · exact h

lemma modulus_mean_nonneg (f : ℕ → ℂ) (N : ℕ) :
    0 ≤ (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) :=
  div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg N)

theorem mean_modulus_zero_of_not_summable_prime_defect {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf : OneBounded f)
    (hns : ¬Summable (primeModulusDefect f)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0) := by
  by_cases hf1 : f 1 = 1
  · have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (primeModulusDefect_nonneg hf)).mp hns
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨M, hM⟩ := (hsum.eventually
      (eventually_ge_atTop (-2 * Real.log (ε / 2)))).exists
    let P := (range M).filter Nat.Prime
    have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
    have hpsum : (∑ p ∈ P, primeModulusDefect f p) =
        ∑ p ∈ range M, primeModulusDefect f p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Prime <;> simp [primeModulusDefect, hp]
    have hprod : (∏ p ∈ P, (1 - (1 - ‖f p‖) *
        (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) ≤ ε / 2 := by
      apply (prime_square_defect_product_le_exp hf P hP).trans
      have hh : -(∑ p ∈ P, primeModulusDefect f p) / 2 ≤ Real.log (ε / 2) := by
        rw [hpsum]
        linarith
      exact (Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hε2)
    let Q := ∏ p ∈ P, (p : ℝ) ^ 2
    have htail : Tendsto (fun N : ℕ => Q / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat Q
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
      ((htail.eventually (gt_mem_nhds hε2)).and (eventually_ge_atTop 1))
    refine ⟨N₀, ?_⟩
    intro N hN
    obtain ⟨hsmall, hN1⟩ := hN₀ N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_mean_nonneg f N)]
    have hbound := primeDefectMajorant_crt_bound hfm hf1 hf P hP N (by omega)
    change _ ≤ _ + Q / N at hbound
    linarith
  · have he : (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ)) =
        fun _ => 0 := by
      funext N
      have hz : (∑ n ∈ range N, ‖f (n + 1)‖) = 0 := by
        apply sum_eq_zero
        intro n _
        rw [hfm.eq_zero_of_one_ne hf1 (n + 1) (by omega), norm_zero]
      rw [hz, zero_div]
    rw [he]
    exact tendsto_const_nhds

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectBias
namespace OAI

/-! Persistent ordinary two-point bias forces finite reciprocal prime-modulus
defect for both factors. This is an elementary consequence of the p² CRT
majorant, with no additional mean-value input. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Topology

lemma shifted_modulus_sum_le {g : ℕ → ℂ} (hg : OneBounded g) (N h : ℕ) :
    (∑ n ∈ range N, ‖g (n + 1 + h)‖) ≤
      (∑ n ∈ range N, ‖g (n + 1)‖) + h := by
  have hleft := sum_range_add (fun n => ‖g (n + 1)‖) h N
  have hright := sum_range_add (fun n => ‖g (n + 1)‖) N h
  have he : (∑ n ∈ range h, ‖g (n + 1)‖) +
      (∑ n ∈ range N, ‖g (n + 1 + h)‖) =
      (∑ n ∈ range N, ‖g (n + 1)‖) +
      (∑ n ∈ range h, ‖g (n + 1 + N)‖) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hleft.symm.trans
      ((congrArg (fun K => ∑ n ∈ range K, ‖g (n + 1)‖) (Nat.add_comm h N)).trans hright)
  have hn : 0 ≤ ∑ n ∈ range h, ‖g (n + 1)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have ht : (∑ n ∈ range h, ‖g (n + 1 + N)‖) ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ range h, (1 : ℝ) := sum_le_sum (fun n _ => hg _ (by omega))
      _ = _ := by simp
  linarith

lemma normalized_correlation_le_first_modulus {f g : ℕ → ℂ} (hg : OneBounded g)
    (h N : ℕ) :
    ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ ≤
      (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) := by
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hg _ (by omega)) (norm_nonneg _)).trans_eq (mul_one _)

lemma normalized_correlation_le_second_modulus {f g : ℕ → ℂ} (hf : OneBounded f)
    (hg : OneBounded g) (h N : ℕ) :
    ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ ≤
      (∑ n ∈ range N, ‖g (n + 1)‖) / (N : ℝ) + (h : ℝ) / N := by
  rw [← add_div, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply le_trans _ (shifted_modulus_sum_le hg N h)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf _ (by omega)) (norm_nonneg _)).trans_eq (one_mul _)

theorem correlation_zero_of_first_modulus_mean_zero {f g : ℕ → ℂ}
    (hg : OneBounded g) (h : ℕ)
    (hz : Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (normalized_correlation_le_first_modulus hg h) hz

theorem correlation_zero_of_second_modulus_mean_zero {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (h : ℕ)
    (hz : Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖g (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := hz.add (tendsto_const_div_atTop_nhds_zero_nat (h : ℝ))
  simp only [zero_add] at ht
  exact squeeze_zero (fun _ => norm_nonneg _)
    (normalized_correlation_le_second_modulus hf hg h) ht

theorem persistent_correlation_prime_defects {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g) (h : ℕ)
    (hbias : ¬Tendsto
      (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0)) :
    Summable (primeModulusDefect f) ∧ Summable (primeModulusDefect g) := by
  constructor
  · by_contra hn
    exact hbias (correlation_zero_of_first_modulus_mean_zero hg h
      (mean_modulus_zero_of_not_summable_prime_defect hfm hf hn))
  · by_contra hn
    exact hbias (correlation_zero_of_second_modulus_mean_zero hf hg h
      (mean_modulus_zero_of_not_summable_prime_defect hgm hg hn))

theorem persistent_correlation_one_values {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g) (h : ℕ)
    (hbias : ¬Tendsto
      (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0)) : f 1 = 1 ∧ g 1 = 1 := by
  have hzero (hz : ∀ n, 0 < n → f n * g (n + h) = 0) : False := by
    apply hbias
    have he : (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)) =
        fun _ => 0 := by
      funext N
      unfold positivePrefix
      rw [sum_eq_zero (fun n _ => hz _ (by omega)), zero_div]
    rw [he]
    exact tendsto_const_nhds
  constructor
  · by_contra hn
    exact hzero (fun n hnpos => by rw [hfm.eq_zero_of_one_ne hn n hnpos, zero_mul])
  · by_contra hn
    exact hzero (fun n hnpos => by rw [hgm.eq_zero_of_one_ne hn (n + h) (by omega), mul_zero])

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedBinSummation
namespace OAI

/-! Sum the retained bin estimates and divide by the retained harmonic
mass. No extra factor is hidden in the mass normalization. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma retained_bin_sum_normalize (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε : ℝ) (hS : 0 < S) (hV : 0 < V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 * R) / (L * V) + (6 * bins.card * ε) / (S * V) := by
  have hp : 0 < S * V / 2 := by positivity
  have hs : ‖∑ j ∈ bins, C j‖ ≤ bins.card * (3 * l ^ 2 * S * R / L + 3 * ε) := by
    calc
      _ ≤ ∑ j ∈ bins, ‖C j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ bins, (3 * l ^ 2 * S * R / L + 3 * ε) := sum_le_sum hC
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ‖∑ j ∈ bins, C j‖ / (S * V / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hp hS₀
    _ ≤ (bins.card * (3 * l ^ 2 * S * R / L + 3 * ε)) / (S * V / 2) :=
      div_le_div_of_nonneg_right hs hp.le
    _ = _ := by field_simp; ring

lemma retained_bin_sum_mass_lower (bins : Finset ℤ) (C : ℤ → ℂ)
    (S V S₀ L l R ε W : ℝ) (J : ℕ)
    (hS : 1 ≤ S) (hW : 1 ≤ W) (hV : W ^ J ≤ V) (hL : 0 < L)
    (hS₀ : S * V / 2 ≤ S₀) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hC : ∀ j ∈ bins, ‖C j‖ ≤ 3 * l ^ 2 * S * R / L + 3 * ε) :
    ‖∑ j ∈ bins, C j‖ / S₀ ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) + 6 * bins.card * ε := by
  have hWp : 0 < W := by linarith
  have hVone : 1 ≤ V := (one_le_pow₀ hW).trans hV
  have hSV : 1 ≤ S * V := by nlinarith
  have hb := retained_bin_sum_normalize bins C S V S₀ L l R ε
    (by linarith) (by linarith) hL hS₀ hC
  apply hb.trans
  have hfirst : (6 * bins.card * l ^ 2 * R) / (L * V) ≤
      (6 * bins.card * l ^ 2 / L) * (R / W ^ J) := by
    calc
      _ ≤ (6 * bins.card * l ^ 2 * R) / (L * W ^ J) := by
        gcongr
      _ = _ := by ring
  have hsecond : (6 * bins.card * ε) / (S * V) ≤ 6 * bins.card * ε :=
    div_le_self (by positivity) hSV
  exact add_le_add hfirst hsecond

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedFinalScale
namespace OAI

/-! The retained graph contribution at the final fixed parameter choice.
The interval exponent is chosen before all affine coefficients. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Classical

lemma retained_spectral_scale (L W : ℝ) (J : ℕ) (l : ℕ) (B : ℝ)
    (hL : 0 < L) (hW : 0 < W) (_hB : 0 ≤ B)
    (hbins : B ≤ 101 * L / Real.exp (-(J : ℝ)))
    (hchoice : Real.exp 5 * ((2 * Real.exp 150) / Real.sqrt W) ≤ Real.exp (-1))
    (herr : L / Real.exp (-(J : ℝ)) * Real.exp (-L) ≤ Real.exp (-(J : ℝ))) :
    (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) +
      6 * B * Real.exp (-L) ≤
        (1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606) * Real.exp (-(J : ℝ)) := by
  have hs : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hratio : (2 * Real.exp 150 * Real.sqrt W) / W =
      (2 * Real.exp 150) / Real.sqrt W := by
    apply (div_eq_div_iff hW.ne' hs.ne').mpr
    rw [mul_assoc, ← pow_two, Real.sq_sqrt hW.le]
  have hspec := quantitative_spectral_term (2 * Real.exp 150) W J (by positivity) hW hchoice
  have hmain : (6 * B * (l : ℝ) ^ 2 / L) *
      ((Real.exp 1 * (2 * (Real.exp (4 * J) *
        (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) ≤
      1212 * Real.exp 1 * (l : ℝ) ^ 2 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ (6 * (101 * L / Real.exp (-(J : ℝ))) * (l : ℝ) ^ 2 / L) *
          ((Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) := by
        gcongr
      _ = (1212 * Real.exp 1 * (l : ℝ) ^ 2) *
          (Real.exp (5 * J) * ((2 * Real.exp 150) / Real.sqrt W) ^ J) := by
        have he : Real.exp (5 * (J : ℝ)) =
            Real.exp (4 * J) * Real.exp (J : ℝ) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hr : (Real.exp 1 * (2 * (Real.exp (4 * J) *
            (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J =
            2 * Real.exp 1 * Real.exp (4 * J) *
              ((2 * Real.exp 150) / Real.sqrt W) ^ J := by
          calc
            _ = (2 * Real.exp 1 * Real.exp (4 * J)) *
                ((2 * Real.exp 150 * Real.sqrt W) ^ J / W ^ J) := by ring
            _ = _ := by rw [← div_pow, hratio]
        rw [hr, he, Real.exp_neg]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hspec (by positivity)
  have herror : 6 * B * Real.exp (-L) ≤ 606 * Real.exp (-(J : ℝ)) := by
    calc
      _ ≤ 6 * (101 * L / Real.exp (-(J : ℝ))) * Real.exp (-L) := by gcongr
      _ = 606 * (L / Real.exp (-(J : ℝ)) * Real.exp (-L)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left herr (by norm_num)
  nlinarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexBinGeometry
namespace OAI

/-! A literal logarithmic bin supplies the integer short range used by five-color orientation. -/

namespace TwoPointCorrelations


lemma logBinStep_pos (h : ℕ) (hh : 0 < h) (η : ℝ) (j : ℤ) :
    0 < logBinStep h η j := by
  apply Int.ceil_pos.mpr
  exact mul_pos (by exact_mod_cast hh) (Real.exp_pos _)

lemma actualPaddingBin_short_shift (h d q : ℕ) (hh : 0 < h) (hd : 0 < d) (hq : 0 < q)
    (η : ℝ) (hη : Real.exp η < 2) (j : ℤ)
    (hb : actualPaddingBin η (Real.log d) j q) :
    logBinStep h η j ≤ (h * q * d : ℕ) ∧
      (h * q * d : ℕ) < 2 * logBinStep h η j := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hlog : Real.log (d * q : ℕ) = Real.log q + Real.log d := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']
    ring
  have hp : (0 : ℝ) < (d * q : ℕ) := by exact_mod_cast Nat.mul_pos hd hq
  have hlo : Real.exp ((j : ℝ) * η) ≤ (d * q : ℕ) := by
    rw [← Real.exp_log hp]
    exact Real.exp_le_exp.mpr (by rw [hlog]; exact hb.1)
  have hhi : (d * q : ℕ) < Real.exp ((j : ℝ) * η) * Real.exp η := by
    rw [← Real.exp_add]
    calc
      _ = Real.exp (Real.log (d * q : ℕ)) := (Real.exp_log hp).symm
      _ < _ := Real.exp_lt_exp.mpr (by rw [hlog]; nlinarith [hb.2])
  have hc : (h : ℝ) * Real.exp ((j : ℝ) * η) ≤ (logBinStep h η j : ℝ) :=
    Int.le_ceil _
  constructor
  · apply Int.ceil_le.mpr
    push_cast
    have he := mul_le_mul_of_nonneg_left hlo hhR.le
    push_cast at he
    nlinarith
  · have he := mul_lt_mul_of_pos_left hhi hhR
    have hex := mul_lt_mul_of_pos_left hη (Real.exp_pos ((j : ℝ) * η))
    have hexh := mul_lt_mul_of_pos_left hex hhR
    have hr : ((h * q * d : ℕ) : ℝ) < 2 * (logBinStep h η j : ℝ) := by
      push_cast at he ⊢
      nlinarith
    exact_mod_cast hr

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexBinSummation
namespace OAI

/-! Sum arbitrary complex directed bins against their actual reciprocal divisor mass. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


theorem ModFiveThetaInput.eventually_canonical_complex_bin_sum
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 → Real.exp η < 2 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (480 * bins.card / L) * (R / W ^ J) + 480 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_bin hBr
  refine ⟨A, hA, ?_⟩
  intro h hh E hE W hW
  filter_upwards [hb h hh E hE W hW, hprime.eventually_canonical_retained_mass E W hW]
    with L hb hm
  intro hL η hη hηone hηtwo bins eligible he hpos hbin F G hF hG N v hN hv
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let S := paddingTiltNormalizer (paddingPrimeSupply E L)
  let V := ∏ j, primeHarmonicMass (P j)
  let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hmass := hm hL η hη
  have hbound (j : ℤ) (hj : j ∈ bins) :
      ‖v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        3 * (1 : ℝ) ^ 2 * S * (80 * R) / L + 3 * (80 * Real.exp (-L)) := by
    have hs : ∀ d q, eligible j d q →
        logBinStep h η j ≤ (h * q * d : ℕ) ∧
          (h * q * d : ℕ) < 2 * logBinStep h η j := by
      intro d q hdq
      exact actualPaddingBin_short_shift h d q hh (hpos j hj d q hdq).1
        (hpos j hj d q hdq).2 η hηtwo j (hbin j hj d q hdq)
    have ht := hb hL η hη hηone (eligible j) (he j hj)
      (logBinStep h η j) (logBinStep_pos h hh η j) hs F G hF hG (N j) (hN j hj)
    have hnorm : ‖v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        ‖canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hv j hj)
    have hval : ‖canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        240 * S * R / L + 240 * Real.exp (-L) := ht
    apply (hnorm.trans hval).trans_eq
    ring
  have hr := retained_bin_sum_mass_lower bins
    (fun j => v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j))
    S V (totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η)
    L 1 (80 * R) (80 * Real.exp (-L)) W J (paddingTiltNormalizer_one_le _) hW
    hmass.1 (by linarith) hmass.2 (by positivity) (by positivity) hbound
  convert (preTransparency := .instances) hr using 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexFinalScale
namespace OAI

/-! The complex retained graph has an exponentially vanishing normalized contribution. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical


lemma exp_neg_nat_exp_lt_two (J : ℕ) (hJ : 1 ≤ J) :
    Real.exp (Real.exp (-(J : ℝ))) < 2 := by
  have hj : Real.exp (-(J : ℝ)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    exact_mod_cast (show -(J : ℤ) ≤ -1 by omega)
  have hlog : Real.exp (-(J : ℝ)) < Real.log 2 := by
    have := Real.log_two_gt_d9
    have := Real.exp_neg_one_lt_half
    linarith
  calc
    _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
    _ = _ := Real.exp_log (by norm_num)

theorem ModFiveThetaInput.eventually_canonical_complex_saving
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (W : ℝ) (hW : 10 ≤ W),
      Real.exp 5 * ((2 * Real.exp 150) / Real.sqrt W) ≤ Real.exp (-1) →
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ᶠ L : ℝ in atTop, ∀ hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL
        (by linarith) hE F G (N j)‖ /
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (80 * (1212 * Real.exp 1 + 606)) * Real.exp (-(J : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_bin_sum hBr
  refine ⟨A, hA, ?_⟩
  intro W hW hchoice h hh E hE
  have hWone : 1 ≤ W := by linarith
  filter_upwards [hb h hh E hE W hWone, eventually_bin_error_saving W hWone,
    eventually_primeSupplyCount_pos W (by linarith), eventually_ge_atTop (1 : ℝ)]
    with L hb herr hJ hL
  intro hL'
  dsimp only
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (by
    dsimp only [J]
    exact neg_nonpos.mpr (Nat.cast_nonneg _))
  have hηtwo : Real.exp η < 2 := exp_neg_nat_exp_lt_two J hJ
  intro eligible he hpos hbin F G hF hG N v hN hv
  have hbound := hb hL' η hη hηone hηtwo (paddingBinIndices L η) eligible he hpos hbin
    F G hF hG N v hN hv
  have hs := retained_spectral_scale L W J 1 (paddingBinIndices L η).card (by linarith)
    (by linarith) (Nat.cast_nonneg _) (paddingBinIndices_card_linear L η hL hη hηone)
    hchoice herr
  simp only [Nat.cast_one, one_pow, mul_one] at hs
  apply hbound.trans
  calc
    _ = 80 * ((6 * (paddingBinIndices L η).card / L) *
        ((Real.exp 1 * (2 * (Real.exp (4 * J) *
          (2 * Real.exp 150 * Real.sqrt W) ^ J))) / W ^ J) +
        6 * (paddingBinIndices L η).card * Real.exp (-L)) := by ring
    _ ≤ 80 * ((1212 * Real.exp 1 + 606) * Real.exp (-(J : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedDeletionBridge
namespace OAI

/-! The actual complex correlation lost at either endpoint is dominated
by the positive deletion costs already estimated on integer intervals. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma integerEdgeKeep_of_larger_eligibility (R : Finset ℕ) (u : ℕ → ℝ)
    (small large : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hu : ∀ q ∈ R, 0 ≤ u q) (hsub : ∀ q ∈ R, small q → large q) (n : ℤ)
    (hk : integerEdgeKeep R u large g L K extra n) :
    integerEdgeKeep R u small g L K extra n := by
  refine ⟨?_, hk.2⟩
  apply le_trans _ hk.1
  unfold paddingDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum
  intro q hq
  by_cases hs : small q ∧ (q : ℤ) ∣ n
  · have hl : large q ∧ (q : ℤ) ∣ n := ⟨hsub q hq hs.1, hs.2⟩
    rw [if_pos hs, if_pos hl]
  · simp only [hs, ite_false]
    split_ifs <;> first | exact hu q hq | exact le_rfl

lemma liouville_edge_norm_le_positive (d q : ℕ) (n m : ℤ) :
    ‖(actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) *
      integerLiouville n * integerLiouville m‖ ≤
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  calc
    _ = |actualPaddingCoefficient q * centeredTuple d.primeFactors n| *
        ‖integerLiouville n‖ * ‖integerLiouville m‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |actualPaddingCoefficient q * centeredTuple d.primeFactors n| * 1 * 1 := by
      gcongr <;> exact integerLiouville_norm_le_one _
    _ ≤ _ := by
      rw [mul_one, mul_one, abs_mul, abs_of_nonneg (actualPaddingCoefficient_nonneg q)]
      exact mul_le_mul_of_nonneg_left (abs_centeredTuple_le_positivePrimeWeight _ _)
        (actualPaddingCoefficient_nonneg q)


lemma norm_sub_optional_le_two_costs (z retained : ℂ) (B : ℝ) (gn gm : Prop)
    (hB : ‖z‖ ≤ B) (hret : retained = z ∨ retained = 0)
    (hgood : gn → gm → retained = z) :
    ‖z - retained‖ ≤ (if gn then 0 else B) + (if gm then 0 else B) := by
  have hB0 := (norm_nonneg z).trans hB
  by_cases hn : gn <;> by_cases hm : gm
  · simp only [hn, hm, ite_true, hgood hn hm, sub_self, norm_zero, add_zero, le_refl]
  all_goals
    rcases hret with rfl | rfl <;> simp only [hn, hm, ite_true, ite_false,
      sub_self, sub_zero, norm_zero, zero_add, add_zero] <;> linarith

lemma retainedNumericalEdge_optional {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (L K W : ℝ) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (bad : ℤ → Prop) (d q : ℕ) (n m : ℤ) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m ∨
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m = 0 := by
  unfold retainedNumericalEdge retainedLiouvilleEdge uncutNumericalEdge
  split_ifs <;> simp_all

lemma retainedNumericalEdge_eq_uncut_of_good {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → Prop) (j : ℤ) (d q : ℕ) (n m : ℤ)
    (hsub : ∀ r ∈ R, eligible d r → actualPaddingBin η (c d) j r)
    (hn : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
      (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad n)
    (hm : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) m ∧
      (actualPaddingDegree (primeTuplePool P) m : ℝ) ≤ 6 * W * J ∧ ¬bad m) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m := by
  have hkn := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub n hn.1
  have hkm := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub m hm.1
  have hdn : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J := hn.2.1
  have hdm : (actualPaddingDegree (univ.biUnion P) m : ℝ) ≤ 6 * W * J := hm.2.1
  by_cases hg : gate d n m
  · simp only [retainedNumericalEdge, retainedLiouvilleEdge, uncutNumericalEdge,
      hn.2.2, hm.2.2, hkn, hkm, hdn, hdm, hn.1.2, hm.1.2, hg,
      and_true, true_and, not_false_eq_true, ite_true]
    congr 1
    apply propext
    tauto
  · simp only [retainedNumericalEdge, uncutNumericalEdge, hg, false_and, ite_false]

lemma positiveDeletionAtom_eq_good_cost {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) (he : eligible j d q) (hq : (q : ℤ) ∣ n)
    (hd : d.primeFactors.card = J) :
    positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n =
      if integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n
      then 0 else actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  have hf : (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
      6 * W * J < (actualPaddingDegree (primeTuplePool P) n : ℝ) ∨ bad j n) ↔
      ¬(integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n) := by
    simp only [not_and_or, not_le, not_not]
  simp only [positiveDeletionAtom, he, hq, hd, ite_true, true_and, hf]
  split_ifs <;> simp_all

lemma positiveDeletionAtom_nonneg (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) :
    0 ≤ positiveDeletionAtom P Q R η c L K W eligible bad j d q n := by
  unfold positiveDeletionAtom
  split_ifs <;> first
    | exact le_rfl
    | exact mul_nonneg (mul_nonneg (actualPaddingCoefficient_nonneg q)
        (positivePrimeWeight_nonneg _ _)) (by norm_num)

/-- On a numerical edge, each discarded correlation is paid by one of
its two actual endpoint costs. No averaging or periodicity premise is added. -/
theorem uncut_sub_retained_edge_le {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ)
    (hsub : ∀ r ∈ R, eligible j d r → actualPaddingBin η (c d) j r)
    (hd : d.primeFactors.card = J) :
    ‖uncutNumericalEdge R (eligible j) h gate d q n (n + (h * q * d : ℕ)) -
      retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
        d q n (n + (h * q * d : ℕ))‖ ≤
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
        (n + (h * q * d : ℕ)) := by
  let m := n + (h * q * d : ℕ)
  let z := uncutNumericalEdge R (eligible j) h gate d q n m
  let r := retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
    (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) d q n m
  have hop : r = z ∨ r = 0 := retainedNumericalEdge_optional P R Q (eligible j)
    L K W h gate (bad j) d q n m
  by_cases ha : gate d n m ∧ q ∈ R ∧ eligible j d q ∧ (q : ℤ) ∣ n
  · have hmdiv : (q : ℤ) ∣ m := by
      dsimp [m]
      apply dvd_add ha.2.2.2
      exact_mod_cast (show q ∣ h * q * d from dvd_mul_of_dvd_left (dvd_mul_left q h) d)
    have hw : positivePrimeWeight d.primeFactors m = positivePrimeWeight d.primeFactors n := by
      have he : (h * q * d : ℕ) = (d : ℤ) * ((h * q : ℕ) : ℤ) := by push_cast; ring
      change positivePrimeWeight d.primeFactors (n + (h * q * d : ℕ)) = _
      rw [he, positivePrimeWeight_add_multiple]
    let good := fun t : ℤ =>
      integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) t ∧
      (actualPaddingDegree (primeTuplePool P) t : ℝ) ≤ 6 * W * J ∧ ¬bad j t
    have hz : ‖z‖ ≤ actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
      dsimp [z, uncutNumericalEdge]
      rw [if_pos ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, rfl⟩]
      exact liouville_edge_norm_le_positive d q n m
    have hg : good n → good m → r = z :=
      fun hn hm => retainedNumericalEdge_eq_uncut_of_good P R Q η c L K W
        (eligible j) h gate (bad j) j d q n m hsub hn hm
    have hb := norm_sub_optional_le_two_costs z r
      (actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n)
      (good n) (good m) hz hop hg
    have hcn := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q n
      ha.2.2.1 ha.2.2.2 hd
    have hcm := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q m
      ha.2.2.1 hmdiv hd
    change ‖z - r‖ ≤ _
    rw [hcn, hcm, hw]
    by_cases hn : good n <;> by_cases hm : good m
    all_goals
      dsimp only [good] at hn hm hb
      simpa only [hn, hm, ite_true, ite_false] using hb
  · have hz : z = 0 := by
      dsimp [z, uncutNumericalEdge]
      exact if_neg (fun hcond => ha ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2.1⟩)
    have hr : r = 0 := hop.elim (fun he => he.trans hz) id
    change ‖z - r‖ ≤ _
    rw [hz, hr, sub_self, norm_zero]
    exact add_nonneg
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q n)
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q m)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexNumericalEdges
namespace OAI

/-! Transfer the existing positive deletion costs to arbitrary complex factors.
Liouville's unit values serve only as an exact algebraic change of test functions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma liouvilleUntwist_norm_le (F G : ℤ → ℂ)
    (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1) (n m : ℤ) :
    ‖liouvilleUntwist F G n m‖ ≤ 1 := by
  unfold liouvilleUntwist
  simp only [norm_mul]
  have ha := mul_le_mul (hF n) (integerLiouville_norm_le_one n)
    (norm_nonneg (integerLiouville n)) (by norm_num : (0 : ℝ) ≤ 1)
  have hb := mul_le_mul (hG m) (integerLiouville_norm_le_one m)
    (norm_nonneg (integerLiouville m)) (by norm_num : (0 : ℝ) ≤ 1)
  have hab := mul_le_mul ha hb
    (mul_nonneg (norm_nonneg (G m)) (norm_nonneg (integerLiouville m)))
    (by norm_num : (0 : ℝ) ≤ 1 * 1)
  simpa only [one_mul] using hab

lemma liouvilleUntwist_cancel (F G : ℤ → ℂ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m)
    (z : ℂ) : liouvilleUntwist F G n m * (z * integerLiouville n * integerLiouville m) =
      z * F n * G m := by
  have hn0 : n.toNat ≠ 0 := by omega
  have hm0 : m.toNat ≠ 0 := by omega
  have hn2 : integerLiouville n ^ 2 = 1 := liouville_sq hn0
  have hm2 : integerLiouville m ^ 2 = 1 := liouville_sq hm0
  calc
    _ = z * F n * G m * integerLiouville n ^ 2 * integerLiouville m ^ 2 := by
      unfold liouvilleUntwist
      ring
    _ = _ := by rw [hn2, hm2, mul_one, mul_one]

lemma retainedComplexPrimeEdge_eq_untwist {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) (hL : L ≠ 0) :
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n m / (L : ℂ) =
      liouvilleUntwist F G n m * retainedNumericalEdge P Q Qp u eligible L K W extra h
        gate keep (∏ j, (e.1 j).val) e.2.val n m := by
  unfold retainedComplexPrimeEdge retainedNumericalEdge retainedLiouvilleEdge retainedRealEdge
  split_ifs
  · rw [liouvilleUntwist_cancel F G n m hn hm]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL]
  all_goals simp

lemma uncutNumericalEdge_untwist (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop) (F G : ℤ → ℂ)
    (d q : ℕ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) :
    liouvilleUntwist F G n m * uncutNumericalEdge R eligible h gate d q n m =
      if gate d n m ∧ q ∈ R ∧ eligible d q ∧ (q : ℤ) ∣ n ∧
        m = n + (h * q * d : ℕ) then
        (actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) * F n * G m
      else 0 := by
  unfold uncutNumericalEdge
  split_ifs
  · exact liouvilleUntwist_cancel F G n m hn hm _
  · simp

lemma complex_uncut_sub_retained_edge_le {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ)
    (hsub : ∀ r ∈ R, eligible j d r → actualPaddingBin η (c d) j r)
    (hd : d.primeFactors.card = J) (F G : ℤ → ℂ)
    (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1) :
    let m := n + (h * q * d : ℕ)
    ‖liouvilleUntwist F G n m * uncutNumericalEdge R (eligible j) h gate d q n m -
      liouvilleUntwist F G n m * retainedNumericalEdge P R Q actualPaddingCoefficient
        (eligible j) L K W (fun _ => actualPaddingDegreeCut Q L) h gate
        (fun z => ¬bad j z) d q n m‖ ≤
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q m := by
  dsimp only
  rw [← mul_sub, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (liouvilleUntwist_norm_le F G hF hG n _)).trans
  exact uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n hsub hd

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrefixDeletionBridge
namespace OAI

/-! Sum the pointwise endpoint loss over the same positive prefixes as
the spectral test, retaining every tuple and padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma normalized_prefix_difference_le (F G : ℕ → ℂ) (cost : ℕ → ℝ) (N : ℕ)
    (hb : ∀ n, ‖F n - G n‖ ≤ cost n) :
    ‖positivePrefix F N / (N : ℂ) - positivePrefix G N / (N : ℂ)‖ ≤
      uniformAverage (fun x : Fin N => cost (x.val + 1)) := by
  rw [← sub_div]
  have he : positivePrefix F N - positivePrefix G N = positivePrefix (fun n => F n - G n) N := by
    simp only [positivePrefix, sum_sub_distrib]
  rw [he, norm_div, Complex.norm_natCast]
  unfold positivePrefix uniformAverage
  rw [Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun x => cost (x + 1)) N]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (norm_sum_le _ _).trans (sum_le_sum (fun n _ => hb (n + 1)))



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedEligibility
namespace OAI

/-! On the actual tuple and padding pools, canonical pair membership
agrees with the original bin eligibility, including inside the density cut. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma canonicalTraceFamily_pair_on_pool (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ)
    (hd : d ∈ primeTupleDivisors
      (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)))
    (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (d, q) ∈ (canonicalTraceFamily h E W L eligible hL hW hE).pairs ↔ eligible d q := by
  rw [canonicalTraceFamily, actualProhibitedPrimeFamily_pairs]
  simp only [hd, (mem_filter.mp hq).1, (mem_filter.mp hq).2, true_and]

lemma integerEdgeKeep_congr_eligible (R : Finset ℕ) (u : ℕ → ℝ)
    (e f : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hef : ∀ q ∈ R, e q ↔ f q) (n : ℤ) :
    integerEdgeKeep R u e g L K extra n ↔ integerEdgeKeep R u f g L K extra n := by
  have he : paddingDensity R u e g n = paddingDensity R u f g n := by
    unfold paddingDensity
    congr 1
    apply sum_congr rfl
    intro q hq
    simp only [hef q hq]
  simp only [integerEdgeKeep, he]

lemma retainedNumericalEdge_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (d q : ℕ) (n m : ℤ) (hq : q ∈ R)
    (hef : ∀ r ∈ R, e d r ↔ f d r) :
    retainedNumericalEdge P R Q u e L K W extra h gate keep d q n m =
      retainedNumericalEdge P R Q u f L K W extra h gate keep d q n m := by
  have hk := integerEdgeKeep_congr_eligible R u (e d) (f d)
    (actualPaddingVertex Q) L K (extra d) hef
  simp only [retainedNumericalEdge, retainedLiouvilleEdge, hef q hq, hk]
  split_ifs <;> rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexNumericalPrefix
namespace OAI

/-! Numerical divisor reindexing of the arbitrary complex retained prefix. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma retainedComplex_row_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (n : ℤ) (hn : 0 < n) (hL : L ≠ 0) :
    (∑ e : ((j : Fin J) → P j) × Q,
      retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) / (L : ℂ) =
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ Q,
        liouvilleUntwist F G n (n + (h * q * d : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep d q n
            (n + (h * q * d : ℕ)) := by
  rw [sum_div, Fintype.sum_prod_type, primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro d _
    calc
      _ = ∑ q : Q, liouvilleUntwist F G n (n + (h * q.val * ∏ j, (d j).val : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
            (∏ j, (d j).val) q.val n (n + (h * q.val * ∏ j, (d j).val : ℕ)) := by
        apply sum_congr rfl
        intro q _
        exact retainedComplexPrimeEdge_eq_untwist P Q Qp u eligible L K W extra h gate keep
          F G (d, q) n _ hn (by omega) hL
      _ = _ := sum_coe_sort Q (fun q =>
        liouvilleUntwist F G n (n + (h * q * ∏ j, (d j).val : ℕ)) *
          retainedNumericalEdge P Q Qp u eligible L K W extra h gate keep
            (∏ j, (d j).val) q n (n + (h * q * ∏ j, (d j).val : ℕ)))
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

lemma retainedComplexPrefix_eq_numerical {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ)
    (hL : L ≠ 0) :
    retainedComplexPrefix P Q Qp u eligible L K W extra h gate keep F G N =
      untwistedRetainedPrefix P Q Qp u eligible L K W extra h gate keep F G N := by
  unfold retainedComplexPrefix untwistedRetainedPrefix
  rw [div_right_comm]
  congr 1
  unfold positivePrefix
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  exact retainedComplex_row_eq_numerical P hprime hdisjoint Q Qp u eligible L K W extra h
    gate keep F G (n + 1 : ℕ) (by omega) hL

lemma untwistedRetainedPrefix_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ)
    (hef : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R, e d q ↔ f d q) :
    untwistedRetainedPrefix P R Q u e L K W extra h gate keep F G N =
      untwistedRetainedPrefix P R Q u f L K W extra h gate keep F G N := by
  unfold untwistedRetainedPrefix
  congr 2
  funext n
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro q hq
  rw [retainedNumericalEdge_congr_eligible P R Q u e f L K W extra h gate keep
    d q n ((n : ℤ) + (h * q * d : ℕ)) hq (hef d hd)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexDeletionPrefix
namespace OAI

/-! The existing positive endpoint costs control ordinary complex prefix loss. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem complex_uncut_sub_retained_prefix_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (N : ℕ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hsub : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q) :
    ‖untwistedUncutPrefix P R (eligible j) h gate F G N -
      untwistedRetainedPrefix P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) F G N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L K W eligible bad j d q (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  unfold untwistedUncutPrefix untwistedRetainedPrefix
  have hb (n : ℕ) :
      ‖(∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
        uncutNumericalEdge R (eligible j) h gate d q n ((n : ℤ) + (h * q * d : ℕ))) -
        (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        liouvilleUntwist F G n ((n : ℤ) + (h * q * d : ℕ)) *
        retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
          (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
          d q n ((n : ℤ) + (h * q * d : ℕ)))‖ ≤
      ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        (positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
        positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
          ((n : ℤ) + (h * q * d : ℕ))) := by
    simp only [← sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro d hd
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro q _
    exact complex_uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n
      (hsub d hd) (primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.1 F G hF hG
  have hp := normalized_prefix_difference_le _ _ _ N hb
  apply hp.trans_eq
  have hadd (f g : Fin N → ℝ) : uniformAverage (fun x => f x + g x) =
      uniformAverage f + uniformAverage g := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [uniformAverage_finset_sum, hadd, sum_add_distrib]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalCorrelationDeletion
namespace OAI

/-! The literal uncut bin correlation differs from the spectral test
by the two canonical endpoint deletion costs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma prefix_start_one_add (n : ℕ) : (1 : ℤ) + n = ((n + 1 : ℕ) : ℤ) := by
  push_cast
  ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexCanonicalDeletion
namespace OAI

/-! The actual complex uncut correlation is controlled by the existing two endpoint costs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma canonical_complex_uncut_sub_retained_prefix (h : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (j : ℤ) (N : ℕ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hbin : ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := paddingPrimeSupply E L
    let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
    let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
      (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
    ‖canonicalComplexUncutPrefix h E W L (eligible j) F G N -
      canonicalComplexPrefix h E W L (eligible j) hL hW hE F G N‖ ≤
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q ((x.val + 1 : ℕ) : ℤ))) +
      (∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        uniformAverage (fun x : Fin N => positiveDeletionAtom (primeTuplePool P) Q R
          η c L (Real.exp (4 * J)) W eligible bad j d q
            (((x.val + 1 : ℕ) : ℤ) + (h * q * d : ℕ)))) := by
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let bad := fun k n => ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible k) hL hW hE).pairs) n
  let active := fun d q => (d, q) ∈ (canonicalTraceFamily h E W L (eligible j) hL hW hE).pairs
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hcongr := untwistedRetainedPrefix_congr_eligible P R Q actualPaddingCoefficient
    active (eligible j) L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L)
    h (fun _ _ _ => True) (fun z => ¬bad j z) F G N
    (fun d hd q hq => canonicalTraceFamily_pair_on_pool h E W L (eligible j) hL hW hE d q hd hq)
  change ‖untwistedUncutPrefix P R (eligible j) h (fun _ _ _ => True) F G N -
    retainedComplexPrefix P R Q actualPaddingCoefficient active L (Real.exp (4 * J)) W
      (fun _ => actualPaddingDegreeCut Q L) h (fun _ _ _ => True)
      (fun z => ¬bad j z) F G N‖ ≤ _
  rw [retainedComplexPrefix_eq_numerical P hp hd R Q actualPaddingCoefficient active
    L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Q L) h (fun _ _ _ => True)
    (fun z => ¬bad j z) F G N (by linarith), hcongr]
  exact complex_uncut_sub_retained_prefix_le P hp hd R Q η c L (Real.exp (4 * J)) W
    eligible h (fun _ _ _ => True) bad j N F G hF hG (fun d _ q _ => hbin d q)

lemma canonical_complex_weighted_correlation_deletion (h : ℕ) (E : Finset ℕ)
    (W L η : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (bins : Finset ℤ)
    (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (N : ℤ → ℕ) (v : ℤ → ℂ)
    (F G : ℤ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q)
    (hv : ∀ j ∈ bins, ‖v j‖ ≤ 1) :
    ‖(∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)) -
      (∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j))‖ ≤
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ _ _ => 0) (fun _ => 1) N +
      canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * primeSupplyCount W L))
        hL hW hE bins c eligible (fun _ d q => (h * q * d : ℕ)) (fun _ => 1) N := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ bins, ‖canonicalComplexUncutPrefix h E W L (eligible j) F G (N j) -
        canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
    _ ≤ ∑ j ∈ bins, _ := sum_le_sum (fun j hj =>
      canonical_complex_uncut_sub_retained_prefix h E W L η hL hW hE c eligible j (N j) F G hF hG (hbin j hj))
    _ = _ := by
      simp only [canonicalShiftedSourceDeletion, Nat.cast_one, prefix_start_one_add,
        sum_add_distrib, add_zero]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FullTupleBinIdentity
namespace OAI

/-! The empty supply subset is exactly the full numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_ite_const (p : Prop) (f : ℕ → ℂ) (N : ℕ) :
    positivePrefix (fun n => if p then f n else 0) N =
      if p then positivePrefix f N else 0 := by
  by_cases hp : p <;> simp only [hp, ite_true, ite_false, positivePrefix, sum_const_zero]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredBinIdentity
namespace OAI

/-! The graph bin and the analytic centering bin are the same finite sum,
with the literal real denominator and no floor-normalization error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma prefix_scalar_real_denominator (f : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    ((N : ℂ) / (T : ℂ)) * (positivePrefix f N / (N : ℂ)) =
      positivePrefix f N / (T : ℂ) := by
  by_cases hN : N = 0
  · subst N
    simp only [positivePrefix, range_zero, sum_empty, Nat.cast_zero, zero_div, mul_zero]
  · have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexCenteredBridge
namespace OAI

/-! The uncut complex graph is the literal centered tuple correlation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma untwistedUncutPrefix_centered {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (h N : ℕ) (F G : ℕ → ℂ) :
    untwistedUncutPrefix P Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) N =
      positivePrefix (fun n => ∑ q ∈ Q, (actualPaddingCoefficient q : ℂ) *
        tupleComplexCenteredProfile P q eligible F G h n) N / (N : ℂ) := by
  unfold untwistedUncutPrefix
  congr 1
  unfold positivePrefix
  apply sum_congr rfl
  intro n _
  dsimp only
  rw [primeTupleDivisors, sum_image]
  · rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    simp only [tupleComplexCenteredProfile, mul_sum]
    apply sum_congr rfl
    intro x _
    rw [uncutNumericalEdge_untwist Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) (∏ j, (x j).val) q
      (n + 1 : ℕ) _ (by omega) (by positivity)]
    simp only [true_and, hq, Int.toNat_natCast, and_true,
      Int.natCast_dvd_natCast, Complex.ofReal_mul]
    have hm : ((n + 1 : ℕ) : ℤ) + (h * q * ∏ j, (x j).val : ℕ) =
        ((n + 1 + h * (q * ∏ j, (x j).val) : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    simp only [Int.toNat_natCast]
    unfold natDivisibilityIndicator
    split_ifs <;> simp_all
    ring
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma tupleComplexPartialProfile_empty {J : ℕ} (P : Fin J → Finset ℕ)
    (q : ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h n : ℕ) :
    tupleComplexPartialProfile P ∅ q eligible F G h n =
      ∑ x : (j : Fin J) → P j,
        if eligible (∏ j, (x j).val) q then
          natDivisibilityIndicator (q * ∏ j, (x j).val) n *
            (F n * G (n + h * (q * ∏ j, (x j).val)))
        else 0 := by
  unfold tupleComplexPartialProfile
  apply sum_congr rfl
  intro x _
  have he : (∏ j : {j // j ∉ (∅ : Finset (Fin J))}, (x j).val) =
      ∏ j, (x j).val := (prod_subtype univ (by simp) (fun j => (x j).val)).symm
  simp only [Fintype.prod_empty, Nat.cast_one, inv_one, one_mul, he]



lemma weighted_complex_uncut_sub_full {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) :
    ((⌊T⌋₊ : ℂ) / (T : ℂ)) * untwistedUncutPrefix P Q eligible h (fun _ _ _ => True)
      (fun z => F z.toNat) (fun z => G z.toNat) ⌊T⌋₊ -
        fullComplexBin P Q eligible F G h T = nonrawComplexBin P Q eligible F G h T := by
  rw [untwistedUncutPrefix_centered P hprime hdisjoint,
    prefix_scalar_real_denominator, positivePrefix_sum_finite, sum_div]
  simp only [positivePrefix_const_mul, fullComplexBin, nonrawComplexBin, mul_div_assoc]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexFullDilation
namespace OAI

/-! The full-divisibility part of the complex bin is the exact dilated correlation. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tupleComplexPartialProfile_empty_prefix {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime) (q : ℕ) (hq : 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h N : ℕ) :
    positivePrefix (tupleComplexPartialProfile P ∅ q eligible F G h) N =
      ∑ x : (j : Fin J) → P j, if eligible (∏ j, (x j).val) q then
        positivePrefix (fun m => F ((q * ∏ j, (x j).val) * m) *
          G ((q * ∏ j, (x j).val) * (m + h))) (N / (q * ∏ j, (x j).val))
      else 0 := by
  change positivePrefix (fun n => tupleComplexPartialProfile P ∅ q eligible F G h n) N = _
  simp_rw [tupleComplexPartialProfile_empty]
  rw [positivePrefix_sum_finite]
  apply sum_congr rfl
  intro x _
  rw [positivePrefix_ite_const]
  by_cases he : eligible (∏ j, (x j).val) q
  · simp only [he, ite_true]
    have hu : 0 < q * ∏ j, (x j).val :=
      Nat.mul_pos hq (prod_pos (fun j _ => (hprime j _ (x j).property).pos))
    rw [divisibility_positivePrefix _ _ _ hu]
    congr 1
    funext m
    rw [show (q * ∏ j, (x j).val) * m + h * (q * ∏ j, (x j).val) =
      (q * ∏ j, (x j).val) * (m + h) by ring]
  · simp only [he, ite_false]

lemma fullComplexBin_eq_dilated {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h : ℕ) (T : ℝ) :
    fullComplexBin P Q eligible F G h T =
      ∑ q ∈ Q, ∑ d ∈ primeTupleDivisors P, if eligible d q then
        (actualPaddingCoefficient q : ℂ) *
          (positivePrefix (fun m => F ((q * d) * m) * G ((q * d) * (m + h)))
            (⌊T⌋₊ / (q * d)) / (T : ℂ))
      else 0 := by
  unfold fullComplexBin
  apply sum_congr rfl
  intro q hq
  rw [tupleComplexPartialProfile_empty_prefix P hprime q (hQ q hq), sum_div, mul_sum,
    primeTupleDivisors, sum_image]
  · apply sum_congr rfl
    intro x _
    split_ifs <;> simp only [zero_div, mul_zero]
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexRawComparison
namespace OAI

/-! Raw complex correlations retain the actual prime-dependent extraction cost.
This is essential when the padding includes small primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma correlation_oneBounded {f g : ℕ → ℂ} (hf : OneBounded f)
    (hg : OneBounded g) (h : ℕ) : OneBounded (fun n => f n * g (n + h)) := by
  intro n hn
  rw [norm_mul]
  exact (mul_le_mul (hf n hn) (hg (n + h) (by omega)) (norm_nonneg _) zero_le_one).trans
    (by norm_num)

lemma dilated_correlation_extraction {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u h : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ u → p ∈ P)
    (T : ℝ) (hT : 0 < T) :
    ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ / (T : ℂ) -
      (f u * g u) * (positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ /
        (T : ℂ))‖ ≤
      (1 / (u : ℝ)) * (4 * (∑ p ∈ P, 1 / (p : ℝ))) + 4 * P.card / T := by
  have he : positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ -
      (f u * g u) * positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ =
      positivePrefix (multiplicativeExtractionGap f g u h) ⌊T / u⌋₊ := by
    unfold positivePrefix multiplicativeExtractionGap
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [← mul_div_assoc, ← sub_div, he, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hfloor : (⌊T / u⌋₊ : ℝ) ≤ T / u := Nat.floor_le (div_nonneg hT.le huR.le)
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ 4 * (⌊T / u⌋₊ : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card :=
      multiplicativeExtraction_sum_bound hfm hgm hf hg u h _ hu P hP hcover
    _ ≤ 4 * (T / u) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card := by
      gcongr
    _ = _ := by field_simp

lemma dilated_correlation_bin_error {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u h : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ u → p ∈ P)
    (X T η : ℝ) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : X * Real.exp (-η) ≤ T / u) (hhi : T / u ≤ X) :
    ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) (⌊T⌋₊ / u) /
        (T : ℂ) -
      ((f u * g u) / (u : ℂ)) *
        (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      (1 / (u : ℝ)) * ((4 * (∑ p ∈ P, 1 / (p : ℝ))) + 2 * η + 1 / X) +
        4 * P.card / T := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hY : 0 < T / u := (mul_pos hX (Real.exp_pos _)).trans_le hlo
  have hT : 0 < T := (div_pos_iff_of_pos_right huR).mp hY
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  let C := f u * g u
  let A := positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ / ((T / u : ℝ) : ℂ)
  let B := positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)
  have hC : ‖C‖ ≤ 1 := by
    dsimp [C]
    rw [norm_mul]
    exact (mul_le_mul (hf u hu) (hg u hu) (norm_nonneg _) zero_le_one).trans (by norm_num)
  have hnear : ‖A - B‖ ≤ 2 * η + 1 / X :=
    real_prefix_log_bin _ (correlation_oneBounded hf hg h) X (T / u) η hX hη hlo hhi
  have hscale : C * (positivePrefix (fun n => f n * g (n + h)) ⌊T / u⌋₊ /
      (T : ℂ)) = (C / (u : ℂ)) * A := by
    dsimp [A]
    push_cast
    field_simp [huC, hTC]
  rw [← Nat.floor_div_natCast]
  have he := dilated_correlation_extraction hfm hgm hf hg u h hu P hP hcover T hT
  change ‖_ - (C / (u : ℂ)) * B‖ ≤ _
  calc
    _ ≤ ‖positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
        (T : ℂ) - (C / (u : ℂ)) * A‖ + ‖(C / (u : ℂ)) * (A - B)‖ := by
      have heq : positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
          (T : ℂ) - (C / (u : ℂ)) * B =
          (positivePrefix (fun n => f (u * n) * g (u * (n + h))) ⌊T / u⌋₊ /
            (T : ℂ) - (C / (u : ℂ)) * A) + (C / (u : ℂ)) * (A - B) := by ring
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ((1 / (u : ℝ)) * (4 * (∑ p ∈ P, 1 / (p : ℝ))) + 4 * P.card / T) +
        (1 / (u : ℝ)) * (2 * η + 1 / X) := by
      apply add_le_add
      · simpa only [← hscale, C] using he
      · rw [norm_mul, norm_div, Complex.norm_natCast]
        exact mul_le_mul (div_le_div_of_nonneg_right hC huR.le) hnear
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexRawSelection
namespace OAI

/-! Numerical phase selection and the raw lower bound use the whole reciprocal
mass. No phase or nonvanishing condition is imposed on individual primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma weighted_dilated_correlation_comparison {ι : Type*} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (S : Finset ι) (w : ι → ℝ) (u : ι → ℕ) (P : ι → Finset ℕ)
    (T : ι → ℝ) (h : ℕ) (X η : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 < u i)
    (hP : ∀ i ∈ S, ∀ p ∈ P i, p.Prime)
    (hcover : ∀ i ∈ S, ∀ p, p.Prime → p ∣ u i → p ∈ P i)
    (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ i ∈ S, X * Real.exp (-η) ≤ T i / u i)
    (hhi : ∀ i ∈ S, T i / u i ≤ X) :
    ‖(∑ i ∈ S, (w i : ℂ) *
        (positivePrefix (fun n => f (u i * n) * g (u i * (n + h)))
          (⌊T i⌋₊ / u i) / (T i : ℂ))) -
      (∑ i ∈ S, (w i : ℂ) * ((f (u i) * g (u i)) / (u i : ℂ))) *
        (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      ∑ i ∈ S, w i * ((1 / (u i : ℝ)) *
        ((4 * (∑ p ∈ P i, 1 / (p : ℝ))) + 2 * η + 1 / X) +
          4 * (P i).card / T i) := by
  rw [sum_mul, ← sum_sub_distrib]
  simp_rw [mul_assoc, ← mul_sub]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro i hi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
  exact mul_le_mul_of_nonneg_left
    (dilated_correlation_bin_error hfm hgm hf hg (u i) h (hu i hi) (P i)
      (hP i hi) (hcover i hi) X (T i) η hX hη (hlo i hi) (hhi i hi)) (hw i hi)

lemma raw_norm_lower_bound (R C M : ℂ) (mass γ : ℝ)
    (_hmass : 0 ≤ mass) (hγ : 0 ≤ γ)
    (hC : mass / 8 ≤ ‖C‖) (hM : γ ≤ ‖M‖)
    (herr : ‖R - C * M‖ ≤ γ * mass / 16) :
    γ * mass / 16 ≤ ‖R‖ := by
  have hprod : (mass / 8) * γ ≤ ‖C * M‖ := by
    rw [norm_mul]
    exact mul_le_mul hC hM hγ (norm_nonneg C)
  have htriangle : ‖C * M‖ ≤ ‖R‖ + ‖R - C * M‖ := by
    calc
      _ = ‖R - (R - C * M)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexPairSelection
namespace OAI

/-! Phase selection on the literal finite numerical pair family. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma complexPairWeight_nonneg (dq : ℕ × ℕ) : 0 ≤ complexPairWeight dq := by
  unfold complexPairWeight
  positivity

lemma eligibleComplexPairs_sum {M : Type*} [AddCommMonoid M]
    (D Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (F : ℕ × ℕ → M) :
    (∑ dq ∈ eligibleComplexPairs D Q eligible, F dq) =
      ∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q, if eligible d q then F (d, q) else 0 := by
  rw [eligibleComplexPairs, sum_filter, sum_product]

lemma eligibleComplexPairs_mass (D Q : Finset ℕ) (L η : ℝ) (hη : 0 < η) :
    (∑ dq ∈ eligibleComplexPairs D Q (PaddingPairEligible L η), complexPairWeight dq) =
      totalPaddingBinMass D Q L η := by
  rw [eligibleComplexPairs_sum, totalPaddingBinMass_eq D Q L η hη]
  rfl



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FinalCorrelationBound
namespace OAI

/-! Arithmetic assembly of the centering, endpoint deletion, and retained
spectral estimates at the manuscript's final parameter choice. -/

namespace TwoPointCorrelations

lemma quantitative_deletion_small (L W C : ℝ) (J : ℕ)
    (hL : 1 ≤ L) (hW : 1 ≤ W) (hC : 0 ≤ C)
    (hJ : 60 * (J : ℝ) ≤ Real.log L)
    (hr : Real.exp (-L ^ (9 / 10 : ℝ)) ≤ Real.exp (-(J : ℝ))) :
    (2 : ℝ) ^ J * (C / Real.exp (4 * J) + L ^ (-100 : ℝ) +
      Real.exp (-2 * W * J)) + 2 * Real.exp (-L ^ (9 / 10 : ℝ)) ≤
        (C + 4) * Real.exp (-(J : ℝ)) := by
  obtain ⟨_, hk, hl, hw⟩ := quantitative_small_terms L W J hL hW hJ
  have hc := mul_le_mul_of_nonneg_left hk hC
  have he : (2 : ℝ) ^ J * (C / Real.exp (4 * J)) =
      C * ((2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ))) := by
    rw [show (4 : ℝ) * J = -(-4 * (J : ℝ)) by ring, Real.exp_neg]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  rw [← he] at hc
  nlinarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComplexGraphUpper
namespace OAI

/-! The complete uncut complex graph is small: the retained graph and the
two endpoint deletion errors share the same exponential saving. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem complex_graph_fixed_scale (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ 10 ≤ W ∧
      ∀ (h : ℕ), 0 < h → ∀ (E : Finset ℕ)
        (_hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L,
      let J := primeSupplyCount W L
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ eligible : ℤ → ℕ → ℕ → Prop,
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      ‖∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
          C * η := by
  obtain ⟨As, hAs, hs⟩ := hP.eventually_canonical_complex_saving hBr
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_canonical_shifted_source_deletion_uniform hP
  obtain ⟨W, hW, hchoice⟩ := exists_fixed_spectral_parameter (2 * Real.exp 150) (by positivity)
  let A := As + Ad
  have hA : 1000 ≤ A := by dsimp only [A]; omega
  have hWone : 1 ≤ W := by linarith
  refine ⟨A, W, hA, hW, ?_⟩
  intro h hh E hE
  obtain ⟨Cd, hCd, hd⟩ := hd h E hE W 3 hW (by norm_num)
  let Cs : ℝ := 80 * (1212 * Real.exp 1 + 606)
  refine ⟨Cs + 4 * (Cd + 4), by dsimp only [Cs]; positivity, ?_⟩
  filter_upwards [hs W hW hchoice h hh E hE, hd,
    hP.eventually_canonical_retained_mass E W hWone,
    eventually_rare_error_saving W hWone, eventually_ge_atTop (101 : ℝ)]
      with L hs hd hm hr hlarge
  intro hL
  dsimp only
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let M := paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j)
  let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
  let bins := paddingBinIndices L η
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  intro eligible he hpos hbin F G hF hG N v hN hv
  have hN' (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hN j hj)
  have hmass := hm hL η hη
  have hV : 1 ≤ ∏ j, primeHarmonicMass (P j) := (one_le_pow₀ hWone).trans hmass.1
  have hM : 0 < M := mul_pos (paddingTiltNormalizer_pos Q) (by linarith)
  have hmS : M / 2 ≤ S₀ := hmass.2
  have hS₀ : 0 < S₀ := (half_pos hM).trans_le hmS
  let raw := ∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j) F G (N j)
  let retained := ∑ j ∈ bins,
    v j * canonicalComplexPrefix h E W L (eligible j) hL hWone hE F G (N j)
  let cost := fun site => canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * J))
    hL hWone hE bins (fun d => Real.log d) eligible site (fun _ => 1) N
  have hret : ‖retained‖ / S₀ ≤ Cs * η :=
    hs hL eligible he hpos hbin F G hF hG N v (hN' As (by dsimp only [A]; omega)) hv
  have hdelete : ‖raw - retained‖ ≤ cost (fun _ _ _ => 0) +
      cost (fun _ d q => (h * q * d : ℕ)) :=
    canonical_complex_weighted_correlation_deletion h E W L η hL hWone hE bins
      (fun d => Real.log d) eligible N v F G hF hG hbin hv
  have hc (site : ℤ → ℕ → ℕ → ℤ) : cost site / M ≤ (Cd + 4) * η := by
    have hx := hd hL η (Real.exp (4 * J)) hη hηone (Real.exp_pos _) bins
      (fun d => Real.log d) eligible
      (paddingBinIndices_card_polynomial L W hlarge hWone) he hbin site (fun _ => 1) N
      (hN' Ad (by dsimp only [A]; omega))
    exact hx.trans (quantitative_deletion_small L W Cd J hL hWone hCd.le
      (primeSupplyCount_final_budget L W hL hWone) hr)
  have hdel : ‖raw - retained‖ ≤ 2 * M * ((Cd + 4) * η) := by
    have h₁ := (div_le_iff₀ hM).mp (hc (fun _ _ _ => 0))
    have h₂ := (div_le_iff₀ hM).mp (hc (fun _ d q => (h * q * d : ℕ)))
    nlinarith
  have hrbound := (div_le_iff₀ hS₀).mp hret
  have hmb := mul_le_mul_of_nonneg_right (show M ≤ 2 * S₀ by linarith)
    (show 0 ≤ 2 * ((Cd + 4) * η) by positivity)
  apply (div_le_iff₀ hS₀).mpr
  have htri : ‖raw‖ ≤ ‖raw - retained‖ + ‖retained‖ := by
    simpa only [sub_add_cancel] using norm_add_le (raw - retained) retained
  change ‖raw‖ ≤ _
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalComplexLimits
namespace OAI

/-! The canonical graph and centering error scales tend to zero with fixed W. -/

namespace TwoPointCorrelations

open _root_.Filter
open scoped _root_.Topology

lemma canonical_eta_tendsto_zero (W : ℝ) (hW : 0 < W) :
    Tendsto (fun L : ℝ => Real.exp (-(primeSupplyCount W L : ℝ))) atTop (𝓝 0) := by
  have hp : 0 < 1 / (1200 * W) := by positivity
  have hb := (tendsto_rpow_neg_atTop hp).const_mul (Real.exp 1)
  simp only [mul_zero] at hb
  apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) _ hb
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact primeSupplyCount_saving L W hL hW

lemma canonical_complex_error_tendsto_zero (W Cg Cc : ℝ) (hW : 0 < W) :
    Tendsto (fun L : ℝ => Cg * Real.exp (-(primeSupplyCount W L : ℝ)) +
      2 * Cc * L ^ (-3 / 40 : ℝ)) atTop (𝓝 0) := by
  have h₁ := (canonical_eta_tendsto_zero W hW).const_mul Cg
  have h₂ := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 40 by norm_num)).const_mul (2 * Cc)
  simpa only [mul_zero, zero_add, neg_div] using h₁.add h₂

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedPairBins
namespace OAI

/-! Reindexing a selected numerical pair family into the literal graph bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selected_pair_bin_sum {M : Type*} [AddCommMonoid M]
    (D R : Finset ℕ) (A : Finset (ℕ × ℕ)) (hA : A ⊆ D ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (F : ℤ → ℕ → ℕ → M) :
    (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R,
      if (d, q) ∈ A ∧ b (d, q) = j then F j d q else 0) =
        ∑ dq ∈ A, F (b dq) dq.1 dq.2 := by
  rw [sum_comm]
  have he (d : ℕ) (q : ℕ) :
      (∑ j ∈ bins, if (d, q) ∈ A ∧ b (d, q) = j then F j d q else 0) =
        if (d, q) ∈ A then F (b (d, q)) d q else 0 := by
    by_cases hmem : (d, q) ∈ A
    · simp only [hmem, true_and]
      rw [sum_eq_single (b (d, q))]
      · simp
      · intro j _ hj
        rw [if_neg (Ne.symm hj)]
      · intro hn
        exact (hn (hb _ hmem)).elim
    · simp only [hmem, false_and, ite_false, sum_const_zero]
  calc
    _ = ∑ d ∈ D, ∑ q ∈ R, if (d, q) ∈ A then F (b (d, q)) d q else 0 := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      exact he d q
    _ = ∑ dq ∈ D ×ˢ R, if dq ∈ A then F (b dq) dq.1 dq.2 else 0 := by
      rw [sum_product]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext dq
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hA h, h⟩⟩

lemma selected_fullComplexBin_sum {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (F G : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    (∑ j ∈ bins, fullComplexBin P R
      (fun d q => (d, q) ∈ A ∧ b (d, q) = j) F G h (T j)) =
      ∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
        (positivePrefix (fun n => F ((dq.2 * dq.1) * n) *
          G ((dq.2 * dq.1) * (n + h)))
            (⌊T (b dq)⌋₊ / (dq.2 * dq.1)) / (T (b dq) : ℂ)) := by
  calc
    _ = ∑ j ∈ bins, ∑ d ∈ primeTupleDivisors P, ∑ q ∈ R,
        if (d, q) ∈ A ∧ b (d, q) = j then
          (actualPaddingCoefficient q : ℂ) *
            (positivePrefix (fun n => F ((q * d) * n) * G ((q * d) * (n + h)))
              (⌊T j⌋₊ / (q * d)) / (T j : ℂ)) else 0 := by
      apply sum_congr rfl
      intro j _
      rw [fullComplexBin_eq_dilated P hprime hdisjoint R
        hR, sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro q _
      by_cases hc : (d, q) ∈ A ∧ b (d, q) = j <;> simp [hc]
    _ = _ := selected_pair_bin_sum (primeTupleDivisors P) R
      A hA bins b hb _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedBinEligibility
namespace OAI

/-! A numerical phase selection gives an admissible graph eligibility in each
actual logarithmic bin, including the padding degree restriction. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma selectedPairBin_properties (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d)
    (hQ : ∀ p ∈ Q, p.Prime) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hη : 0 < η)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    {j : ℤ} {d q : ℕ} (he : selectedPairBin η A j d q) :
    0 < d ∧ 0 < q ∧ PaddingPairEligible L η d q ∧
      actualPaddingBin η (Real.log d) j q := by
  have hm := mem_filter.mp (hA he.1)
  have hd := (mem_product.mp hm.1).1
  have hq := (mem_product.mp hm.1).2
  have hdp := hD d hd
  have hqp := retainedPrimeDivisor_pos Q hQ hq
  refine ⟨hdp, hqp, hm.2, ?_⟩
  have hh := (paddingBin_eq_iff η 0 (Real.log (d * q : ℕ)) j hη).mp he.2
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdp.ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.ne'
  simpa only [actualPaddingBin, Nat.cast_mul, Real.log_mul hd0 hq0, add_zero,
    add_comm, zero_add] using hh

lemma selectedPairBin_index (D Q : Finset ℕ) (A : Finset (ℕ × ℕ)) (L η : ℝ)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    {dq : ℕ × ℕ} (hdq : dq ∈ A) :
    paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) ∈ paddingBinIndices L η :=
  (mem_filter.mp (hA hdq)).2.2

lemma selected_pairs_bounded_padding (D Q : Finset ℕ) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hL : 1 ≤ L)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η)) :
    A ⊆ D ×ˢ boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊ := by
  intro dq hdq
  have hm := mem_filter.mp (hA hdq)
  obtain ⟨hd, hq⟩ := mem_product.mp hm.1
  apply mem_product.mpr
  refine ⟨hd, mem_filter.mpr ⟨hq, ?_⟩⟩
  exact (Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))).mpr hm.2.1

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedRawComparison
namespace OAI

/-! The raw sum for a phase-selected pair family compares to one original
correlation, with its actual reciprocal prime cost and a finite boundary term. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma selectedRawMean_comparison {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ) (h : ℕ) (X η : ℝ)
    (hpos : ∀ dq ∈ A, 0 < dq.1 * dq.2) (hX : 0 < X) (hη : 0 ≤ η)
    (hlo : ∀ dq ∈ A, X * Real.exp (-η) ≤ T dq / (dq.1 * dq.2 : ℕ))
    (hhi : ∀ dq ∈ A, T dq / (dq.1 * dq.2 : ℕ) ≤ X) :
    ‖selectedRawMean A T f g h - selectedRawCoefficient A f g *
      (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ))‖ ≤
      ∑ dq ∈ A, actualPaddingCoefficient dq.2 *
        ((1 / (dq.1 * dq.2 : ℕ)) *
          ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
            4 * (dq.1 * dq.2).primeFactors.card / T dq) := by
  have he := weighted_dilated_correlation_comparison hfm hgm hf hg A
    (fun dq => actualPaddingCoefficient dq.2) (fun dq => dq.1 * dq.2)
    (fun dq => (dq.1 * dq.2).primeFactors) T h X η
    (fun dq _ => actualPaddingCoefficient_nonneg dq.2) hpos
    (fun dq _ _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun dq hd p hp hdiv => Nat.mem_primeFactors.mpr ⟨hp, hdiv, (hpos dq hd).ne'⟩)
    hX hη hlo hhi
  have hC : (∑ dq ∈ A, (actualPaddingCoefficient dq.2 : ℂ) *
      ((f (dq.1 * dq.2) * g (dq.1 * dq.2)) / ((dq.1 * dq.2 : ℕ) : ℂ))) =
        selectedRawCoefficient A f g := by
    unfold selectedRawCoefficient complexPairWeight actualPaddingCoefficient
    push_cast
    apply sum_congr rfl
    intro dq _
    ring
  simpa only [selectedRawMean, hC] using he

lemma selectedRawComparison_cost_bound (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ)
    (X η : ℝ) (hX : 0 < X) (hT : ∀ dq ∈ A, X ≤ T dq) :
    (∑ dq ∈ A, actualPaddingCoefficient dq.2 *
      ((1 / (dq.1 * dq.2 : ℕ)) *
        ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
          4 * (dq.1 * dq.2).primeFactors.card / T dq)) ≤
      4 * (∑ dq ∈ A, complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
      (2 * η + 1 / X) * (∑ dq ∈ A, complexPairWeight dq) +
      (∑ dq ∈ A, 4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X := by
  have hpoint (dq : ℕ × ℕ) (hd : dq ∈ A) :
      actualPaddingCoefficient dq.2 *
        ((1 / (dq.1 * dq.2 : ℕ)) *
          ((4 * (∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ))) + 2 * η + 1 / X) +
            4 * (dq.1 * dq.2).primeFactors.card / T dq) ≤
      4 * (complexPairWeight dq * ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
        (2 * η + 1 / X) * complexPairWeight dq +
          (4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X := by
    have hb := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤
        4 * (dq.1 * dq.2).primeFactors.card) hX (hT dq hd))
      (actualPaddingCoefficient_nonneg dq.2)
    unfold complexPairWeight actualPaddingCoefficient at *
    simp only [div_eq_mul_inv] at *
    nlinarith only [hb]
  calc
    _ ≤ ∑ dq ∈ A, (4 * (complexPairWeight dq *
        ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) +
        (2 * η + 1 / X) * complexPairWeight dq +
          (4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X) :=
      sum_le_sum hpoint
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, sum_div]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedCenteringIdentity
namespace OAI

/-! The selected raw sum is exactly the full-divisibility component of the
same centered graph bins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selectedRawMean_eq_full_bins {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (f g : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    selectedRawMean A (fun dq => T (b dq)) f g h =
      ∑ j ∈ bins, fullComplexBin P R
        (fun d q => (d, q) ∈ A ∧ b (d, q) = j) f g h (T j) := by
  rw [selected_fullComplexBin_sum P hprime hdisjoint R hR A hA bins b hb]
  unfold selectedRawMean
  apply sum_congr rfl
  intro dq _
  simp only [Nat.mul_comm dq.1 dq.2]

lemma selected_uncut_sub_raw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (f g : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    (∑ j ∈ bins, ((⌊T j⌋₊ : ℂ) / (T j : ℂ)) *
      untwistedUncutPrefix P R (fun d q => (d, q) ∈ A ∧ b (d, q) = j) h
        (fun _ _ _ => True) (fun n => f n.toNat) (fun n => g n.toNat) ⌊T j⌋₊) -
      selectedRawMean A (fun dq => T (b dq)) f g h =
        ∑ j ∈ bins, nonrawComplexBin P R
          (fun d q => (d, q) ∈ A ∧ b (d, q) = j) f g h (T j) := by
  rw [selectedRawMean_eq_full_bins P hprime hdisjoint R hR A hA bins b hb,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  exact weighted_complex_uncut_sub_full P hprime hdisjoint R _ f g h (T j)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedPairCosts
namespace OAI

/-! Passing the proved prime-cost moments to arbitrary selected pair subfamilies. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selected_pair_mass_le (D Q : Finset ℕ) (A : Finset (ℕ × ℕ))
    (L η : ℝ) (hη : 0 < η)
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η)) :
    (∑ dq ∈ A, complexPairWeight dq) ≤ totalPaddingBinMass D Q L η := by
  rw [← eligibleComplexPairs_mass D Q L η hη]
  exact sum_le_sum_of_subset_of_nonneg hA (fun dq _ _ => complexPairWeight_nonneg dq)



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedRawLowerBound
namespace OAI

/-! The raw lower bound for an actual phase-selected family. All losses are
the explicit prime-cost, logarithmic-bin and finite-prefix errors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selectedRawMean_lower_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (A : Finset (ℕ × ℕ)) (T : ℕ × ℕ → ℝ) (h : ℕ)
    (X η mass γ : ℝ) (hX : 0 < X) (hη : 0 ≤ η) (hmass : 0 ≤ mass) (hγ : 0 ≤ γ)
    (hpos : ∀ dq ∈ A, 0 < dq.1 * dq.2)
    (hlo : ∀ dq ∈ A, X * Real.exp (-η) ≤ T dq / (dq.1 * dq.2 : ℕ))
    (hhi : ∀ dq ∈ A, T dq / (dq.1 * dq.2 : ℕ) ≤ X)
    (hT : ∀ dq ∈ A, X ≤ T dq)
    (hweight : (∑ dq ∈ A, complexPairWeight dq) ≤ mass)
    (hphase : mass / 8 ≤ ‖selectedRawCoefficient A f g‖)
    (hcost : (∑ dq ∈ A, complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤ γ * mass / 128)
    (hsmall : η ≤ γ / 128)
    (hlong : (mass + ∑ dq ∈ A,
      4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card) / X ≤
        γ * mass / 64)
    (hbias : γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖) :
    γ * mass / 16 ≤ ‖selectedRawMean A T f g h‖ := by
  apply raw_norm_lower_bound _ (selectedRawCoefficient A f g)
    (positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)) mass γ
    hmass hγ hphase hbias
  have hc := (selectedRawMean_comparison hfm hgm hf hg A T h X η hpos hX hη hlo hhi).trans
    (selectedRawComparison_cost_bound A T X η hX hT)
  have hw := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ 2 * η + 1 / X by positivity)
  have he := mul_le_mul_of_nonneg_right hsmall hmass
  rw [add_div] at hlong
  simp only [div_eq_mul_inv] at hc hw he hcost hlong ⊢
  nlinarith only [hc, hw, he, hcost, hlong]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedRawBinsLower
namespace OAI

/-! The phase-selected raw lower bound holds at every sufficiently long
biased original cutoff, using exactly the graph's logarithmic bins. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

theorem selected_raw_bins_lower {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (A : Finset (ℕ × ℕ))
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    (h : ℕ) (hmass : 0 < totalPaddingBinMass D Q L η)
    (hphase : totalPaddingBinMass D Q L η / 8 ≤ ‖selectedRawCoefficient A f g‖)
    (hcost : (∑ dq ∈ A, complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
        γ * totalPaddingBinMass D Q L η / 128)
    (hsmall : η ≤ γ / 128) :
    ∀ᶠ X : ℝ in atTop,
      γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖ →
      γ * totalPaddingBinMass D Q L η / 16 ≤
        ‖selectedRawMean A (fun dq => X * Real.exp
          ((paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) : ℝ) * η)) f g h‖ := by
  let mass := totalPaddingBinMass D Q L η
  let K := mass + ∑ dq ∈ A,
    4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card
  have ht : Tendsto (fun X : ℝ => K / X) atTop (𝓝 0) := tendsto_id.const_div_atTop K
  have hε : 0 < γ * mass / 64 := by dsimp only [mass]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with X hlong hX
  intro hbias
  have hprop (dq : ℕ × ℕ) (hdq : dq ∈ A) :
      0 < dq.1 ∧ 0 < dq.2 ∧ PaddingPairEligible L η dq.1 dq.2 ∧
        actualPaddingBin η (Real.log dq.1)
          (paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ))) dq.2 :=
    selectedPairBin_properties D Q hD hQ A L η hη hA ⟨hdq, rfl⟩
  apply selectedRawMean_lower_bound hfm hgm hf hg A _ h X η mass γ hX hη.le hmass.le hγ.le
    (fun dq hdq => Nat.mul_pos (hprop dq hdq).1 (hprop dq hdq).2.1)
    (fun dq hdq => (actualPaddingBin_cutoff dq.1 dq.2 (hprop dq hdq).1
      (hprop dq hdq).2.1 η X hX _ (hprop dq hdq).2.2.2).1)
    (fun dq hdq => (actualPaddingBin_cutoff dq.1 dq.2 (hprop dq hdq).1
      (hprop dq hdq).2.1 η X hX _ (hprop dq hdq).2.2.2).2)
    _ (selected_pair_mass_le D Q A L η hη hA) hphase hcost hsmall hlong.le hbias
  intro dq hdq
  have hi := (mem_paddingBinIndices_iff L η _ hη).mp
    (selectedPairBin_index D Q A L η hA hdq)
  have hiR : (0 : ℝ) ≤ paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) := by
    exact_mod_cast hi.1
  exact le_mul_of_one_le_right hX.le (Real.one_le_exp (mul_nonneg hiR hη.le))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ConditionalComplexCore
namespace OAI

/-! Conditional ordinary two-point cancellation. The only hypotheses beyond
the original multiplicative functions are the four cited published inputs. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

theorem conditional_complex_positive_core (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  have hfb : OneBounded f := fun n _ => hf n
  have hgb : OneBounded g := fun n _ => hg n
  by_contra hn
  have hfail : ¬∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ < ε := by
    intro hall
    apply hn
    rw [Metric.tendsto_nhds]
    simpa only [dist_zero_right] using hall
  push Not at hfail
  obtain ⟨γ, hγ, hfreq⟩ := hfail
  obtain ⟨hsf, hsg⟩ := persistent_correlation_prime_defects hfm hgm hfb hgb h hn
  obtain ⟨hf1, hg1⟩ := persistent_correlation_one_values hfm hgm h hn
  obtain ⟨Ag, W, hAg, hW, hgraph⟩ := complex_graph_fixed_scale hP hBr
  have hWone : 1 ≤ W := by linarith
  have hWp : 0 < W := by linarith
  obtain ⟨E, hE, hselect⟩ := canonical_raw_pair_selection hP hfm hgm hf1 hg1 hfb hgb
    hsf hsg h hh W γ hWone hγ
  obtain ⟨Cg, hCg, hgraph⟩ := hgraph h hh E hE
  obtain ⟨Cc, hCc, hcenter⟩ := qualitative_canonical_nonraw_total hP hM hMRT
    hfm hgm hfb hgb hnp h hh E W hWone
  have hηsmall := (canonical_eta_tendsto_zero W hWp).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < γ / 128))
  have herrors := (canonical_complex_error_tendsto_zero W Cg Cc hWp).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < γ / 16))
  obtain ⟨L, hgraphL, hcenterL, hselectL, hmassL, hηL, herrL, hLlarge⟩ :=
    (hgraph.and (hcenter.and (hselect.and
      ((hP.eventually_canonical_retained_mass E W hWone).and
        (hηsmall.and (herrors.and (eventually_ge_atTop (2 : ℝ)))))))).exists
  have hL : 1 ≤ L := by linarith
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let S₀ := totalPaddingBinMass D Q L η
  let M := paddingTiltNormalizer Q * ∏ j, primeHarmonicMass (P j)
  let bins := paddingBinIndices L η
  have hη : 0 < η := Real.exp_pos _
  obtain ⟨hS₀, A, hA, hphase, hweight, hcost⟩ := hselectL hL η hη
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j k, k ≠ j → Disjoint (P j) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hWone)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd'
    exact Nat.pos_of_ne_zero (primeTupleDivisors_arithmetic P hp hd hd').1.ne_zero
  have hR : ∀ q ∈ R, 0 < q := fun q hq' => retainedPrimeDivisor_pos Q hq (mem_filter.mp hq').1
  let b := fun dq : ℕ × ℕ => paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ))
  let eligible := selectedPairBin η A
  have hAb : A ⊆ D ×ˢ R := selected_pairs_bounded_padding D Q A L η hL hA
  have hb : ∀ dq ∈ A, b dq ∈ bins := fun _ hdq => selectedPairBin_index D Q A L η hA hdq
  have hprop (j : ℤ) (d q : ℕ) (he : eligible j d q) :=
    selectedPairBin_properties D Q hD hq A L η hη hA he
  have he : ∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q :=
    fun j _ d q he => (hprop j d q he).2.2.1
  have hpos : ∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q :=
    fun j _ d q he => ⟨(hprop j d q he).1, (hprop j d q he).2.1⟩
  have hbin : ∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q :=
    fun j _ d q he => (hprop j d q he).2.2.2
  have hlower := selected_raw_bins_lower hfm hgm hfb hgb D Q hD hq L η γ hη hγ
    A hA h hS₀ hphase hcost hηL.le
  have hcent := hcenterL R (filter_subset _ _)
  have hlarge : ∀ᶠ X : ℝ in atTop, Real.exp (L ^ Ag) ≤ X := eventually_ge_atTop _
  have hevent : ∀ᶠ X : ℝ in atTop,
      γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖ → False := by
    filter_upwards [hlower, hcent, hlarge] with X hlower hcent hX
    intro hbiased
    have hXp : 0 < X := (Real.exp_pos _).trans_le hX
    let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
    let N := fun j : ℤ => ⌊T j⌋₊
    let v := fun j : ℤ => (N j : ℂ) / (T j : ℂ)
    let raw := ∑ j ∈ bins, v j * canonicalComplexUncutPrefix h E W L (eligible j)
      (fun n => f n.toNat) (fun n => g n.toNat) (N j)
    let full := selectedRawMean A (fun dq => T (b dq)) f g h
    have hv : ∀ j ∈ bins, ‖v j‖ ≤ 1 := fun j _ =>
      floor_cutoff_weight_norm_le (T j) (mul_pos hXp (Real.exp_pos _))
    have hN : ∀ j ∈ bins, Real.exp (L ^ Ag / 2) ≤ (N j : ℝ) := fun j hj =>
      (final_bin_windows L X η Ag hLlarge hAg hX hη j hj).2
    have hupper : ‖raw‖ / S₀ ≤ Cg * η :=
      hgraphL hL eligible he hpos hbin (fun n => f n.toNat) (fun n => g n.toNat)
        (fun n => hf n.toNat) (fun n => hg n.toNat) N v hN hv
    have hid : raw - full = ∑ j ∈ bins, nonrawComplexBin P R (eligible j) f g h (T j) :=
      selected_uncut_sub_raw P hp hd R hR A hAb bins b hb f g h T
    have hcerr : ‖raw - full‖ ≤ Cc * L ^ (-3 / 40 : ℝ) * M := by
      rw [hid]
      simpa only [one_mul, M, mul_assoc] using
        hcent eligible (fun _ => (1 : ℂ)) hbin (fun _ _ => by norm_num)
    have hmS : M / 2 ≤ S₀ := (hmassL hL η hη).2
    have hCm := mul_le_mul_of_nonneg_left (show M ≤ 2 * S₀ by linarith)
      (show 0 ≤ Cc * L ^ (-3 / 40 : ℝ) by positivity)
    have hgnum := (div_le_iff₀ hS₀).mp hupper
    have hl := hlower hbiased
    change γ * S₀ / 16 ≤ ‖full‖ at hl
    have htri : ‖full‖ ≤ ‖raw‖ + ‖raw - full‖ := by
      calc
        _ = ‖raw - (raw - full)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hstrict := mul_lt_mul_of_pos_right herrL hS₀
    nlinarith
  have heventN := tendsto_natCast_atTop_atTop.eventually hevent
  have hbad : ∀ᶠ N : ℕ in atTop,
      ¬γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ := by
    filter_upwards [heventN] with N hN
    simpa only [Nat.floor_natCast, Complex.ofReal_natCast] using hN
  exact hfreq hbad

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ConditionalElliott
namespace OAI

/-! Theorem 1.2 and Corollary 1.3 of the manuscript, conditionally on the
explicit published short-sum, prime-distribution and circuit inputs. -/

namespace TwoPointCorrelations

theorem conditional_unshiftedCorrectedElliott (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : UnshiftedCorrectedElliott := by
  intro f g hfm hgm hf hg hnp h hh
  have hnp' : UniformlyNonpretentious (positiveNormalization f) ∨
      UniformlyNonpretentious (positiveNormalization g) :=
    hnp.imp (fun hn => hn.positiveNormalization hf) (fun hn => hn.positiveNormalization hg)
  have hc := conditional_complex_positive_core hP hBr hM hMRT
    hfm.positiveNormalization hgm.positiveNormalization
    (positiveNormalization_norm hf) (positiveNormalization_norm hg) hnp' h hh
  simpa only [positiveNormalization_prefix, correlationSum_eq_positivePrefix] using hc

theorem conditional_binaryCorrectedElliott_oai (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) : BinaryCorrectedElliott :=
  (conditional_unshiftedCorrectedElliott hP hBr hM hMRT).binary


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.conditional_binaryCorrectedElliott_oai := @OAI.TwoPointCorrelations.conditional_binaryCorrectedElliott_oai
