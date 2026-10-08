-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_prohibited_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:26:47.405029+00:00
-- url     : https://prove2.me/submissions/b18543d3-85da-4587-837f-9f65fa32ee04

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset


/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

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

open _root_.Finset hiding sum_le_sum_of_injOn


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









lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num

lemma probability_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.probability E ≤ 1 := by
  classical
  apply (μ.average_mono (g := fun _ => 1) ?_).trans_eq (μ.average_const 1)
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

open _root_.Finset hiding sum_le_sum_of_injOn

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw

omit [DecidableEq A] in
lemma average_const_mul (μ : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    μ.average (fun x => c * f x) = c * μ.average f := by
  simp only [average, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  ring










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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw
namespace OAI

/-! Restore the harmonic mass after using the normalized prime law. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical




variable {α : Type*} [Fintype α] [DecidableEq α]

lemma primeReciprocalLaw_mass_product (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (x : α → P) :
    primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).weight x =
      ∏ z, ((x z).val : ℝ)⁻¹ := by
  change primeHarmonicMass P ^ Fintype.card α *
    (∏ z, ((x z).val : ℝ)⁻¹ / primeHarmonicMass P) = _
  rw [prod_div_distrib]
  simp only [prod_const, card_univ]
  exact mul_div_cancel₀ _ (pow_ne_zero _ hV.ne')

/-- Every abstract label keeps its reciprocal factor, even when distinct
labels receive the same numerical prime. -/
lemma primeReciprocalLaw_restore (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) =
      primeHarmonicMass P ^ Fintype.card α *
        (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E := by
  classical
  simp only [FiniteLaw.probability, FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : E x
  · simp only [hx, ite_true, mul_one]
    exact (primeReciprocalLaw_mass_product P hV x).symm
  · simp only [hx, ite_false, mul_zero]

lemma primeReciprocalLaw_restore_bound (P : Finset ℕ) (hV : 0 < primeHarmonicMass P)
    (E : (α → P) → Prop) (B : ℝ)
    (hB : (FiniteLaw.independent (fun _ : α => primeReciprocalLaw P hV)).probability E ≤ B) :
    (∑ x : α → P, if E x then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card α * B := by
  rw [primeReciprocalLaw_restore P hV E]
  exact mul_le_mul_of_nonneg_left hB (pow_nonneg hV.le _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalProgressions
namespace OAI

/-! Reciprocal savings for one prime variable in a nondegenerate congruence. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

/-- A finite subset of one residue class has at most one exceptional initial
term; every subsequent reciprocal is bounded by a harmonic term divided by
the modulus. The set may consist only of primes or satisfy extra restrictions. -/
theorem reciprocal_congruence_sum (S : Finset ℕ) (H N p : ℕ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : 0 < p)
    (hlower : ∀ x ∈ S, H ≤ x) (hupper : ∀ x ∈ S, x ≤ N)
    (hcongruent : ∀ x ∈ S, ∀ y ∈ S, Nat.ModEq p x y) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  classical
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := min'_mem S hS
    let R := S.erase a
    let k : ℕ → ℕ := fun x => (x - a) / p
    have hkprod (x : ℕ) (hx : x ∈ R) : p * k x = x - a := by
      exact Nat.mul_div_cancel' ((hcongruent a ha x (mem_erase.mp hx).2).dvd')
    have hkpositive (x : ℕ) (hx : x ∈ R) : 0 < k x := by
      have hax := min'_le S x (mem_erase.mp hx).2
      have hne := (mem_erase.mp hx).1
      have hprod := hkprod x hx
      by_contra hn
      have hz : k x = 0 := by omega
      rw [hz, mul_zero] at hprod
      omega
    have hkupper (x : ℕ) (hx : x ∈ R) : k x ≤ N :=
      (Nat.div_le_self (x - a) p).trans ((Nat.sub_le x a).trans (hupper x (mem_erase.mp hx).2))
    have hkinj : Set.InjOn k R := by
      intro x hx y hy heq
      have hxprod := hkprod x hx
      have hyprod := hkprod y hy
      have hax := min'_le S x (mem_erase.mp hx).2
      have hay := min'_le S y (mem_erase.mp hy).2
      rw [heq] at hxprod
      omega
    have hweight (x : ℕ) (hx : x ∈ R) :
        (x : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * (k x : ℝ)⁻¹ := by
      have hprod : (p : ℝ) * (k x : ℝ) ≤ x := by
        exact_mod_cast (show p * k x ≤ x by rw [hkprod x hx]; exact Nat.sub_le _ _)
      have hpos : 0 < (p : ℝ) * (k x : ℝ) := by
        exact mul_pos (by exact_mod_cast hp) (by exact_mod_cast hkpositive x hx)
      simpa only [mul_inv] using ((inv_le_inv₀ (lt_of_lt_of_le hpos hprod) hpos).mpr hprod)
    have hsubset : R.image k ⊆ Icc 1 N := by
      intro j hj
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨hkpositive x hx, hkupper x hx⟩
    have hrest : ∑ x ∈ R, (x : ℝ)⁻¹ ≤ (1 + Real.log N) / p := by
      calc
        _ ≤ ∑ x ∈ R, (p : ℝ)⁻¹ * (k x : ℝ)⁻¹ := sum_le_sum hweight
        _ = ∑ j ∈ R.image k, (p : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
          rw [sum_image hkinj]
        _ ≤ ∑ j ∈ Icc 1 N, (p : ℝ)⁻¹ * (j : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg hsubset
          intro j _ _
          positivity
        _ = (p : ℝ)⁻¹ * (harmonic N : ℝ) := by
          simp only [← mul_sum, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        _ ≤ (p : ℝ)⁻¹ * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)
        _ = (1 + Real.log N) / p := by rw [div_eq_mul_inv]; ring
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    have hHale : (H : ℝ) ≤ a := by exact_mod_cast hlower a ha
    have hfirst : (a : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ :=
      (inv_le_inv₀ (lt_of_lt_of_le hHreal hHale) hHreal).mpr hHale
    calc
      _ = (a : ℝ)⁻¹ + ∑ x ∈ R, (x : ℝ)⁻¹ := by
        rw [← sum_erase_add S (fun x : ℕ => (x : ℝ)⁻¹) ha]
        simp only [R]
        ring
      _ ≤ _ := add_le_add hfirst hrest
  · have hzero : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, sum_empty]
    positivity

/-- A congruence with a nonzero coefficient modulo a prime admits only one
residue class, without any assumption that a larger matrix is invertible. -/
lemma congruence_same_residue {p x y : ℕ} (hp : p.Prime) {A B : ℤ}
    (hA : ¬(p : ℤ) ∣ A)
    (hx : (p : ℤ) ∣ A * x + B) (hy : (p : ℤ) ∣ A * y + B) :
    Nat.ModEq p x y := by
  have hprime : Prime (p : ℤ) := Int.prime_ofNat_iff.mpr hp
  have hdiff : (p : ℤ) ∣ A * ((y : ℤ) - x) := by
    convert (preTransparency := .instances) hy.sub hx using 1
    ring
  exact Nat.modEq_iff_dvd.mpr ((hprime.dvd_mul.mp hdiff).resolve_left hA)

/-- The reciprocal saving used for each selected triangular relation. -/
theorem reciprocal_linear_congruence_sum (S : Finset ℕ) (H N p : ℕ) (A B : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime) (hA : ¬(p : ℤ) ∣ A)
    (hlower : ∀ x ∈ S, H ≤ x) (hupper : ∀ x ∈ S, x ≤ N)
    (hcongruence : ∀ x ∈ S, (p : ℤ) ∣ A * x + B) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  apply reciprocal_congruence_sum S H N p hH hN hp.pos hlower hupper
  intro x hx y hy
  exact congruence_same_residue hp hA (hcongruence x hx) (hcongruence y hy)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]

omit [Fintype ι] [Fintype A] in
lemma restoreCoordinate_update (i : ι) (a b : A) (y : {j : ι // j ≠ i} → A) :
    Function.update (restoreCoordinate i a y) i b = restoreCoordinate i b y := by
  funext j
  by_cases hj : j = i <;> simp [restoreCoordinate, hj]

namespace FiniteLaw

lemma independent_weight_restore (μ : ι → FiniteLaw A) (i : ι)
    (a : A) (y : {j : ι // j ≠ i} → A) :
    (independent μ).weight (restoreCoordinate i a y) =
      (μ i).weight a * (independent (fun j : {j : ι // j ≠ i} => μ j)).weight y := by
  change (∏ j, (μ j).weight (restoreCoordinate i a y j)) = _
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ i)]
  rw [restoreCoordinate_same]
  congr 1
  rw [Finset.prod_subtype (p := fun j : ι => j ≠ i) (univ \ {i}) (by intro j; simp)]
  apply prod_congr rfl
  intro j _
  rw [restoreCoordinate_other]

/-- Expose one original independent coordinate, keeping all other variables
fixed and retaining their original product law. -/
lemma independent_average_one_coordinate (μ : ι → FiniteLaw A) (i : ι)
    (F : (ι → A) → ℝ) :
    (independent μ).average F =
      (independent (fun j : {j : ι // j ≠ i} => μ j)).average (fun y =>
        (μ i).average (fun a => F (restoreCoordinate i a y))) := by
  let e := Equiv.funSplitAt i A
  have he (a : A) (y : {j : ι // j ≠ i} → A) : e.symm (a, y) = restoreCoordinate i a y := by
    funext j
    by_cases hj : j = i <;> simp [e, Equiv.funSplitAt, Equiv.piSplitAt, restoreCoordinate, hj]
  calc
    _ = ∑ z : A × ({j : ι // j ≠ i} → A),
        (independent μ).weight (restoreCoordinate i z.1 z.2) * F (restoreCoordinate i z.1 z.2) := by
      simpa only [he, average] using (e.symm.sum_comp (fun x => (independent μ).weight x * F x)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_restore, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro a _
      ring

/-- One elimination step. All retained events ignore the variable being
summed; only its own event is charged its conditional probability bound. -/
theorem eliminate_coordinate [Nonempty A] (μ : ι → FiniteLaw A) (i : ι)
    (E F : (ι → A) → Prop) (δ : ℝ)
    (hE : ∀ x a, E (Function.update x i a) ↔ E x)
    (hF : ∀ x, (μ i).probability (fun a => F (Function.update x i a)) ≤ δ) :
    (independent μ).probability (fun x => E x ∧ F x) ≤
      δ * (independent μ).probability E := by
  classical
  let a₀ : A := Classical.choice inferInstance
  let ν := independent (fun j : {j : ι // j ≠ i} => μ j)
  have hE' (y : {j : ι // j ≠ i} → A) (a : A) :
      E (restoreCoordinate i a y) ↔ E (restoreCoordinate i a₀ y) := by
    simpa only [restoreCoordinate_update] using hE (restoreCoordinate i a₀ y) a
  have hF' (y : {j : ι // j ≠ i} → A) :
      (μ i).probability (fun a => F (restoreCoordinate i a y)) ≤ δ := by
    simpa only [restoreCoordinate_update] using hF (restoreCoordinate i a₀ y)
  have hrest : (independent μ).probability E =
      ν.average (fun y => if E (restoreCoordinate i a₀ y) then 1 else 0) := by
    rw [probability, independent_average_one_coordinate μ i]
    apply congrArg ν.average
    funext y
    simp only [hE']
    exact (μ i).average_const _
  rw [hrest, ← average_const_mul]
  unfold probability
  rw [independent_average_one_coordinate μ i]
  apply ν.average_mono
  intro y
  by_cases hy : E (restoreCoordinate i a₀ y)
  · simpa only [probability, hE', hy, true_and, ite_true, mul_one] using hF' y
  · simp only [hE', hy, false_and, ite_false, average_const, mul_zero]
    exact le_rfl


end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeRelations
namespace OAI

/-!
# Exact prime-variable relations

A monomial has one factor for each distinct label in a squarefree tuple.
Its integer coefficient contains the orientation, common shift multiplier,
and padding. Numerical coincidences among different labels are allowed.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


namespace PrimeMonomial

variable {ι : Type*} [DecidableEq ι]




lemma eval_affine (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    m.eval x = x i * m.coefficientAt i x + m.constantAt i x := by
  by_cases hi : i ∈ m.labels
  · simp only [eval, coefficientAt, constantAt, hi, ite_true, add_zero]
    rw [← Finset.mul_prod_erase m.labels x hi]
    ring
  · simp only [coefficientAt, constantAt, hi, ite_false, mul_zero, zero_add]

lemma eval_update_of_not_mem (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ)
    (hi : i ∉ m.labels) : m.eval (Function.update x i a) = m.eval x := by
  unfold eval
  congr 1
  apply prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [hji]

lemma coefficientAt_update_self (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ) :
    m.coefficientAt i (Function.update x i a) = m.coefficientAt i x := by
  unfold coefficientAt
  split
  · congr 1
    apply prod_congr rfl
    intro j hj
    simp [(mem_erase.mp hj).1]
  · rfl

lemma constantAt_update_self (m : PrimeMonomial ι) (i : ι) (x : ι → ℤ) (a : ℤ) :
    m.constantAt i (Function.update x i a) = m.constantAt i x := by
  unfold constantAt
  split
  · rfl
  · exact m.eval_update_of_not_mem i x a ‹i ∉ m.labels›

lemma coefficientAt_update_of_not_mem (m : PrimeMonomial ι) (i j : ι)
    (x : ι → ℤ) (a : ℤ) (hj : j ∉ m.labels) :
    m.coefficientAt i (Function.update x j a) = m.coefficientAt i x := by
  unfold coefficientAt
  split
  · congr 1
    apply prod_congr rfl
    intro k hk
    have hkj : k ≠ j := fun h => hj (h ▸ (mem_erase.mp hk).2)
    simp [hkj]
  · rfl

end PrimeMonomial

variable {ι τ : Type*} [DecidableEq ι] [Fintype τ]






lemma primeRelation_affine (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    primeRelationEval m x = x i * primeRelationCoefficient m i x + primeRelationConstant m i x := by
  unfold primeRelationEval primeRelationCoefficient primeRelationConstant
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  exact (m t).eval_affine i x

lemma primeRelation_contribution_eq (m : τ → PrimeMonomial ι) (i : ι) (x : ι → ℤ) :
    primeRelationContribution m i x = x i * primeRelationCoefficient m i x := by
  unfold primeRelationContribution primeRelationCoefficient
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  by_cases hi : i ∈ (m t).labels
  · rw [if_pos hi, (m t).eval_affine i x]
    simp only [PrimeMonomial.constantAt, hi, ite_true, add_zero]
  · simp only [hi, ite_false, PrimeMonomial.coefficientAt, mul_zero]

lemma primeRelation_coefficient_update_self (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationCoefficient m i (Function.update x i a) = primeRelationCoefficient m i x := by
  unfold primeRelationCoefficient
  exact sum_congr rfl (fun t _ => (m t).coefficientAt_update_self i x a)

lemma primeRelation_constant_update_self (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationConstant m i (Function.update x i a) = primeRelationConstant m i x := by
  unfold primeRelationConstant
  exact sum_congr rfl (fun t _ => (m t).constantAt_update_self i x a)

lemma primeRelation_update_affine (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) :
    primeRelationEval m (Function.update x i a) =
      a * primeRelationCoefficient m i x + primeRelationConstant m i x := by
  rw [primeRelation_affine m i, Function.update_self,
    primeRelation_coefficient_update_self, primeRelation_constant_update_self]

lemma primeRelation_update_of_not_mem (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (a : ℤ) (hi : i ∉ primeRelationSupport m) :
    primeRelationEval m (Function.update x i a) = primeRelationEval m x := by
  unfold primeRelationEval
  apply sum_congr rfl
  intro t _
  apply (m t).eval_update_of_not_mem
  exact fun hit => hi (mem_biUnion.mpr ⟨t, mem_univ _, hit⟩)

lemma primeRelation_coefficient_update_of_not_mem (m : τ → PrimeMonomial ι)
    (i j : ι) (x : ι → ℤ) (a : ℤ) (hj : j ∉ primeRelationSupport m) :
    primeRelationCoefficient m i (Function.update x j a) = primeRelationCoefficient m i x := by
  unfold primeRelationCoefficient
  apply sum_congr rfl
  intro t _
  apply (m t).coefficientAt_update_of_not_mem
  exact fun hjt => hj (mem_biUnion.mpr ⟨t, mem_univ _, hjt⟩)

/-- Retaining the nonzero-contribution test gives precisely the coefficient
condition needed for a single-prime reciprocal saving. -/
lemma primeRelation_coefficient_nondegenerate (m : τ → PrimeMonomial ι)
    (i : ι) (x : ι → ℤ) (p : ℤ)
    (hnonzero : ¬p ∣ primeRelationContribution m i x) :
    ¬p ∣ primeRelationCoefficient m i x := by
  intro hd
  apply hnonzero
  rw [primeRelation_contribution_eq]
  exact hd.mul_left (x i)


lemma primeRelationEvent_update (m : τ → PrimeMonomial ι) (selected control j : ι)
    (x : ι → ℤ) (a : ℤ) (hj : j ∉ primeRelationSupport m) (hjc : control ≠ j) :
    primeRelationEvent m selected control (Function.update x j a) ↔
      primeRelationEvent m selected control x := by
  unfold primeRelationEvent
  rw [Function.update_of_ne hjc, primeRelation_update_of_not_mem m j x a hj,
    primeRelation_coefficient_update_of_not_mem m selected j x a hj]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalSampling
namespace OAI

/-! Reciprocal-weighted prime sampling and concrete triangular relation bounds. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

namespace FiniteLaw

variable {A : Type*} [Fintype A]

/-- A reciprocal atom majorant transfers the finite progression bound to
sampling probability. For the normalized law `1/(Vp)`, it suffices that
`V ≥ 1`, exactly as in the singleton argument. -/
theorem reciprocal_probability_bound (μ : FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N p : ℕ) (C D : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime) (hC : ¬(p : ℤ) ∣ C)
    (hlo : ∀ a, H ≤ value a) (hhi : ∀ a, value a ≤ N)
    (hweight : ∀ a, μ.weight a ≤ (value a : ℝ)⁻¹)
    (E : A → Prop) (hE : ∀ a, E a → (p : ℤ) ∣ C * value a + D) :
    μ.probability E ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  classical
  let S : Finset A := univ.filter E
  let T : Finset ℕ := S.image value
  have hprob : μ.probability E = ∑ a ∈ S, μ.weight a := by
    simp only [probability, average, S, sum_filter, mul_ite, mul_one, mul_zero]
  have himage : (∑ a ∈ S, (value a : ℝ)⁻¹) = ∑ x ∈ T, (x : ℝ)⁻¹ := by
    dsimp [T]
    rw [sum_image (fun a _ b _ hab => hinj hab)]
  rw [hprob]
  apply (sum_le_sum (fun a _ => hweight a)).trans
  rw [himage]
  apply reciprocal_linear_congruence_sum T H N p C D hH hN hp hC
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact hlo a
  · intro x hx
    obtain ⟨a, _, rfl⟩ := mem_image.mp hx
    exact hhi a
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact hE a (mem_filter.mp ha).2

/-- Retain the coefficient test during summation. A vanishing coefficient
makes the event empty and costs zero, so no case is lost by resampling. -/
theorem nondegenerate_reciprocal_probability_bound (μ : FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N p : ℕ) (C D : ℤ)
    (hH : 0 < H) (hN : 1 ≤ N) (hp : p.Prime)
    (hlo : ∀ a, H ≤ value a) (hhi : ∀ a, value a ≤ N)
    (hweight : ∀ a, μ.weight a ≤ (value a : ℝ)⁻¹) :
    μ.probability (fun a => (p : ℤ) ∣ C * value a + D ∧ ¬(p : ℤ) ∣ C) ≤
      (H : ℝ)⁻¹ + (1 + Real.log N) / p := by
  by_cases hC : (p : ℤ) ∣ C
  · have hzero : μ.probability (fun a => (p : ℤ) ∣ C * value a + D ∧ ¬(p : ℤ) ∣ C) = 0 := by
      simp [probability, average, hC]
    rw [hzero]
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  · exact reciprocal_probability_bound μ value hinj H N p C D hH hN hp hC hlo hhi hweight
      _ (fun _ ha => ha.1)

end FiniteLaw

variable {ι A : Type*} [DecidableEq ι]


lemma integerPrimeAssignment_update (value : A → ℕ) (x : ι → A) (i : ι) (a : A) :
    integerPrimeAssignment value (Function.update x i a) =
      Function.update (integerPrimeAssignment value x) i (value a) := by
  funext j
  by_cases hji : j = i <;> simp [integerPrimeAssignment, hji]

/-- At a selected coordinate, the concrete monomial event is precisely a
single nondegenerate linear congruence with all remaining variables fixed. -/
lemma primeRelationEvent_update_selected {τ : Type*} [Fintype τ]
    (m : τ → PrimeMonomial ι) (selected control : ι) (hne : control ≠ selected)
    (value : A → ℕ) (x : ι → A) (a : A) :
    primeRelationEvent m selected control
        (integerPrimeAssignment value (Function.update x selected a)) ↔
      (value (x control) : ℤ) ∣
          primeRelationCoefficient m selected (integerPrimeAssignment value x) * value a +
          primeRelationConstant m selected (integerPrimeAssignment value x) ∧
        ¬(value (x control) : ℤ) ∣
          primeRelationCoefficient m selected (integerPrimeAssignment value x) := by
  rw [integerPrimeAssignment_update]
  unfold primeRelationEvent
  rw [Function.update_of_ne hne, primeRelation_update_affine,
    primeRelation_coefficient_update_self]
  simp only [integerPrimeAssignment]
  rw [mul_comm (value a : ℤ)]

/-- The pointwise support exclusion proved for the witness ordering is the
exact update invariance required by finite triangular elimination. -/
lemma primeRelationEvent_update_irrelevant {τ : Type*} [Fintype τ]
    (m : τ → PrimeMonomial ι) (selected control j : ι)
    (value : A → ℕ) (x : ι → A) (a : A)
    (hj : j ∉ primeRelationSupport m) (hjc : control ≠ j) :
    primeRelationEvent m selected control (integerPrimeAssignment value (Function.update x j a)) ↔
      primeRelationEvent m selected control (integerPrimeAssignment value x) := by
  rw [integerPrimeAssignment_update]
  exact primeRelationEvent_update m selected control j _ _ hj hjc

namespace FiniteLaw


end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OrderedElimination
namespace OAI

/-! Eliminate labels in the order of witness records, independently of label names. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

namespace FiniteLaw

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- The order belongs to the relation records. The ambient prime labels
need no compatible order and all unselected coordinates keep their law. -/
theorem ordered_coordinate_probability_bound {κ : Type*} [LinearOrder κ]
    [Nonempty A] (coordinate : κ → ι)
    (μ : ι → FiniteLaw A) (E : κ → (ι → A) → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (R : Finset κ)
    (hdepends : ∀ i ∈ R, ∀ j ∈ R, i < j → ∀ x a,
      E i (Function.update x (coordinate j) a) ↔ E i x)
    (hconditional : ∀ i ∈ R, ∀ x,
      (μ (coordinate i)).probability (fun a => E i (Function.update x (coordinate i) a)) ≤ δ) :
    (independent μ).probability (fun x => ∀ i ∈ R, E i x) ≤ δ ^ R.card := by
  classical
  revert hdepends hconditional
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    intro hdepends hconditional
    by_cases hR : R.Nonempty
    · let i := R.max' hR
      have hi : i ∈ R := max'_mem R hR
      have hjlt (j : κ) (hj : j ∈ R.erase i) : j < i := by
        have hjR := (mem_erase.mp hj).2
        have hji := (mem_erase.mp hj).1
        exact lt_of_le_of_ne (le_max' R j hjR) hji
      have hretained : ∀ x a,
          (∀ j ∈ R.erase i, E j (Function.update x (coordinate i) a)) ↔ ∀ j ∈ R.erase i, E j x := by
        intro x a
        constructor <;> intro hx j hj
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mp (hx j hj)
        · exact (hdepends j (mem_erase.mp hj).2 i hi (hjlt j hj) x a).mpr (hx j hj)
      have hstep := eliminate_coordinate μ (coordinate i) (fun x => ∀ j ∈ R.erase i, E j x)
        (E i) δ hretained (hconditional i hi)
      have hevent : (fun x => ∀ j ∈ R, E j x) =
          (fun x => (∀ j ∈ R.erase i, E j x) ∧ E i x) := by
        funext x
        apply propext
        constructor
        · intro hx
          exact ⟨fun j hj => hx j (mem_erase.mp hj).2, hx i hi⟩
        · rintro ⟨hx, hxi⟩ j hj
          by_cases hji : j = i
          · simpa only [hji] using hxi
          · exact hx j (mem_erase.mpr ⟨hji, hj⟩)
      rw [hevent]
      apply hstep.trans
      have hrest := ih (R.erase i) (Finset.erase_ssubset hi)
        (fun j hj k hk hjk x a => hdepends j (mem_erase.mp hj).2 k (mem_erase.mp hk).2 hjk x a)
        (fun j hj => hconditional j (mem_erase.mp hj).2)
      have hmul := mul_le_mul_of_nonneg_left hrest hδ
      have hcard : R.card = (R.erase i).card + 1 := by
        rw [card_erase_of_mem hi]
        have hpos := card_pos.mpr hR
        omega
      simpa only [hcard, pow_succ, mul_comm] using hmul
    · have hzero : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      rw [hzero, card_empty, pow_zero]
      exact probability_le_one _ _


/-- Ordered nondegenerate prime relations: selected coordinates can be
any labels in the ambient assignment, not necessarily an initial segment. -/
theorem ordered_prime_relation_probability {κ : Type*} [LinearOrder κ]
    (τ : κ → Type*) [∀ i, Fintype (τ i)]
    [Nonempty A] (μ : ι → FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hprime : ∀ a, (value a).Prime) (hlo : ∀ a, H ≤ value a)
    (hhi : ∀ a, value a ≤ N) (hweight : ∀ i a, (μ i).weight a ≤ (value a : ℝ)⁻¹)
    (m : (i : κ) → τ i → PrimeMonomial ι) (selected control : κ → ι) (R : Finset κ)
    (hcontrol : ∀ i ∈ R, control i ≠ selected i)
    (htriangular : ∀ i ∈ R, ∀ j ∈ R, i < j →
      selected j ∉ primeRelationSupport (m i) ∧ control i ≠ selected j) :
    (independent μ).probability (fun x => ∀ i ∈ R,
      primeRelationEvent (m i) (selected i) (control i) (integerPrimeAssignment value x)) ≤
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ R.card := by
  classical
  let E : κ → (ι → A) → Prop := fun i x =>
    primeRelationEvent (m i) (selected i) (control i) (integerPrimeAssignment value x)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  apply ordered_coordinate_probability_bound selected μ E _ (by positivity) R ?_ ?_
  · intro i hi j hj hij x a
    exact primeRelationEvent_update_irrelevant (m i) (selected i) (control i) (selected j)
      value x a (htriangular i hi j hj hij).1 (htriangular i hi j hj hij).2
  · intro i hi x
    have hlinear := nondegenerate_reciprocal_probability_bound (μ (selected i)) value hinj
      H N (value (x (control i)))
      (primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x))
      (primeRelationConstant (m i) (selected i) (integerPrimeAssignment value x))
      hH hN (hprime _) hlo hhi (hweight (selected i))
    have hevent : (fun a => E i (Function.update x (selected i) a)) =
        (fun a => (value (x (control i)) : ℤ) ∣
          primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x) * value a +
          primeRelationConstant (m i) (selected i) (integerPrimeAssignment value x) ∧
          ¬(value (x (control i)) : ℤ) ∣
            primeRelationCoefficient (m i) (selected i) (integerPrimeAssignment value x)) := by
      funext a
      exact propext (primeRelationEvent_update_selected (m i) (selected i) (control i)
        (hcontrol i hi) value x a)
    rw [hevent]
    apply hlinear.trans
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_left (by linarith) (by exact_mod_cast hH)
      (by exact_mod_cast hlo (x (control i)))

end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OrderedPrimeSystems
namespace OAI

/-! A finite ordered family packages the precise output of witness selection. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


attribute [instance] OrderedPrimeSystem.indexFintype OrderedPrimeSystem.indexOrder
  OrderedPrimeSystem.termFintype

namespace OrderedPrimeSystem

variable {ι : Type*} [DecidableEq ι]



/-- Each selected interval or comparison earns its own factor; every
unselected prime variable is averaged with its original product law. -/
theorem probability_bound [Fintype ι] {A : Type*} [Fintype A] [Nonempty A]
    (S : OrderedPrimeSystem ι) (μ : ι → FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hprime : ∀ a, (value a).Prime) (hlo : ∀ a, H ≤ value a)
    (hhi : ∀ a, value a ≤ N) (hweight : ∀ i a, (μ i).weight a ≤ (value a : ℝ)⁻¹) :
    (FiniteLaw.independent μ).probability (fun x => S.Holds (integerPrimeAssignment value x)) ≤
      ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ S.size := by
  simpa only [Holds, Finset.mem_univ, forall_true_left, card_univ, size] using
    FiniteLaw.ordered_prime_relation_probability S.Term μ value hinj H N hH hN hprime
      hlo hhi hweight S.relation S.selected S.control univ
      (fun i _ => S.control_ne i) (fun i _ j _ hij => S.triangular i j hij)

/-- The actual reciprocal sum for a fixed recorded system. Keeping the
nonzero coefficient tests in `Holds` makes every elimination valid after
resampling, including samples with coincident numerical primes. -/
theorem reciprocal_sum_bound [Fintype ι] (S : OrderedPrimeSystem ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ N) :
    (∑ x : ι → P, if S.Holds (integerPrimeAssignment Subtype.val x)
      then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ S.size := by
  classical
  have hVp : 0 < primeHarmonicMass P := lt_of_lt_of_le zero_lt_one hV
  have hPnonempty : Nonempty P := by
    have hPn : P.Nonempty := by
      by_contra hn
      have hpempty : P = ∅ := not_nonempty_iff_eq_empty.mp hn
      have hz : primeHarmonicMass P = 0 := by
        subst P
        simp [primeHarmonicMass]
      linarith
    obtain ⟨p, hp⟩ := hPn
    exact ⟨⟨p, hp⟩⟩
  have : Nonempty P := hPnonempty
  apply primeReciprocalLaw_restore_bound P hVp _ _
  apply S.probability_bound (fun _ => primeReciprocalLaw P hVp) Subtype.val
    Subtype.val_injective H N hH hN (fun p => hP p.val p.property)
    (fun p => hlo p.val p.property) (fun p => hhi p.val p.property)
  intro i p
  change (p.val : ℝ)⁻¹ / primeHarmonicMass P ≤ (p.val : ℝ)⁻¹
  exact div_le_self (by positivity) hV

end OrderedPrimeSystem

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


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

open _root_.Finset hiding sum_le_sum_of_injOn










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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {α : Type*} [DecidableEq α] {N : ℕ}




lemma columnRepresentative_mem (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    columnRepresentative label perfect i ∈ columnRepresentativeCandidates label perfect i :=
  min'_mem _ _

/-- A reference always carries the intended label. -/
theorem columnRepresentative_label (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    label (columnRepresentative label perfect i) = label i := by
  have hm := columnRepresentative_mem label perfect i
  dsimp only [columnRepresentativeCandidates] at hm
  split_ifs at hm <;> exact (mem_filter.mp hm).2



theorem columnRepresentative_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (i j : Fin N) : columnRepresentative label perfect i = columnRepresentative label perfect j ↔
      label i = label j := by
  constructor
  · intro h
    exact (columnRepresentative_label label perfect i).symm.trans
      ((congrArg label h).trans (columnRepresentative_label label perfect j))
  · intro h
    have hc : columnRepresentativeCandidates label perfect i =
        columnRepresentativeCandidates label perfect j := by
      simp only [columnRepresentativeCandidates, h]
    unfold columnRepresentative
    simp only [hc]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical






theorem card_crudeWordCode (R N D : ℕ) :
    Fintype.card (CrudeWordCode R N D) = 2 ^ R * (N ^ N * (D ^ N * 2 ^ N)) := by
  simp only [CrudeWordCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]



/-- A finite union bound for arbitrary events under the concrete finite law. -/
theorem FiniteLaw.probability_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (μ : FiniteLaw A) (E : I → A → Prop) :
    μ.probability (fun x => ∃ i, E i x) ≤ ∑ i, μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [← μ.average_sum]
  apply μ.average_mono
  intro x
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    simp only [if_pos (show ∃ j, E j x from ⟨i, hi⟩)]
    apply (le_trans ?_ (single_le_sum (f := fun i => if E i x then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)))
    simp [hi]
  · simp only [if_neg hx]
    exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)


lemma card_crudeWordCode_exp (R N D : ℕ) :
    (Fintype.card (CrudeWordCode R N D) : ℝ) ≤
      Real.exp (R * Real.log 2 + N * Real.log (N + 1) +
        N * Real.log (D + 1) + N * Real.log 2) := by
  have hp (n k : ℕ) : (n : ℝ) ^ k ≤ Real.exp ((k : ℝ) * Real.log (n + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k
  have htwo (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [card_crudeWordCode]
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ R * (Real.exp ((N : ℝ) * Real.log (N + 1)) *
        (Real.exp ((N : ℝ) * Real.log (D + 1)) * 2 ^ N)) := by
      gcongr
      · exact hp N N
      · exact hp D N
    _ = _ := by rw [htwo, htwo, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring


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

lemma divisor_dvd_displacement (h : ℕ) (a : SignedStep) : a.divisor ∣ a.displacement h := by
  refine ⟨(if a.forward then 1 else -1) * (h : ℤ), ?_⟩
  simp only [divisor, displacement]
  ring

@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl


/-- The exclusions on the common multiplier, padding, and tuple imply the
exact absence of this prime from the integer displacement. -/
lemma prime_not_dvd_displacement (h p : ℕ) (hp : p.Prime) (a : SignedStep)
    (hh : ¬p ∣ h) (hq : ¬p ∣ a.padding) (hd : ¬p ∣ a.tuple) :
    ¬(p : ℤ) ∣ a.displacement h := by
  have hn : ¬p ∣ h * a.padding * a.tuple := hp.not_dvd_mul (hp.not_dvd_mul hh hq) hd
  have hi : ¬(p : ℤ) ∣ ((h * a.padding * a.tuple : ℕ) : ℤ) := by exact_mod_cast hn
  rcases a with ⟨b, d, q⟩
  cases b <;> simpa [displacement, Int.natCast_mul, mul_assoc] using hi

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotCode
namespace OAI

/-! A complete equality-pattern code for tuple and padding prime occurrences. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


namespace PrimeSlotData

variable {R N : ℕ}





lemma code_class_eq_iff (a : PrimeSlotData R N) (i j : Fin N) :
    a.code.2.1 i = a.code.2.1 j ↔ a.prime i = a.prime j :=
  columnRepresentative_eq_iff a.prime ∅ i j

lemma code_class_prime (a : PrimeSlotData R N) (i : Fin N) :
    a.prime (a.code.2.1 i) = a.prime i :=
  columnRepresentative_label a.prime ∅ i

end PrimeSlotData

namespace CrudeWordCode

variable {R N : ℕ}





lemma primeData_encode (a : PrimeSlotData R N) :
    a.code.primeData (fun c => a.prime c.val) = a := by
  cases a with
  | mk forward row isPadding prime =>
      unfold primeData PrimeSlotData.code
      congr 1
      funext i
      exact columnRepresentative_label prime ∅ i

lemma numericalWord_encode (a : PrimeSlotData R N) :
    a.code.numericalWord (fun c => a.prime c.val) = a.word := by
  exact congrArg PrimeSlotData.word (primeData_encode a)


/-- Padding is reconstructed from the same prime classes as tuple factors,
so repetitions across steps never introduce new independent numerical choices. -/
lemma numericalWord_get (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) (i : Fin R) :
    (c.numericalWord value)[i.val]'(by rw [numericalWord_length]; exact i.isLt) =
      ⟨c.1 i,
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = false), value (c.classAt j),
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = true), value (c.classAt j)⟩ := by
  simp [numericalWord, PrimeSlotData.word, PrimeSlotData.factor, PrimeSlotData.slots, primeData]
  constructor <;> congr 1

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeSlots
namespace OAI

/-! Actual prime factors give a complete bounded-slot code for a numerical word. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

variable {R : ℕ}






theorem actualPrimeSlot_card_le (w : Fin R → SignedStep) (J M : ℕ)
    (hJ : ∀ i, (w i).tuple.primeFactors.card ≤ J)
    (hM : ∀ i, (w i).padding.primeFactors.card ≤ M) :
    Fintype.card (ActualPrimeSlot w) ≤ R * (J + M) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ i : Fin R, ((w i).tuple.primeFactors.card + (w i).padding.primeFactors.card) := by
      simp only [Fintype.card_sum, Fintype.card_coe]
    _ ≤ ∑ _i : Fin R, (J + M) := sum_le_sum (fun i _ => Nat.add_le_add (hJ i) (hM i))
    _ = _ := by simp



lemma actualSlot_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (∏ s : ActualPrimeSlot w,
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1) =
        if b then (w i).padding else (w i).tuple := by
  rw [Fintype.prod_sigma]
  rw [prod_eq_single i]
  · rw [Fintype.prod_sum_type]
    cases b
    · have hp := (Finset.prod_coe_sort (s := (w i).tuple.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree ht)
      simpa [actualSlotKind, actualSlotPrime] using hp
    · have hp := (Finset.prod_coe_sort (s := (w i).padding.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree hq)
      simpa [actualSlotKind, actualSlotPrime] using hp
  · intro j _ hji
    simp only [hji, false_and, ite_false, prod_const_one]
  · simp

lemma actualPrimeSlotData_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (actualPrimeSlotData w).factor i b = if b then (w i).padding else (w i).tuple := by
  have he := (actualPrimeSlotEquiv w).symm.prod_comp
    (fun s : ActualPrimeSlot w =>
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1)
  calc
    _ = ∏ s : ActualPrimeSlot w,
        if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1 := by
      unfold PrimeSlotData.factor PrimeSlotData.slots
      rw [prod_filter]
      refine Eq.trans ?_ he
      apply prod_congr rfl
      intro j _
      dsimp only [actualPrimeSlotData]
      congr 1
    _ = _ := actualSlot_factor w i b ht hq

theorem actualPrimeSlotData_word (w : Fin R → SignedStep)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding) :
    (actualPrimeSlotData w).word = List.ofFn w := by
  unfold PrimeSlotData.word
  congr 1
  funext i
  rw [actualPrimeSlotData_factor w i false (ht i) (hq i),
    actualPrimeSlotData_factor w i true (ht i) (hq i)]
  cases he : w i
  simp [actualPrimeSlotData, he]


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

open _root_.Finset hiding sum_le_sum_of_injOn






lemma intervalDisplacement_eq_sub (D : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    intervalDisplacement D a b = (∑ i ∈ range b, D i) - ∑ i ∈ range a, D i :=
  sum_Ico_eq_sub D hab


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

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn


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



lemma wordSlice_split (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    w.take a ++ wordSlice w a b = w.take b := by
  have h := List.take_append_drop a (w.take b)
  simpa only [List.take_take, Nat.min_eq_left hab, List.drop_take, wordSlice] using h


lemma wordSlice_displacement (h : ℕ) (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    wordDisplacement h (wordSlice w a b) = intervalDisplacement (wordStepDisplacement h w) a b := by
  have hs := congrArg (wordDisplacement h) (wordSlice_split w hab)
  rw [wordDisplacement_append, wordDisplacement_take, wordDisplacement_take] at hs
  rw [intervalDisplacement_eq_sub _ hab]
  omega



lemma TuplePrimeAt.index_lt {w : List SignedStep} {p i : ℕ} (hp : TuplePrimeAt w p i) :
    i < w.length := by
  obtain ⟨_, a, ha, _⟩ := hp
  exact (List.getElem?_eq_some_iff.mp ha).1



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry
namespace OAI

/-! Geometry of actual surviving positive words, including the prime-support checks. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

lemma tuplePrimeAt_iff_getElem (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt w p i ↔ p.Prime ∧ p ∣ w[i].tuple := by
  simp [TuplePrimeAt, List.getElem?_eq_getElem hi]

lemma wordStepDisplacement_getElem (h : ℕ) (w : List SignedStep) (i : ℕ) (hi : i < w.length) :
    wordStepDisplacement h w i = w[i].displacement h := by
  simp [wordStepDisplacement, List.getElem?_eq_getElem hi]

lemma tuplePrime_dvd_step {h p i : ℕ} {w : List SignedStep} (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ wordStepDisplacement h w i := by
  have hi := hp.index_lt
  have hpd := ((tuplePrimeAt_iff_getElem w p i hi).mp hp).2
  have hcast : (p : ℤ) ∣ (w[i].tuple : ℤ) := by exact_mod_cast hpd
  rw [wordStepDisplacement_getElem h w i hi]
  exact (hcast.mul_left (w[i].padding : ℤ)).trans (w[i].divisor_dvd_displacement h)




/-- Every tuple prime is coprime to the common multiplier and every padding.
Consequently an absent tuple prime cannot divide a step's displacement. -/
lemma word_prime_support {h : ℕ} {w : List SignedStep}
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding) :
    ∀ p i, (∃ j, j < w.length ∧ TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i := by
  intro p i hseen hi hnot
  obtain ⟨j, _, hpj⟩ := hseen
  have hp := hpj.1
  have hdata := hsupport p j hpj
  have ha := List.getElem_mem hi
  have htuple : ¬p ∣ w[i].tuple := by
    intro hdiv
    exact hnot ((tuplePrimeAt_iff_getElem w p i hi).mpr ⟨hp, hdiv⟩)
  rw [wordStepDisplacement_getElem h w i hi]
  exact w[i].prime_not_dvd_displacement h p hp hdata.1 (hdata.2 _ ha) htuple



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActiveLabels
namespace OAI

/-! Active numerical labels in minimal prohibited witnesses. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn




lemma wordPrimeContribution_eq_singleton (h : ℕ) (w : List SignedStep) (p a b j : ℕ)
    (hj : j ∈ Ico a b) (hp : TuplePrimeAt w p j)
    (hunique : ∀ i ∈ Ico a b, TuplePrimeAt w p i → i = j) :
    wordPrimeContribution h w p a b = wordStepDisplacement h w j := by
  classical
  unfold wordPrimeContribution
  rw [sum_eq_single j]
  · simp only [hp, ite_true]
  · intro i hi hne
    have hnot : ¬TuplePrimeAt w p i := fun hpi => hne (hunique i hi hpi)
    simp only [hnot, ite_false]
  · exact fun h => False.elim (h hj)

/-- A label first entering at the last step is active in the original
prohibited suffix, because its contribution is exactly that last step. -/
lemma ForwardProhibited.last_new_active {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : ForwardProhibited h s supply w) {z : ℕ}
    (hz : TuplePrimeAt w z (w.length - 1))
    (hearlier : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i)
    (hoff : ∀ p i, (∃ j, TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i) :
    ActivePrime h w z := by
  rcases hw with ⟨hlen, _, _, _, _, c, hc, hclast, a, ha, halast, hdiv⟩
  refine ⟨c, a, w.length, by omega, le_rfl, ⟨0, hc⟩, ?_, ?_⟩
  · simpa only [wordSlice, Nat.sub_self, List.take_length, List.length_drop] using
      (show (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a w.length from by
        rw [← wordSlice_displacement h w (by omega)]
        simpa only [wordSlice, ← List.length_drop, List.take_length] using hdiv)
  · rw [wordPrimeContribution_eq_singleton h w z a w.length (w.length - 1)
      (by simp only [mem_Ico]; omega) hz]
    · exact hoff c (w.length - 1) ⟨0, hc⟩ (by omega) hclast
    · intro i hi hzi
      have hi' := (mem_Ico.mp hi).2
      by_contra hne
      exact hearlier i (by omega) hzi

lemma prime_dvd_wordPrimeContribution (h : ℕ) (w : List SignedStep) (p a b : ℕ) :
    (p : ℤ) ∣ wordPrimeContribution h w p a b := by
  classical
  unfold wordPrimeContribution
  apply Finset.dvd_sum
  intro i _
  by_cases hpi : TuplePrimeAt w p i
  · simpa only [hpi, ite_true] using (tuplePrime_dvd_step (h := h) hpi)
  · simp only [hpi, ite_false, dvd_zero]

lemma ActivePrime.distinct_controller {h p : ℕ} {w : List SignedStep}
    (hp : ActivePrime h w p) :
    ∃ c a b, c ≠ p ∧ a ≤ b ∧ b ≤ w.length ∧ (∃ i, TuplePrimeAt w c i) ∧
      (c : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b ∧
      ¬(c : ℤ) ∣ wordPrimeContribution h w p a b := by
  obtain ⟨c, a, b, hab, hb, hc, hd, hn⟩ := hp
  refine ⟨c, a, b, ?_, hab, hb, hc, hd, hn⟩
  intro heq
  subst c
  exact hn (prime_dvd_wordPrimeContribution h w p a b)





/-- Equal-size squarefree tuples that change must also acquire a new prime. -/
lemma adjacent_tuple_new_prime (w : List SignedStep) (J : ℕ)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    ∀ i, i + 1 < w.length → ∃ p, TuplePrimeAt w p (i + 1) ∧ ¬TuplePrimeAt w p i := by
  intro i hi
  have hi0 : i < w.length := by omega
  have ha := List.getElem_mem hi0
  have hb := List.getElem_mem hi
  have hneq : w[i].tuple ≠ w[i + 1].tuple := (List.isChain_iff_getElem.mp hchain) i hi
  have hsets : w[i + 1].tuple.primeFactors ≠ w[i].tuple.primeFactors := by
    intro heq
    apply hneq
    calc
      _ = ∏ p ∈ w[i].tuple.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq _ ha)).symm
      _ = ∏ p ∈ w[i + 1].tuple.primeFactors, p := by rw [heq]
      _ = _ := Nat.prod_primeFactors_of_squarefree (hsq _ hb)
  have hnot : ¬w[i + 1].tuple.primeFactors ⊆ w[i].tuple.primeFactors := by
    intro hsub
    apply hsets
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard _ ha, hcard _ hb])
  obtain ⟨p, hpb, hpa⟩ := Finset.not_subset.mp hnot
  have hp := Nat.mem_primeFactors.mp hpb
  refine ⟨p, (tuplePrimeAt_iff_getElem w p (i + 1) hi).mpr ⟨hp.1, hp.2.1⟩, ?_⟩
  intro hpi
  have hpai := (tuplePrimeAt_iff_getElem w p i hi0).mp hpi
  exact hpa (Nat.mem_primeFactors.mpr ⟨hpai.1, hpai.2, (hsq _ ha).ne_zero⟩)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledPrimeWords
namespace OAI

/-! Identifying squarefree-label polynomials with numerical signed words. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]



omit [DecidableEq ι] in
lemma monomial_eval (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hw : w.Realizes value) (i : Fin w.word.length) :
    (w.monomial h i).eval (fun j => (value j : ℤ)) = wordStepDisplacement h w.word i := by
  rw [wordStepDisplacement_getElem h w.word i i.isLt]
  unfold monomial PrimeMonomial.eval SignedStep.displacement
  rw [← Nat.cast_prod, hw i]

omit [DecidableEq ι] in
lemma label_iff_occurrence (w : LabeledPrimeWord ι) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (i : Fin w.word.length) :
    y ∈ w.labels i ↔ TuplePrimeAt w.word (value y) i := by
  rw [tuplePrimeAt_iff_getElem w.word (value y) i i.isLt, ← hw i]
  constructor
  · intro hy
    exact ⟨hprime y, Finset.dvd_prod_of_mem value hy⟩
  · rintro ⟨_, hy⟩
    obtain ⟨j, hj, hyj⟩ := ((hprime y).prime.dvd_finsetProd_iff value).mp hy
    have heq := hinj ((Nat.prime_dvd_prime_iff_eq (hprime y) (hprime j)).mp hyj)
    exact heq.symm ▸ hj



end LabeledPrimeWord

lemma sum_fin_interval (n a b : ℕ) (D : ℕ → ℤ) (hb : b ≤ n) :
    (∑ i : Fin n, if a ≤ i.val ∧ i.val < b then D i.val else 0) = ∑ i ∈ Ico a b, D i := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if a ≤ i ∧ i < b then D i else 0) n]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_Ico]
  omega

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma intervalRelation_eval (w : LabeledPrimeWord ι) (h a b : ℕ) (value : ι → ℕ)
    (hw : w.Realizes value) (hb : b ≤ w.word.length) :
    primeRelationEval (w.intervalRelation h a b) (fun j => (value j : ℤ)) =
      intervalDisplacement (wordStepDisplacement h w.word) a b := by
  unfold primeRelationEval
  have ht (i : Fin w.word.length) :
      (w.intervalRelation h a b i).eval (fun j => (value j : ℤ)) =
        if a ≤ i.val ∧ i.val < b then wordStepDisplacement h w.word i.val else 0 := by
    by_cases hi : a ≤ i.val ∧ i.val < b
    · simp only [intervalRelation, if_pos hi]
      exact w.monomial_eval h value hw i
    · simp only [intervalRelation, if_neg hi, PrimeMonomial.eval, zero_mul]
  simp_rw [ht]
  exact sum_fin_interval _ _ _ _ hb

lemma intervalRelation_contribution (w : LabeledPrimeWord ι) (h a b : ℕ)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (hb : b ≤ w.word.length) (y : ι) :
    primeRelationContribution (w.intervalRelation h a b) y (fun j => (value j : ℤ)) =
      wordPrimeContribution h w.word (value y) a b := by
  classical
  unfold primeRelationContribution
  have ht (i : Fin w.word.length) :
      (if y ∈ (w.intervalRelation h a b i).labels
        then (w.intervalRelation h a b i).eval (fun j => (value j : ℤ)) else 0) =
      if a ≤ i.val ∧ i.val < b then
        (if TuplePrimeAt w.word (value y) i.val then wordStepDisplacement h w.word i.val else 0)
      else 0 := by
    by_cases hi : a ≤ i.val ∧ i.val < b
    · simp only [intervalRelation, if_pos hi, monomial]
      by_cases hy : y ∈ w.labels i
      · have hp := (w.label_iff_occurrence value hinj hprime hw y i).mp hy
        simp only [hy, hp, ite_true]
        exact w.monomial_eval h value hw i
      · have hp : ¬TuplePrimeAt w.word (value y) i.val := fun hp =>
          hy ((w.label_iff_occurrence value hinj hprime hw y i).mpr hp)
        simp only [hy, hp, ite_false]
    · simp only [intervalRelation, if_neg hi, notMem_empty, ite_false]
  simp_rw [ht]
  unfold wordPrimeContribution
  exact sum_fin_interval w.word.length a b
    (fun i => if TuplePrimeAt w.word (value y) i then wordStepDisplacement h w.word i else 0) hb



end LabeledPrimeWord

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordRelations
namespace OAI

/-! Concrete internal and comparison congruences as prime-variable relations. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]









namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma occurrence_has_label (w : LabeledPrimeWord ι) (value : ι → ℕ)
    (hprime : ∀ j, (value j).Prime) (hw : w.Realizes value)
    (p : ℕ) (i : Fin w.word.length) (hp : TuplePrimeAt w.word p i) :
    ∃ c ∈ w.labels i, value c = p := by
  rw [tuplePrimeAt_iff_getElem w.word p i i.isLt, ← hw i] at hp
  obtain ⟨c, hc, hpc⟩ := (hp.1.prime.dvd_finsetProd_iff value).mp hp.2
  exact ⟨c, hc, ((Nat.prime_dvd_prime_iff_eq hp.1 (hprime c)).mp hpc).symm⟩

/-- The active numerical relation supplies a concrete interval polynomial
with the required nonzero coefficient and a distinct controlling label. -/
theorem active_relation (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (hy : ActivePrime h w.word (value y)) :
    ∃ c a b, c ≠ y ∧ a ≤ b ∧ b ≤ w.word.length ∧
      primeRelationEvent (w.intervalRelation h a b) y c (fun j => (value j : ℤ)) := by
  obtain ⟨p, a, b, hpy, hab, hb, ⟨r, hpr⟩, hdiv, hnonzero⟩ := hy.distinct_controller
  obtain ⟨c, _, hc⟩ := w.occurrence_has_label value hprime hw p ⟨r, hpr.index_lt⟩ hpr
  refine ⟨c, a, b, ?_, hab, hb, ?_, ?_⟩
  · intro heq
    exact hpy (by simpa only [heq] using hc.symm)
  · rw [w.intervalRelation_eval h a b value hw hb]
    change (value c : ℤ) ∣ _
    simpa only [hc] using hdiv
  · apply primeRelation_coefficient_nondegenerate
    rw [w.intervalRelation_contribution h a b value hinj hprime hw hb y]
    change ¬(value c : ℤ) ∣ _
    simpa only [hc] using hnonzero


end LabeledPrimeWord






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RelationReindex
namespace OAI

/-! Reindexing finite monomial relations preserves their events and supports. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]

omit [DecidableEq ι] in
lemma primeRelationEval_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) (x : ι → ℤ) :
    primeRelationEval n x = primeRelationEval m x := by
  unfold primeRelationEval
  rw [← e.sum_comp (fun i => (n i).eval x)]
  exact sum_congr rfl (fun i _ => by rw [hm])

lemma primeRelationCoefficient_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) (y : ι) (x : ι → ℤ) :
    primeRelationCoefficient n y x = primeRelationCoefficient m y x := by
  unfold primeRelationCoefficient
  rw [← e.sum_comp (fun i => (n i).coefficientAt y x)]
  exact sum_congr rfl (fun i _ => by rw [hm])


lemma primeRelationEvent_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i)
    (selected control : ι) (x : ι → ℤ) :
    primeRelationEvent n selected control x ↔ primeRelationEvent m selected control x := by
  unfold primeRelationEvent
  rw [primeRelationEval_reindex e m n hm, primeRelationCoefficient_reindex e m n hm]

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

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace AC0Circuit





end AC0Circuit





lemma decodeStepWord_length {pairs : Finset (ℕ × ℕ)} {s : ℕ}
    (c : BoundedStepWords pairs s) : (decodeStepWord c).length = c.1.val := by
  simp [decodeStepWord]

















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

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma FiniteLaw.probability_mono_of_imp {A : Type*} [Fintype A]
    (μ : FiniteLaw A) {E F : A → Prop} (h : ∀ x, E x → F x) :
    μ.probability E ≤ μ.probability F := by
  apply μ.average_mono
  intro x
  by_cases he : E x
  · simp only [if_pos he, if_pos (h x he), le_refl]
  · simp only [if_neg he]
    split_ifs <;> norm_num

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



/-- One reciprocal factor for every used residue coordinate. Repeated
occurrences can only make the event smaller, by adding compatibility tests. -/
theorem residuePositiveWord_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (h : ℕ) (w : List SignedStep) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ResiduePositiveWord p h w (fun i => ((x i).val : ZMod (p i)))) ≤
      ∏ i ∈ univ.filter (fun i => p i ∈ wordDivisorPrimeSupport w), (p i : ℝ)⁻¹ := by
  let E : ∀ i, Fin B → Prop := fun i x => ∀ k : Fin w.length,
    p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors →
      (x.val : ZMod (p i)) = -((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))
  have he : (fun x : ι → Fin B => ResiduePositiveWord p h w
      (fun i => ((x i).val : ZMod (p i)))) = (fun x => ∀ i, E i (x i)) := by
    funext x
    exact propext (forall_comm)
  rw [he, FiniteLaw.independent_probability_all]
  rw [prod_filter]
  apply Finset.prod_le_prod
  · intro i _
    exact FiniteLaw.probability_nonneg _ _
  · intro i _
    by_cases hi : p i ∈ wordDivisorPrimeSupport w
    · rw [if_pos hi]
      obtain ⟨k, hk⟩ := (mem_wordDivisorPrimeSupport w (p i)).mp hi
      exact ((uniformResidueLaw B (p i) (hp i) (hpB i)).probability_mono_of_imp
        (fun x hx => hx k hk)).trans_eq
          (uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i)
            (-((wordDisplacement h (w.take k.val) : ℤ) : ZMod (p i))))
    · rw [if_neg hi]
      exact FiniteLaw.probability_le_one _ _

/-- For an injectively indexed prime pool covering every step factor, the
bound is literally the product over distinct numerical primes in the word. -/
theorem residuePositiveWord_probability_distinct_primes {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (h : ℕ) (w : List SignedStep)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ResiduePositiveWord p h w (fun i => ((x i).val : ZMod (p i)))) ≤
      ∏ q ∈ wordDivisorPrimeSupport w, (q : ℝ)⁻¹ := by
  have himage : (univ.filter (fun i => p i ∈ wordDivisorPrimeSupport w)).image p =
      wordDivisorPrimeSupport w := by
    ext q
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hq
      obtain ⟨i, rfl⟩ := hcover q hq
      exact ⟨i, hq, rfl⟩
  have hbound := residuePositiveWord_probability_le B p hp hpB h w
  rw [← himage, prod_image (fun i _ j _ hij => hinj hij)]
  exact hbound


/-- A literal union bound for the actual minimal-word catalog. The remaining
arithmetic task is to sum these distinct-prime weights over that catalog. -/
theorem prohibited_residue_probability_le_catalog {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (pairs : Finset (ℕ × ℕ)) (h s : ℕ)
    (hcover : ∀ c : ProhibitedCatalog pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), ∃ i, p i = q) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (fun x => ∃ c : ProhibitedCatalog pairs h s,
        ResiduePositiveWord p h (decodeStepWord c.val)
          (fun i => ((x i).val : ZMod (p i)))) ≤
      ∑ c : ProhibitedCatalog pairs h s,
        ∏ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (q : ℝ)⁻¹ := by
  apply (FiniteLaw.probability_exists_le _ _).trans
  apply sum_le_sum
  intro c _
  exact residuePositiveWord_probability_distinct_primes B p hinj hp hpB h _ (hcover c)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BadEventDecay
namespace OAI

/-! A single prime saving dominates the short prohibited-word enumeration. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_short_word_cost (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ (1 / 10 : ℝ) * (Real.log L) ^ 2 ≤
        (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (179 / 200 : ℝ)) (by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hh
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hs : C * (Real.log L) ^ 2 ≤ (1 / 2 : ℝ) * L ^ (179 / 200 : ℝ) := by
    calc
      _ ≤ (C + 1) * (Real.log L) ^ 2 := by nlinarith [sq_nonneg (Real.log L)]
      _ ≤ (C + 1) * (((1 / 2 : ℝ) / (C + 1)) * L ^ (179 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [show C + 1 ≠ 0 by linarith]
  have ht := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le (1 / 10 : ℝ))
  have he : L ^ (179 / 200 : ℝ) * L ^ (1 / 10 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  nlinarith

/-- The complete short-word cost may include pattern and endpoint choices,
all reciprocal masses, and summation over lengths. No further saving is
used beyond the single nondegenerate last-prime relation. -/
theorem eventually_bad_event_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℕ) (H B cost total : ℝ),
      (s : ℝ) ≤ L ^ (1 / 10 : ℝ) → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      1 ≤ B → B ≤ Real.exp L →
      cost ≤ Real.exp (C * s * (Real.log L) ^ 2) →
      total ≤ cost * (H⁻¹ + (1 + Real.log B) / H) →
      total ≤ Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_short_word_cost (C + 2) (by positivity)] with L hL hlog hshort
  intro s H B cost total hs hH hB hBupper hcost htotal
  have hLp : 0 < L := by linarith
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hBp : 0 < B := by linarith
  have hlogB : Real.log B ≤ L := by
    have hh := Real.log_le_log hBp hBupper
    simpa only [Real.log_exp] using hh
  have hlogBpos : 0 ≤ Real.log B := Real.log_nonneg hB
  have hinv : H⁻¹ ≤ Real.exp (-L ^ (199 / 200 : ℝ)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hH
  have hpoly : 2 + Real.log B ≤ Real.exp (2 * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hLp] using Real.exp_nat_mul (Real.log L) 2
    rw [he]
    nlinarith
  have hbase : H⁻¹ + (1 + Real.log B) / H ≤
      Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) := by
    calc
      _ = (2 + Real.log B) * H⁻¹ := by ring
      _ ≤ Real.exp (2 * Real.log L) * Real.exp (-L ^ (199 / 200 : ℝ)) :=
        mul_le_mul hpoly hinv (inv_nonneg.mpr hHp.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; rfl
  have hone : 1 ≤ L ^ (1 / 10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hexp : C * s * (Real.log L) ^ 2 + 2 * Real.log L ≤
      (C + 2) * L ^ (1 / 10 : ℝ) * (Real.log L) ^ 2 := by
    have hterm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hC) (sq_nonneg (Real.log L))
    have hlog2 : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sq_nonneg (Real.log L))]
  calc
    total ≤ Real.exp (C * s * (Real.log L) ^ 2) *
        (H⁻¹ + (1 + Real.log B) / H) :=
      htotal.trans (mul_le_mul_of_nonneg_right hcost (by positivity))
    _ ≤ Real.exp (C * s * (Real.log L) ^ 2) *
        Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (C * s * (Real.log L) ^ 2 + 2 * Real.log L - L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; linarith

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordResampling
namespace OAI

/-! Numerical resampling preserves the symbolic witness relations. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
lemma PatternEquiv.interval {w v : LabeledPrimeWord ι} (e : PatternEquiv w v)
    (h a b : ℕ) (i : Fin w.word.length) :
    v.intervalRelation h a b (e.index i) = w.intervalRelation h a b i := by
  simp only [intervalRelation, e.index_val, e.monomial]



omit [DecidableEq ι] in
lemma resample_realizes (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    (w.resample value).Realizes value := by
  intro i
  simp [resample, List.getElem_ofFn]


end LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]



namespace WitnessSystemData

variable {n N : ℕ}




end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BadWordRelations
namespace OAI

/-! One actual nondegenerate relation for each forward prohibited word. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

/-- The last transition of a prohibited word acquires a new prime. Its
contribution to the prohibited suffix is exactly the last step. -/
theorem ForwardProhibited.exists_active {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : ForwardProhibited h s supply w)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding) :
    ∃ z, ActivePrime h w z := by
  have hlen : 3 ≤ w.length := hw.1
  have hinter : TuplePrimeIntervals w := hw.2.2.2.2.1
  obtain ⟨z, hz, hzprev⟩ := adjacent_tuple_new_prime w J hsq hcard hw.2.2.2.1
    (w.length - 2) (by omega)
  have hlast : w.length - 2 + 1 = w.length - 1 := by omega
  have hzlast : TuplePrimeAt w z (w.length - 1) := hlast ▸ hz
  have hearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i := by
    intro i hi hzi
    exact hzprev (hinter z i (w.length - 2) (w.length - 1)
      (by omega) (by omega) (by omega) hzi hzlast)
  refine ⟨z, hw.last_new_active hzlast hearly ?_⟩
  intro p i hp hi hnot
  apply word_prime_support hsupport p i ?_ hi hnot
  obtain ⟨j, hj⟩ := hp
  exact ⟨j, hj.index_lt, hj⟩


namespace BadRelationCode

variable {N : ℕ} {ι : Type*} [DecidableEq ι]



lemma toSystem_size (d : BadRelationCode N ι) (w : LabeledPrimeWord ι) (h : ℕ)
    (hne : d.2.1 ≠ d.1) : (d.toSystem w h hne).size = 1 := by
  change Fintype.card (Fin 1) = 1
  exact Fintype.card_fin 1

end BadRelationCode


theorem resampled_prohibited_relation {ι : Type*} [DecidableEq ι]
    {h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    (w : LabeledPrimeWord ι) (hN : w.word.length ≤ N) (value : ι → ℕ)
    (hevent : ResampledProhibitedEvent w h s J supply value) :
    ∃ d : BadRelationCode N ι, d.Holds w h (fun i => (value i : ℤ)) := by
  rcases hevent with ⟨hinj, hprime, hpro, hsq, hcard, hsupport⟩
  obtain ⟨z, hz⟩ := hpro.exists_active hsq hcard hsupport
  have hzseen : ∃ r, TuplePrimeAt (w.resample value).word z r := by
    by_contra! hn
    rcases hz with ⟨c, a, b, _, _, _, _, hnonzero⟩
    apply hnonzero
    have he : wordPrimeContribution h (w.resample value).word z a b = 0 := by
      unfold wordPrimeContribution
      simp only [hn, ite_false, sum_const_zero]
    rw [he]
    exact dvd_zero _
  obtain ⟨rz, hrz⟩ := hzseen
  obtain ⟨y, _, hy⟩ := (w.resample value).occurrence_has_label value hprime
    (w.resample_realizes value) z ⟨rz, hrz.index_lt⟩ hrz
  have hyactive : ActivePrime h (w.resample value).word (value y) := by simpa only [hy] using hz
  obtain ⟨control, a, b, hne, hab, hb, he⟩ := (w.resample value).active_relation h value
    hinj hprime (w.resample_realizes value) y hyactive
  have hbn : b ≤ N := hb.trans (by simpa only [LabeledPrimeWord.resample_length] using hN)
  refine ⟨⟨y, control, ⟨a, by omega⟩, ⟨b, by omega⟩⟩, hne, ?_⟩
  exact (primeRelationEvent_reindex (w.resamplePattern value).index _ _
    ((w.resamplePattern value).interval h a b) y control _).mp he

theorem bad_relation_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N h : ℕ) (w : LabeledPrimeWord ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ x : ι → P, if ∃ d : BadRelationCode N ι,
      d.Holds w h (integerPrimeAssignment Subtype.val x)
      then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  let D := {d : BadRelationCode N ι // d.2.1 ≠ d.1}
  have hone (d : D) :
      (∑ x : ι → P, if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
        then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
    have hs := (d.val.toSystem w h d.property).reciprocal_sum_bound P hP hV H B hH hB hlo hhi
    rw [BadRelationCode.toSystem_size, pow_one] at hs
    have he (x : ι → ℤ) : d.val.Holds w h x ↔ (d.val.toSystem w h d.property).Holds x := by
      constructor
      · intro hx _
        exact hx.2
      · intro hx
        exact ⟨d.property, hx (0 : Fin 1)⟩
    simpa only [he] using hs
  calc
    _ ≤ ∑ d : D, ∑ x : ι → P,
        if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
          then ∏ i, ((x i).val : ℝ)⁻¹ else 0 := by
      rw [sum_comm]
      apply sum_le_sum
      intro x _
      by_cases hx : ∃ d : BadRelationCode N ι, d.Holds w h (integerPrimeAssignment Subtype.val x)
      · rw [if_pos hx]
        obtain ⟨d, hd⟩ := hx
        have hi := single_le_sum (f := fun d : D =>
          if d.val.Holds w h (integerPrimeAssignment Subtype.val x)
            then ∏ i, ((x i).val : ℝ)⁻¹ else 0)
          (fun _ _ => by split_ifs <;> positivity) (mem_univ (⟨d, hd.1⟩ : D))
        simpa only [if_pos hd] using hi
      · rw [if_neg hx]
        exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    _ ≤ (Fintype.card D : ℝ) * (primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H)) := by
      simpa only [sum_const, card_univ, nsmul_eq_mul] using
        (sum_le_sum (s := (univ : Finset D)) (fun d _ => hone d))
    _ ≤ _ := by
      have hc : Fintype.card D ≤ Fintype.card ι ^ 2 * (N + 1) ^ 2 := by
        apply (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans_eq
        simp only [BadRelationCode, Fintype.card_prod, Fintype.card_fin]
        ring
      have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
      calc
        _ ≤ (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) *
            (primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
        _ = _ := by ring

/-- The numerical prohibited event enters the fixed metadata union. The
ambient prime assignment may be enlarged after this inclusion is proved. -/
theorem resampled_prohibited_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (N h : ℕ) (w : LabeledPrimeWord ι) (hN : w.word.length ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ x : ι → P, if ResampledProhibitedEvent w h s J supply (fun i => (x i).val)
      then ∏ i, ((x i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (N + 1) ^ 2 : ℕ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply le_trans _ (bad_relation_reciprocal_bound N h w P hP hV H B hH hB hlo hhi)
  apply sum_le_sum
  intro x _
  by_cases he : ResampledProhibitedEvent w h s J supply (fun i => (x i).val)
  · have hd : ∃ d : BadRelationCode N ι, d.Holds w h (integerPrimeAssignment Subtype.val x) :=
      resampled_prohibited_relation w hN (fun i => (x i).val) he
    rw [if_pos he, if_pos hd]
  · rw [if_neg he]
    split_ifs <;> positivity

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses
namespace OAI

/-! Tuple classes can be resampled while all padding classes remain fixed. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}






lemma classAt_mem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = false) : c.classAt j ∈ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  exact (hc j).trans hj

lemma classAt_notMem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = true) : c.classAt j ∉ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  rw [hc j, hj]
  decide

/-- Rowwise squarefreeness makes the tuple product a product over its classes. -/
lemma tuple_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (i : Fin R) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i false,
      joinCoordinates c.tupleClasses a b (c.classAt j)) =
        ∏ z ∈ c.tupleLabels i, a z := by
  let f (j : Fin N) (hj : j ∈ c.recordedSlots i false) : c.tupleClasses :=
    ⟨c.classAt j, c.classAt_mem_tupleClasses hc j (mem_filter.mp hj).2.2⟩
  apply prod_bij f
  · intro j hj
    exact mem_subtype.mpr (mem_image.mpr ⟨j, hj, rfl⟩)
  · intro j hj k hk he
    exact hi i false hj hk (congrArg (fun z : c.tupleClasses => z.val.val) he)
  · intro z hz
    obtain ⟨j, hj, he⟩ := mem_image.mp (mem_subtype.mp hz)
    exact ⟨j, hj, Subtype.ext he⟩
  · intro j hj
    exact joinCoordinates_mem c.tupleClasses a b (f j hj)

lemma padding_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (i : Fin R) (a a' : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a b (c.classAt j)) =
      ∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a' b (c.classAt j) := by
  apply prod_congr rfl
  intro j hj
  have hn := c.classAt_notMem_tupleClasses hc j (mem_filter.mp hj).2.2
  simp only [joinCoordinates, hn, dite_false]


lemma labeledWord_length (c : CrudeWordCode R N R)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (c.labeledWord b).word.length = R := c.numericalWord_length _

/-- Resampling changes exactly the tuple primes, with no additional padding choices. -/
theorem labeledWord_resample (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    ((c.labeledWord b).resample a).word =
      c.numericalWord (joinCoordinates c.tupleClasses a b) := by
  apply List.ext_getElem
  · rw [LabeledPrimeWord.resample_length, labeledWord_length, numericalWord_length]
  · intro i hi₁ hi₂
    have hiR : i < R := by simpa only [numericalWord_length] using hi₂
    let j : Fin R := ⟨i, hiR⟩
    have hp := c.padding_product hc j (fun _ => 1) a b
    have ht := c.tuple_product hc hi j a b
    have hf := c.numericalWord_get (joinCoordinates c.tupleClasses (fun _ => 1) b) j
    simp only [LabeledPrimeWord.resample, List.getElem_ofFn, labeledWord]
    rw [c.numericalWord_get _ j]
    congr 1
    · exact congrArg SignedStep.forward hf
    · exact ht.symm
    · exact (congrArg SignedStep.padding hf).trans hp

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualSlotClasses
namespace OAI

/-! Actual squarefree prime occurrences satisfy the code's class conditions. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace PrimeSlotData

variable {R N : ℕ}

lemma code_value_injective (a : PrimeSlotData R N) :
    Function.Injective (fun z : a.code.usedClasses => a.prime z.val) := by
  intro z t h
  obtain ⟨i, _, hi⟩ := mem_image.mp z.property
  obtain ⟨j, _, hj⟩ := mem_image.mp t.property
  apply Subtype.ext
  rw [← hi, ← hj]
  apply (a.code_class_eq_iff i j).mpr
  have he : a.prime (a.code.2.1 i) = a.prime (a.code.2.1 j) := by
    simpa only [hi, hj] using h
  exact (a.code_class_prime i).symm.trans (he.trans
    (a.code_class_prime j))

lemma code_value_image (a : PrimeSlotData R N) :
    (univ.image (fun z : a.code.usedClasses => a.prime z.val)) = univ.image a.prime := by
  ext p
  constructor
  · rintro hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨z.val, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨a.code.classAt i, mem_univ _, a.code_class_prime i⟩

lemma code_kindConsistent (a : PrimeSlotData R N)
    (hk : ∀ i j, a.prime i = a.prime j → a.isPadding i = a.isPadding j) :
    a.code.KindConsistent := by
  intro j
  exact hk _ _ (a.code_class_prime j)

lemma code_rowInjective (a : PrimeSlotData R N)
    (hi : ∀ i j, a.row i = a.row j → a.isPadding i = a.isPadding j →
      a.prime i = a.prime j → i = j) : a.code.RowInjective := by
  intro r b i hi' j hj' he
  have hir := (mem_filter.mp hi').2
  have hjr := (mem_filter.mp hj').2
  exact hi i j (hir.1.trans hjr.1.symm) (hir.2.trans hjr.2.symm)
    ((a.code_class_eq_iff i j).mp he)

end PrimeSlotData

variable {R : ℕ}

lemma actualSlot_eq_of_data (w : Fin R → SignedStep) (s t : ActualPrimeSlot w)
    (hr : s.1 = t.1) (hk : actualSlotKind w s = actualSlotKind w t)
    (hp : actualSlotPrime w s = actualSlotPrime w t) : s = t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩ <;> cases hr
  · congr 2
    exact Subtype.ext hp
  · cases hk
  · cases hk
  · congr 2
    exact Subtype.ext hp

lemma actualSlot_kind_of_prime (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (s t : ActualPrimeSlot w) (hp : actualSlotPrime w s = actualSlotPrime w t) :
    actualSlotKind w s = actualSlotKind w t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩
  · rfl
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd i j)) p.property
      (by simpa only [hp] using q.property))
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd j i)) q.property
      (by simpa only [← hp] using p.property))
  · rfl

theorem actualPrimeSlotData_code_kindConsistent (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    (actualPrimeSlotData w).code.KindConsistent := by
  apply PrimeSlotData.code_kindConsistent
  intro i j hp
  exact actualSlot_kind_of_prime w hd _ _ hp

theorem actualPrimeSlotData_code_rowInjective (w : Fin R → SignedStep) :
    (actualPrimeSlotData w).code.RowInjective := by
  apply PrimeSlotData.code_rowInjective
  intro i j hr hk hp
  apply (actualPrimeSlotEquiv w).symm.injective
  exact actualSlot_eq_of_data w _ _ hr hk hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualCodeAssignments
namespace OAI

/-! Actual code assignments preserve prime pools and the distinct-prime weight. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

variable {R : ℕ}

lemma actualSlotPrime_mem_tuplePool (w : Fin R → SignedStep) (P : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = false) : actualSlotPrime w s ∈ P := by
  rcases s with ⟨i, p | p⟩
  · exact hP i p.property
  · cases hs

lemma actualSlotPrime_mem_paddingPool (w : Fin R → SignedStep) (Q : Finset ℕ)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = true) : actualSlotPrime w s ∈ Q := by
  rcases s with ⟨i, p | p⟩
  · cases hs
  · exact hQ i p.property

lemma actualPrimeSlotData_prime_image (w : Fin R → SignedStep) :
    univ.image (actualPrimeSlotData w).prime = univ.image (actualSlotPrime w) := by
  ext p
  constructor
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨(actualPrimeSlotEquiv w).symm i, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨s, _, rfl⟩ := mem_image.mp hp
    refine mem_image.mpr ⟨actualPrimeSlotEquiv w s, mem_univ _, ?_⟩
    change actualSlotPrime w ((actualPrimeSlotEquiv w).symm (actualPrimeSlotEquiv w s)) = _
    rw [Equiv.symm_apply_apply]

lemma actualPrimeSlot_support (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    wordDivisorPrimeSupport (List.ofFn w) = univ.image (actualSlotPrime w) := by
  ext p
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    rw [Nat.primeFactors_mul (hq i) (ht i), mem_union] at hp
    rcases hp with hp | hp
    · exact mem_image.mpr ⟨⟨i, Sum.inr ⟨p, hp⟩⟩, mem_univ _, rfl⟩
    · exact mem_image.mpr ⟨⟨i, Sum.inl ⟨p, hp⟩⟩, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨⟨i, p | p⟩, _, rfl⟩ := mem_image.mp hp
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inr p.property
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inl p.property

/-- The encoded assignment pays exactly one reciprocal per distinct prime. -/
theorem actual_code_reciprocal_weight (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    (∏ z : (actualPrimeSlotData w).code.usedClasses,
      ((actualPrimeSlotData w).prime z.val : ℝ)⁻¹) =
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  rw [actualPrimeSlot_support w ht hq, ← actualPrimeSlotData_prime_image]
  rw [← PrimeSlotData.code_value_image, prod_image]
  exact fun z _ t _ h => (actualPrimeSlotData w).code_value_injective h

/-- Actual tuple and padding classes inhabit their separate numerical pools. -/
theorem actual_code_pool_assignments (w : Fin R → SignedStep) (P Q : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) :
    ∃ a : (actualPrimeSlotData w).code.tupleClasses → P,
      ∃ b : {z : (actualPrimeSlotData w).code.usedClasses //
        z ∉ (actualPrimeSlotData w).code.tupleClasses} → Q,
      joinCoordinates (actualPrimeSlotData w).code.tupleClasses
        (fun z => (a z).val) (fun z => (b z).val) =
          fun z => (actualPrimeSlotData w).prime z.val := by
  let c := (actualPrimeSlotData w).code
  have htuple (z : c.tupleClasses) : (actualPrimeSlotData w).prime z.val.val ∈ P := by
    apply actualSlotPrime_mem_tuplePool w P hP
      ((actualPrimeSlotEquiv w).symm z.val.val)
    exact (mem_filter.mp z.property).2
  have hpadding (z : {z : c.usedClasses // z ∉ c.tupleClasses}) :
      (actualPrimeSlotData w).prime z.val.val ∈ Q := by
    apply actualSlotPrime_mem_paddingPool w Q hQ
      ((actualPrimeSlotEquiv w).symm z.val.val)
    have hn : ¬c.2.2.2 z.val.val = false := by
      intro hz
      exact z.property (mem_filter.mpr ⟨mem_univ _, hz⟩)
    change c.2.2.2 z.val.val = true
    cases he : c.2.2.2 z.val.val <;> simp_all
  refine ⟨(fun z => ⟨_, htuple z⟩), (fun z => ⟨_, hpadding z⟩), ?_⟩
  funext z
  dsimp only [joinCoordinates]
  split_ifs <;> rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding
namespace OAI

/-! A single finite universe covers all numerical words with bounded prime slots. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}



lemma weight_nonneg (e : PrimeWordEncoding R T P Q) : 0 ≤ e.weight := by
  unfold weight
  exact prod_nonneg (fun _ _ => by positivity)

/-- No loss in the reciprocal weight occurs on encoding an actual word. -/
theorem covers (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    ∃ e : PrimeWordEncoding R T P Q, e.decode = List.ofFn w ∧
      e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
      Function.Injective (fun z => (e.2.2.1 z).val) ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  obtain ⟨a, b, hab⟩ := actual_code_pool_assignments w P Q hP hQ
  let c := (actualPrimeSlotData w).code
  let e : PrimeWordEncoding R T P Q :=
    ⟨⟨Fintype.card (ActualPrimeSlot w), by omega⟩, c, a, b⟩
  refine ⟨e, ?_, actualPrimeSlotData_code_kindConsistent w hd,
    actualPrimeSlotData_code_rowInjective w, ?_, ?_⟩
  · change c.numericalWord (joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val)) = _
    rw [hab, CrudeWordCode.numericalWord_encode]
    exact actualPrimeSlotData_word w ht hq
  · have ha (z : c.tupleClasses) : (a z).val = (actualPrimeSlotData w).prime z.val.val := by
      have hz := congrFun hab z.val
      simpa only [joinCoordinates_mem] using hz
    intro u v huv
    apply Subtype.ext
    apply (actualPrimeSlotData w).code_value_injective
    change (actualPrimeSlotData w).prime u.val.val = (actualPrimeSlotData w).prime v.val.val
    exact (ha u).symm.trans (huv.trans (ha v))
  · change (∏ z : c.usedClasses, ((joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val) z : ℕ) : ℝ)⁻¹) = _
    rw [hab]
    exact actual_code_reciprocal_weight w (fun i => (ht i).ne_zero) (fun i => (hq i).ne_zero)

end PrimeWordEncoding

/-- A finite decoding cover also covers every nonnegative weighted sum.
The chosen representatives are injective because decoding recovers the word. -/
theorem finite_decoding_weight_bound {W C : Type*} [DecidableEq W] [Fintype C]
    (F : Finset W) (decode : C → W) (weight : W → ℝ) (cost : C → ℝ)
    (hcost : ∀ c, 0 ≤ cost c)
    (hcover : ∀ w ∈ F, ∃ c, decode c = w ∧ weight w ≤ cost c) :
    (∑ w ∈ F, weight w) ≤ ∑ c, cost c := by
  let choose (w : F) : C := Classical.choose (hcover w.val w.property)
  have hchoose (w : F) : decode (choose w) = w.val ∧ weight w.val ≤ cost (choose w) :=
    Classical.choose_spec (hcover w.val w.property)
  have hinj : Function.Injective choose := by
    intro u v h
    apply Subtype.ext
    exact (hchoose u).1.symm.trans ((congrArg decode h).trans (hchoose v).1)
  calc
    _ = ∑ w : F, weight w.val := (Finset.sum_coe_sort F weight).symm
    _ ≤ ∑ c, cost c := sum_le_sum_of_injOn choose
      (fun u _ v _ h => hinj h) (subset_univ _)
      (fun w _ => (hchoose w).2) (fun c _ _ => hcost c)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum
namespace OAI

/-!
# Summing tuple and padding classes in the required order

The padding assignment is frozen before applying the nondegenerate tuple
relation. It is then averaged with one reciprocal per padding class. The
statement permits different symbolic words for different padding choices,
since every bound is uniform in those choices.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma sum_reciprocal_assignments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) :
    (∑ x : ι → P, ∏ i, ((x i).val : ℝ)⁻¹) = primeHarmonicMass P ^ Fintype.card ι := by
  simpa only [prod_const, card_univ, primeHarmonicMass] using
    (Fintype.prod_sum (fun (_ : ι) (p : P) => (p.val : ℝ)⁻¹)).symm

/-- Splitting the class set preserves the original reciprocal product. -/
lemma reciprocal_product_join {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : S → ℕ) (b : {i // i ∉ S} → ℕ) :
    (∏ i, ((joinCoordinates S a b i : ℕ) : ℝ)⁻¹) =
      (∏ i : S, (a i : ℝ)⁻¹) * ∏ i : {i // i ∉ S}, (b i : ℝ)⁻¹ := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- The complete finite weighted estimate for one fixed equality pattern.
Tuple and padding labels remain separate even after numerical enlargement. -/
theorem split_prohibited_reciprocal_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (R h : ℕ) (P Q : Finset ℕ) (word : (κ → Q) → LabeledPrimeWord ι)
    (hlen : ∀ b, (word b).word.length ≤ R)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) *
      ∑ a : ι → P, if ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val)
        then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  let C : ℝ := (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
    primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H)
  have hinner (b : κ → Q) :
      (∑ a : ι → P, if ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val)
        then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤ C :=
    resampled_prohibited_reciprocal_bound R h (word b) (hlen b)
      P hP hVP H B hH hB hlo hhi
  calc
    _ ≤ ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) * C := by
      exact sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hinner b)
        (prod_nonneg (fun j _ => by positivity)))
    _ = (∑ b : κ → Q, ∏ j, ((b j).val : ℝ)⁻¹) * C := (sum_mul _ _ _).symm
    _ = primeHarmonicMass Q ^ Fintype.card κ * C := by
      rw [sum_reciprocal_assignments (ι := κ) Q]
    _ = _ := by dsimp [C]; ring

/-- An actual admissible fiber may contain additional bin, distinctness,
or positivity conditions. Their removal only enlarges this positive sum. -/
theorem split_prohibited_fiber_bound {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {s J : ℕ} {supply : ℕ → ℕ → Prop}
    (R h : ℕ) (P Q : Finset ℕ) (word : (κ → Q) → LabeledPrimeWord ι)
    (hlen : ∀ b, (word b).word.length ≤ R)
    (E : (ι → P) → (κ → Q) → Prop)
    (hE : ∀ a b, E a b →
      ResampledProhibitedEvent (word b) h s J supply (fun i => (a i).val))
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : κ → Q, ∑ a : ι → P, if E a b then
      (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card ι ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply le_trans _ (split_prohibited_reciprocal_bound (s := s) (J := J) (supply := supply)
    R h P Q word hlen
    hP hVP H B hH hB hlo hhi)
  apply sum_le_sum
  intro b _
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  by_cases he : E a b
  · simp only [if_pos he, if_pos (hE a b he)]
    exact le_of_eq (mul_comm _ _)
  · simp only [if_neg he]
    split_ifs <;> positivity

/-- Concrete application to the complete tuple/padding equality code. The
input conditions concern its reconstructed numerical word; the resampling
identity exchanges the order of the two weighted sums. -/
theorem CrudeWordCode.prohibited_fiber_reciprocal_bound {R N s J h : ℕ}
    {supply : ℕ → ℕ → Prop} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective) (P Q : Finset ℕ)
    (E : (c.tupleClasses → P) → ({z : c.usedClasses // z ∉ c.tupleClasses} → Q) → Prop)
    (hE : ∀ a b, E a b →
      let w := c.numericalWord (joinCoordinates c.tupleClasses
        (fun i => (a i).val) (fun j => (b j).val))
      Function.Injective (fun i => (a i).val) ∧
      ForwardProhibited h s supply w ∧
      (∀ t ∈ w, Squarefree t.tuple) ∧
      (∀ t ∈ w, t.tuple.primeFactors.card = J) ∧
      (∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ t ∈ w, ¬p ∣ t.padding))
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
      ∑ a : c.tupleClasses → P, if E a b then
        (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
        primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  apply split_prohibited_fiber_bound (s := s) (J := J) (supply := supply) R h P Q
    (fun b => c.labeledWord (fun j => (b j).val))
    (fun b => (c.labeledWord_length _).le) E ?_ hP hVP H B hH hB hlo hhi
  intro a b hab
  have he := hE a b hab
  unfold ResampledProhibitedEvent
  rw [c.labeledWord_resample hc hi]
  exact ⟨he.1, fun i => hP (a i).val (a i).property, he.2⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BadCatalogCost
namespace OAI

/-!
# The cost of the complete short-word catalog

Numerical primes are summed by reciprocal weight, rather than counted as
additional symbols.  This leaves only signs, equality classes, row records,
and tuple/padding flags.  The bound includes every length and every slot
count up to the stated budgets, including invalid codes.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}


lemma badReciprocalCost_nonneg (c : CrudeWordCode R N R) {VP VQ : ℝ}
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) : 0 ≤ c.badReciprocalCost VP VQ := by
  unfold badReciprocalCost
  positivity

lemma tuple_padding_class_count (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} =
        Fintype.card c.usedClasses := by
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le (fun z => z ∈ c.tupleClasses))

lemma class_count_le_slots (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ N := by
  rw [c.tuple_padding_class_count]
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun z : Fin N => z ∈ c.usedClasses))

/-- Tuple and padding classes together use at most one reciprocal mass per slot. -/
lemma class_mass_le (c : CrudeWordCode R N R) {VP VQ A : ℝ}
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) (hPA : VP ≤ A) (hQA : VQ ≤ A)
    (hA : 1 ≤ A) :
    VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ A ^ N := by
  calc
    _ ≤ A ^ Fintype.card c.tupleClasses *
        A ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} :=
      mul_le_mul (pow_le_pow_left₀ hP hPA _) (pow_le_pow_left₀ hQ hQA _)
        (pow_nonneg hQ _) (pow_nonneg (zero_le_one.trans hA) _)
    _ = A ^ (Fintype.card c.tupleClasses +
        Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := (pow_add _ _ _).symm
    _ ≤ A ^ N := pow_le_pow_right₀ hA c.class_count_le_slots

end CrudeWordCode


lemma short_log_le_square (s : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hlog : 1 ≤ Real.log L) : Real.log L ≤ s * (Real.log L) ^ 2 := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (sq_nonneg (Real.log L))]

lemma short_polynomial_exp_bound (s k : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hL : 0 < L) (hlog : 1 ≤ Real.log L) :
    L ^ k ≤ Real.exp ((k : ℝ) * s * (Real.log L) ^ 2) := by
  calc
    _ = Real.exp ((k : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log hL]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (short_log_le_square s L hs hlog)
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith

/-- Unlike the coarser pattern estimate, this bound does not need `R ≤ N`;
empty or invalid codes may therefore be retained in the catalog. -/
lemma short_crudeWordCode_bound (R N s : ℕ) (L C : ℝ)
    (hlog : 1 ≤ Real.log L) (hR : R ≤ s)
    (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (CrudeWordCode R N R) : ℝ) ≤
      Real.exp ((1 + 5 * C) * s * (Real.log L) ^ 2) := by
  have hlog2 : Real.log 2 ≤ Real.log L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have hr : (R : ℝ) ≤ s := by exact_mod_cast hR
    linarith
  have hlogR : Real.log ((R : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hRpoly
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have h1 : (R : ℝ) * Real.log 2 ≤ s * Real.log L :=
    mul_le_mul (by exact_mod_cast hR) hlog2
      (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h3 := mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h4 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h5 := mul_le_mul_of_nonneg_right hslots (show 0 ≤ Real.log L by linarith)
  have h6 : (s : ℝ) * Real.log L ≤ s * (Real.log L) ^ 2 := by
    have hh : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
  apply (card_crudeWordCode_exp R N R).trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The reciprocal masses and the choice of one relation cost only an
additional `exp ((8 + 2 C) s log² L)` for a fixed code. -/
lemma short_badReciprocalCost_bound {R N s : ℕ} (c : CrudeWordCode R N R)
    (VP VQ L C : ℝ) (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : R ≤ s) (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    c.badReciprocalCost VP VQ ≤
      Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have htu : Fintype.card c.tupleClasses ≤ N := by
    have hh := c.class_count_le_slots
    omega
  have ht : (Fintype.card c.tupleClasses : ℝ) ≤ L ^ (2 : ℕ) := by
    have hh : (Fintype.card c.tupleClasses : ℝ) ≤ N := by exact_mod_cast htu
    linarith
  have hr : (R : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have hh : (R : ℝ) ≤ s := by exact_mod_cast hR
    linarith
  have hmeta : (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) ≤
      Real.exp ((8 : ℝ) * s * (Real.log L) ^ 2) := by
    calc
      _ = (Fintype.card c.tupleClasses : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2 := by
        push_cast
        rfl
      _ ≤ (L ^ (2 : ℕ)) ^ 2 * (L ^ (2 : ℕ)) ^ 2 := by gcongr
      _ = L ^ (8 : ℕ) := by ring
      _ ≤ _ := short_polynomial_exp_bound s 8 L hs hLp hlog
  have hmass : VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤
        Real.exp (2 * C * s * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ (2 : ℕ)) ^ N :=
        c.class_mass_le hP hQ hPupper hQupper (one_le_pow₀ hL)
      _ = Real.exp ((N : ℝ) * (2 * Real.log L)) := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
          Real.exp_add, Real.exp_log hLp]
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hslots
          (show 0 ≤ 2 * Real.log L by linarith)
        nlinarith
  calc
    c.badReciprocalCost VP VQ =
        (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
          (VP ^ Fintype.card c.tupleClasses *
            VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := by
      unfold CrudeWordCode.badReciprocalCost
      ring
    _ ≤ Real.exp ((8 : ℝ) * s * (Real.log L) ^ 2) *
        Real.exp (2 * C * s * (Real.log L) ^ 2) :=
      mul_le_mul hmeta hmass (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Sum over every code of one fixed length and slot count. -/
lemma short_badCode_sum_bound (R N s : ℕ) (VP VQ L C : ℝ)
    (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : R ≤ s) (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    (∑ c : CrudeWordCode R N R, c.badReciprocalCost VP VQ) ≤
      Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
  calc
    _ ≤ ∑ _c : CrudeWordCode R N R,
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
      exact sum_le_sum (fun c _ => short_badReciprocalCost_bound c VP VQ L C
        hs hL hlog hR hslots hN hspoly hP hQ hPupper hQupper)
    _ = (Fintype.card (CrudeWordCode R N R) : ℝ) *
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ Real.exp ((1 + 5 * C) * s * (Real.log L) ^ 2) *
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (short_crudeWordCode_bound R N s L C hlog hR hslots hN hspoly)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The complete catalog, including both bounded integer parameters, has
the required `exp (O(s log² L))` reciprocal cost. -/
theorem badCatalogCost_exp_bound (s T : ℕ) (VP VQ L C : ℝ)
    (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * s * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    badCatalogCost s T VP VQ ≤
      Real.exp ((13 + 7 * C) * s * (Real.log L) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hfactor : ((s + 1) * (T + 1) : ℕ) ≤
      Real.exp ((4 : ℝ) * s * (Real.log L) ^ 2) := by
    calc
      _ = ((s : ℝ) + 1) * ((T : ℝ) + 1) := by push_cast; rfl
      _ ≤ L ^ (2 : ℕ) * L ^ (2 : ℕ) := by gcongr
      _ = L ^ (4 : ℕ) := by ring
      _ ≤ _ := short_polynomial_exp_bound s 4 L hs hLp hlog
  calc
    badCatalogCost s T VP VQ ≤ ∑ _R : Fin (s + 1), ∑ _N : Fin (T + 1),
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
      apply sum_le_sum
      intro R _
      apply sum_le_sum
      intro N _
      apply short_badCode_sum_bound R.val N.val s VP VQ L C hs hL hlog
        (Nat.le_of_lt_succ R.isLt) _ _ hspoly hP hQ hPupper hQupper
      · have hh : (N.val : ℝ) ≤ T := by exact_mod_cast Nat.le_of_lt_succ N.isLt
        exact hh.trans hslots
      · have hh : (N.val : ℝ) ≤ T := by exact_mod_cast Nat.le_of_lt_succ N.isLt
        linarith
    _ = (((s + 1) * (T + 1) : ℕ) : ℝ) *
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ Real.exp ((4 : ℝ) * s * (Real.log L) ^ 2) *
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

open _root_.Filter

/-- The polynomial side conditions in the finite estimate follow from the
actual short-word and slot budgets once the scale is sufficiently large. -/
theorem eventually_badCatalogCost_exp_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s T : ℕ) (VP VQ : ℝ),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      (T : ℝ) ≤ C * s * Real.log L →
      0 ≤ VP → 0 ≤ VQ → VP ≤ L ^ (2 : ℕ) → VQ ≤ L ^ (2 : ℕ) →
      badCatalogCost s T VP VQ ≤
        Real.exp ((13 + 7 * C) * s * (Real.log L) ^ 2) := by
  have hsmall := (isLittleO_log_rpow_atTop
    (show 0 < (9 / 10 : ℝ) by norm_num)).bound
      (show 0 < 1 / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1), hsmall] with L hL hlog hh
  intro s T VP VQ hs hsupper hslots hP hQ hPupper hQupper
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.log L by linarith),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hClog : C * Real.log L ≤ L ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ (C + 1) * Real.log L := by nlinarith
      _ ≤ (C + 1) * ((1 / (C + 1)) * L ^ (9 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [show C + 1 ≠ 0 by linarith]
  have hsL : (s : ℝ) ≤ L := by
    apply hsupper.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (show 1 ≤ L by linarith)
        (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hTL : (T : ℝ) ≤ L := by
    calc
      _ ≤ (s : ℝ) * (C * Real.log L) := by nlinarith [hslots]
      _ ≤ L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) :=
        mul_le_mul hsupper hClog (by positivity) (by positivity)
      _ = L := by rw [← Real.rpow_add hLp]; norm_num
  exact badCatalogCost_exp_bound s T VP VQ L C hs (by linarith) hlog hslots
    (by nlinarith) (by nlinarith) hP hQ hPupper hQupper

/-- The full short-word enumeration is dominated by the single prime
saving. This is the numerical end of the prohibited-site density estimate. -/
theorem eventually_badCatalog_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s T : ℕ) (VP VQ H B total : ℝ),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      (T : ℝ) ≤ C * s * Real.log L →
      0 ≤ VP → 0 ≤ VQ → VP ≤ L ^ (2 : ℕ) → VQ ≤ L ^ (2 : ℕ) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → 1 ≤ B → B ≤ Real.exp L →
      total ≤ badCatalogCost s T VP VQ * (H⁻¹ + (1 + Real.log B) / H) →
      total ≤ Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_badCatalogCost_exp_bound C hC,
    eventually_bad_event_decay (13 + 7 * C) (by positivity)] with L hcost hdecay
  intro s T VP VQ H B total hs hsupper hslots hP hQ hPupper hQupper hH hB hBupper htotal
  exact hdecay s H B (badCatalogCost s T VP VQ) total hsupper hH hB hBupper
    (hcost s T VP VQ hs hsupper hslots hP hQ hPupper hQupper) htotal

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedPrimeEncoding
namespace OAI

/-! Encoding the actual prohibited numerical words in the reciprocal catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}


theorem covers_prohibited (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hw : ForwardProhibited h s supply (List.ofFn w))
    (hJ : ∀ i, (w i).tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt (List.ofFn w) p j →
      ¬p ∣ h ∧ ∀ a ∈ List.ofFn w, ¬p ∣ a.padding) :
    ∃ e : PrimeWordEncoding R T P Q, e.Prohibited h s J supply ∧
      e.decode = List.ofFn w ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  obtain ⟨e, he, hc, hi, hinj, hweight⟩ := covers w hT ht hq hP hQ hd
  refine ⟨e, ⟨hc, hi, hinj, ?_⟩, he, hweight⟩
  rw [he]
  refine ⟨hw, ?_, ?_, hsupport⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ht i
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hJ i

end PrimeWordEncoding

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedBadSum
namespace OAI

/-! The prohibited-word reciprocal estimate summed over all finite codes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem encoded_prohibited_sum_le (R T h s J : ℕ) (P Q : Finset ℕ)
    (supply : ℕ → ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ e : PrimeWordEncoding R T P Q,
      if e.Prohibited h s J supply then e.weight else 0) ≤
      (∑ n : Fin (T + 1), ∑ c : CrudeWordCode R n.val R,
        c.badReciprocalCost (primeHarmonicMass P) (primeHarmonicMass Q)) *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  rw [Fintype.sum_sigma]
  rw [sum_mul]
  apply sum_le_sum
  intro n _
  rw [Fintype.sum_sigma]
  rw [sum_mul]
  apply sum_le_sum
  intro c _
  rw [Fintype.sum_prod_type]
  by_cases hc : c.KindConsistent
  · by_cases hi : c.RowInjective
    · rw [sum_comm]
      let E (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) : Prop :=
        PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply
      have hE : ∀ a b, E a b →
          let w := c.numericalWord (joinCoordinates c.tupleClasses
            (fun z => (a z).val) (fun z => (b z).val))
          Function.Injective (fun z => (a z).val) ∧
          ForwardProhibited h s supply w ∧
          (∀ t ∈ w, Squarefree t.tuple) ∧
          (∀ t ∈ w, t.tuple.primeFactors.card = J) ∧
          (∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ t ∈ w, ¬p ∣ t.padding) := by
        intro a b he
        exact he.2.2
      have hb := c.prohibited_fiber_reciprocal_bound hc hi P Q E hE
        hP hVP H B hH hB hlo hhi
      have heq : (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
          ∑ a : c.tupleClasses → P,
            if PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply
              then PrimeWordEncoding.weight ⟨n, c, a, b⟩ else 0) =
          ∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
            ∑ a : c.tupleClasses → P, if E a b then
              (∏ i, ((a i).val : ℝ)⁻¹) * ∏ j, ((b j).val : ℝ)⁻¹ else 0 := by
        apply sum_congr rfl
        intro b _
        apply sum_congr rfl
        intro a _
        dsimp only [E, PrimeWordEncoding.weight]
        rw [reciprocal_product_join]
      rw [heq]
      exact hb
    · have he (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
          ¬PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply := fun he => hi he.2.1
      simp only [he, ite_false, sum_const_zero]
      exact mul_nonneg (c.badReciprocalCost_nonneg
        (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
        (by positivity)
  · have he (a : c.tupleClasses → P)
        (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
        ¬PrimeWordEncoding.Prohibited ⟨n, c, a, b⟩ h s J supply := fun he => hc he.1
    simp only [he, ite_false, sum_const_zero]
    exact mul_nonneg (c.badReciprocalCost_nonneg
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
      (by positivity)

/-- Length and slot-count summation retain the one-prime saving. -/
theorem bounded_encoded_prohibited_sum_le (T h s J : ℕ) (P Q : Finset ℕ)
    (supply : ℕ → ℕ → Prop)
    (hP : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ R : Fin (s + 1), ∑ e : PrimeWordEncoding R.val T P Q,
      if e.Prohibited h s J supply then e.weight else 0) ≤
      badCatalogCost s T (primeHarmonicMass P) (primeHarmonicMass Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  unfold badCatalogCost
  rw [sum_mul]
  exact sum_le_sum (fun R _ => encoded_prohibited_sum_le R.val T h s J P Q supply
    hP hVP H B hH hB hlo hhi)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCatalogEncoding
namespace OAI

/-! Covering the manuscript's literal prohibited-word catalog by finite prime codes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma decodeStep_injective {pairs : Finset (ℕ × ℕ)} :
    Function.Injective (decodeStep (pairs := pairs)) := by
  intro a b h
  apply Prod.ext
  · exact congrArg SignedStep.forward h
  · apply Subtype.ext
    exact Prod.ext (congrArg SignedStep.tuple h) (congrArg SignedStep.padding h)

lemma decodeStepWord_injective {pairs : Finset (ℕ × ℕ)} {s : ℕ} :
    Function.Injective (decodeStepWord (pairs := pairs) (s := s)) := by
  rintro ⟨m, a⟩ ⟨n, b⟩ h
  have hm : m = n := by
    apply Fin.ext
    simpa only [decodeStepWord_length] using congrArg List.length h
  subst n
  have hab : a = b := by
    funext i
    apply decodeStep_injective
    exact congrFun (List.ofFn_injective h) i
  cases hab
  rfl

lemma prohibitedCatalog_decode_injective (pairs : Finset (ℕ × ℕ)) (h s : ℕ) :
    Function.Injective (fun c : ProhibitedCatalog pairs h s => decodeStepWord c.val) := by
  intro a b hab
  exact Subtype.ext (decodeStepWord_injective hab)

/-- The supplied finite pair family discharges every side condition used by
the nondegenerate last-prime relation, including the global padding exclusion. -/
theorem prohibitedCatalog_has_encoding (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ)
    (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h)
    (c : ProhibitedCatalog pairs h s) :
    ∃ e : PrimeWordEncoding c.val.1.val (s * (J + M)) P Q,
      e.Prohibited h s J (fun d q => (d, q) ∈ pairs) ∧
      e.decode = decodeStepWord c.val ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹ := by
  let w : Fin c.val.1.val → SignedStep := fun i => decodeStep (c.val.2 i)
  have hw (i : Fin c.val.1.val) : ((w i).tuple, (w i).padding) ∈ pairs :=
    (c.val.2 i).2.property
  have hpairs (a : SignedStep) (ha : a ∈ List.ofFn w) : (a.tuple, a.padding) ∈ pairs := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hw i
  have hT : Fintype.card (ActualPrimeSlot w) ≤ s * (J + M) := by
    apply (actualPrimeSlot_card_le w J M (fun i => (hJ _ (hw i)).le)
      (fun i => hM _ (hw i))).trans
    exact Nat.mul_le_mul_right (J + M) (Nat.le_of_lt_succ c.val.1.isLt)
  apply PrimeWordEncoding.covers_prohibited w hT
    (fun i => ht _ (hw i)) (fun i => hq _ (hw i))
    (fun i => hP _ (hw i)) (fun i => hQ _ (hw i))
    (fun i j => hd.mono (hP _ (hw i)) (hQ _ (hw j))) h s J _ c.property.1
    (fun i => hJ _ (hw i))
  intro p j hp
  obtain ⟨hpprime, a, ha, hpa⟩ := hp
  have hapairs := hpairs a (List.mem_of_getElem? ha)
  have hpP : p ∈ P := hP _ hapairs (hpprime.mem_primeFactors hpa (ht _ hapairs).ne_zero)
  refine ⟨hh p hpP, ?_⟩
  intro b hb hpb
  have hbpairs := hpairs b hb
  have hpQ : p ∈ Q := hQ _ hbpairs (hpprime.mem_primeFactors hpb (hq _ hbpairs).ne_zero)
  exact disjoint_left.mp hd hpP hpQ

/-- The actual catalog sum is bounded by the finite code sum, with each
numerical prime still carrying exactly one reciprocal. -/
theorem prohibitedCatalog_reciprocal_sum_le_encodings
    (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ) (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h) :
    (∑ c : ProhibitedCatalog pairs h s,
      ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹) ≤
      ∑ R : Fin (s + 1), ∑ e : PrimeWordEncoding R.val (s * (J + M)) P Q,
        if e.Prohibited h s J (fun d q => (d, q) ∈ pairs) then e.weight else 0 := by
  let F := (univ : Finset (ProhibitedCatalog pairs h s)).image (fun c => decodeStepWord c.val)
  let C := (R : Fin (s + 1)) × PrimeWordEncoding R.val (s * (J + M)) P Q
  let decode : C → List SignedStep := fun e => e.2.decode
  let weight (w : List SignedStep) : ℝ := ∏ p ∈ wordDivisorPrimeSupport w, (p : ℝ)⁻¹
  let cost (e : C) : ℝ :=
    if e.2.Prohibited h s J (fun d q => (d, q) ∈ pairs) then e.2.weight else 0
  have hsum : (∑ c : ProhibitedCatalog pairs h s, weight (decodeStepWord c.val)) =
      ∑ w ∈ F, weight w := by
    symm
    exact sum_image (fun a _ b _ hab => prohibitedCatalog_decode_injective pairs h s hab)
  have hcost (e : C) : 0 ≤ cost e := by
    dsimp only [cost]
    split_ifs
    · exact e.2.weight_nonneg
    · exact le_rfl
  have hcover (w : List SignedStep) (hw : w ∈ F) :
      ∃ e : C, decode e = w ∧ weight w ≤ cost e := by
    obtain ⟨c, _, rfl⟩ := mem_image.mp hw
    obtain ⟨e, he, hdecode, hweight⟩ :=
      prohibitedCatalog_has_encoding pairs P Q h s J M ht hq hJ hM hP hQ hd hh c
    refine ⟨⟨c.val.1, e⟩, hdecode, ?_⟩
    dsimp only [cost, weight]
    rw [if_pos he, hweight]
  rw [hsum]
  exact (finite_decoding_weight_bound F decode weight cost hcost hcover).trans_eq
    (Fintype.sum_sigma cost)

/-- Full reciprocal estimate for the manuscript's minimal prohibited words. -/
theorem prohibitedCatalog_reciprocal_bound
    (pairs : Finset (ℕ × ℕ)) (P Q : Finset ℕ) (h s J M : ℕ)
    (ht : ∀ dq ∈ pairs, Squarefree dq.1) (hq : ∀ dq ∈ pairs, Squarefree dq.2)
    (hJ : ∀ dq ∈ pairs, dq.1.primeFactors.card = J)
    (hM : ∀ dq ∈ pairs, dq.2.primeFactors.card ≤ M)
    (hP : ∀ dq ∈ pairs, dq.1.primeFactors ⊆ P)
    (hQ : ∀ dq ∈ pairs, dq.2.primeFactors ⊆ Q)
    (hd : Disjoint P Q) (hh : ∀ p ∈ P, ¬p ∣ h)
    (hprime : ∀ p ∈ P, p.Prime) (hVP : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B) :
    (∑ c : ProhibitedCatalog pairs h s,
      ∏ p ∈ wordDivisorPrimeSupport (decodeStepWord c.val), (p : ℝ)⁻¹) ≤
      badCatalogCost s (s * (J + M)) (primeHarmonicMass P) (primeHarmonicMass Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) :=
  (prohibitedCatalog_reciprocal_sum_le_encodings pairs P Q h s J M
    ht hq hJ hM hP hQ hd hh).trans
    (bounded_encoded_prohibited_sum_le (s * (J + M)) h s J P Q
      (fun d q => (d, q) ∈ pairs) hprime hVP H B hH hB hlo hhi)

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







/-- No code count or numerical assignment sum is left implicit here. -/
theorem probability_bound (s B H : ℕ)
    (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B)
    (hVP : 1 ≤ primeHarmonicMass F.P) (hH : 0 < H) (hBone : 1 ≤ B)
    (hlo : ∀ p ∈ F.P, H ≤ p) :
    (F.residueLaw B hB).probability (F.deletedEvent s B) ≤
      badCatalogCost s (s * (J + M)) (primeHarmonicMass F.P) (primeHarmonicMass F.Q) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) := by
  have hc : ∀ c : ProhibitedCatalog F.pairs h s,
      ∀ q ∈ wordDivisorPrimeSupport (decodeStepWord c.val),
      ∃ p : ↥(F.P ∪ F.Q), p.val = q := by
    intro c q hq
    exact ⟨⟨q, F.support_subset s c hq⟩, rfl⟩
  exact (prohibited_residue_probability_le_catalog B (fun p : ↥(F.P ∪ F.Q) => p.val)
    Subtype.val_injective (fun p => (F.prime p).pos) (fun p => hB _ p.property)
    F.pairs h s hc).trans
      (prohibitedCatalog_reciprocal_bound F.pairs F.P F.Q h s J M
        F.tuple_squarefree F.padding_squarefree F.tuple_card F.padding_card
        F.tuple_pool F.padding_pool F.disjoint F.excluded F.primeP hVP
        H B hH hBone hlo (fun p hp => hB p (mem_union_left _ hp)))

end ProhibitedPrimeFamily

open _root_.Filter

/-- The density assertion of `q:bad`, proved from the actual pair family
and independent uniform residues, with the published prime estimates isolated
as their numerical mass and scale consequences. -/
theorem eventually_prohibited_density (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h s J M B H : ℕ) (F : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ F.P ∪ F.Q, p ≤ B),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      ((s * (J + M) : ℕ) : ℝ) ≤ C * s * Real.log L →
      1 ≤ primeHarmonicMass F.P →
      primeHarmonicMass F.P ≤ L ^ (2 : ℕ) → primeHarmonicMass F.Q ≤ L ^ (2 : ℕ) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → 1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ F.P, H ≤ p) →
      (F.residueLaw B hB).probability (F.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_badCatalog_decay C hC] with L hdecay
  intro h s J M B H F hB hs hsupper hslots hVP hPupper hQupper hH hBone hBupper hlo
  have hHpos : 0 < H := by
    exact_mod_cast (Real.exp_pos _).trans_le hH
  exact hdecay s (s * (J + M)) (primeHarmonicMass F.P) (primeHarmonicMass F.Q)
    H B ((F.residueLaw B hB).probability (F.deletedEvent s B)) hs hsupper hslots
    (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity)
    hPupper hQupper hH (by exact_mod_cast hBone) hBupper
    (F.probability_bound s B H hB hVP hHpos hBone hlo)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_prohibited_density := @OAI.TwoPointCorrelations.eventually_prohibited_density
