-- Prove2me | solution 1 for OAI.TwoPointCorrelations.encoded_witness_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:26:31.03259+00:00
-- url     : https://prove2.me/submissions/d2ec0926-c326-4033-8c86-efd6b1a99e7a

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




lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))













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

open _root_.Finset
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

open _root_.Finset

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

open _root_.Finset

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

open _root_.Finset


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

open _root_.Finset

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

open _root_.Finset

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

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonFamily
namespace OAI

/-! Sum the reciprocal savings of fixed singleton relation records. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

/-- The nonzero tests stay in every system event, so the estimate remains
valid for all resampled prime assignments. -/
theorem singleton_family_bound (system : I → OrderedPrimeSystem ι) (K : ℕ)
    (hsize : ∀ i, K ≤ (system i).size)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ N)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log N) / H ≤ 1)
    (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    (∑ i, weight i * ∑ x : ι → P,
      if (system i).Holds (integerPrimeAssignment Subtype.val x)
        then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      (∑ i, weight i) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ K := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hd : 0 ≤ (H : ℝ)⁻¹ + (1 + Real.log N) / H := by positivity
  rw [mul_assoc, sum_mul]
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  apply ((system i).reciprocal_sum_bound P hP hV H N hH hN hlo hhi).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hd hdelta (hsize i))
    (pow_nonneg (by linarith) _)



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








lemma reverseWord_infix {u w : List SignedStep} (hu : u <:+: w) :
    reverseWord u <:+: reverseWord w := hu.reverse.map SignedStep.flip














end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotCode
namespace OAI

/-! A complete equality-pattern code for tuple and padding prime occurrences. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PrimeSlotData

variable {R N : ℕ}







end PrimeSlotData

namespace CrudeWordCode

variable {R N : ℕ}








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


lemma wordSlice_length (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) :
    (wordSlice w a b).length = b - a := by
  simp only [wordSlice, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

lemma wordSlice_split (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    w.take a ++ wordSlice w a b = w.take b := by
  have h := List.take_append_drop a (w.take b)
  simpa only [List.take_take, Nat.min_eq_left hab, List.drop_take, wordSlice] using h

lemma wordSlice_infix (w : List SignedStep) (a b : ℕ) : wordSlice w a b <:+: w := by
  refine ⟨w.take a, (w.drop a).drop (b - a), ?_⟩
  change (w.take a ++ (w.drop a).take (b - a)) ++ (w.drop a).drop (b - a) = w
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

lemma wordSlice_displacement (h : ℕ) (w : List SignedStep) {a b : ℕ} (hab : a ≤ b) :
    wordDisplacement h (wordSlice w a b) = intervalDisplacement (wordStepDisplacement h w) a b := by
  have hs := congrArg (wordDisplacement h) (wordSlice_split w hab)
  rw [wordDisplacement_append, wordDisplacement_take, wordDisplacement_take] at hs
  rw [intervalDisplacement_eq_sub _ hab]
  omega


lemma tuplePrimeAt_slice (w : List SignedStep) (a b p i : ℕ) (hi : i < b - a) :
    TuplePrimeAt (wordSlice w a b) p i ↔ TuplePrimeAt w p (a + i) := by
  unfold TuplePrimeAt wordSlice
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

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

open _root_.Finset

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

/-- Positivity supplies each tuple-prime divisibility at the exact prefix sum. -/
lemma PositiveWord.tuplePrime_departure {h p i : ℕ} {x : ℤ} {w : List SignedStep}
    (hw : PositiveWord h x w) (hp : TuplePrimeAt w p i) :
    (p : ℤ) ∣ x + wordDisplacement h (w.take i) := by
  induction w generalizing x i with
  | nil => simp [TuplePrimeAt] at hp
  | cons a w ih =>
      rcases hw with ⟨ha, hw⟩
      cases i with
      | zero =>
          have hp' := (tuplePrimeAt_iff_getElem (a :: w) p 0 (by simp)).mp hp
          have hcast : (p : ℤ) ∣ (a.tuple : ℤ) := by exact_mod_cast hp'.2
          simpa only [List.take_zero, wordDisplacement_nil, add_zero] using
            (hcast.mul_left (a.padding : ℤ)).trans ha
      | succ i =>
          have hp' : TuplePrimeAt w p i := by simpa [TuplePrimeAt] using hp
          simpa only [List.take_succ_cons, wordDisplacement_cons, add_assoc] using ih hw hp'



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ReversedSegments
namespace OAI

/-! Reversed prohibited subwords used in the active-label descent. -/

namespace TwoPointCorrelations

lemma tuplePrimeAt_reverseWord (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt (reverseWord w) p i ↔ TuplePrimeAt w p (w.length - 1 - i) := by
  rw [tuplePrimeAt_iff_getElem _ _ _ (by simpa using hi),
    tuplePrimeAt_iff_getElem _ _ _ (by omega)]
  simp [reverseWord, SignedStep.flip]

lemma TuplePrimeIntervals.slice {w : List SignedStep} (hw : TuplePrimeIntervals w)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ w.length) : TuplePrimeIntervals (wordSlice w a b) := by
  have hlen := wordSlice_length w hab hb
  intro p i j k hij hjk hk hpi hpk
  have hi : i < b - a := by omega
  have hj : j < b - a := by omega
  have hk' : k < b - a := by omega
  apply (tuplePrimeAt_slice w a b p j hj).mpr
  exact hw p (a + i) (a + j) (a + k) (by omega) (by omega) (by omega)
    ((tuplePrimeAt_slice w a b p i hi).mp hpi)
    ((tuplePrimeAt_slice w a b p k hk').mp hpk)

lemma TuplePrimeIntervals.reverse {w : List SignedStep} (hw : TuplePrimeIntervals w) :
    TuplePrimeIntervals (reverseWord w) := by
  intro p i j k hij hjk hk hpi hpk
  have hk' : k < w.length := by simpa using hk
  rw [tuplePrimeAt_reverseWord w p j (by omega)]
  exact hw p (w.length - 1 - k) (w.length - 1 - j) (w.length - 1 - i)
    (by omega) (by omega) (by omega)
    ((tuplePrimeAt_reverseWord w p k hk').mp hpk)
    ((tuplePrimeAt_reverseWord w p i (by omega)).mp hpi)

lemma reverseWord_drop (w : List SignedStep) (i : ℕ) :
    (reverseWord w).drop i = reverseWord (w.take (w.length - i)) := by
  simp [reverseWord, List.drop_reverse]

lemma reverseWord_slice_drop (w : List SignedStep) {a b c : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (hb : b ≤ w.length) :
    (reverseWord (wordSlice w a b)).drop (b - c) = reverseWord (wordSlice w a c) := by
  rw [reverseWord_drop, wordSlice_length w (by omega) hb]
  rw [show b - a - (b - c) = c - a by omega]
  congr 1
  simp only [wordSlice, List.take_take, Nat.min_eq_left (by omega : c - a ≤ b - a)]

lemma reverseWord_chain {w : List SignedStep}
    (hw : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    (reverseWord w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  rw [List.isChain_iff_getElem] at hw ⊢
  intro i hi
  have hi' : i + 1 < w.length := by simpa using hi
  have h := hw (w.length - 2 - i) (by omega)
  have heq : w.length - 2 - i + 1 = w.length - 1 - i := by omega
  simp only [reverseWord, List.getElem_map, List.getElem_reverse,
    SignedStep.flip] at *
  simpa only [heq, show w.length - 1 - (i + 1) = w.length - 2 - i by omega] using h.symm

/-- The reversed interval is genuinely forward-prohibited. The divisible
suffix has length `c-a`, while its preceding part has positive length. -/
lemma reversed_interval_forwardProhibited (h s : ℕ) (supply : ℕ → ℕ → Prop)
    (w : List SignedStep) (hlen : w.length ≤ s)
    (hsupply : ∀ t ∈ w, supply t.tuple t.padding)
    (hchain : w.IsChain (fun a b => a.tuple ≠ b.tuple))
    (hinterval : TuplePrimeIntervals w) {a b c p : ℕ}
    (hac : a + 1 < c) (hcb : c < b) (hb : b ≤ w.length)
    (hp : TuplePrimeAt w p (b - 1)) (hnot : ¬TuplePrimeAt w p a)
    (hdiv : (p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a c) :
    ForwardProhibited h s supply (reverseWord (wordSlice w a b)) := by
  have hab : a ≤ b := by omega
  have hlength := wordSlice_length w hab hb
  refine ⟨by simp only [reverseWord_length, hlength]; omega,
    by simp only [reverseWord_length, hlength]; omega, ?_,
    reverseWord_chain ((hchain.drop a).take (b - a)),
    (hinterval.slice hab hb).reverse, p, ?_, ?_, b - c, by omega, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    have hum : u ∈ wordSlice w a b := by simpa using hu
    exact hsupply u ((wordSlice_infix w a b).subset hum)
  · rw [tuplePrimeAt_reverseWord _ _ _ (by omega)]
    apply (tuplePrimeAt_slice w a b p _ (by omega)).mpr
    simpa only [show a + ((wordSlice w a b).length - 1 - 0) = b - 1 by omega] using hp
  · intro hp'
    rw [tuplePrimeAt_reverseWord _ _ _ (by simp only [reverseWord_length] at *; omega)] at hp'
    have hp'' := (tuplePrimeAt_slice w a b p _ (by omega)).mp hp'
    exact hnot (by simpa only [reverseWord_length,
      show a + ((wordSlice w a b).length - 1 - ((wordSlice w a b).length - 1)) = a by omega] using hp'')
  · simp only [reverseWord_length, hlength]
    omega
  · rw [reverseWord_slice_drop w (by omega) (by omega) hb,
      wordDisplacement_reverseWord, wordSlice_displacement h w (by omega)]
    exact hdiv.neg_right

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActiveLabels
namespace OAI

/-! Active numerical labels in minimal prohibited witnesses. -/

namespace TwoPointCorrelations

open _root_.Finset




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

/-- Intersecting an interval-shaped occurrence set with a prefix gives an
explicit nonempty interval of indices. -/
lemma TuplePrimeIntervals.prefix_occurrences {w : List SignedStep}
    (hw : TuplePrimeIntervals w) (p n : ℕ) (hn : n ≤ w.length)
    (hp : ∃ j, j < n ∧ TuplePrimeAt w p j) :
    ∃ a b, a < b ∧ b ≤ n ∧ ∀ i, i < n →
      (TuplePrimeAt w p i ↔ a ≤ i ∧ i < b) := by
  classical
  let S := (range n).filter (TuplePrimeAt w p)
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hpj⟩ := hp
    exact ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, hpj⟩⟩
  let a := S.min' hS
  let b := S.max' hS + 1
  have haS : a ∈ S := min'_mem S hS
  have hbS : b - 1 ∈ S := by
    simpa only [b, Nat.add_sub_cancel] using max'_mem S hS
  have han := (mem_range.mp (mem_filter.mp haS).1)
  have hbn := (mem_range.mp (mem_filter.mp hbS).1)
  have hab : a < b := by
    have h := min'_le S (S.max' hS) (max'_mem S hS)
    dsimp [a, b]
    omega
  refine ⟨a, b, hab, by dsimp [b] at *; omega, ?_⟩
  intro i hi
  constructor
  · intro hpi
    have hiS : i ∈ S := mem_filter.mpr ⟨mem_range.mpr hi, hpi⟩
    exact ⟨min'_le S i hiS, Nat.lt_succ_of_le (le_max' S i hiS)⟩
  · rintro ⟨hai, hib⟩
    exact hw p a i (b - 1) hai (by omega) (by omega)
      (mem_filter.mp haS).2 (mem_filter.mp hbS).2

lemma wordPrimeContribution_restrict (h : ℕ) (w : List SignedStep) (p n a b : ℕ)
    (hbn : b ≤ n)
    (hp : ∀ i, i < n → (TuplePrimeAt w p i ↔ a ≤ i ∧ i < b)) :
    wordPrimeContribution h w p 0 n = intervalDisplacement (wordStepDisplacement h w) a b := by
  classical
  unfold wordPrimeContribution intervalDisplacement
  calc
    _ = ∑ i ∈ Ico a b, if TuplePrimeAt w p i then wordStepDisplacement h w i else 0 := by
      symm
      apply Finset.sum_subset (Ico_subset_Ico (Nat.zero_le a) hbn)
      intro i hi hin
      have hnot : ¬TuplePrimeAt w p i := by
        intro hpi
        exact hin (mem_Ico.mpr ((hp i (mem_Ico.mp hi).2).mp hpi))
      simp only [hnot, ite_false]
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      simp only [(hp i (lt_of_lt_of_le (mem_Ico.mp hi).2 hbn)).mpr
        ⟨(mem_Ico.mp hi).1, (mem_Ico.mp hi).2⟩, ite_true]

/-- Minimality forbids a reversed suffix starting at a strictly positive
index, when an internal initial segment is divisible by its final prime. -/
lemma MinimalWord.no_reversed_divisible_interval {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : MinimalWord (ForwardProhibited h s supply) w)
    {a c p : ℕ} (ha : 0 < a) (hac : a + 1 < c) (hc : c < w.length)
    (hp : TuplePrimeAt w p (w.length - 1)) (hnot : ¬TuplePrimeAt w p a) :
    ¬(p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a c := by
  intro hdiv
  have hpro := reversed_interval_forwardProhibited h s supply w hw.1.2.1 hw.1.2.2.1
    hw.1.2.2.2.1 hw.1.2.2.2.2.1 hac hc le_rfl hp hnot hdiv
  apply hw.2 (reverseWord (wordSlice w a w.length))
    (Or.inr (reverseWord_infix (wordSlice_infix w a w.length))) ?_ hpro
  rw [reverseWord_length, wordSlice_length w (by omega) le_rfl]
  omega

/-- Every label of a minimal prohibited word is active or has a nonzero
prefix contribution modulo an active label used at that departure. -/
theorem MinimalWord.active_dichotomy {h s : ℕ} {supply : ℕ → ℕ → Prop}
    {w : List SignedStep} (hw : MinimalWord (ForwardProhibited h s supply) w)
    (hnew : ∀ i, i + 1 < w.length →
      ∃ p, TuplePrimeAt w p (i + 1) ∧ ¬TuplePrimeAt w p i)
    (hoff : ∀ p i, (∃ j, TuplePrimeAt w p j) → i < w.length →
      ¬TuplePrimeAt w p i → ¬(p : ℤ) ∣ wordStepDisplacement h w i)
    (y : ℕ) (hy : ∃ j, TuplePrimeAt w y j) :
    ActivePrime h w y ∨ ∃ z i, ActivePrime h w z ∧ TuplePrimeAt w z i ∧
      ¬(z : ℤ) ∣ wordPrimeContribution h w y 0 i := by
  classical
  have hlen : 3 ≤ w.length := hw.1.1
  have hinter : TuplePrimeIntervals w := hw.1.2.2.2.2.1
  obtain ⟨z, hzlast', hzprev⟩ := hnew (w.length - 2) (by omega)
  have heqlast : w.length - 2 + 1 = w.length - 1 := by omega
  have hzlast : TuplePrimeAt w z (w.length - 1) := heqlast ▸ hzlast'
  have hzearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w z i := by
    intro i hi hzi
    exact hzprev (hinter z i (w.length - 2) (w.length - 1)
      (by omega) (by omega) (by omega) hzi hzlast)
  have hzactive := hw.1.last_new_active hzlast hzearly hoff
  by_cases hypre : ∃ j, j < w.length - 1 ∧ TuplePrimeAt w y j
  · obtain ⟨a, b, hab, hbn, hyinterval⟩ :=
      hinter.prefix_occurrences y (w.length - 1) (by omega) hypre
    have hyeq := wordPrimeContribution_restrict h w y (w.length - 1) a b hbn hyinterval
    by_cases hzd : (z : ℤ) ∣ wordPrimeContribution h w y 0 (w.length - 1)
    · have hdiv : (z : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) a b := by
        rwa [hyeq] at hzd
      have hab2 : a + 1 < b := by
        by_contra hn
        have hb : b = a + 1 := by omega
        have hd := hoff z a ⟨w.length - 1, hzlast⟩ (by omega) (hzearly a (by omega))
        exact hd (by simpa only [hb, intervalDisplacement_singleton] using hdiv)
      have ha : a = 0 := by
        by_contra hn
        exact hw.no_reversed_divisible_interval (by omega) hab2 (by omega)
          hzlast (hzearly a (by omega)) hdiv
      obtain ⟨z', hz'one, hz'zero⟩ := hnew 0 (by omega)
      obtain ⟨a', b', hab', hb'b, hz'interval⟩ :=
        hinter.prefix_occurrences z' b (by omega) ⟨1, by omega, hz'one⟩
      have ha' : a' = 1 := by
        have hle := ((hz'interval 1 (by omega)).mp hz'one).1
        have hne : a' ≠ 0 := by
          intro heq
          have hp := (hz'interval a' (by omega)).mpr ⟨le_rfl, hab'⟩
          exact hz'zero (by simpa only [heq] using hp)
        omega
      have hzeq := wordPrimeContribution_restrict h w z' b a' b' hb'b hz'interval
      have hnonzero : ¬(z : ℤ) ∣ wordPrimeContribution h w z' 0 b := by
        intro hzero
        have hdiv' : (z : ℤ) ∣ intervalDisplacement (wordStepDisplacement h w) 1 b' := by
          simpa only [hzeq, ha'] using hzero
        have hb' : 2 < b' := by
          by_contra hn
          have hb'eq : b' = 1 + 1 := by omega
          exact (hoff z 1 ⟨w.length - 1, hzlast⟩ (by omega) (hzearly 1 (by omega)))
            (by simpa only [hb'eq, intervalDisplacement_singleton] using hdiv')
        exact hw.no_reversed_divisible_interval (by omega) hb' (by omega)
          hzlast (hzearly 1 (by omega)) hdiv'
      have hz'active : ActivePrime h w z' := by
        refine ⟨z, 0, b, by omega, by omega, ⟨w.length - 1, hzlast⟩, ?_, hnonzero⟩
        simpa only [ha] using hdiv
      right
      refine ⟨z', 1, hz'active, hz'one, ?_⟩
      have hyzero : TuplePrimeAt w y 0 := (hyinterval 0 (by omega)).mpr ⟨by omega, by omega⟩
      rw [wordPrimeContribution_eq_singleton h w y 0 1 0 (by simp) hyzero]
      · exact hoff z' 0 ⟨1, hz'one⟩ (by omega) hz'zero
      · intro i hi _
        have := mem_Ico.mp hi
        omega
    · exact Or.inr ⟨z, w.length - 1, hzactive, hzlast, hzd⟩
  · left
    have hyearly : ∀ i, i < w.length - 1 → ¬TuplePrimeAt w y i := by
      intro i hi hpi
      exact hypre ⟨i, hi, hpi⟩
    obtain ⟨j, hyj⟩ := hy
    have hj := hyj.index_lt
    have hjeq : j = w.length - 1 := by
      by_contra hn
      exact hyearly j (by omega) hyj
    exact hw.1.last_new_active (hjeq ▸ hyj) hyearly hoff

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

/-- The active-label dichotomy with the manuscript's concrete arithmetic
hypotheses: squarefree whole tuples of fixed prime-factor count, and prime
exclusion from the common multiplier and all padding factors. -/
theorem MinimalWord.active_dichotomy_of_squarefree {h s J : ℕ}
    {supply : ℕ → ℕ → Prop} {w : List SignedStep}
    (hw : MinimalWord (ForwardProhibited h s supply) w)
    (hsq : ∀ a ∈ w, Squarefree a.tuple)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt w p j → ¬p ∣ h ∧ ∀ a ∈ w, ¬p ∣ a.padding)
    (y : ℕ) (hy : ∃ j, TuplePrimeAt w y j) :
    ActivePrime h w y ∨ ∃ z i, ActivePrime h w z ∧ TuplePrimeAt w z i ∧
      ¬(z : ℤ) ∣ wordPrimeContribution h w y 0 i := by
  apply hw.active_dichotomy (adjacent_tuple_new_prime w J hsq hcard hw.1.2.2.2.1) ?_ y hy
  intro p i hseen hi hnot
  apply word_prime_support hsupport p i ?_ hi hnot
  obtain ⟨j, hj⟩ := hseen
  exact ⟨j, hj.index_lt, hj⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSupport
namespace OAI

/-! Concrete prime supports of numerical witness words. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma mem_wordPrimeSupport (p : ℕ) (w : List SignedStep) :
    p ∈ wordPrimeSupport w ↔ ∃ a ∈ w, p ∈ a.tuple.primeFactors := by
  induction w with
  | nil => simp [wordPrimeSupport]
  | cons a w ih => simp only [wordPrimeSupport, mem_union, ih, List.mem_cons]; aesop

lemma mem_wordPrimeSupport_iff (p : ℕ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree a.tuple) :
    p ∈ wordPrimeSupport w ↔ ∃ i, TuplePrimeAt w p i := by
  rw [mem_wordPrimeSupport]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hprime := Nat.mem_primeFactors.mp hp
    exact ⟨i, hprime.1, a, hi, hprime.2.1⟩
  · rintro ⟨i, hp, a, hi, hpa⟩
    have ha : a ∈ w := List.mem_iff_getElem?.mpr ⟨i, hi⟩
    exact ⟨a, ha, Nat.mem_primeFactors.mpr ⟨hp, hpa, (hsq a ha).ne_zero⟩⟩






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSelection
namespace OAI

/-!
# Selecting a triangular family of witness relations

The finite split in the singleton argument is performed on actual numerical
witness words. The comparison alternatives retain the neighboring witness,
its control prime, the selected internal departure, and the nonzero private
prime contribution at that departure.
-/

namespace TwoPointCorrelations

open _root_.Finset



/-- The internal active alternative and the two ordered comparison
alternatives needed for successive elimination. -/
theorem select_witness_relations {n K h s J : ℕ} {supply : ℕ → ℕ → Prop}
    (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n)
    (hminimal : ∀ i, MinimalWord (ForwardProhibited h s supply) (word i))
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hcard : ∀ i t, t ∈ word i → t.tuple.primeFactors.card = J)
    (hsupport : ∀ i p j, TuplePrimeAt (word i) p j →
      ¬p ∣ h ∧ ∀ t ∈ word i, ¬p ∣ t.padding)
    (hmark : ∀ i, mark i ∈ wordPrimeSupport (word i))
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j)) :
    ∃ R : Finset (Fin n), K ≤ R.card ∧
      ((∀ i ∈ R, freshActiveBefore h word i) ∨
       (∀ i ∈ R, freshActiveAfter h word i) ∨
       (∀ i ∈ R, attachment i ≤ position i ∧
         ∃ z r j, j < i ∧ ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
           ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
           z ∈ wordPrimeSupport (word j)) ∨
       (∀ i ∈ R, position i < attachment i ∧
         ∃ z r j, i < j ∧ ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
           ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
           z ∈ wordPrimeSupport (word j))) := by
  classical
  let B : Finset (Fin n) := univ.filter (freshActiveBefore h word)
  let A : Finset (Fin n) := univ.filter (freshActiveAfter h word)
  let C : Finset (Fin n) := univ.filter (fun i =>
    i ∉ B ∧ i ∉ A ∧ attachment i ≤ position i)
  let D : Finset (Fin n) := univ.filter (fun i =>
    i ∉ B ∧ i ∉ A ∧ position i < attachment i)
  have hcover : B ∪ A ∪ C ∪ D = univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_cases hiB : i ∈ B
    · simp only [mem_union]; tauto
    by_cases hiA : i ∈ A
    · simp only [mem_union]; tauto
    by_cases hi : attachment i ≤ position i
    · have hiC : i ∈ C := mem_filter.mpr ⟨mem_univ _, hiB, hiA, hi⟩
      simp only [mem_union]; tauto
    · have hiD : i ∈ D := mem_filter.mpr ⟨mem_univ _, hiB, hiA, by omega⟩
      simp only [mem_union]; tauto
  have hcount : n ≤ B.card + A.card + C.card + D.card := by
    have hBA := card_union_le B A
    have hBAC := card_union_le (B ∪ A) C
    have hBACD := card_union_le (B ∪ A ∪ C) D
    rw [hcover, card_univ, Fintype.card_fin] at hBACD
    omega
  have hcompare (i : Fin n) (hiB : i ∉ B) (hiA : i ∉ A) :
      ∃ z r, ActivePrime h (word i) z ∧ TuplePrimeAt (word i) z r ∧
        ¬(z : ℤ) ∣ wordPrimeContribution h (word i) (mark i) 0 r ∧
        (∃ j : Fin n, j < i ∧ z ∈ wordPrimeSupport (word j)) ∧
        (∃ j : Fin n, i < j ∧ z ∈ wordPrimeSupport (word j)) := by
    have hnotactive : ¬ActivePrime h (word i) (mark i) := by
      intro ha
      apply hiB
      exact mem_filter.mpr ⟨mem_univ _, mark i, ha,
        fun j hji => hprivate i j (ne_of_lt hji)⟩
    have hocc := (mem_wordPrimeSupport_iff (mark i) (word i) (hsq i)).mp (hmark i)
    rcases (hminimal i).active_dichotomy_of_squarefree (hsq i) (hcard i) (hsupport i)
      (mark i) hocc with ha | ⟨z, r, hz, hzr, hn⟩
    · exact False.elim (hnotactive ha)
    · refine ⟨z, r, hz, hzr, hn, ?_, ?_⟩
      · by_contra! hj
        exact hiB (mem_filter.mpr ⟨mem_univ _, z, hz, hj⟩)
      · by_contra! hj
        exact hiA (mem_filter.mpr ⟨mem_univ _, z, hz, hj⟩)
  by_cases hB : K ≤ B.card
  · exact ⟨B, hB, Or.inl (fun i hi => (mem_filter.mp hi).2)⟩
  by_cases hA : K ≤ A.card
  · exact ⟨A, hA, Or.inr (Or.inl (fun i hi => (mem_filter.mp hi).2))⟩
  by_cases hC : K ≤ C.card
  · refine ⟨C, hC, Or.inr (Or.inr (Or.inl ?_))⟩
    intro i hi
    rcases (mem_filter.mp hi).2 with ⟨hiB, hiA, htime⟩
    obtain ⟨z, r, hz, hzr, hn, ⟨j, hji, hzj⟩, _⟩ := hcompare i hiB hiA
    exact ⟨htime, z, r, j, hji, hz, hzr, hn, hzj⟩
  · have hD : K ≤ D.card := by omega
    refine ⟨D, hD, Or.inr (Or.inr (Or.inr ?_))⟩
    intro i hi
    rcases (mem_filter.mp hi).2 with ⟨hiB, hiA, htime⟩
    obtain ⟨z, r, hz, hzr, hn, _, ⟨j, hij, hzj⟩⟩ := hcompare i hiB hiA
    exact ⟨htime, z, r, j, hij, hz, hzr, hn, hzj⟩

lemma wordPrimeContribution_zero_of_not_mem (h : ℕ) (w : List SignedStep) (p a b : ℕ)
    (hsq : ∀ t ∈ w, Squarefree t.tuple) (hp : p ∉ wordPrimeSupport w) :
    wordPrimeContribution h w p a b = 0 := by
  classical
  unfold wordPrimeContribution
  apply sum_eq_zero
  intro i _
  have hnot : ¬TuplePrimeAt w p i := fun hpi =>
    hp ((mem_wordPrimeSupport_iff p w hsq).mpr ⟨i, hpi⟩)
  simp only [hnot, ite_false]

lemma ActivePrime.mem_wordPrimeSupport {h p : ℕ} {w : List SignedStep}
    (hp : ActivePrime h w p) (hsq : ∀ t ∈ w, Squarefree t.tuple) :
    p ∈ wordPrimeSupport w := by
  by_contra hnot
  obtain ⟨c, a, b, _, _, _, _, hnonzero⟩ := hp
  apply hnonzero
  rw [wordPrimeContribution_zero_of_not_mem h w p a b hsq hnot]
  exact dvd_zero _

/-- Fresh active labels can be chosen injectively. Earlier internal relations
contain none of the later chosen variables. -/
theorem select_fresh_before_labels {n h : ℕ} (word : Fin n → List SignedStep)
    (R : Finset (Fin n)) (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hfresh : ∀ i ∈ R, freshActiveBefore h word i) :
    ∃ z : R → ℕ, Function.Injective z ∧
      (∀ i : R, ActivePrime h (word i) (z i)) ∧
      ∀ i j : R, i.val < j.val → z j ∉ wordPrimeSupport (word i) := by
  classical
  have hex (i : R) : ∃ z, ActivePrime h (word i) z ∧
      ∀ j : Fin n, j < i.val → z ∉ wordPrimeSupport (word j) := hfresh i i.property
  choose z hz using hex
  refine ⟨z, ?_, (fun i => (hz i).1), fun i j hij => (hz j).2 i hij⟩
  intro i j heq
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (hz j).2 i hij (heq ▸ (hz i).1.mem_wordPrimeSupport (hsq i))
  · exact (hz i).2 j hji (heq.symm ▸ (hz j).1.mem_wordPrimeSupport (hsq j))

/-- The reversed order gives the other internal triangular system. -/
theorem select_fresh_after_labels {n h : ℕ} (word : Fin n → List SignedStep)
    (R : Finset (Fin n)) (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hfresh : ∀ i ∈ R, freshActiveAfter h word i) :
    ∃ z : R → ℕ, Function.Injective z ∧
      (∀ i : R, ActivePrime h (word i) (z i)) ∧
      ∀ i j : R, j.val < i.val → z j ∉ wordPrimeSupport (word i) := by
  classical
  have hex (i : R) : ∃ z, ActivePrime h (word i) z ∧
      ∀ j : Fin n, i.val < j → z ∉ wordPrimeSupport (word j) := hfresh i i.property
  choose z hz using hex
  refine ⟨z, ?_, (fun i => (hz i).1), fun i j hji => (hz j).2 i hji⟩
  intro i j heq
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (hz i).2 j hij (heq.symm ▸ (hz j).1.mem_wordPrimeSupport (hsq j))
  · exact (hz j).2 i hji (heq ▸ (hz i).1.mem_wordPrimeSupport (hsq i))

/-- A prime shared by two different witnesses is none of their family's
private marked primes. This includes the comparison's controlling prime. -/
lemma shared_prime_ne_private {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j : Fin n} (hij : i ≠ j) {z : ℕ}
    (hi : z ∈ wordPrimeSupport (word i)) (hj : z ∈ wordPrimeSupport (word j)) :
    ∀ k, z ≠ mark k := by
  intro k heq
  by_cases hki : k = i
  · subst k
    exact hprivate i j hij.symm (heq ▸ hj)
  · exact hprivate k i (fun heq => hki heq.symm) (heq ▸ hi)

/-- In the earlier-comparison case, every later selected private label is
absent from both witness prefixes and from the entire main segment. -/
lemma earlier_comparison_excludes_later {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j k : Fin n} (hji : j < i) (hik : i < k) (hpos : attachment k ≤ position k) :
    mark k ∉ wordPrimeSupport (word i) ∧ mark k ∉ wordPrimeSupport (word j) ∧
      ∀ v ∈ Ico (attachment j) (attachment i), v ≠ position k := by
  refine ⟨hprivate k i (ne_of_lt hik), hprivate k j (ne_of_lt (hji.trans hik)), ?_⟩
  intro v hv heq
  have hle := horder hik.le
  have hv' := (mem_Ico.mp hv).2
  omega

/-- In the later-comparison case, reverse attachment order gives the same
absence for every still-to-be-eliminated private variable. -/
lemma later_comparison_excludes_earlier {n : ℕ} (word : Fin n → List SignedStep)
    (mark : Fin n → ℕ) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    {i j k : Fin n} (hij : i < j) (hki : k < i) (hpos : position k < attachment k) :
    mark k ∉ wordPrimeSupport (word i) ∧ mark k ∉ wordPrimeSupport (word j) ∧
      ∀ v ∈ Ico (attachment i) (attachment j), v ≠ position k := by
  refine ⟨hprivate k i (ne_of_gt hki), hprivate k j (ne_of_gt (hki.trans hij)), ?_⟩
  intro v hv heq
  have hle := horder hki.le
  have hv' := (mem_Ico.mp hv).1
  omega

/-- Positivity at two departures in the same configuration gives the exact
comparison congruence used by the selected triangular systems. -/
lemma PositiveWord.comparison_relation {h p ri rj : ℕ} {xi xj : ℤ}
    {wi wj : List SignedStep} (hi : PositiveWord h xi wi) (hj : PositiveWord h xj wj)
    (hpi : TuplePrimeAt wi p ri) (hpj : TuplePrimeAt wj p rj) :
    (p : ℤ) ∣ (xi + wordDisplacement h (wi.take ri)) -
      (xj + wordDisplacement h (wj.take rj)) :=
  (hi.tuplePrime_departure hpi).sub (hj.tuplePrime_departure hpj)

lemma wordPrimeContribution_zero_of_avoids (h : ℕ) (w : List SignedStep) (p a b : ℕ)
    (hp : ∀ i ∈ Ico a b, ¬TuplePrimeAt w p i) :
    wordPrimeContribution h w p a b = 0 := by
  classical
  unfold wordPrimeContribution
  apply sum_eq_zero
  intro i hi
  simp only [hp i hi, ite_false]

lemma wordPrimeContribution_zero_of_unique_position (h : ℕ) (w : List SignedStep)
    (p a b position : ℕ) (hunique : ∀ i, TuplePrimeAt w p i → i = position)
    (hposition : ∀ i ∈ Ico a b, i ≠ position) :
    wordPrimeContribution h w p a b = 0 := by
  apply wordPrimeContribution_zero_of_avoids
  intro i hi hpi
  exact hposition i hi (hunique i hpi)

lemma PositiveWord.main_comparison_relation {h p ai aj ri rj : ℕ} {x : ℤ}
    {main wi wj : List SignedStep} (haji : aj ≤ ai)
    (hi : PositiveWord h (x + wordDisplacement h (main.take ai)) wi)
    (hj : PositiveWord h (x + wordDisplacement h (main.take aj)) wj)
    (hpi : TuplePrimeAt wi p ri) (hpj : TuplePrimeAt wj p rj) :
    (p : ℤ) ∣ intervalDisplacement (wordStepDisplacement h main) aj ai +
      wordDisplacement h (wi.take ri) - wordDisplacement h (wj.take rj) := by
  have hr := hi.comparison_relation hj hpi hpj
  rw [intervalDisplacement_eq_sub _ haji]
  simp only [wordDisplacement_take] at hr ⊢
  convert (preTransparency := .instances) hr using 1
  ring

/-- The private selected prime has exactly its designated nonzero prefix
contribution in an earlier comparison; all other contributions vanish. -/
lemma earlier_comparison_private_contribution {n h : ℕ}
    (main : List SignedStep) (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    (hmain : ∀ i v, TuplePrimeAt main (mark i) v → v = position i)
    {i j : Fin n} (hji : j < i) (hpos : attachment i ≤ position i)
    (ri rj : ℕ) :
    wordPrimeContribution h main (mark i) (attachment j) (attachment i) +
      wordPrimeContribution h (word i) (mark i) 0 ri -
      wordPrimeContribution h (word j) (mark i) 0 rj =
      wordPrimeContribution h (word i) (mark i) 0 ri := by
  have hm : wordPrimeContribution h main (mark i) (attachment j) (attachment i) = 0 := by
    apply wordPrimeContribution_zero_of_unique_position h main (mark i) _ _ (position i) (hmain i)
    intro v hv heq
    have hv' := (mem_Ico.mp hv).2
    omega
  have hjzero := wordPrimeContribution_zero_of_not_mem h (word j) (mark i) 0 rj
    (hsq j) (hprivate i j (ne_of_lt hji))
  rw [hm, hjzero]
  ring

/-- The later comparison changes the selected prefix's sign, preserving its
nonvanishing modulo the controlling prime. -/
lemma later_comparison_private_contribution {n h : ℕ}
    (main : List SignedStep) (word : Fin n → List SignedStep) (mark : Fin n → ℕ)
    (attachment position : Fin n → ℕ)
    (hsq : ∀ i t, t ∈ word i → Squarefree t.tuple)
    (hprivate : ∀ i j, j ≠ i → mark i ∉ wordPrimeSupport (word j))
    (hmain : ∀ i v, TuplePrimeAt main (mark i) v → v = position i)
    {i j : Fin n} (hij : i < j) (hpos : position i < attachment i)
    (ri rj : ℕ) :
    wordPrimeContribution h main (mark i) (attachment i) (attachment j) +
      wordPrimeContribution h (word j) (mark i) 0 rj -
      wordPrimeContribution h (word i) (mark i) 0 ri =
      -wordPrimeContribution h (word i) (mark i) 0 ri := by
  have hm : wordPrimeContribution h main (mark i) (attachment i) (attachment j) = 0 := by
    apply wordPrimeContribution_zero_of_unique_position h main (mark i) _ _ (position i) (hmain i)
    intro v hv heq
    have hv' := (mem_Ico.mp hv).1
    omega
  have hjzero := wordPrimeContribution_zero_of_not_mem h (word j) (mark i) 0 rj
    (hsq j) (hprivate i j (ne_of_gt hij))
  rw [hm, hjzero]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledPrimeWords
namespace OAI

/-! Identifying squarefree-label polynomials with numerical signed words. -/

namespace TwoPointCorrelations

open _root_.Finset


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


lemma intervalRelation_support (w : LabeledPrimeWord ι) (h a b : ℕ) (y : ι) :
    y ∈ primeRelationSupport (w.intervalRelation h a b) ↔
      ∃ i : Fin w.word.length, a ≤ i.val ∧ i.val < b ∧ y ∈ w.labels i := by
  simp only [primeRelationSupport, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hab : a ≤ i.val ∧ i.val < b
    · exact ⟨i, hab.1, hab.2, by simpa only [intervalRelation, if_pos hab, monomial] using hi⟩
    · simp only [intervalRelation, if_neg hab, notMem_empty] at hi
  · rintro ⟨i, hai, hib, hi⟩
    exact ⟨i, by simpa only [intervalRelation, if_pos (And.intro hai hib), monomial] using hi⟩

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

open _root_.Finset

variable {ι τ σ : Type*} [DecidableEq ι] [Fintype τ] [Fintype σ]



omit [DecidableEq ι] in
lemma relationAdd_eval (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) (x : ι → ℤ) :
    primeRelationEval (relationAdd m n) x = primeRelationEval m x + primeRelationEval n x := by
  simp [primeRelationEval, relationAdd, Fintype.sum_sum_type]

omit [DecidableEq ι] in
lemma relationNeg_eval (m : τ → PrimeMonomial ι) (x : ι → ℤ) :
    primeRelationEval (relationNeg m) x = -primeRelationEval m x := by
  simp [primeRelationEval, relationNeg, PrimeMonomial.eval]

lemma relationAdd_contribution (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι)
    (y : ι) (x : ι → ℤ) :
    primeRelationContribution (relationAdd m n) y x =
      primeRelationContribution m y x + primeRelationContribution n y x := by
  simp only [primeRelationContribution, relationAdd, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  congr 1

lemma relationNeg_contribution (m : τ → PrimeMonomial ι) (y : ι) (x : ι → ℤ) :
    primeRelationContribution (relationNeg m) y x = -primeRelationContribution m y x := by
  unfold primeRelationContribution
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro t _
  by_cases ht : y ∈ (m t).labels <;> simp [relationNeg, PrimeMonomial.eval, ht]

lemma relationAdd_support (m : τ → PrimeMonomial ι) (n : σ → PrimeMonomial ι) :
    primeRelationSupport (relationAdd m n) = primeRelationSupport m ∪ primeRelationSupport n := by
  ext y
  simp [primeRelationSupport, relationAdd, Sum.exists]

lemma relationNeg_support (m : τ → PrimeMonomial ι) :
    primeRelationSupport (relationNeg m) = primeRelationSupport m := rfl

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


lemma intervalRelation_not_mem (w : LabeledPrimeWord ι) (h a b : ℕ)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι)
    (hno : ∀ r, a ≤ r → r < b → ¬TuplePrimeAt w.word (value y) r) :
    y ∉ primeRelationSupport (w.intervalRelation h a b) := by
  intro hy
  obtain ⟨r, har, hrb, hyr⟩ := (w.intervalRelation_support h a b y).mp hy
  exact hno r har hrb ((w.label_iff_occurrence value hinj hprime hw y r).mp hyr)

end LabeledPrimeWord


lemma comparisonRelation_eval {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (hri : ri ≤ wi.word.length) (hrj : rj ≤ wj.word.length) :
    primeRelationEval (comparisonRelation main wi wj h aj ai ri rj) (fun j => (value j : ℤ)) =
      intervalDisplacement (wordStepDisplacement h main.word) aj ai +
        wordDisplacement h (wi.word.take ri) - wordDisplacement h (wj.word.take rj) := by
  rw [comparisonRelation, relationAdd_eval, relationAdd_eval, relationNeg_eval,
    main.intervalRelation_eval h aj ai value hm hai,
    wi.intervalRelation_eval h 0 ri value hi hri, wj.intervalRelation_eval h 0 rj value hj hrj]
  simp only [intervalDisplacement, Nat.Ico_zero_eq_range, wordDisplacement_take]
  ring

lemma comparisonRelation_contribution {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (hri : ri ≤ wi.word.length) (hrj : rj ≤ wj.word.length) (y : ι) :
    primeRelationContribution (comparisonRelation main wi wj h aj ai ri rj) y
        (fun j => (value j : ℤ)) =
      wordPrimeContribution h main.word (value y) aj ai +
        wordPrimeContribution h wi.word (value y) 0 ri -
        wordPrimeContribution h wj.word (value y) 0 rj := by
  rw [comparisonRelation, relationAdd_contribution, relationAdd_contribution, relationNeg_contribution,
    main.intervalRelation_contribution h aj ai value hinj hprime hm hai y,
    wi.intervalRelation_contribution h 0 ri value hinj hprime hi hri y,
    wj.intervalRelation_contribution h 0 rj value hinj hprime hj hrj y]
  ring

lemma comparisonRelation_not_mem {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value) (y : ι)
    (hmain : ∀ r, aj ≤ r → r < ai → ¬TuplePrimeAt main.word (value y) r)
    (hwi : ∀ r, ¬TuplePrimeAt wi.word (value y) r)
    (hwj : ∀ r, ¬TuplePrimeAt wj.word (value y) r) :
    y ∉ primeRelationSupport (comparisonRelation main wi wj h aj ai ri rj) := by
  rw [comparisonRelation, relationAdd_support, relationAdd_support, relationNeg_support]
  simp only [mem_union, not_or]
  exact ⟨main.intervalRelation_not_mem h aj ai value hinj hprime hm y hmain,
    wi.intervalRelation_not_mem h 0 ri value hinj hprime hi y (fun r _ _ => hwi r),
    wj.intervalRelation_not_mem h 0 rj value hinj hprime hj y (fun r _ _ => hwj r)⟩

/-- Simultaneous positivity supplies the comparison congruence, and the
exact selected contribution supplies its retained nondegeneracy test. -/
lemma comparisonRelation_event {ι : Type*} [DecidableEq ι]
    (main wi wj : LabeledPrimeWord ι) (h aj ai ri rj : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hi : wi.Realizes value) (hj : wj.Realizes value)
    (hai : ai ≤ main.word.length) (haji : aj ≤ ai) (x : ℤ) (selected control : ι)
    (hwi : PositiveWord h (x + wordDisplacement h (main.word.take ai)) wi.word)
    (hwj : PositiveWord h (x + wordDisplacement h (main.word.take aj)) wj.word)
    (hci : TuplePrimeAt wi.word (value control) ri)
    (hcj : TuplePrimeAt wj.word (value control) rj)
    (hnonzero : ¬(value control : ℤ) ∣
      wordPrimeContribution h main.word (value selected) aj ai +
        wordPrimeContribution h wi.word (value selected) 0 ri -
        wordPrimeContribution h wj.word (value selected) 0 rj) :
    primeRelationEvent (comparisonRelation main wi wj h aj ai ri rj) selected control
      (fun j => (value j : ℤ)) := by
  constructor
  · rw [comparisonRelation_eval main wi wj h aj ai ri rj value hm hi hj hai
      hci.index_lt.le hcj.index_lt.le]
    exact hwi.main_comparison_relation haji hwj hci hcj
  · apply primeRelation_coefficient_nondegenerate
    rw [comparisonRelation_contribution main wi wj h aj ai ri rj value hinj hprime hm hi hj
      hai hci.index_lt.le hcj.index_lt.le selected]
    exact hnonzero

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ComparisonRelationSelection
namespace OAI

/-! Exact triangular comparison systems selected from positive witness words. -/

namespace TwoPointCorrelations

open _root_.Finset

/-- Earlier partners give a comparison system ordered by increasing
attachment, with the actual private labels as selected variables. -/
theorem select_earlier_comparison_relations {n h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word)
    (R : Finset (Fin n)) (partner : R → Fin n) (hpartner : ∀ i, partner i < i.val)
    (ri rj prime : R → ℕ) (hpos : ∀ i : R, attachment i ≤ position i)
    (hocc : ∀ i : R, TuplePrimeAt (word i).word (prime i) (ri i))
    (hocc' : ∀ i : R, TuplePrimeAt (word (partner i)).word (prime i) (rj i))
    (hnonzero : ∀ i : R, ¬(prime i : ℤ) ∣
      wordPrimeContribution h (word i).word (value (mark i)) 0 (ri i)) :
    ∃ control : R → ι,
      (∀ i : R, value (control i) = prime i ∧ control i ≠ mark i ∧
        primeRelationEvent
          (comparisonRelation main (word i) (word (partner i)) h
            (attachment (partner i)) (attachment i) (ri i) (rj i))
          (mark i) (control i) (fun z => (value z : ℤ))) ∧
      ∀ i j : R, i.val < j.val →
        mark j ∉ primeRelationSupport
          (comparisonRelation main (word i) (word (partner i)) h
            (attachment (partner i)) (attachment i) (ri i) (rj i)) ∧
          control i ≠ mark j := by
  classical
  have hc (i : R) : ∃ c : ι, value c = prime i := by
    obtain ⟨c, _, hc⟩ := (word i).occurrence_has_label value hprime (hw i) (prime i)
      ⟨ri i, (hocc i).index_lt⟩ (hocc i)
    exact ⟨c, hc⟩
  choose control hcontrol using hc
  have hshared (i : R) : ∀ k, prime i ≠ value (mark k) := by
    apply shared_prime_ne_private (fun i => (word i).word) (fun i => value (mark i)) hprivate
      (ne_of_gt (hpartner i))
    · exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨ri i, hocc i⟩
    · exact (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨rj i, hocc' i⟩
  refine ⟨control, ?_, ?_⟩
  · intro i
    refine ⟨hcontrol i, ?_, ?_⟩
    · intro heq
      exact hshared i i (by simpa only [heq] using (hcontrol i).symm)
    · apply comparisonRelation_event main (word i) (word (partner i)) h
        (attachment (partner i)) (attachment i) (ri i) (rj i) value hinj hprime hm
        (hw i) (hw (partner i)) (hbound i) (horder (hpartner i).le) x
        (mark i) (control i) (hpositive i) (hpositive (partner i))
        (by simpa only [hcontrol i] using hocc i)
        (by simpa only [hcontrol i] using hocc' i)
      rw [earlier_comparison_private_contribution main.word (fun i => (word i).word)
        (fun i => value (mark i)) attachment position hsq hprivate hmain
        (hpartner i) (hpos i) (ri i) (rj i)]
      simpa only [hcontrol i] using hnonzero i
  · intro i j hij
    have he := earlier_comparison_excludes_later (fun i => (word i).word)
      (fun i => value (mark i)) attachment position horder hprivate (hpartner i) hij (hpos j)
    constructor
    · apply comparisonRelation_not_mem main (word i) (word (partner i)) h
        (attachment (partner i)) (attachment i) (ri i) (rj i) value hinj hprime hm
        (hw i) (hw (partner i)) (mark j)
      · intro r har hri hpr
        exact he.2.2 r (mem_Ico.mpr ⟨har, hri⟩) (hmain j r hpr)
      · intro r hpr
        exact he.1 ((mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩)
      · intro r hpr
        exact he.2.1 ((mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨r, hpr⟩)
    · intro heq
      exact hshared i j (by simpa only [heq] using (hcontrol i).symm)

/-- Later partners give the same system in the reverse witness order.
The selected contribution changes sign, which preserves nondivisibility. -/
theorem select_later_comparison_relations {n h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word)
    (R : Finset (Fin n)) (partner : R → Fin n) (hpartner : ∀ i, i.val < partner i)
    (ri rj prime : R → ℕ) (hpos : ∀ i : R, position i < attachment i)
    (hocc : ∀ i : R, TuplePrimeAt (word i).word (prime i) (ri i))
    (hocc' : ∀ i : R, TuplePrimeAt (word (partner i)).word (prime i) (rj i))
    (hnonzero : ∀ i : R, ¬(prime i : ℤ) ∣
      wordPrimeContribution h (word i).word (value (mark i)) 0 (ri i)) :
    ∃ control : R → ι,
      (∀ i : R, value (control i) = prime i ∧ control i ≠ mark i ∧
        primeRelationEvent
          (comparisonRelation main (word (partner i)) (word i) h
            (attachment i) (attachment (partner i)) (rj i) (ri i))
          (mark i) (control i) (fun z => (value z : ℤ))) ∧
      ∀ i j : R, j.val < i.val →
        mark j ∉ primeRelationSupport
          (comparisonRelation main (word (partner i)) (word i) h
            (attachment i) (attachment (partner i)) (rj i) (ri i)) ∧
          control i ≠ mark j := by
  classical
  have hc (i : R) : ∃ c : ι, value c = prime i := by
    obtain ⟨c, _, hc⟩ := (word i).occurrence_has_label value hprime (hw i) (prime i)
      ⟨ri i, (hocc i).index_lt⟩ (hocc i)
    exact ⟨c, hc⟩
  choose control hcontrol using hc
  have hshared (i : R) : ∀ k, prime i ≠ value (mark k) := by
    apply shared_prime_ne_private (fun i => (word i).word) (fun i => value (mark i)) hprivate
      (ne_of_lt (hpartner i))
    · exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨ri i, hocc i⟩
    · exact (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨rj i, hocc' i⟩
  refine ⟨control, ?_, ?_⟩
  · intro i
    refine ⟨hcontrol i, ?_, ?_⟩
    · intro heq
      exact hshared i i (by simpa only [heq] using (hcontrol i).symm)
    · apply comparisonRelation_event main (word (partner i)) (word i) h
        (attachment i) (attachment (partner i)) (rj i) (ri i) value hinj hprime hm
        (hw (partner i)) (hw i) (hbound (partner i)) (horder (hpartner i).le) x
        (mark i) (control i) (hpositive (partner i)) (hpositive i)
        (by simpa only [hcontrol i] using hocc' i)
        (by simpa only [hcontrol i] using hocc i)
      rw [later_comparison_private_contribution main.word (fun i => (word i).word)
        (fun i => value (mark i)) attachment position hsq hprivate hmain
        (hpartner i) (hpos i) (ri i) (rj i)]
      rw [dvd_neg]
      simpa only [hcontrol i] using hnonzero i
  · intro i j hji
    have he := later_comparison_excludes_earlier (fun i => (word i).word)
      (fun i => value (mark i)) attachment position horder hprivate (hpartner i) hji (hpos j)
    constructor
    · apply comparisonRelation_not_mem main (word (partner i)) (word i) h
        (attachment i) (attachment (partner i)) (rj i) (ri i) value hinj hprime hm
        (hw (partner i)) (hw i) (mark j)
      · intro r har hri hpr
        exact he.2.2 r (mem_Ico.mpr ⟨har, hri⟩) (hmain j r hpr)
      · intro r hpr
        exact he.2.1 ((mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨r, hpr⟩)
      · intro r hpr
        exact he.1 ((mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩)
    · intro heq
      exact hshared i j (by simpa only [heq] using (hcontrol i).symm)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.InternalRelationSelection
namespace OAI

/-! Actual active witness intervals give a triangular system on the ambient labels. -/

namespace TwoPointCorrelations

open _root_.Finset

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

/-- Record also an occurrence of the controlling prime. This proves that
later fresh labels cannot occur as an earlier controlling modulus. -/
theorem active_relation_with_control (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (hy : ActivePrime h w.word (value y)) :
    ∃ c a b r, c ≠ y ∧ a ≤ b ∧ b ≤ w.word.length ∧
      TuplePrimeAt w.word (value c) r ∧
      primeRelationEvent (w.intervalRelation h a b) y c (fun j => (value j : ℤ)) := by
  obtain ⟨p, a, b, hpy, hab, hb, ⟨r, hpr⟩, hdiv, hnonzero⟩ := hy.distinct_controller
  obtain ⟨c, _, hc⟩ := w.occurrence_has_label value hprime hw p ⟨r, hpr.index_lt⟩ hpr
  refine ⟨c, a, b, r, ?_, hab, hb, ?_, ?_, ?_⟩
  · intro heq
    exact hpy (by simpa only [heq] using hc.symm)
  · simpa only [hc] using hpr
  · rw [w.intervalRelation_eval h a b value hw hb]
    change (value c : ℤ) ∣ _
    simpa only [hc] using hdiv
  · apply primeRelation_coefficient_nondegenerate
    rw [w.intervalRelation_contribution h a b value hinj hprime hw hb y]
    change ¬(value c : ℤ) ∣ _
    simpa only [hc] using hnonzero

end LabeledPrimeWord

/-- A family of active primes absent from all earlier witnesses gives
actual interval relations, ordered independently of the names of the
selected labels. The conclusion includes the controlling-prime exclusion. -/
theorem select_internal_relations {κ ι : Type*} [Fintype κ] [LinearOrder κ]
    [DecidableEq ι] (word : κ → LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (active : κ → ℕ) (hactive : ∀ i, ActivePrime h (word i).word (active i))
    (hfresh : ∀ i j, i < j → active j ∉ wordPrimeSupport (word i).word) :
    ∃ selected control : κ → ι, ∃ left right : κ → ℕ,
      Function.Injective selected ∧
      (∀ i, value (selected i) = active i) ∧
      (∀ i, control i ≠ selected i ∧ left i ≤ right i ∧ right i ≤ (word i).word.length ∧
        primeRelationEvent ((word i).intervalRelation h (left i) (right i))
          (selected i) (control i) (fun j => (value j : ℤ))) ∧
      ∀ i j, i < j →
        selected j ∉ primeRelationSupport ((word i).intervalRelation h (left i) (right i)) ∧
          control i ≠ selected j := by
  classical
  have hsel (i : κ) : ∃ y : ι, value y = active i := by
    have hm := (hactive i).mem_wordPrimeSupport (hsq i)
    obtain ⟨r, hr⟩ := (mem_wordPrimeSupport_iff _ _ (hsq i)).mp hm
    obtain ⟨y, _, hy⟩ := (word i).occurrence_has_label value hprime (hw i) (active i)
      ⟨r, hr.index_lt⟩ hr
    exact ⟨y, hy⟩
  choose selected hselected using hsel
  have hrel (i : κ) := (word i).active_relation_with_control h value hinj hprime (hw i)
    (selected i) (by simpa only [hselected i] using hactive i)
  choose control left right occurrence hc hl hr hocc hevent using hrel
  refine ⟨selected, control, left, right, ?_, hselected,
    (fun i => ⟨hc i, hl i, hr i, hevent i⟩), ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · apply hfresh i j hij'
      rw [← hselected j, ← hij, hselected i]
      exact (hactive i).mem_wordPrimeSupport (hsq i)
    · apply hfresh j i hji'
      rw [← hselected i, hij, hselected j]
      exact (hactive j).mem_wordPrimeSupport (hsq j)
  · intro i j hij
    have hnot : ∀ r, ¬TuplePrimeAt (word i).word (value (selected j)) r := by
      intro r hpr
      apply hfresh i j hij
      rw [← hselected j]
      exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩
    refine ⟨(word i).intervalRelation_not_mem h (left i) (right i) value hinj hprime
      (hw i) (selected j) (fun r _ _ => hnot r), ?_⟩
    intro heq
    exact hnot (occurrence i) (by simpa only [← heq] using hocc i)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RelationReindex
namespace OAI

/-! Reindexing finite monomial relations preserves their events and supports. -/

namespace TwoPointCorrelations

open _root_.Finset

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

lemma primeRelationSupport_reindex (e : τ ≃ σ) (m : τ → PrimeMonomial ι)
    (n : σ → PrimeMonomial ι) (hm : ∀ i, n (e i) = m i) :
    primeRelationSupport n = primeRelationSupport m := by
  ext y
  simp only [primeRelationSupport, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, by simpa only [hm] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa only [hm] using hi⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessMetadata
namespace OAI

/-! The actual witness selector lands in the bounded metadata universe. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma internal_witness_metadata {n N h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (R : Finset (Fin n)) (reverse : Bool)
    (selected control : R → ι) (left right : R → ℕ)
    (hleft : ∀ i, left i ≤ N) (hright : ∀ i, right i ≤ N)
    (hcontrol : ∀ i, control i ≠ selected i)
    (htriangular : ∀ i j : R, (if reverse then j.val < i.val else i.val < j.val) →
      selected j ∉ primeRelationSupport ((word i).intervalRelation h (left i) (right i)) ∧
        control i ≠ selected j)
    (value : ι → ℕ)
    (hholds : ∀ i : R, primeRelationEvent ((word i).intervalRelation h (left i) (right i))
      (selected i) (control i) (fun z => (value z : ℤ))) :
    ∃ d : WitnessSystemData n N ι, d.chosen = R ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  let d : WitnessSystemData n N ι := {
    mode := if reverse then 1 else 0
    chosen := R
    slot := fun i => (selected i, control i, i.val,
      ⟨left i, Nat.lt_succ_of_le (hleft i)⟩, ⟨right i, Nat.lt_succ_of_le (hright i)⟩, 0, 0) }
  refine ⟨d, rfl, ?_, ?_⟩
  · cases reverse <;> exact ⟨hcontrol, htriangular⟩
  · cases reverse <;> exact hholds

/-- Every index in the constructed metadata is bounded by the total
recorded-length bound. Thus the actual four-way selector is covered by
the finite code count, with no numerical-prime values in its code. -/
theorem witness_system_metadata {n K h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n)
    (hminimal : ∀ i, MinimalWord (ForwardProhibited h s supply) (word i).word)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (hcard : ∀ i t, t ∈ (word i).word → t.tuple.primeFactors.card = J)
    (hsupport : ∀ i p j, TuplePrimeAt (word i).word p j →
      ¬p ∣ h ∧ ∀ t ∈ (word i).word, ¬p ∣ t.padding)
    (hmark : ∀ i, value (mark i) ∈ wordPrimeSupport (word i).word)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (hmainLength : main.word.length ≤ N) (hwordLength : ∀ i, (word i).word.length ≤ N)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word) :
    ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  classical
  obtain ⟨R, hRK, hcase⟩ := select_witness_relations (fun i => (word i).word)
    (fun i => value (mark i)) attachment position hsize hminimal hsq hcard hsupport hmark hprivate
  rcases hcase with hbefore | hafter | hearlier | hlater
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_before_labels (fun i => (word i).word)
      R hsq hbefore
    obtain ⟨selected, control, left, right, _, _, hd, ht⟩ :=
      select_internal_relations (fun i : R => word i) h value hinj hprime
        (fun i => hw i) (fun i => hsq i) active hactive (fun i j hij => hfresh i j hij)
    obtain ⟨d, hR, htri, hholds⟩ := internal_witness_metadata main word R false selected control left right
      (fun i : R => (hd i).2.1.trans ((hd i).2.2.1.trans (hwordLength i)))
      (fun i : R => (hd i).2.2.1.trans (hwordLength i)) (fun i : R => (hd i).1)
      ht value (fun i : R => (hd i).2.2.2)
    exact ⟨d, by simpa only [hR] using hRK, htri, hholds⟩
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_after_labels (fun i => (word i).word)
      R hsq hafter
    obtain ⟨selected, control, left, right, _, _, hd, ht⟩ :=
      select_internal_relations (fun i : OrderDual R => word (OrderDual.ofDual i).val) h value hinj hprime
        (fun i => hw (OrderDual.ofDual i).val) (fun i => hsq (OrderDual.ofDual i).val)
        active hactive (fun i j hij => hfresh i j hij)
    obtain ⟨d, hR, htri, hholds⟩ := internal_witness_metadata main word R true selected control left right
      (fun i : R => (hd i).2.1.trans ((hd i).2.2.1.trans (hwordLength i)))
      (fun i : R => (hd i).2.2.1.trans (hwordLength i)) (fun i : R => (hd i).1)
      ht value (fun i : R => (hd i).2.2.2)
    exact ⟨d, by simpa only [hR] using hRK, htri, hholds⟩
  · have hdata (i : R) := (hearlier i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hearlier i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_earlier_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let d : WitnessSystemData n N ι := {
      mode := 2
      chosen := R
      slot := fun i => (mark i, control i, partner i,
        ⟨attachment (partner i), Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨attachment i, Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨ri i, Nat.lt_succ_of_le ((hocc i).index_lt.le.trans (hwordLength i))⟩,
        ⟨rj i, Nat.lt_succ_of_le ((hocc' i).index_lt.le.trans (hwordLength (partner i)))⟩) }
    refine ⟨d, hRK, ?_, ?_⟩
    · constructor
      · exact fun i => (hc i).2.1
      · intro i j hij
        apply ht i j
        with_unfolding_all exact hij
    · exact fun i => (hc i).2.2
  · have hdata (i : R) := (hlater i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hlater i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_later_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let d : WitnessSystemData n N ι := {
      mode := 3
      chosen := R
      slot := fun i => (mark i, control i, partner i,
        ⟨attachment i, Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨attachment (partner i), Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨ri i, Nat.lt_succ_of_le ((hocc i).index_lt.le.trans (hwordLength i))⟩,
        ⟨rj i, Nat.lt_succ_of_le ((hocc' i).index_lt.le.trans (hwordLength (partner i)))⟩) }
    refine ⟨d, hRK, ?_, ?_⟩
    · constructor
      · exact fun i => (hc i).2.1
      · intro i j hij
        apply ht i j
        with_unfolding_all exact hij
    · exact fun i => (hc i).2.2

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessMetadataBounds
namespace OAI

/-! The finite metadata universe yields the actual union bound for singleton systems. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

private lemma nonnegative_cover_sum {A I : Type*} [Fintype A] [Fintype I]
    (weight : A → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (E : A → Prop) (F : I → A → Prop) (hcover : ∀ x, E x → ∃ i, F i x) :
    (∑ x, if E x then weight x else 0) ≤
      ∑ i, ∑ x, if F i x then weight x else 0 := by
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases hx : E x
  · obtain ⟨i, hi⟩ := hcover x hx
    simp only [hx, ite_true]
    have hs := single_le_sum (f := fun i => if F i x then weight x else 0)
      (fun j _ => by split_ifs; exact hw x; exact le_rfl) (mem_univ i)
    simpa only [hi, ite_true] using hs
  · simp only [hx, ite_false]
    exact sum_nonneg (fun i _ => by split_ifs; exact hw x; exact le_rfl)

/-- Count every bounded mode/label/endpoint record and impose only those
support conditions needed for successive elimination. Thus this bound
contains no assumed probability estimate or assumed number of systems. -/
theorem witness_metadata_reciprocal_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n N K h : ℕ) (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ x : ι → P, if ∃ d : WitnessSystemData n N ι,
      K ≤ d.chosen.card ∧ d.Triangular main word h ∧
        d.Holds main word h (integerPrimeAssignment Subtype.val x)
      then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let D := {d : WitnessSystemData n N ι // K ≤ d.chosen.card ∧ d.Triangular main word h}
  let system (d : D) : OrderedPrimeSystem ι := d.val.toSystem main word h d.property.2
  have hcover (x : ι → P)
      (hx : ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
        d.Holds main word h (integerPrimeAssignment Subtype.val x)) :
      ∃ d : D, (system d).Holds (integerPrimeAssignment Subtype.val x) := by
    obtain ⟨d, hd, ht, hh⟩ := hx
    exact ⟨⟨d, hd, ht⟩, hh⟩
  have hu := nonnegative_cover_sum (fun x : ι → P => ∏ z, ((x z).val : ℝ)⁻¹)
    (fun _ => by positivity) _
    (fun d : D => fun x : ι → P => (system d).Holds (integerPrimeAssignment Subtype.val x)) hcover
  have hs := singleton_family_bound system K
    (fun d => by simpa only [system, WitnessSystemData.toSystem_size] using d.property.1)
    P hP hV H B hH hB hlo hhi hdelta (fun _ => 1) (fun _ => by positivity)
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul, mul_one] at hs
  refine le_trans ?_ (hs.trans ?_)
  · convert (preTransparency := .instances) hu using 1
    apply sum_congr rfl
    intro x _
    split_ifs <;> rfl
  · have hc : Fintype.card D ≤ Fintype.card (WitnessSystemData n N ι) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg (by linarith) _))
      (by positivity)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordResampling
namespace OAI

/-! Numerical resampling preserves the symbolic witness relations. -/

namespace TwoPointCorrelations

open _root_.Finset

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


lemma comparisonRelation_pattern {main wi wj main' wi' wj' : LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hi : LabeledPrimeWord.PatternEquiv wi wi')
    (hj : LabeledPrimeWord.PatternEquiv wj wj') (h a b r s : ℕ)
    (i : Fin main.word.length ⊕ (Fin wi.word.length ⊕ Fin wj.word.length)) :
    comparisonRelation main' wi' wj' h a b r s (comparisonIndexEquiv hm hi hj i) =
      comparisonRelation main wi wj h a b r s i := by
  rcases i with i | i | i
  · exact hm.interval h a b i
  · exact hi.interval h 0 r i
  · change PrimeMonomial.mk (-(wj'.intervalRelation h 0 s (hj.index i)).coefficient)
        (wj'.intervalRelation h 0 s (hj.index i)).labels = _
    rw [hj.interval h 0 s i]
    rfl

namespace WitnessSystemData

variable {n N : ℕ}

/-- Every mode decodes to the same expression after changing numerical tuples. -/
theorem relationPattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) (i : d.chosen) :
    (∃ e : (d.relation main word h i).Term ≃ (d.relation main' word' h i).Term,
      ∀ t, (d.relation main' word' h i).monomial (e t) = (d.relation main word h i).monomial t) := by
  rcases d with ⟨mode, chosen, slot⟩
  fin_cases mode
  · exact ⟨(hw i).index, fun t => (hw i).interval _ _ _ t⟩
  · exact ⟨(hw i).index, fun t => (hw i).interval _ _ _ t⟩
  · exact ⟨comparisonIndexEquiv hm (hw i) (hw (slot i).2.2.1),
      comparisonRelation_pattern hm (hw i) (hw (slot i).2.2.1) _ _ _ _ _⟩
  · exact ⟨comparisonIndexEquiv hm (hw (slot i).2.2.1) (hw i),
      comparisonRelation_pattern hm (hw (slot i).2.2.1) (hw i) _ _ _ _ _⟩

lemma holds_pattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) (x : ι → ℤ) :
    d.Holds main' word' h x ↔ d.Holds main word h x := by
  unfold Holds
  apply forall_congr'
  intro i
  obtain ⟨e, he⟩ := d.relationPattern hm hw h i
  exact primeRelationEvent_reindex e _ _ he _ _ _

lemma triangular_pattern (d : WitnessSystemData n N ι)
    {main main' : LabeledPrimeWord ι} {word word' : Fin n → LabeledPrimeWord ι}
    (hm : LabeledPrimeWord.PatternEquiv main main')
    (hw : ∀ i, LabeledPrimeWord.PatternEquiv (word i) (word' i)) (h : ℕ) :
    d.Triangular main' word' h ↔ d.Triangular main word h := by
  have hs (i : d.chosen) : primeRelationSupport (d.relation main' word' h i).monomial =
      primeRelationSupport (d.relation main word h i).monomial := by
    obtain ⟨e, he⟩ := d.relationPattern hm hw h i
    exact primeRelationSupport_reindex e _ _ he
  simp only [Triangular, hs]

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

omit [DecidableEq ι] in
lemma segment_resample_word (w : LabeledPrimeWord ι) (a n : ℕ) (value : ι → ℕ) :
    ((w.segment a n).resample value).word = ((w.resample value).word.drop a).take n := by
  apply List.ext_getElem
  · simp only [resample_length, segment_length, List.length_take, List.length_drop]
  · intro i hi hj
    have hi' : i < ((w.word.drop a).take n).length := by
      simpa only [resample_length, segment] using hi
    have hj' : a + i < w.word.length := by
      have ht : i < min n (w.word.length - a) := by
        simpa only [List.length_take, List.length_drop] using hi'
      have := (lt_min_iff.mp ht).2
      omega
    rw [List.getElem_take, List.getElem_drop]
    simp only [resample, List.getElem_ofFn]
    change (⟨(((w.word.drop a).take n)[i]'hi').forward,
      ∏ z ∈ w.labels ⟨a + i, hj'⟩, value z,
      (((w.word.drop a).take n)[i]'hi').padding⟩ : SignedStep) =
      ⟨(w.word[a + i]'hj').forward, ∏ z ∈ w.labels ⟨a + i, hj'⟩, value z,
        (w.word[a + i]'hj').padding⟩
    simp only [List.getElem_take, List.getElem_drop]


end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses
namespace OAI

/-! Tuple classes can be resampled while all padding classes remain fixed. -/

namespace TwoPointCorrelations

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResampledWitnesses
namespace OAI

/-! Actual positive minimal witnesses enter the fixed symbolic metadata union. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma resampled_witness_metadata {n K h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n) (horder : Monotone attachment)
    (hbound : ∀ i, attachment i ≤ main.word.length)
    (hmainLength : main.word.length ≤ N) (hwordLength : ∀ i, (word i).word.length ≤ N)
    (value : ι → ℕ) (hevent : ResampledWitnessEvent main word h s J supply mark attachment position value) :
    ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  rcases hevent with ⟨hinj, hprime, hminimal, hsq, hcard, hsupport, hmark, hprivate, hmain, x, hpositive⟩
  obtain ⟨d, hd, ht, hh⟩ := witness_system_metadata
    (main.resample value) (fun i => (word i).resample value) value hinj hprime
    (main.resample_realizes value) (fun i => (word i).resample_realizes value)
    mark attachment position hsize hminimal hsq hcard hsupport hmark hprivate horder
    (by simpa only [LabeledPrimeWord.resample_length] using hbound) hmain
    (by simpa only [LabeledPrimeWord.resample_length] using hmainLength)
    (by simpa only [LabeledPrimeWord.resample_length] using hwordLength) x hpositive
  exact ⟨d, hd,
    (d.triangular_pattern (main.resamplePattern value) (fun i => (word i).resamplePattern value) h).mp ht,
    (d.holds_pattern (main.resamplePattern value) (fun i => (word i).resamplePattern value) h _).mp hh⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ExistentialWitnesses
namespace OAI

/-! Witness choices are eliminated by the existing relation metadata union. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem has_resampled_witnesses_reciprocal_bound {n K h s J N : ℕ}
    {supply : ℕ → ℕ → Prop} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (hsize : 8 * K ≤ n) (hmainLength : main.word.length ≤ N)
    (hwordLength : ∀ i, (word i).word.length ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ a : ι → P, if HasResampledWitnesses main word h s J supply
      (fun z => (a z).val) then ∏ z, ((a z).val : ℝ)⁻¹ else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) * primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  apply le_trans _ (witness_metadata_reciprocal_bound n N K h main word P hP hV
    H B hH hB hlo hhi hdelta)
  apply sum_le_sum
  intro a _
  by_cases he : HasResampledWitnesses main word h s J supply (fun z => (a z).val)
  · obtain ⟨mark, attachment, position, horder, hbound, hevent⟩ := he
    have hd := resampled_witness_metadata main word mark attachment position hsize horder
      hbound hmainLength hwordLength (fun z => (a z).val) hevent
    have hd' : ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧
        d.Triangular main word h ∧ d.Holds main word h (integerPrimeAssignment Subtype.val a) := hd
    simp only [if_pos (show HasResampledWitnesses main word h s J supply
      (fun z => (a z).val) from ⟨mark, attachment, position, horder, hbound, hevent⟩),
      if_pos hd']
    exact le_rfl
  · simp only [he, ite_false]
    split_ifs <;> positivity

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalWitnessEvent
namespace OAI

/-! A numerical formulation of the witness event and its exact coded segments. -/

namespace TwoPointCorrelations


lemma has_resampled_witnesses_iff {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) (value : ι → ℕ) :
    HasResampledWitnesses main word h s J supply value ↔
      NumericalWitnessEvent (main.resample value).word
        (fun i => ((word i).resample value).word) value h s J supply := by
  simp only [HasResampledWitnesses, NumericalWitnessEvent, ResampledWitnessEvent,
    LabeledPrimeWord.resample_length]

lemma CrudeWordCode.segment_resample_word {R N : ℕ} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective)
    (a : c.tupleClasses → ℕ) (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ)
    (start len : ℕ) :
    (((c.labeledWord b).segment start len).resample a).word =
      ((c.numericalWord (joinCoordinates c.tupleClasses a b)).drop start).take len := by
  rw [LabeledPrimeWord.segment_resample_word, c.labeledWord_resample hc hi]

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

open _root_.Finset
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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SplitWitnessSum
namespace OAI

/-! Integrate padding after the singleton witness relations, with distinct-prime weights. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem split_witness_reciprocal_bound {n K h s J N : ℕ}
    {supply : ℕ → ℕ → Prop} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P Q : Finset ℕ) (main : (κ → Q) → LabeledPrimeWord ι)
    (word : (κ → Q) → Fin n → LabeledPrimeWord ι)
    (hsize : 8 * K ≤ n) (hmain : ∀ b, (main b).word.length ≤ N)
    (hword : ∀ b i, (word b i).word.length ≤ N)
    (E : (ι → P) → (κ → Q) → Prop)
    (hE : ∀ a b, E a b → HasResampledWitnesses (main b) (word b) h s J supply
      (fun z => (a z).val))
    (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ b : κ → Q, ∑ a : ι → P, if E a b then
      (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card (WitnessSystemData n N ι) : ℝ) *
        primeHarmonicMass P ^ Fintype.card ι * primeHarmonicMass Q ^ Fintype.card κ *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let C : ℝ := (Fintype.card (WitnessSystemData n N ι) : ℝ) *
    primeHarmonicMass P ^ Fintype.card ι * ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K
  have hb (b : κ → Q) : (∑ a : ι → P, if E a b then ∏ i, ((a i).val : ℝ)⁻¹ else 0) ≤ C := by
    apply le_trans _ (has_resampled_witnesses_reciprocal_bound (h := h) (s := s) (J := J)
      (supply := supply) (main b) (word b)
      hsize (hmain b) (hword b) P hP hV H B hH hB hlo hhi hdelta)
    apply sum_le_sum
    intro a _
    by_cases he : E a b
    · simp only [if_pos he, if_pos (hE a b he)]
      exact le_rfl
    · simp only [he, ite_false]
      split_ifs <;> positivity
  calc
    _ = ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) *
        (∑ a : ι → P, if E a b then ∏ i, ((a i).val : ℝ)⁻¹ else 0) := by
      apply sum_congr rfl
      intro b _
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      split_ifs <;> ring
    _ ≤ ∑ b : κ → Q, (∏ j, ((b j).val : ℝ)⁻¹) * C :=
      sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hb b) (by positivity))
    _ = (∑ b : κ → Q, ∏ j, ((b j).val : ℝ)⁻¹) * C := (sum_mul _ _ _).symm
    _ = _ := by rw [sum_reciprocal_assignments]; dsimp [C]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CodedWitnessFiber
namespace OAI

/-! Actual numerical main/witness segments satisfy the fixed-code reciprocal bound. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem CrudeWordCode.witness_fiber_reciprocal_bound {R N n K M h s J : ℕ}
    {supply : ℕ → ℕ → Prop} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective) (hRM : R ≤ M)
    (mainLength : ℕ) (start len : Fin n → ℕ) (P Q : Finset ℕ)
    (E : (c.tupleClasses → P) → ({z : c.usedClasses // z ∉ c.tupleClasses} → Q) → Prop)
    (hE : ∀ a b, E a b →
      let w := c.numericalWord (joinCoordinates c.tupleClasses
        (fun i => (a i).val) (fun j => (b j).val))
      NumericalWitnessEvent (w.take mainLength)
        (fun i => (w.drop (start i)).take (len i)) (fun i => (a i).val) h s J supply)
    (hsize : 8 * K ≤ n) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
      ∑ a : c.tupleClasses → P, if E a b then
        (∏ i, ((a i).val : ℝ)⁻¹) * (∏ j, ((b j).val : ℝ)⁻¹) else 0) ≤
      (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
        primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} *
          ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  let main := fun b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q =>
    (c.labeledWord (fun j => (b j).val)).segment 0 mainLength
  let word := fun b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q =>
    fun i => (c.labeledWord (fun j => (b j).val)).segment (start i) (len i)
  have hm (b) : (main b).word.length ≤ M := by
    dsimp [main]
    rw [LabeledPrimeWord.segment_length, c.labeledWord_length]
    omega
  have hw (b) (i) : (word b i).word.length ≤ M := by
    dsimp [word]
    rw [LabeledPrimeWord.segment_length, c.labeledWord_length]
    omega
  apply split_witness_reciprocal_bound (h := h) (s := s) (J := J)
    (supply := supply) P Q main word hsize hm hw E ?_
    hP hV H B hH hB hlo hhi hdelta
  intro a b he
  rw [has_resampled_witnesses_iff]
  dsimp [main, word]
  simp only [c.segment_resample_word hc hi, List.drop_zero]
  exact hE a b he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessSum
namespace OAI

/-! Sum the numerical singleton-witness event over the complete prime-slot catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem encoded_witness_sum_le (R T n K M mainLength h s J : ℕ)
    (start len : Fin n → ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (hRM : R ≤ M) (hsize : 8 * K ≤ n)
    (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H B : ℕ) (hH : 0 < H) (hB : 1 ≤ B)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ B)
    (hdelta : (H : ℝ)⁻¹ + (1 + Real.log B) / H ≤ 1) :
    (∑ e : PrimeWordEncoding R T P Q,
      if e.Witnesses n mainLength start len h s J supply then e.weight else 0) ≤
      (∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
        (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
          primeHarmonicMass P ^ Fintype.card c.tupleClasses *
          primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) *
        ((H : ℝ)⁻¹ + (1 + Real.log B) / H) ^ K := by
  have hP0 : 0 ≤ primeHarmonicMass P := by unfold primeHarmonicMass; positivity
  have hQ0 : 0 ≤ primeHarmonicMass Q := by unfold primeHarmonicMass; positivity
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  rw [Fintype.sum_sigma, sum_mul]
  apply sum_le_sum
  intro t _
  rw [Fintype.sum_sigma, sum_mul]
  apply sum_le_sum
  intro c _
  rw [Fintype.sum_prod_type]
  by_cases hc : c.KindConsistent
  · by_cases hi : c.RowInjective
    · rw [sum_comm]
      let E (a : c.tupleClasses → P)
          (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) : Prop :=
        (show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
          n mainLength start len h s J supply
      have hb := c.witness_fiber_reciprocal_bound hc hi hRM mainLength start len P Q E
        (fun a b he => he.2.2) hsize hP hV H B hH hB hlo hhi hdelta
      have heq : (∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
          ∑ a : c.tupleClasses → P,
            if (show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
                n mainLength start len h s J supply
              then PrimeWordEncoding.weight ⟨t, c, a, b⟩ else 0) =
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
          ¬(show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
            n mainLength start len h s J supply := fun he => hi he.2.1
      simp only [he, ite_false, sum_const_zero]
      positivity
  · have he (a : c.tupleClasses → P)
        (b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q) :
        ¬(show PrimeWordEncoding R T P Q from ⟨t, c, a, b⟩).Witnesses
          n mainLength start len h s J supply := fun he => hc he.1
    simp only [he, ite_false, sum_const_zero]
    positivity

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.encoded_witness_sum_le := @OAI.TwoPointCorrelations.encoded_witness_sum_le
