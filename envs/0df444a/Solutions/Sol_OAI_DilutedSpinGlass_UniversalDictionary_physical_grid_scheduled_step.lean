-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:08:58.411967+00:00
-- url     : https://prove2.me/submissions/e3faaa22-720d-42f8-ac17-cbfdb7e09d8d

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section
-- module Solutions.OAIQ041_DS.Compat
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

theorem expect_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  exact congrArg P.expect (funext h)

theorem expect_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g := by
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

theorem covariance_centered (f g : Ω → ℝ) :
    P.covariance f g = P.expect (fun x => (f x - P.expect f) * (g x - P.expect g)) := by
  rw [covariance]
  calc
    _ = P.expect (fun x => f x * g x - f x * P.expect g -
        P.expect f * g x + P.expect f * P.expect g) := by simp
    _ = _ := P.expect_congr (fun x => by ring)

/-- Two independent centered copies have second moment twice the covariance. -/
theorem difference_product (f g : Ω → ℝ) :
    P.expect (fun y => P.expect (fun z => (f y - f z) * (g y - g z))) =
      2 * P.covariance f g := by
  calc
    _ = P.expect (fun y => P.expect (fun z =>
        f y * g y - f y * g z - f z * g y + f z * g z)) := by
          apply P.expect_congr
          intro y
          exact P.expect_congr (fun z => by ring)
    _ = _ := by simp [covariance]; ring

variable {n : ℕ}

theorem dot_sub_right (x y z : Fin n → ℝ) :
    dot x y - dot x z = dot x (fun i => y i - z i) := by
  simp [dot, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem dot_sq (x y : Fin n → ℝ) :
    dot x y ^ 2 = (∑ i, ∑ j, x i * x j * (y i * y j)) / (n : ℝ)^2 := by
  rw [dot, div_pow, pow_two, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact finite-conditional-law three-copy identity, with a square remainder.
No boundedness assumption is needed for this algebraic ingredient. -/
theorem three_copy_identity (X : Ω → Fin n → ℝ) :
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
    (2 / (n : ℝ)^2) *
      ((∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) +
        P.expect (fun x => (∑ i, P.expect (fun y => X y i) *
          (X x i - P.expect (fun y => X y i)))^2)) := by
  let μ : Fin n → ℝ := fun i => P.expect (fun x => X x i)
  let C : Fin n → Fin n → ℝ := fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)
  have hrem : P.expect (fun x => (∑ i, μ i * (X x i - μ i))^2) =
      ∑ i, ∑ j, μ i * μ j * C i j := by
    have hsq (x : Ω) : (∑ i, μ i * (X x i - μ i))^2 =
        ∑ i, ∑ j, μ i * μ j * ((X x i - μ i) * (X x j - μ j)) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hsq, expect_fintype_sum, expect_mul_left]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [C, μ]
    rw [covariance_centered]
  have hmain : P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) =
      (∑ i, ∑ j, 2 * (C i j + μ i * μ j) * C i j) / (n : ℝ)^2 := by
    simp_rw [dot_sub_right, dot_sq, expect_div, expect_fintype_sum,
      expect_mul_left, difference_product, expect_mul_right]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [C, covariance, μ]
    ring
  rw [hmain]
  change _ = (2 / (n : ℝ)^2) * ((∑ i, ∑ j, C i j ^ 2) + _)
  rw [hrem, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  rw [div_mul_eq_mul_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- decor:three-copy-bound for each finite conditional path law. -/
theorem three_copy_bound (X : Ω → Fin n → ℝ) :
    (2 / (n : ℝ)^2) *
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j)^2) ≤
    P.expect (fun x => P.expect (fun y => P.expect (fun z =>
      (dot (X x) (X y) - dot (X x) (X z))^2))) := by
  rw [P.three_copy_identity X]
  apply mul_le_mul_of_nonneg_left
  · exact le_add_of_nonneg_right (P.expect_nonneg (fun _ => sq_nonneg _))
  · positivity

/-- Matrix Cauchy-Schwarz with exactly the manuscript's normalization. -/
theorem normalized_abs_sum_le (C : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, |C i j|) / (n : ℝ)^2 ≤
      Real.sqrt ((∑ i, ∑ j, C i j ^ 2) / (n : ℝ)^2) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsq : (∑ i, ∑ j, |C i j|)^2 ≤ (n : ℝ)^2 * (∑ i, ∑ j, C i j ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun ij : Fin n × Fin n => |C ij.1 ij.2|)
    simpa [Fintype.sum_prod_type, sq_abs, pow_two] using h
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (sq_pos_of_pos hn') 2) (sq_pos_of_pos hn')).mpr
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (n : ℝ))]

/-- The exact second moment if the other vector is held fixed. -/
theorem centered_contraction_identity (X : Ω → Fin n → ℝ) (b : Fin n → ℝ) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) =
      (∑ i, ∑ j, P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)) /
        (n : ℝ)^2 := by
  simp_rw [dot_sq, expect_div, expect_fintype_sum, expect_mul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_centered]

/-- decor:contraction-bound, before the last square root, for a fixed multiplier. -/
theorem centered_contraction_bound (X : Ω → Fin n → ℝ) (b : Fin n → ℝ)
    (hb : ∀ i, |b i| ≤ 1) :
    P.expect (fun x => (dot (fun i => X x i - P.expect (fun y => X y i)) b)^2) ≤
      Real.sqrt (P.covarianceEnergy X) := by
  rw [centered_contraction_identity]
  apply le_trans _ (normalized_abs_sum_le (fun i j =>
    P.covariance (fun x => X x i) (fun x => X x j)))
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j) * (b i * b j)| := le_abs_self _
    _ = |P.covariance (fun x => X x i) (fun x => X x j)| * (|b i| * |b j|) := by
      simp only [abs_mul]
    _ ≤ |P.covariance (fun x => X x i) (fun x => X x j)| * (1 * 1) := by
      gcongr <;> exact hb _
    _ = _ := by ring

/-- The other multiplier may itself be random, independently sampled under Q. -/
theorem independent_contraction_bound {Λ : Type*} [Fintype Λ]
    (Q : FiniteLaw Λ) (X : Ω → Fin n → ℝ) (B : Λ → Fin n → ℝ)
    (hB : ∀ z i, |B z i| ≤ 1) :
    Q.expect (fun z => P.expect (fun x =>
      (dot (fun i => X x i - P.expect (fun y => X y i)) (B z))^2)) ≤
      Real.sqrt (P.covarianceEnergy X) := by
  calc
    _ ≤ Q.expect (fun _ => Real.sqrt (P.covarianceEnergy X)) :=
      Q.expect_mono (fun z => P.centered_contraction_bound X (B z) (hB z))
    _ = _ := Q.expect_const _

/-- Elementary Jensen for the square, proved from its nonnegative variance. -/
theorem expect_sq_sub_expect (f : Ω → ℝ) :
    P.expect (fun x => (f x - P.expect f)^2) =
      P.expect (fun x => f x ^ 2) - P.expect f ^ 2 := by
  calc
    _ = P.expect (fun x => f x ^ 2 - 2 * P.expect f * f x + P.expect f ^ 2) :=
      P.expect_congr (fun _ => by ring)
    _ = _ := by simp; ring

theorem sq_expect_le_expect_sq (f : Ω → ℝ) :
    P.expect f ^ 2 ≤ P.expect (fun x => f x ^ 2) := by
  have h := P.expect_nonneg (fun x => sq_nonneg (f x - P.expect f))
  rw [expect_sq_sub_expect] at h
  linarith

/-- Jensen for the square root, including possible zero coordinates. -/
theorem expect_sqrt_le (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    P.expect (fun x => Real.sqrt (f x)) ≤ Real.sqrt (P.expect f) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.sq_sqrt (hf _)] using
    P.sq_expect_le_expect_sq (fun x => Real.sqrt (f x))

/-- Finite-law Cauchy-Schwarz. -/
theorem expect_mul_sq_le (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x)^2 ≤
      P.expect (fun x => f x^2) * P.expect (fun x => g x^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (P.weight x) * f x)
    (fun x => Real.sqrt (P.weight x) * g x)
  have hm (x : Ω) : Real.sqrt (P.weight x) * f x *
      (Real.sqrt (P.weight x) * g x) = P.weight x * (f x * g x) := by
    calc
      _ = Real.sqrt (P.weight x)^2 * (f x * g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (P.nonneg x)]
  simpa only [hm, mul_pow, Real.sq_sqrt (P.nonneg _), expect] using h

theorem l2_nonneg (f : Ω → ℝ) : 0 ≤ P.l2 f := Real.sqrt_nonneg _

theorem expect_mul_le_l2 (f g : Ω → ℝ) :
    P.expect (fun x => f x * g x) ≤ P.l2 f * P.l2 g := by
  have h := P.expect_mul_sq_le f g
  have hf := P.l2_nonneg f
  have hg := P.l2_nonneg g
  rw [← P.l2_sq f, ← P.l2_sq g, ← mul_pow] at h
  exact (sq_le_sq₀ (by positivity) (mul_nonneg hf hg)).mp
    (by simpa only [sq_abs] using h) |>.trans' (le_abs_self _)

/-- Minkowski is used for successive projection of independent child shapes. -/
theorem l2_add_le (f g : Ω → ℝ) :
    P.l2 (fun x => f x + g x) ≤ P.l2 f + P.l2 g := by
  apply (sq_le_sq₀ (P.l2_nonneg _) (add_nonneg (P.l2_nonneg _) (P.l2_nonneg _))).mp
  rw [l2_sq]
  have heq : P.expect (fun x => (f x + g x)^2) =
      P.expect (fun x => f x^2) + 2 * P.expect (fun x => f x * g x) +
        P.expect (fun x => g x^2) := by
    calc
      _ = P.expect (fun x => f x^2 + 2 * (f x * g x) + g x^2) :=
        P.expect_congr (fun _ => by ring)
      _ = _ := by simp
  rw [heq, ← P.l2_sq f, ← P.l2_sq g]
  nlinarith [P.expect_mul_le_l2 f g]

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

theorem abs_expect_le {f : Ω → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    |P.expect f| ≤ B := by
  apply abs_le.mpr
  constructor
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).1)
    simpa only [expect_const] using h
  · have h := P.expect_mono (fun x => (abs_le.mp (hf x)).2)
    simpa only [expect_const] using h

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Fubini at an arbitrary coordinate, retaining dependent finite sample types. -/
theorem expect_pi_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (i : ι) (H : ((i : ι) → α i) → ℝ) :
    (pi Q).expect H = (Q i).expect (fun a =>
      (pi (fun j : {j // j ≠ i} => Q j)).expect
        (fun rest => H ((Equiv.piSplitAt i α).symm (a,rest)))) := by
  classical
  have hprod (x : (i : ι) → α i) :
      (∏ j, (Q j).weight (x j)) =
        (Q i).weight (x i) * ∏ j : {j // j ≠ i}, (Q j).weight (x j) := by
    let : Fintype {j : ι // j = i} := Subtype.fintype (fun j => j = i)
    have hh := Fintype.prod_subtype_mul_prod_subtype (fun j => j = i)
      (fun j => (Q j).weight (x j))
    rw [Fintype.prod_subsingleton _ ⟨i,rfl⟩] at hh
    exact hh.symm
  simp only [expect, pi]
  rw [← (Equiv.piSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hprod]
  have hh : (∏ j : {j // j ≠ i}, (Q j).weight
      ((Equiv.piSplitAt i α).symm (a,rest) j)) =
      ∏ j : {j // j ≠ i}, (Q j).weight (rest j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.piSplitAt_symm_apply, dite_eq_right j.property]
  rw [hh]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  ring

/-- Split off the new first child at a root attachment. -/
theorem expect_pi_cons {n : ℕ} {α : Fin (n+1) → Type*} [∀ i, Fintype (α i)]
    (Q : (i : Fin (n+1)) → FiniteLaw (α i)) (H : ((i : Fin (n+1)) → α i) → ℝ) :
    (pi Q).expect H = (Q 0).expect (fun a =>
      (pi (fun j : Fin n => Q j.succ)).expect (fun rest => H (Fin.cons a rest))) := by
  classical
  simp only [expect, pi]
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Fin.prod_univ_succ]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  ring_nf
  rfl

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

private theorem delta_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    (x y : (i : ι) → α i) :
    (∏ i, delta (x i) (y i)) = delta x y := by
  classical
  by_cases h : x = y
  · subst y
    simp [delta]
  · have hn : ∃ i, x i ≠ y i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    obtain ⟨i,hi⟩ := hn
    rw [delta, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [delta,hi])

private theorem expand_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (H : ((i : ι) → α i) → ℝ)
    (x : (i : ι) → α i) : H x = ∑ y, H y * ∏ i, delta (x i) (y i) := by
  classical
  simp_rw [delta_pi]
  simp [delta]

private theorem expect_pi_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (φ : (i : ι) → α i → β i)
    (w : (i : ι) → α i → ℝ) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      ∑ y, H y * ∏ i, (P i).expect (fun x => w i x * delta (φ i x) (y i)) := by
  classical
  have heq (x : (i : ι) → α i) :
      H (fun i => φ i (x i)) * (∏ i, w i (x i)) =
        ∑ y, H y * ∏ i, (w i (x i) * delta (φ i (x i)) (y i)) := by
    rw [expand_pi H (fun i => φ i (x i)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.prod_mul_distrib]
    ring
  rw [(pi P).expect_congr heq]
  simp only [expect_fintype_sum, expect_mul_left]
  apply Finset.sum_congr rfl
  intro y _
  rw [expect_pi_product P (fun i x => w i x * delta (φ i x) (y i))]

/-- Tensorization of arbitrary signed one-coordinate changes. This permits
inserting a marked new branch at a single child without assuming the test
factors across the old children. -/
theorem expect_pi_weighted_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (P : (i : ι) → FiniteLaw (α i)) (Q : (i : ι) → FiniteLaw (β i))
    (φ : (i : ι) → α i → β i) (w : (i : ι) → α i → ℝ) (v : (i : ι) → β i → ℝ)
    (h : ∀ i (g : β i → ℝ), (P i).expect (fun x => w i x * g (φ i x)) =
      (Q i).expect (fun y => v i y * g y)) (H : ((i : ι) → β i) → ℝ) :
    (pi P).expect (fun x => H (fun i => φ i (x i)) * ∏ i, w i (x i)) =
      (pi Q).expect (fun y => H y * ∏ i, v i (y i)) := by
  rw [expect_pi_expand P φ w H, expect_pi_expand Q (fun _ y => y) v H]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact h i (fun x => delta x (y i))

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw

theorem expect_pi_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : (i : ι) → FiniteLaw (α i))
    (i : ι) (f : α i → ℝ) : (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  erw [expect_pi_split P i]
  simp! only [Equiv.piSplitAt_symm_apply, dite_true, expect_const]

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- A single uncontracted tree samples exactly a whole conditional path. -/
theorem single_expect (n : ℕ) (T : KernelTower Ω n) (D : FinitePath Ω n → ℝ) :
    (sampleLaw (single n) T).expect (fun x => D (singlePath n x)) =
      (KernelTower.law n T).expect D := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases T with ⟨μ,K⟩
    change (FiniteLaw.pi (fun _ : Fin 1 => μ.bind
      (fun z => sampleLaw (single n) (K z)))).expect
        (fun x => D ((x 0).1,singlePath n (x 0).2)) = _
    have e := FiniteLaw.expect_pi_marginal
      (fun _ : Fin 1 => μ.bind (fun z => sampleLaw (single n) (K z))) (0 : Fin 1)
      (fun y => D (y.1,singlePath n y.2))
    refine e.trans ?_
    erw [FiniteLaw.expect_bind]
    erw [KernelTower.law_succ_expect]
    change μ.expect (fun z => _) = μ.expect (fun z => _)
    apply FiniteLaw.expect_congr
    intro z
    exact ih (K z) (fun y => D (z,y))

private theorem bind_expect_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (μ : FiniteLaw Ω) (K : Ω → KernelTower Ω n) (f : Ω × Sample Ω S → ℝ) :
    (μ.bind (fun z => sampleLaw S' (K z))).expect
      (fun x => f (cast (congrArg (fun R => Ω × Sample Ω R) h) x)) =
    (μ.bind (fun z => sampleLaw S (K z))).expect f := by
  subst S'
  rfl

/-- The operational extension identity. New descendants are sampled afresh
conditional on their shared prefix; no assumption is made about the old test. -/
theorem extension_sampling {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (v : Internal S) (H : Sample Ω S → ℝ) (D : FinitePath Ω n → ℝ) :
    (sampleLaw (grow S v) T).expect (fun x => H (oldSample S v x) * D (newPath S v x)) =
      (sampleLaw S T).expect (fun x => H x * freshEval S T v D x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      let α : Fin (k+1) → Type := fun j => Ω × Sample Ω (Fin.cases (single n) C j)
      let Q : (j : Fin (k+1)) → FiniteLaw (α j) := fun j => μ.bind
        (fun z => sampleLaw (Fin.cases (single n) C j) (K z))
      change (FiniteLaw.pi Q).expect _ = _
      erw [FiniteLaw.expect_pi_cons]
      have he : (μ.bind (fun z => sampleLaw (single n) (K z))).expect
          (fun y => D (y.1,singlePath n y.2)) = (KernelTower.law (n+1) (μ,K)).expect D := by
        erw [FiniteLaw.expect_bind]
        erw [KernelTower.law_succ_expect]
        apply FiniteLaw.expect_congr
        intro z
        exact single_expect n (K z) (fun y => D (z,y))
      change (μ.bind (fun z => sampleLaw (single n) (K z))).expect
          (fun a => (sampleLaw (.node k C) (μ,K)).expect
            (fun rest => H rest * D (a.1,singlePath n a.2))) =
          (sampleLaw (.node k C) (μ,K)).expect (fun x => H x * (KernelTower.law (n+1) (μ,K)).expect D)
      simp! only [FiniteLaw.expect_mul_right, FiniteLaw.expect_mul_left, he]
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      let P (j : Fin k) := μ.bind (fun z => sampleLaw (C' j) (K z))
      let Q (j : Fin k) := μ.bind (fun z => sampleLaw (C j) (K z))
      let φ (j : Fin k) : Ω × Sample Ω (C' j) → Ω × Sample Ω (C j) := by
        intro y
        by_cases hj : j = i
        · subst j
          have yy : Ω × Sample Ω (grow (C i) v) := by simpa! only [C', Function.update_self] using y
          exact (yy.1, oldSample (C i) v yy.2)
        · exact cast (by simp! only [C', Function.update_of_ne hj]) y
      let W (j : Fin k) : Ω × Sample Ω (C' j) → ℝ := by
        intro y
        by_cases hj : j = i
        · subst j
          have yy : Ω × Sample Ω (grow (C i) v) := by simpa! only [C', Function.update_self] using y
          exact D (yy.1, newPath (C i) v yy.2)
        · exact 1
      let V (j : Fin k) : Ω × Sample Ω (C j) → ℝ := by
        intro y
        by_cases hj : j = i
        · subst j
          exact freshEval (C i) (K y.1) v (fun z => D (y.1,z)) y.2
        · exact 1
      have hchanged : ∀ j (g : Ω × Sample Ω (C j) → ℝ),
          (P j).expect (fun x => W j x * g (φ j x)) =
            (Q j).expect (fun y => V j y * g y) := by
        intro j g
        by_cases hj : j = i
        · subst j
          have e : (μ.bind (fun z => sampleLaw (grow (C i) v) (K z))).expect
              (fun x => D (x.1,newPath (C i) v x.2) * g (x.1,oldSample (C i) v x.2)) =
              (Q i).expect (fun y => freshEval (C i) (K y.1) v (fun z => D (y.1,z)) y.2 * g y) := by
            simp! only [Q, FiniteLaw.expect_bind]
            apply FiniteLaw.expect_congr
            intro z
            calc
              _ = (sampleLaw (grow (C i) v) (K z)).expect
                  (fun y => g (z,oldSample (C i) v y) * D (z,newPath (C i) v y)) :=
                FiniteLaw.expect_congr _ (fun _ => mul_comm _ _)
              _ = _ := (ih i (K z) v (fun y => g (z,y)) (fun y => D (z,y))).trans
                (FiniteLaw.expect_congr _ (fun _ => mul_comm _ _))
          have hc := bind_expect_cast (grow (C i) v) (C' i)
            (Function.update_self ..) μ K
            (fun x => D (x.1,newPath (C i) v x.2) * g (x.1,oldSample (C i) v x.2))
          exact (show (P i).expect (fun x => W i x * g (φ i x)) = _ from by
            simp only [W, φ, dite_eq_left rfl]
            exact hc).trans (by
              simpa only [V, dite_eq_left rfl] using e)
        · have hc := bind_expect_cast (C j) (C' j)
            (Function.update_of_ne hj ..) μ K g
          simpa only [W, V, φ, dite_eq_right hj, one_mul] using hc
      have ht := FiniteLaw.expect_pi_weighted_map P Q φ W V hchanged H
      have hp (x : Sample Ω (grow (.node k C) (some ⟨i,v⟩))) :
          oldSample (.node k C) (some ⟨i,v⟩) x = fun j => φ j (x j) := by
        funext j
        by_cases hj : j = i
        · subst j
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [φ, dite_eq_left rfl, dite_true]
        · erw [oldSample.eq_1]
          dsimp only [id]
          simp only [φ, dite_eq_right hj]
          rfl
      have hw (x : Sample Ω (grow (.node k C) (some ⟨i,v⟩))) :
          (∏ j, W j (x j)) = D (newPath (.node k C) (some ⟨i,v⟩) x) := by
        erw [Finset.prod_eq_single i]
        · erw [newPath.eq_1]
          dsimp! only
          simp! only [W, dite_eq_left rfl]
          rfl
        · intro j _ hj
          simp! only [W, dite_eq_right hj]
        · simp
      have hv (x : Sample Ω (.node k C)) :
          (∏ j, V j (x j)) = freshEval (.node k C) (μ,K) (some ⟨i,v⟩) D x := by
        erw [Finset.prod_eq_single i]
        · simp only [V, dite_eq_left rfl]
          rfl
        · intro j _ hj
          simp! only [V, dite_eq_right hj]
        · simp
      change (FiniteLaw.pi P).expect _ = (FiniteLaw.pi Q).expect _
      calc
        _ = (FiniteLaw.pi P).expect (fun x => H (fun j => φ j (x j)) * ∏ j, W j (x j)) := by
          apply FiniteLaw.expect_congr
          intro x
          exact congrArg₂ (· * ·) (congrArg H (hp x)) (hw x).symm
        _ = _ := ht
        _ = _ := FiniteLaw.expect_congr _ (fun x => congrArg (H x * ·) (hv x))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type}

theorem leafSum_single (n : ℕ) (f : FinitePath Ω n → ℝ) (x : Sample Ω (single n)) :
    leafSum (single n) f x = f (singlePath n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ i : Fin 1, leafSum (single n) (fun y => f ((x i).1,y)) (x i).2) = _
    rw [Fintype.sum_subsingleton]
    exact ih _ _

private theorem leafSum_cast {n : ℕ} (S S' : PrescribedTree n) (h : S' = S)
    (f : FinitePath Ω (n+1) → ℝ) (x : Ω × Sample Ω S') :
    leafSum S' (fun y => f (x.1,y)) x.2 =
    leafSum S (fun y => f ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,y))
      (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2 := by
  subst S'
  rfl

/-- Exactly one terminal mark is added by growth, and its ancestry is the
new path, not a path chosen by equality of sample values. -/
theorem leafSum_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (f : FinitePath Ω n → ℝ) (x : Sample Ω (grow S v)) :
    leafSum (grow S v) f x = leafSum S f (oldSample S v x) + f (newPath S v x) := by
  classical
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (∑ j : Fin (k+1), leafSum (Fin.cases (single n) C j)
        (fun y => f ((x j).1,y)) (x j).2) = _
      erw [Fin.sum_univ_succ]
      have hh := leafSum_single n (fun y => f ((x 0).1,y)) (x 0).2
      calc
        _ = f ((x 0).1,singlePath n (x 0).2) +
            ∑ i : Fin k, leafSum (C i) (fun y => f ((x i.succ).1,y)) (x i.succ).2 :=
          congrArg₂ (· + ·) hh rfl
        _ = _ := add_comm _ _
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      have hp (j : Fin k) :
          leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2 =
          leafSum (C j) (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
              if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0 := by
        by_cases hj : j = i
        · subst j
          have hcast := leafSum_cast (grow (C i) v) (C' i)
            (Function.update_self ..) f (x i)
          let y : Ω × Sample Ω (grow (C i) v) :=
            cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
          have hh := ih i v (fun z => f (y.1,z)) y.2
          have he : leafSum (C' i) (fun z => f ((x i).1,z)) (x i).2 =
              leafSum (C i) (fun z => f (y.1,z)) (oldSample (C i) v y.2) +
                f (y.1,newPath (C i) v y.2) := hcast.trans hh
          erw [oldSample.eq_1, newPath.eq_1]
          dsimp only [id]
          simp only [dite_true, ite_true]
          exact he
        · have hc := leafSum_cast (C j) (C' j) (Function.update_of_ne hj ..) f (x j)
          erw [oldSample.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hj, ite_eq_right hj, add_zero]
          exact hc
      change (∑ j, leafSum (C' j) (fun y => f ((x j).1,y)) (x j).2) = _
      calc
        _ = ∑ j, (leafSum (C j)
            (fun y => f ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,y))
            (oldSample (.node k C) (some ⟨i,v⟩) x j).2 +
            if j = i then f (newPath (.node k C) (some ⟨i,v⟩) x) else 0) :=
          Finset.sum_congr rfl (fun j _ => hp j)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ i)]; rfl

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

/-- The exact signed budget for internal extensions with finite exponent indices. -/
theorem sum_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ) :
    (∑ v : Internal S, gamma S m v) = m 0 - (leaves S : ℝ) * m (Fin.last n) := by
  induction S with
  | leaf =>
    change (∑ v : Empty, gamma .leaf m v) = _
    have hs : (∑ v : Empty, gamma .leaf m v) = 0 :=
      Finset.sum_eq_zero (fun v _ => nomatch v)
    rw [hs]
    simp [leaves, Fin.last_zero]
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    erw [Fintype.sum_option, Fintype.sum_sigma]
    change m 0 - (k : ℝ) * m 1 +
      (∑ i, ∑ v : Internal (C i), gamma (C i) (fun j => m j.succ) v) = _
    simp_rw [ih]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_fin, leaves, Nat.cast_sum, Fin.succ_last, Fin.succ_zero_eq_one]
    rw [← Finset.sum_mul]
    ring

theorem gamma_nonpos {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (v : Internal S) : gamma S m v ≤ 0 := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change m 0 - (k : ℝ) * m 1 ≤ 0
      have hh : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.property
      have h01 := hm (show (0 : Fin (n+2)) ≤ 1 by exact Fin.zero_le _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hh) (hpos 1)]
    | some v =>
      obtain ⟨i,v⟩ := v
      exact ih i (fun j => m j.succ) (fun a b h => hm (Fin.succ_le_succ_iff.mpr h))
        (fun j => hpos j.succ) v

/-- Absolute coefficients sum to the number of old leaves. -/
theorem sum_abs_gamma {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) :
    (∑ v : Internal S, |gamma S m v|) = (leaves S : ℝ) := by
  simp_rw [abs_of_nonpos (gamma_nonpos S m hm hpos _)]
  rw [Finset.sum_neg_distrib, sum_gamma, hroot, hend]
  ring

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem leafSum_const {Ω : Type} {n : ℕ} (S : PrescribedTree n)
    (c : ℝ) (x : Sample Ω S) : leafSum S (fun _ => c) x = (leaves S : ℝ) * c := by
  induction S with
  | leaf => simp [leafSum, leaves]
  | @node n k C ih =>
    change (∑ i, leafSum (C i) (fun _ => c) (x i).2) = _
    simp_rw [ih]
    simp only [leaves, Nat.cast_sum, Finset.sum_mul]

theorem leaves_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    leaves (grow S v) = leaves S + 1 := by
  have hh := @leafSum_grow Unit n S v (fun _ => 1) (trivialSample (grow S v))
  simp only [leafSum_const, mul_one] at hh
  exact_mod_cast hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Perturbations
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass.KernelTower
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_path_expect (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f g : X → FinitePath Ω L → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y))
    (hg : ∀ y, Measurable (fun x => g x y)) :
    Measurable (fun x => (law L (tilt L T m (f x))).expect (g x)) := by
  induction L with
  | zero => simpa only [law_zero_expect] using hg ()
  | succ L ih =>
    simp_rw [law_succ_expect (Ω := Ω) L]
    exact T.1.measurable_tilt_expect (m 0)
      (fun a => measurable_backwardLog L (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)))
      (fun a => ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b)) (fun b => hg (a,b)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace DilutedSpinGlass.PrescribedTree

variable {Ω : Type}

theorem pathAt_singleLeaf (n : ℕ) (x : Sample Ω (single n)) :
    pathAt (single n) (singleLeaf n) x = singlePath n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((x 0).1, pathAt (single n) (singleLeaf n) (x 0).2) =
      ((x 0).1, singlePath n (x 0).2)
    rw [ih]

theorem pathAt_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A)
    (a : Leaf A) (x : Ω × Sample Ω B) :
    (x.1, pathAt B (cast (congrArg Leaf h.symm) a) x.2) =
      ((cast (congrArg (fun R => Ω × Sample Ω R) h) x).1,
        pathAt A a (cast (congrArg (fun R => Ω × Sample Ω R) h) x).2) := by
  subst B
  rfl

theorem pathAt_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (a : Leaf S) (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (oldLeaf S v a) x = pathAt S a (oldSample S v x) := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => rfl
    | some z =>
      obtain ⟨i,v⟩ := z
      obtain ⟨j,a⟩ := a
      change _ = ((oldSample (.node k C) (some ⟨i,v⟩) x j).1,
        pathAt (C j) a (oldSample (.node k C) (some ⟨i,v⟩) x j).2)
      let C' := Function.update C i (grow (C i) v)
      by_cases h : j = i
      · subst j
        let y : Ω × Sample Ω (grow (C i) v) :=
          cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
        have hc := pathAt_cast (grow (C i) v) (C' i)
          (Function.update_self ..) (oldLeaf (C i) v a) (x i)
        have hh := congrArg (fun z => (y.1,z)) (ih i v a y.2)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only
        exact hc.trans hh
      · have hc := pathAt_cast (C j) (C' j) (Function.update_of_ne h ..) a (x j)
        erw [oldLeaf.eq_1, oldSample.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        exact hc

theorem pathAt_newLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (x : Sample Ω (grow S v)) :
    pathAt (grow S v) (newLeaf S v) x = newPath S v x := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact congrArg (fun y => ((x 0).1,y)) (pathAt_singleLeaf n (x 0).2)
    | some z =>
      obtain ⟨i,v⟩ := z
      let C' := Function.update C i (grow (C i) v)
      let y : Ω × Sample Ω (grow (C i) v) :=
        cast (congrArg (fun R => Ω × Sample Ω R) (Function.update_self i (grow (C i) v) C)) (x i)
      have hc := pathAt_cast (grow (C i) v) (C' i)
        (Function.update_self ..) (newLeaf (C i) v) (x i)
      have hh := congrArg (fun z => (y.1,z)) (ih i v y.2)
      erw [newLeaf.eq_1, newPath.eq_1]
      dsimp only [id]
      exact hc.trans hh

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable
/-- Full cancellation inside a reference-free subtree, indexed by actual
leaf positions and actual internal vertices. -/
theorem all_choices_total {n : ℕ} (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) :
    (∑ _a : Leaf S, (1 : ℝ)) + (∑ v : Internal S, gamma S m v) = m 0 := by
  have hcard : Fintype.card (Leaf S) = leaves S := by
    clear hend m
    induction S with
    | leaf => exact Fintype.card_unit
    | @node height arity children inductionHypotheses =>
      change Fintype.card ((index : Fin arity) × Leaf (children index)) = _
      simp [Fintype.card_sigma, leaves, inductionHypotheses]
  rw [sum_gamma]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, hend]
  ring

/-- The signed normalizing sum of ALL eligible old-or-fresh choices with a
specified deepest reference prefix is independent of all unused old branches.
Unlike reference_total, this is stated on the actual global choice indices. -/
theorem divergence_choice_total {n : ℕ} {S : PrescribedTree n}
    (D : Divergence S) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ a : Leaf S, if D.oldAllowed a then (1 : ℝ) else 0) +
      (∑ v : Internal S, if D.freshAllowed v then gamma S m v else 0) = D.coefficient m := by
  induction D with
  | @here n k C J =>
    change (∑ a : (i : Fin k) × Leaf (C i), _) +
      (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (i : Fin k) (a : Leaf (C i)) :
        (Divergence.here J : Divergence (.node k C)).oldAllowed (⟨i,a⟩ : Leaf (.node k C)) ↔ i ∉ J := by
      erw [Divergence.oldAllowed.eq_1]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_true]
    change (∑ i, ∑ _a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
      (m 0 - (k:ℝ)*m 1 + ∑ i, ∑ v : Internal (C i),
        if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
      m 0 - (J.card:ℝ)*m 1
    have hm' : (fun j : Fin (n+1) => m j.succ) (Fin.last n) = 1 := hend
    have ht (i : Fin k) :
        (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0) =
          if i ∉ J then m 1 else 0 := by
      by_cases hi : i ∉ J
      · simp only [hi]
        exact all_choices_total (C i) _ hm'
      · simp only [hi, ite_false, Finset.sum_const_zero, zero_add]
    calc
      _ = m 0 - (k:ℝ)*m 1 + ∑ i, (
          (∑ a : Leaf (C i), if i ∉ J then (1:ℝ) else 0) +
          (∑ v : Internal (C i), if i ∉ J then gamma (C i) (fun j => m j.succ) v else 0)) := by
        rw [Finset.sum_add_distrib]; ring
      _ = m 0 - (k:ℝ)*m 1 + ∑ i : Fin k, if i ∉ J then m 1 else 0 := by simp_rw [ht]
      _ = _ := by
        rw [← Finset.sum_filter]
        have hset : Finset.univ.filter (fun i : Fin k => i ∉ J) = Finset.univ \ J := by ext i; simp
        rw [hset, Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff, Finset.inter_univ,
          Nat.cast_sub (Finset.card_le_card (Finset.subset_univ J))]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring
  | @descend n k C i D ih =>
    change (∑ a : (j : Fin k) × Leaf (C j), _) +
      (∑ v : Option ((j : Fin k) × Internal (C j)), _) = _
    rw [Fintype.sum_sigma, Fintype.sum_option, Fintype.sum_sigma]
    have ho_def (j : Fin k) (a : Leaf (C j)) :
        (Divergence.descend i D).oldAllowed (⟨j,a⟩ : Leaf (.node k C)) ↔
          ∃ h : j = i, D.oldAllowed (h ▸ a) := by
      erw [Divergence.oldAllowed.eq_2]
    simp_rw [ho_def]
    simp! only [Divergence.freshAllowed, Divergence.coefficient, gamma, ite_false]
    change (∑ j, ∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) +
      (0 + ∑ j, ∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
        gamma (C j) (fun q => m q.succ) v else 0) = D.coefficient (fun q => m q.succ)
    rw [zero_add]
    have ho (j : Fin k) :
        (∑ a : Leaf (C j), if ∃ h : j = i, D.oldAllowed (h ▸ a) then (1:ℝ) else 0) =
          if j = i then (∑ a : Leaf (C i), if D.oldAllowed a then (1:ℝ) else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    have hf (j : Fin k) :
        (∑ v : Internal (C j), if ∃ h : j = i, D.freshAllowed (h ▸ v) then
          gamma (C j) (fun q => m q.succ) v else 0) =
          if j = i then (∑ v : Internal (C i), if D.freshAllowed v then
            gamma (C i) (fun q => m q.succ) v else 0) else 0 := by
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    simp_rw [ho, hf]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ih _ hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_cast {n : ℕ} (A B : PrescribedTree n) (h : B = A) (a b : Leaf A) :
    splitDepth B (cast (congrArg Leaf h.symm) a) (cast (congrArg Leaf h.symm) b) =
      splitDepth A a b := by
  subst B
  rfl

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_1
/-- Fresh splitting refers to the enlarged tree's actual labeled positions. -/
theorem splitDepth_new_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    splitDepth (grow S v) (newLeaf S v) (oldLeaf S v a) = freshSplitDepth S v a := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if h : (0 : Fin (k+1)) = a.1.succ then _ else 0) = 0
      rw [dite_eq_right (Ne.symm (Fin.succ_ne_zero a.1))]
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases h : j = i
      · subst j
        let C' := Function.update C i (grow (C i) v)
        have heq : C' i = grow (C i) v := Function.update_self ..
        have hc := splitDepth_cast (grow (C i) v) (C' i) heq
          (newLeaf (C i) v) (oldLeaf (C i) v a)
        erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_left]
        change (if h : i = i then 1 + splitDepth (C' i)
          (cast (congrArg Leaf heq.symm) (newLeaf (C i) v))
          (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a)) else 0) =
          (if h : i = i then 1 + freshSplitDepth (C i) v a else 0)
        simp only
        rw [hc, ih]
      · erw [newLeaf.eq_1, oldLeaf.eq_1]
        dsimp only [id]
        simp only [dite_eq_right h]
        change (if h' : i = j then _ else 0) = (if h' : j = i then _ else 0)
        rw [dite_eq_right (Ne.symm h), dite_eq_right h]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_2
/-- Ancestry constraints with ALL existing references, not merely a local
subtree, are exactly the global eligible-old-leaf selector. -/
theorem referenceDivergence_oldAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (b : Leaf S) :
    (referenceDivergence S a d hd R).oldAllowed b ↔ matchesOldProfile S R a d b := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero =>
      change b.1 ∉ R.image (fun a => a.1) ↔
        ∀ r ∈ R, splitDepth (.node k C) b r = 0
      constructor
      · intro h r hr
        apply (splitDepth_node_zero C b r).mpr
        intro heq
        exact h (Finset.mem_image.mpr ⟨r,hr,heq.symm⟩)
      · intro h hb
        obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
        exact ((splitDepth_node_zero C b r).mp (h r hr)) heq.symm
    | succ d =>
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      have hd' : d < n := by omega
      by_cases hji : j = i
      · subst j
        have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
        have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨i,b⟩ ↔
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed b := by
          change (∃ h : i = i,
            (referenceDivergence (C i) a d hd' (childRefs R i)).oldAllowed (h ▸ b)) ↔ _
          simp
        rw [hreduce, ih i a d hd' (childRefs R i) hchild b]
        constructor
        · intro h r hr
          obtain ⟨j,r⟩ := r
          by_cases hji : j = i
          · subst j
            have hh := h r ((mem_childRefs R i r).mpr hr)
            rw [splitDepth_same_child, splitDepth_same_child]
            omega
          · rw [splitDepth_diff_child C i j (Ne.symm hji),
              splitDepth_diff_child C i j (Ne.symm hji)]
            exact (Nat.min_zero _).symm
        · intro h r hr
          have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
          rw [splitDepth_same_child, splitDepth_same_child] at hh
          omega
      · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).oldAllowed ⟨j,b⟩ := by
          change ¬∃ h : j = i, _
          exact fun ⟨h,_⟩ => hji h
        rw [iff_false_left hnone]
        intro h
        have hh := h ⟨i,a⟩ ha
        rw [splitDepth_diff_child C j i hji] at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_3
theorem freshSplitDepth_same_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (C i)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨i,a⟩ = 1 + freshSplitDepth (C i) v a := by
  change (if h : i = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = _
  simp

theorem freshSplitDepth_diff_child {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i j : Fin k) (hij : j ≠ i) (v : Internal (C i)) (a : Leaf (C j)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) ⟨j,a⟩ = 0 := by
  change (if h : j = i then 1 + freshSplitDepth (C i) v (h ▸ a) else 0) = 0
  rw [dite_eq_right hij]

theorem freshSplitDepth_node_zero {n : ℕ} {k : ℕ+} (C : Fin k → PrescribedTree n)
    (i : Fin k) (v : Internal (C i)) (a : Leaf (.node k C)) :
    freshSplitDepth (.node k C) (some ⟨i,v⟩) a = 0 ↔ a.1 ≠ i := by
  obtain ⟨j,a⟩ := a
  by_cases h : j = i
  · subst j
    rw [freshSplitDepth_same_child]
    simp
  · rw [freshSplitDepth_diff_child C i j h]
    simp [h]

/-- Fresh divergences satisfy exactly the same all-reference positional profile
as the old-choice selector; the profile is also the actual new leaf's profile
in the enlarged tree, by splitDepth_new_old. -/
theorem referenceDivergence_freshAllowed {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R) (v : Internal S) :
    (referenceDivergence S a d hd R).freshAllowed v ↔ matchesFreshProfile S R a d v := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases d with
    | zero =>
      cases v with
      | none =>
        change True ↔ ∀ r ∈ R, (0 : ℕ) = 0
        simp
      | some v =>
        obtain ⟨i,v⟩ := v
        change i ∉ R.image (fun a => a.1) ↔
          ∀ r ∈ R, freshSplitDepth (.node k C) (some ⟨i,v⟩) r = 0
        constructor
        · intro h r hr
          apply (freshSplitDepth_node_zero C i v r).mpr
          intro heq
          exact h (Finset.mem_image.mpr ⟨r,hr,heq⟩)
        · intro h hb
          obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hb
          exact ((freshSplitDepth_node_zero C i v r).mp (h r hr)) heq
    | succ d =>
      obtain ⟨i,a⟩ := a
      have hd' : d < n := by omega
      cases v with
      | none =>
        change False ↔ _
        rw [false_iff]
        intro h
        have hh := h ⟨i,a⟩ ha
        change 0 = min (d+1) (splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩) at hh
        have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
          splitDepth_self _ _
        rw [hhself] at hh
        omega
      | some v =>
        obtain ⟨j,v⟩ := v
        by_cases hji : j = i
        · subst j
          have hchild : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
          have hreduce : (referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨i,v⟩) ↔
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed v := by
            change (∃ h : i = i,
              (referenceDivergence (C i) a d hd' (childRefs R i)).freshAllowed (h ▸ v)) ↔ _
            simp
          rw [hreduce, ih i a d hd' (childRefs R i) hchild v]
          constructor
          · intro h r hr
            obtain ⟨j,r⟩ := r
            by_cases hji : j = i
            · subst j
              have hh := h r ((mem_childRefs R i r).mpr hr)
              rw [freshSplitDepth_same_child, splitDepth_same_child]
              omega
            · rw [freshSplitDepth_diff_child C i j hji,
                splitDepth_diff_child C i j (Ne.symm hji)]
              exact (Nat.min_zero _).symm
          · intro h r hr
            have hh := h ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
            rw [freshSplitDepth_same_child, splitDepth_same_child] at hh
            omega
        · have hnone : ¬(referenceDivergence (.node k C) ⟨i,a⟩ (d+1) hd R).freshAllowed (some ⟨j,v⟩) := by
            change ¬∃ h : j = i, _
            exact fun ⟨h,_⟩ => hji h
          rw [iff_false_left hnone]
          intro h
          have hh := h ⟨i,a⟩ ha
          rw [freshSplitDepth_diff_child C j i (Ne.symm hji)] at hh
          have hhself : splitDepth (.node k C) (⟨i,a⟩ : Leaf (.node k C)) ⟨i,a⟩ = n+1 :=
            splitDepth_self _ _
          rw [hhself] at hh
          omega

/-- The reference-path normalizing identity over globally admissible old or
fresh labels. No conditioning on sampled spin values occurs in the selector. -/
theorem reference_profile_total {n : ℕ} (S : PrescribedTree n)
    (a : Leaf S) (d : ℕ) (hd : d < n) (R : Finset (Leaf S)) (ha : a ∈ R)
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : Leaf S, if matchesOldProfile S R a d b then (1 : ℝ) else 0) +
      (∑ v : Internal S, if matchesFreshProfile S R a d v then gamma S m v else 0) =
      (referenceDivergence S a d hd R).coefficient m := by
  simp_rw [← referenceDivergence_oldAllowed S a d hd R ha,
    ← referenceDivergence_freshAllowed S a d hd R ha]
  exact divergence_choice_total _ m hend

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

noncomputable local instance instDecidable_4_re47a78_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Freshness is positional and survives deterministic or atomic spin laws. -/
theorem freshSplitDepth_lt {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    freshSplitDepth S v a < n := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none => exact Nat.zero_lt_succ n
    | some v =>
      obtain ⟨i,v⟩ := v
      obtain ⟨j,a⟩ := a
      by_cases hji : j = i
      · subst j
        rw [freshSplitDepth_same_child]
        have := ih i v a
        omega
      · rw [freshSplitDepth_diff_child C i j hji]
        omega

/-- Old leaves retain their pairwise positional ancestry under actual grow. -/
theorem splitDepth_old_old {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a b : Leaf S) :
    splitDepth (grow S v) (oldLeaf S v a) (oldLeaf S v b) = splitDepth S a b := by
  induction S with
  | leaf => exact v.elim
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    obtain ⟨j,a⟩ := a
    obtain ⟨l,b⟩ := b
    cases v with
    | none =>
      let D : Fin ((k+1 : ℕ+) : ℕ) → PrescribedTree n := Fin.cases (single n) C
      change splitDepth (.node (k+1) D) ⟨j.succ,a⟩ ⟨l.succ,b⟩ =
        splitDepth (.node k C) ⟨j,a⟩ ⟨l,b⟩
      by_cases h : j = l
      · subst l
        exact (@splitDepth_same_child n (k+1) D j.succ a b).trans
          (splitDepth_same_child C j a b).symm
      · exact (@splitDepth_diff_child n (k+1) D j.succ l.succ
          (fun he => h (Fin.succ_inj.mp he)) a b).trans
          (splitDepth_diff_child C j l h a b).symm
    | some v =>
      obtain ⟨i,v⟩ := v
      let C' := Function.update C i (grow (C i) v)
      by_cases hjl : j = l
      · subst l
        rw [splitDepth_same_child]
        by_cases hji : j = i
        · subst j
          have heq : C' i = grow (C i) v := Function.update_self ..
          have hc := splitDepth_cast (grow (C i) v) (C' i) heq
            (oldLeaf (C i) v a) (oldLeaf (C i) v b)
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_left]
          change (if h : i = i then 1 + splitDepth (C' i)
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v a))
            (cast (congrArg Leaf heq.symm) (oldLeaf (C i) v b)) else 0) = _
          simp only [dite_eq_left, hc, ih]
        · have heq : C' j = C j := Function.update_of_ne hji ..
          have hc := splitDepth_cast (C j) (C' j) heq a b
          erw [oldLeaf.eq_1, oldLeaf.eq_1]
          dsimp only [id]
          simp only [dite_eq_right hji]
          change (if h : j = j then 1 + splitDepth (C' j)
            (cast (congrArg Leaf heq.symm) a)
            (cast (congrArg Leaf heq.symm) b) else 0) = _
          simp only [dite_eq_left, hc]
      · rw [splitDepth_diff_child C j l hjl]
        apply (splitDepth_node_zero C' _ _).mpr
        change j ≠ l
        exact hjl

theorem oldLeaf_injective {n : ℕ} (S : PrescribedTree n) (v : Internal S) :
    Function.Injective (oldLeaf S v) := by
  intro a b hab
  apply (splitDepth_eq_height S a b).mp
  rw [← splitDepth_old_old S v a b, hab, splitDepth_self]

theorem newLeaf_ne_oldLeaf {n : ℕ} (S : PrescribedTree n) (v : Internal S) (a : Leaf S) :
    newLeaf S v ≠ oldLeaf S v a := by
  intro h
  have he := splitDepth_new_old S v a
  rw [h, splitDepth_self] at he
  have := freshSplitDepth_lt S v a
  omega

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_5
/-- A finite number of represented equivalence classes depends only on the
kernel relation, not on their ambient set of representatives. -/
theorem card_image_of_same_kernel {ι α β : Type*} [DecidableEq ι]
    [DecidableEq α] [DecidableEq β] (R : Finset ι) (f : ι → α) (g : ι → β)
    (h : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j) :
    (R.image f).card = (R.image g).card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have hR : ∀ i ∈ R, ∀ j ∈ R, f i = f j ↔ g i = g j := by
      intro i hi j hj
      exact h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have he : f a ∈ R.image f ↔ g a ∈ R.image g := by
      constructor
      · intro hh
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hh
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mp heq⟩
      · intro hg
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hg
        exact Finset.mem_image.mpr ⟨i,hi,(h i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self ..)).mpr heq⟩
    rw [Finset.image_insert, Finset.image_insert]
    by_cases hf : f a ∈ R.image f
    · rw [Finset.card_insert_of_mem hf, Finset.card_insert_of_mem (he.mp hf), ih hR]
    · rw [Finset.card_insert_of_notMem hf,
        Finset.card_insert_of_notMem (fun hg => hf (he.mpr hg)), ih hR]

theorem sigma_cast_snd {α : Type*} {β : α → Type*} (x : Sigma β) (i : α)
    (h : x.1 = i) : (⟨i,h ▸ x.2⟩ : Sigma β) = x := by
  obtain ⟨j,x⟩ := x
  dsimp at h
  subst i
  rfl

/-- Returning a restricted reference label to its original tree. -/
theorem childLabelLeaf_embed {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} (r : ι → Leaf (.node k C)) (i : Fin k) (l : ChildLabels r i) :
    (⟨i,childLabelLeaf r i l⟩ : Leaf (.node k C)) = r l.val := by
  exact sigma_cast_snd (r l.val) i l.property

/-- The child reference set really is the image of the child-restricted labels. -/
theorem childRefs_image {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    {ι : Type} [Fintype ι] (r : ι → Leaf (.node k C)) (i : Fin k) :
    childRefs (Finset.univ.image r) i =
      Finset.univ.image (childLabelLeaf r i) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := r)).mp ((mem_childRefs _ i b).mp hb)
    have hi : (r l).1 = i := congrArg Sigma.fst hl
    apply Finset.mem_image.mpr
    refine ⟨⟨l,hi⟩,Finset.mem_univ _, ?_⟩
    have he := (childLabelLeaf_embed r i ⟨l,hi⟩).trans hl
    exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)
  · intro hb
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
    apply (mem_childRefs _ i b).mpr
    exact (Finset.mem_image (f := r)).mpr ⟨l.val,Finset.mem_univ _, by
      rw [← childLabelLeaf_embed r i l, hl]⟩


/-- One-step signed reference normalization is determined by the entire
labeled splitting matrix, not by the unused old leaves of its realization. -/
theorem reference_coefficient_invariant {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (referenceDivergence S (r a) d hd (Finset.univ.image r)).coefficient m =
      (referenceDivergence T (s a) d hd (Finset.univ.image s)).coefficient m := by
  classical
  induction n generalizing ι d with
  | zero => omega
  | succ n ih =>
    cases S with | node k C =>
    cases T with | node k' C' =>
    have hf (i j : ι) : (r i).1 = (r j).1 ↔ (s i).1 = (s j).1 := by
      have he := hsplit i j
      have hr := splitDepth_node_zero C (r i) (r j)
      have hs := splitDepth_node_zero C' (s i) (s j)
      rw [he] at hr
      tauto
    cases d with
    | zero =>
      change m 0 - (((Finset.univ.image r).image (fun b => b.1)).card : ℝ)*m 1 =
        m 0 - (((Finset.univ.image s).image (fun b => b.1)).card : ℝ)*m 1
      rw [Finset.image_image, Finset.image_image]
      have he := card_image_of_same_kernel Finset.univ (fun i => (r i).1)
        (fun i => (s i).1) (fun i _ j _ => hf i j)
      dsimp only [Function.comp_def]
      erw [he]
    | succ d =>
      let I := ChildLabels r (r a).1
      let rr : I → Leaf (C (r a).1) := childLabelLeaf r (r a).1
      let ss : I → Leaf (C' (s a).1) := fun l =>
        childLabelLeaf s (s a).1 ⟨l.val,(hf l.val a).mp l.property⟩
      let aa : I := ⟨a,rfl⟩
      have hr (i : I) : (⟨(r a).1,rr i⟩ : Leaf (.node k C)) = r i.val :=
        childLabelLeaf_embed r _ i
      have hs (i : I) : (⟨(s a).1,ss i⟩ : Leaf (.node k' C')) = s i.val :=
        childLabelLeaf_embed s _ _
      have hsplit' (i j : I) : splitDepth (C (r a).1) (rr i) (rr j) =
          splitDepth (C' (s a).1) (ss i) (ss j) := by
        have he := hsplit i.val j.val
        rw [← hr i, ← hr j, ← hs i, ← hs j,
          splitDepth_same_child, splitDepth_same_child] at he
        omega
      have hR := childRefs_image r (r a).1
      have hS : childRefs (Finset.univ.image s) (s a).1 = Finset.univ.image ss := by
        ext b
        constructor
        · intro hb
          obtain ⟨l,_,hl⟩ := (Finset.mem_image (f := s)).mp ((mem_childRefs _ _ b).mp hb)
          have hls : (s l).1 = (s a).1 := by
            have hh := congrArg (fun x : Leaf (.node k' C') => x.1) hl
            exact hh
          let l' : I := ⟨l,(hf l a).mpr hls⟩
          refine Finset.mem_image.mpr ⟨l',Finset.mem_univ _, ?_⟩
          have hh := (hs l').trans hl
          exact eq_of_heq ((Sigma.mk.inj_iff.mp hh).2)
        · intro hb
          obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hb
          apply (mem_childRefs _ _ b).mpr
          exact (Finset.mem_image (f := s)).mpr ⟨l.val,Finset.mem_univ _, by rw [← hs l, hl]⟩
      have hd' : d < n := by omega
      change (referenceDivergence (C (r a).1) (r a).2 d hd'
        (childRefs (Finset.univ.image r) (r a).1)).coefficient (fun j => m j.succ) =
        (referenceDivergence (C' (s a).1) (s a).2 d hd'
        (childRefs (Finset.univ.image s) (s a).1)).coefficient (fun j => m j.succ)
      rw [hR,hS]
      exact ih _ _ rr ss aa hsplit' d hd' _

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree

theorem splitDepth_symm {n : ℕ} (S : PrescribedTree n) (a b : Leaf S) :
    splitDepth S a b = splitDepth S b a := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases h : i = j
    · subst j
      rw [splitDepth_same_child, splitDepth_same_child, ih]
    · rw [splitDepth_diff_child C i j h, splitDepth_diff_child C j i (Ne.symm h)]

noncomputable local instance instDecidable_6_re47a78_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Positional ancestry is an ultrametric similarity, independently of spins. -/
theorem splitDepth_ultrametric {n : ℕ} (S : PrescribedTree n) (a b c : Leaf S) :
    min (splitDepth S a b) (splitDepth S b c) ≤ splitDepth S a c := by
  induction S with
  | leaf => exact le_refl _
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    obtain ⟨l,c⟩ := c
    by_cases hij : i = j
    · subst j
      by_cases hil : i = l
      · subst l
        rw [splitDepth_same_child, splitDepth_same_child, splitDepth_same_child]
        have h := ih i a b c
        omega
      · rw [splitDepth_diff_child C i l hil, Nat.min_zero]
        exact Nat.zero_le _
    · rw [splitDepth_diff_child C i j hij, Nat.zero_min]
      exact Nat.zero_le _

 
theorem deepest_reference_profile {n : ℕ} (S : PrescribedTree n) (b a r : Leaf S)
    (hmax : splitDepth S b r ≤ splitDepth S b a) :
    splitDepth S b r = min (splitDepth S b a) (splitDepth S a r) := by
  have h1 := splitDepth_ultrametric S b a r
  have h2 := splitDepth_ultrametric S a b r
  rw [splitDepth_symm S a b, min_eq_right hmax] at h2
  exact le_antisymm (le_min hmax h2) h1

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_7
theorem labeledOldMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (x : Leaf S) :
    labeledOldMatch S T r s b x ↔
      matchesOldProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) x := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

theorem labeledFreshMatch_profile {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a)) (v : Internal S) :
    labeledFreshMatch S T r s b v ↔
      matchesFreshProfile S (Finset.univ.image r) (r a) (splitDepth T b (s a)) v := by
  constructor
  · intro h y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    rw [h i, hsplit, deepest_reference_profile T b (s a) (s i) (hmax i)]
  · intro h i
    have hh := h (r i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hsplit] at hh
    rw [hh, deepest_reference_profile T b (s a) (s i) (hmax i)]

/-- Every eligible old or fresh choice is counted once. Its signed total
depends only on the prescribed reference splitting matrix. -/
theorem labeled_choice_total {n : ℕ} (S T : PrescribedTree n)
    {ι : Type} [Fintype ι] (r : ι → Leaf S) (s : ι → Leaf T) (b : Leaf T) (a : ι)
    (hsplit : ∀ i j, splitDepth S (r i) (r j) = splitDepth T (s i) (s j))
    (hne : b ≠ s a) (hmax : ∀ i, splitDepth T b (s i) ≤ splitDepth T b (s a))
    (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ x : Leaf S, if labeledOldMatch S T r s b x then (1:ℝ) else 0) +
      (∑ v : Internal S, if labeledFreshMatch S T r s b v then gamma S m v else 0) =
      (referenceDivergence T (s a) (splitDepth T b (s a))
        (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image s)).coefficient m := by
  simp_rw [labeledOldMatch_profile S T r s b a hsplit hmax,
    labeledFreshMatch_profile S T r s b a hsplit hmax]
  rw [reference_profile_total S (r a) (splitDepth T b (s a))
    (splitDepth_lt_of_ne T b (s a) hne) (Finset.univ.image r)
    (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) m hend]
  exact reference_coefficient_invariant S T r s a hsplit _ _ m

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

theorem branchProduct_succ (x y : ℝ) {k : ℕ} (hk : 0 < k) :
    branchProduct x y (k+1) = branchProduct x y k * (x-(k:ℝ)*y) := by
  classical
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [branchProduct, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]


attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_1
noncomputable local instance (priority := 2000) instDecidableEqSigma_re47a78_1 {α : Type*} (β : α → Type*) : DecidableEq (Sigma β) := Classical.decEq _
theorem childRefs_insert_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (insert (⟨i,a⟩ : Leaf (.node k C)) R) j = childRefs R j := by
  classical
  ext b
  constructor
  · intro h
    have hh := (mem_childRefs _ j b).mp h
    rcases Finset.mem_insert.mp hh with hab | hb
    · exact (hij (congrArg Sigma.fst hab)).elim
    · exact (mem_childRefs R j b).mpr hb
  · intro h
    apply (mem_childRefs _ j b).mpr
    exact Finset.mem_insert_of_mem ((mem_childRefs R j b).mp h)

theorem childRefs_singleton_other {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (i j : Fin k) (hij : j ≠ i) (a : Leaf (C i)) :
    childRefs (C := C) ({⟨i,a⟩} : Finset (Leaf (.node k C))) j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hh := Finset.mem_singleton.mp ((mem_childRefs _ j b).mp hb)
  exact hij (congrArg Sigma.fst hh)

@[simp] theorem partialKappa_singleton {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (a : Leaf S) : partialKappa S m {a} = 1 := by
  classical
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    change branchProduct (m 0) (m 1) (Finset.image (fun a : Sigma (fun j => Leaf (C j)) => a.1) {⟨i,a⟩}).card * _ = 1
    rw [Finset.image_singleton,Finset.card_singleton,branchProduct_one,one_mul]
    apply Finset.prod_eq_one
    intro j _
    by_cases hji : j = i
    · subst j
      rw [childRefs_singleton_same]
      exact ih i (fun j => m j.succ) a
    · rw [childRefs_singleton_other i j hji,partialKappa_empty]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

private theorem prod_local_factor {α : Type*} [Fintype α] (f g : α → ℝ) (i : α) (c : ℝ)
    (hi : f i = c*g i) (ho : ∀ j, j ≠ i → f j = g j) :
    (∏ j, f j) = c*∏ j, g j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),hi]
  have he : (∏ j ∈ Finset.univ.erase i, f j) = ∏ j ∈ Finset.univ.erase i, g j :=
    Finset.prod_congr rfl (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  rw [he,mul_assoc]

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableEqLeaf_2
private theorem childRefs_eq_empty_of_unoccupied {n : ℕ} {k : ℕ+} {C : Fin k → PrescribedTree n}
    (R : Finset (Leaf (.node k C))) (i : Fin k) (hi : i ∉ R.image (fun a => a.1)) :
    childRefs R i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact hi (Finset.mem_image.mpr ⟨⟨i,a⟩,(mem_childRefs R i a).mp ha,rfl⟩)

 
theorem partialKappa_insert {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (R : Finset (Leaf S)) (a b : Leaf S)
    (ha : a ∈ R) (hb : b ∉ R)
    (hmax : ∀ r ∈ R, splitDepth S b r ≤ splitDepth S b a) :
    partialKappa S m (insert b R) =
      (referenceDivergence S a (splitDepth S b a)
        (splitDepth_lt_of_ne S b a (fun h => hb (h ▸ ha))) R).coefficient m *
        partialKappa S m R := by
  classical
  induction S with
  | leaf =>
    have he : a = b := @Subsingleton.elim Unit (inferInstanceAs (Subsingleton Unit)) a b
    exact (hb (he ▸ ha)).elim
  | @node n k C ih =>
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hji : j = i
    · subst j
      have hai : a ∈ childRefs R i := (mem_childRefs R i a).mpr ha
      have hbi : b ∉ childRefs R i := fun h => hb ((mem_childRefs R i b).mp h)
      have hmi : ∀ r ∈ childRefs R i, splitDepth (C i) b r ≤ splitDepth (C i) b a := by
        intro r hr
        have hh := hmax ⟨i,r⟩ ((mem_childRefs R i r).mp hr)
        rw [splitDepth_same_child,splitDepth_same_child] at hh
        omega
      have hei : i ∈ R.image (fun r => r.1) := Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩
      have hroot : (insert (⟨i,b⟩ : Leaf (.node k C)) R).image (fun r => r.1) =
          R.image (fun r => r.1) := by
        erw [Finset.image_insert]
        exact Finset.insert_eq_of_mem hei
      let c := (referenceDivergence (C i) a (splitDepth (C i) b a)
        (splitDepth_lt_of_ne _ b a (fun h => hbi (h ▸ hai))) (childRefs R i)).coefficient
          (fun z => m z.succ)
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨i,b⟩ : Leaf (.node k C)) R) t)) =
          c*∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply prod_local_factor _ _ i c
        · rw [childRefs_insert_same]
          exact ih i (fun z => m z.succ) (childRefs R i) a b hai hbi hmi
        · intro t hti
          rw [childRefs_insert_other R i t hti]
      change branchProduct (m 0) (m 1) ((insert (⟨i,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod]
      simp only [splitDepth_same_child,Nat.add_comm 1]
      change branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * (c*_) =
        c*(branchProduct (m 0) (m 1) (R.image (fun r => r.1)).card * _)
      ring
    · have hz : splitDepth (.node k C) (⟨j,b⟩ : Leaf (.node k C)) ⟨i,a⟩ = 0 :=
        splitDepth_diff_child C j i hji b a
      have hj : j ∉ R.image (fun r => r.1) := by
        intro h
        obtain ⟨⟨t,r⟩,hr,ht⟩ := Finset.mem_image.mp h
        change t = j at ht
        subst t
        have hh := hmax ⟨j,r⟩ hr
        rw [hz,splitDepth_same_child] at hh
        omega
      have hchild := childRefs_eq_empty_of_unoccupied R j hj
      have hcard : 0 < (R.image (fun r => r.1)).card :=
        Finset.card_pos.mpr ⟨i,Finset.mem_image.mpr ⟨⟨i,a⟩,ha,rfl⟩⟩
      have hroot : ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image (fun r => r.1)).card =
          (R.image (fun r => r.1)).card+1 := by
        erw [Finset.image_insert,Finset.card_insert_of_notMem hj]
      have hprod : (∏ t, partialKappa (C t) (fun z => m z.succ)
          (childRefs (insert (⟨j,b⟩ : Leaf (.node k C)) R) t)) =
          ∏ t, partialKappa (C t) (fun z => m z.succ) (childRefs R t) := by
        apply Finset.prod_congr rfl
        intro t _
        by_cases ht : t = j
        · subst t
          rw [childRefs_insert_same,hchild,Finset.insert_empty,partialKappa_singleton,
            partialKappa_empty]
        · rw [childRefs_insert_other R j t ht]
      change branchProduct (m 0) (m 1) ((insert (⟨j,b⟩ : Leaf (.node k C)) R).image
        (fun r => r.1)).card * _ = _
      erw [hroot,hprod,branchProduct_succ _ _ hcard]
      simp only [hz]
      change (_ * (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1))*_ =
        (m 0-((R.image (fun r => r.1)).card : ℝ)*m 1)*(_*_)
      ring

end DilutedSpinGlass.PrescribedTree

end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_10
theorem leaves_pos {n : ℕ} (S : PrescribedTree n) : 0 < leaves S := by
  induction S with
  | leaf => decide
  | @node n k C ih =>
    exact Finset.sum_pos (fun i _ => ih i) Finset.univ_nonempty

/-- One fresh growth creates at most one branching vertex; new continuations
are unary. This holds even at coincident depths elsewhere in the tree. -/
theorem branchingCount_grow {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (P : ℕ → Prop) :
    branchingCount (grow S v) P = branchingCount S P +
      (if P (vertexDepth S v) ∧ vertexArity S v = 1 then 1 else 0) := by
  classical
  induction S generalizing P with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (if P 0 ∧ 1 < (k:ℕ)+1 then 1 else 0) +
        (∑ j : Fin ((k:ℕ)+1), branchingCount (Fin.cases (single n) C j) (fun d => P (d+1))) =
        ((if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
          ∑ j : Fin k, branchingCount (C j) (fun d => P (d+1))) +
            (if P 0 ∧ (k:ℕ)=1 then 1 else 0)
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, branchingCount_single, zero_add]
      have hk : 0 < (k:ℕ) := k.property
      by_cases hP : P 0 <;> by_cases hk1 : (k:ℕ) = 1 <;>
        simp [hP, hk1, show ¬1 < (k:ℕ) ↔ (k:ℕ)=1 by omega, Nat.add_comm]
    | some v =>
      obtain ⟨i,v⟩ := v
      simp only [grow, branchingCount, vertexDepth, vertexArity]
      have hsum : (∑ j, branchingCount (Function.update C i (grow (C i) v) j)
          (fun d => P (d+1))) =
          (∑ j, branchingCount (C j) (fun d => P (d+1))) +
            (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0) := by
        calc
          _ = ∑ j, (branchingCount (C j) (fun d => P (d+1)) +
                if j = i then
                  (if P (vertexDepth (C i) v + 1) ∧ vertexArity (C i) v = 1 then 1 else 0)
                else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp only [Function.update_self, ite_true]
                exact ih i v (fun d => P (d+1))
              · simp [hji]
          _ = _ := by simp [Finset.sum_add_distrib]
      rw [hsum, Nat.add_assoc]

theorem depthCount_le_leaves {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    depthCount S d ≤ leaves S := by
  induction S generalizing d with
  | leaf => simp [depthCount, leaves]
  | @node n k C ih =>
    cases d with
    | zero => exact leaves_pos (.node k C)
    | succ d => exact Finset.sum_le_sum (fun i _ => ih i d)

/-- Identification with the actual finite internal-vertex index type. -/
theorem depthCount_eq_sum {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = d then (1:ℕ) else 0) = depthCount S d := by
  classical
  induction S generalizing d with
  | leaf => exact Finset.sum_eq_zero (fun v _ => nomatch v)
  | @node n k C ih =>
    change (∑ v : Option ((i : Fin k) × Internal (C i)), _) = _
    rw [Fintype.sum_option, Fintype.sum_sigma]
    cases d with
    | zero => simp [vertexDepth, depthCount]
    | succ d => simpa [vertexDepth, depthCount] using congrArg (Finset.sum Finset.univ) (funext (fun i => ih i d))

theorem gamma_grid_unary {n : ℕ} (S : PrescribedTree n) (v : Internal S)
    (d L : ℕ) (hv : vertexArity S v = 1) :
    gamma S (grid n d L) v = -(L:ℝ)⁻¹ := by
  induction S generalizing d with
  | leaf => nomatch v
  | @node n k C ih =>
    change Option ((i : Fin k) × Internal (C i)) at v
    cases v with
    | none =>
      change (k:ℕ) = 1 at hv
      simp [gamma, grid, hv, Nat.cast_add, Nat.cast_one, add_div]
    | some v =>
      obtain ⟨i,v⟩ := v
      change gamma (C i) (fun j => grid (n+1) d L j.succ) v = _
      have heq : (fun j : Fin (n+1) => grid (n+1) d L j.succ) = grid n (d+1) L := by
        funext j
        simp [grid, Fin.val_succ, Nat.add_comm, Nat.add_left_comm]
      rw [heq]
      exact ih i v (d+1) hv

/-- The sum of coefficients of unary splits at a specified depth is at most
`leaves/L`, uniformly in the total number of levels. -/
theorem unary_depth_budget {n : ℕ} (S : PrescribedTree n) (d L q : ℕ) :
    (∑ v : Internal S, if vertexDepth S v = q ∧ vertexArity S v = 1 then
      |gamma S (grid n d L) v| else 0) ≤ (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ ≤ ∑ v : Internal S, (if vertexDepth S v = q then (1:ℝ) else 0) * (L:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : vertexDepth S v = q ∧ vertexArity S v = 1
      · rw [ite_eq_left hv, gamma_grid_unary S v d L hv.2, abs_neg,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), ite_eq_left hv.1, one_mul]
      · rw [ite_eq_right hv]
        positivity
    _ = (depthCount S q:ℝ) * (L:ℝ)⁻¹ := by
      rw [← Finset.sum_mul, ← depthCount_eq_sum S q]
      push_cast
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast depthCount_le_leaves S q)
      (inv_nonneg.mpr (Nat.cast_nonneg _))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_11
theorem unary_set_budget {n : ℕ} (S : PrescribedTree n) (d L : ℕ) (Q : Finset ℕ) :
    (∑ v : Internal S, if charged S Q v then |gamma S (grid n d L) v| else 0) ≤
      (Q.card:ℝ) * (leaves S:ℝ) * (L:ℝ)⁻¹ := by
  classical
  calc
    _ = ∑ q ∈ Q, ∑ v : Internal S,
        if vertexDepth S v = q ∧ vertexArity S v = 1 then
          |gamma S (grid n d L) v| else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      by_cases ha : vertexArity S v = 1
      · simp [charged, ha]
      · simp [charged, ha]
    _ ≤ ∑ _q ∈ Q, (leaves S:ℝ) * (L:ℝ)⁻¹ :=
      Finset.sum_le_sum (fun q _ => unary_depth_budget S d L q)
    _ = _ := by simp [mul_assoc]

theorem sum_abs_gamma_grid {L : ℕ} (hL : 0 < L) (S : PrescribedTree L) :
    (∑ v : Internal S, |gamma S (grid L 0 L) v|) = (leaves S:ℝ) := by
  apply sum_abs_gamma
  · intro i j hij
    simp only [grid, Nat.zero_add]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp [grid]
  · simp [grid, ne_of_gt hL]

/-- Exact correspondence between charging steps and actual terminal branching
vertices. Distinct vertices at the same depth are counted separately. -/
theorem chargeMass_eq_historyMass {L : ℕ} (Q : Finset ℕ) (B k a : ℕ)
    (S : PrescribedTree L) :
    chargeMass Q k S a (B - branchingCount S (· ∈ Q)) =
      historyMass (fun T => if B ≤ branchingCount T (· ∈ Q) then 1 else 0) k S a := by
  classical
  induction k generalizing S a with
  | zero => simp [chargeMass, historyMass, Nat.sub_eq_zero_iff_le]
  | succ k ih =>
    simp only [chargeMass, historyMass, ih]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    have heq : B - branchingCount (grow S v) (· ∈ Q) =
        B - branchingCount S (· ∈ Q) - (if charged S Q v then 1 else 0) := by
      rw [branchingCount_grow, Nat.sub_add_eq]
      by_cases hh : charged S Q v
      · have h := hh
        simp only [charged] at h
        simp [h, hh]
      · have h : ¬ (vertexDepth S v ∈ Q ∧ vertexArity S v = 1) := hh
        simp [h, hh]
    rw [← heq, ih]

theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

/-- Every specified split contributes one factor delta; constants are independent
of the grid denominator. This also handles arbitrarily repeated target depths. -/
theorem chargeBound_scale (C D δ : ℝ) (k b : ℕ) :
    chargeBound C (D*δ) k b = chargeBound C D k b * δ^b := by
  induction k generalizing b with
  | zero =>
    cases b <;> simp [chargeBound]
  | succ k ih =>
    cases b with
    | zero => simp only [chargeBound, ih, pow_zero, mul_one]
    | succ b => simp only [chargeBound, ih, pow_succ]; ring

/-- A genuine history estimate, not a distribution postulated from the desired
identity. R bounds the leaves during all the remaining growth steps. -/
theorem chargeMass_bound {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (R k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) (hR : leaves S + k ≤ R) :
    chargeMass Q k S a b ≤
      chargeBound (2*(R:ℝ)) ((Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹) k b := by
  classical
  let C : ℝ := 2*(R:ℝ)
  let D : ℝ := (Q.card:ℝ)*(R:ℝ)*(L:ℝ)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  change chargeMass Q k S a b ≤ chargeBound C D k b
  induction k generalizing S a b with
  | zero => rfl
  | succ k ih =>
    have ho := fun b => ih b (a-1) S (Nat.le_trans (Nat.sub_le _ _) ha) (by omega)
    have hf := fun b (v : Internal S) => ih b a (grow S v) (by rw [leaves_grow]; omega)
      (by rw [leaves_grow]; omega)
    have hle : (leaves S:ℝ) ≤ (R:ℝ) := by exact_mod_cast (show leaves S ≤ R by omega)
    have haR : (a:ℝ) + (leaves S:ℝ) ≤ C := by
      have haa : (a:ℝ) ≤ (leaves S:ℝ) := by exact_mod_cast ha
      dsimp [C]
      linarith
    have hsum := sum_abs_gamma_grid hL S
    have hgood : (∑ v : Internal S, if charged S Q v then
        |gamma S (grid L 0 L) v| else 0) ≤ D :=
      (unary_set_budget S 0 L Q).trans (by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
    cases b with
    | zero =>
      simp only [chargeMass, Nat.zero_sub, chargeBound]
      calc
        _ ≤ (a:ℝ) * chargeBound C D k 0 +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| * chargeBound C D k 0 := by
          apply add_le_add (mul_le_mul_of_nonneg_left (ho 0) (Nat.cast_nonneg _))
          exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf 0 v) (abs_nonneg _))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k 0 := by
          rw [← Finset.sum_mul, hsum]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _)
    | succ b =>
      have hf' (v : Internal S) :
          chargeMass Q k (grow S v) a (b+1 - if charged S Q v then 1 else 0) ≤
            chargeBound C D k (b+1) +
              (if charged S Q v then chargeBound C D k b else 0) := by
        by_cases hv : charged S Q v
        · simp only [ite_eq_left hv, Nat.add_sub_cancel]
          exact (hf b v).trans (le_add_of_nonneg_left (chargeBound_nonneg hC hD _ _))
        · simp only [ite_eq_right hv, Nat.sub_zero, add_zero]
          exact hf (b+1) v
      change (a:ℝ)*chargeMass Q k S (a-1) (b+1) + _ ≤
        C*chargeBound C D k (b+1) + D*chargeBound C D k b
      calc
        _ ≤ (a:ℝ) * chargeBound C D k (b+1) +
            ∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (chargeBound C D k (b+1) +
                if charged S Q v then chargeBound C D k b else 0) := by
          exact add_le_add (mul_le_mul_of_nonneg_left (ho _) (Nat.cast_nonneg _))
            (Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hf' v) (abs_nonneg _)))
        _ = ((a:ℝ)+(leaves S:ℝ))*chargeBound C D k (b+1) +
            (∑ v : Internal S, if charged S Q v then
              |gamma S (grid L 0 L) v| else 0) * chargeBound C D k b := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
          rw [Finset.sum_mul]
          have heq : (∑ v : Internal S, |gamma S (grid L 0 L) v| *
              (if charged S Q v then chargeBound C D k b else 0)) =
              ∑ v : Internal S, (if charged S Q v then |gamma S (grid L 0 L) v| else 0) *
                chargeBound C D k b := by
            apply Finset.sum_congr rfl
            intro v _
            split <;> simp_all only [mul_zero, zero_mul]
          rw [heq]
          ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right haR (chargeBound_nonneg hC hD _ _))
          (mul_le_mul_of_nonneg_right hgood (chargeBound_nonneg hC hD _ _))

 
theorem charging_final_shape {L : ℕ} (hL : 0 < L) (Q : Finset ℕ) (k b a : ℕ)
    (S : PrescribedTree L) (ha : a ≤ leaves S) :
    historyMass (fun T => if branchingCount S (· ∈ Q) + b ≤
        branchingCount T (· ∈ Q) then 1 else 0) k S a ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k b *
        (L:ℝ)⁻¹^b := by
  rw [← chargeMass_eq_historyMass Q, Nat.add_sub_cancel_left]
  have hh := chargeMass_bound hL Q (leaves S+k) k b a S ha le_rfl
  rw [chargeBound_scale] at hh
  exact hh

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMarkLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

noncomputable local instance treeMarkLawPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Deleting a newly sampled branch preserves the joint law of ALL old paths.
The old test may be arbitrarily correlated with any retained old prefixes. -/
theorem grow_projectivity {n : ℕ} (S : PrescribedTree n) (K : KernelTower Ω n)
    (v : Internal S) (H : Sample Ω S → ℝ) :
    (sampleLaw (grow S v) K).expect (fun x => H (oldSample S v x)) =
      (sampleLaw S K).expect H := by
  simpa only [mul_one,freshEval_const] using
    extension_sampling S K v H (fun _ => (1:ℝ))


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_Polarization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory

lemma abs_integral_le_one {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |∫ z, f z ∂μ| ≤ 1 := by
  calc
    _ ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z : Z, (1:ℝ) ∂μ := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => abs_nonneg (f z))) (integrable_const 1)
      (Filter.Eventually.of_forall hf)
    _ = 1 := by simp

lemma centered_scalar_div_bound {H H1 F A J δ : ℝ}
    (_hJ : J ≠ 0) (hδ : 0 ≤ δ) (hF : |F| ≤ 1) (hA : |A| ≤ 1)
    (h1 : H1/J = -δ*A) :
    H/J ≤ |H-F*H1|/|J|+δ := by
  have he : H/J = (H-F*H1)/J+F*(H1/J) := by ring
  have hD : (H-F*H1)/J ≤ |H-F*H1|/|J| := by
    simpa only [abs_div] using le_abs_self ((H-F*H1)/J)
  have hFA : |F*A| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hF hA (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hl := (abs_le.mp hFA).1
  rw [he,h1]
  nlinarith

/-- Root averaging MUST precede the absolute value of the covariance. This
lemma retains that quantifier order, while integrating genuine single-copy
projection errors. There is no root-wise concentration hypothesis. -/
theorem root_matrix_error_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (E H H1 F A Et Eo : Z → ℝ) (J δ c B M : ℝ)
    (hJ : J ≠ 0) (hδ : 0 ≤ δ)
    (hF : ∀ z, |F z| ≤ 1) (hA : ∀ z, |A z| ≤ 1)
    (h1 : ∀ z, H1 z/J = -δ*A z)
    (hE : Integrable E μ) (hH : Integrable H μ) (_hAint : Integrable A μ)
    (hEt : Integrable Et μ) (hEo : Integrable Eo μ)
    (hpoint : ∀ z, c*E z ≤ δ+H z/J+Et z*B/|J|+M*Eo z) :
    c*(∫ z, E z ∂μ) ≤ 2*δ+
      |(∫ z, H z ∂μ)-(∫ z, F z ∂μ)*(∫ z, H1 z ∂μ)|/|J|+
      (∫ z, Et z ∂μ)*B/|J|+M*(∫ z, Eo z ∂μ) := by
  have hh1 : (∫ z, H1 z ∂μ)/J = -δ*(∫ z, A z ∂μ) := by
    rw [← integral_div]
    simp_rw [h1]
    rw [integral_const_mul]
  have hs := centered_scalar_div_bound (H := ∫ z, H z ∂μ) hJ hδ (abs_integral_le_one μ F hF)
    (abs_integral_le_one μ A hA) hh1
  have hi1 : Integrable (fun z => δ+H z/J) μ := (integrable_const δ).add (hH.div_const J)
  have hi2 : Integrable (fun z => δ+H z/J+Et z*B/|J|) μ := hi1.add ((hEt.mul_const B).div_const |J|)
  have hi := integral_mono (hE.const_mul c) (hi2.add (hEo.const_mul M)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add hi2 (hEo.const_mul M),
    integral_add hi1 ((hEt.mul_const B).div_const |J|),
    integral_add (integrable_const δ) (hH.div_const J),
    integral_div,integral_div,integral_mul_const,integral_const_mul] at hi
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
  linarith

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeEmbedding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every old leaf of a prescribed tree has exactly the full kernel path law. -/
theorem leaf_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a : S.Leaf) (D : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => D (S.pathAt a x)) = (KernelTower.law n T).expect D := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun j => μ.bind (fun z => sampleLaw (C j) (K z)))).expect
      (fun x => D ((x i).1,(C i).pathAt a (x i).2)) = _
    have e := FiniteLaw.expect_pi_marginal
      (fun j => μ.bind (fun z => sampleLaw (C j) (K z))) i
      (fun y => D (y.1,(C i).pathAt a y.2))
    refine e.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply FiniteLaw.expect_congr
    intro z
    exact ih i (K z) a (fun y => D (z,y))

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {T S : PrescribedTree n}

variable {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

lemma childIndex_injective (f : SplitMap (.node k C) (.node l D)) :
    Function.Injective f.childIndex := by
  intro i j hij
  by_contra h
  have hz : splitDepth (.node l D) (f.leaf ⟨i,firstLeaf (C i)⟩)
      (f.leaf ⟨j,firstLeaf (C j)⟩) = 0 := by
    exact (f.split ⟨i,firstLeaf (C i)⟩ ⟨j,firstLeaf (C j)⟩).trans
      (splitDepth_diff_child C i j h _ _)
  exact (splitDepth_node_zero D _ _).mp hz hij

lemma arity_le (f : SplitMap (.node k C) (.node l D)) : (k:ℕ) ≤ l := by
  have h := Fintype.card_le_of_injective _ f.childIndex_injective
  simpa only [Fintype.card_fin] using h

/-- Exact split constraints force every target branching vertex to occur in
the actual history, even when several different vertices have equal depths. -/
theorem branchingCount_le {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  induction T generalizing P with
  | leaf => cases S; exact le_rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      change (if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
        (∑ i, branchingCount (C i) (fun d => P (d+1))) ≤
        (if P 0 ∧ 1 < (l:ℕ) then 1 else 0) +
        (∑ j, branchingCount (D j) (fun d => P (d+1)))
      apply Nat.add_le_add
      · split_ifs with hk hl hl
        · exact le_rfl
        · exact False.elim (hl ⟨hk.1,hk.2.trans_le f.arity_le⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · calc
          _ ≤ ∑ i, branchingCount (D (f.childIndex i)) (fun d => P (d+1)) :=
            Finset.sum_le_sum (fun i _ => ih i (f.child i) (fun d => P (d+1)))
          _ = ∑ j ∈ Finset.univ.image f.childIndex, branchingCount (D j) (fun d => P (d+1)) := by
            rw [Finset.sum_image]
            exact fun i _ j _ h => f.childIndex_injective h
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_LabeledColorHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma expect_pi_pair (P : (i : ι) → FiniteLaw (α i)) (i j : ι) (hij : j ≠ i)
    (f : α i → α j → ℝ) :
    (pi P).expect (fun x => f (x i) (x j)) =
      (P i).expect (fun x => (P j).expect (f x)) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hij]
  exact expect_pi_marginal (fun k : {k // k ≠ i} => P k) ⟨j,hij⟩ (f x)

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- The complete TWO-path joint law is determined by geometric splitting,
not by coincidences of configurations. Unused branches are marginalized. -/
theorem pair_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      KernelTower.pairExpect n T (splitDepth S a b) f := by
  induction S with
  | leaf =>
    change KernelTower.unitLaw.expect (fun _ => f () ()) = f () ()
    exact FiniteLaw.expect_const _ _
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    by_cases hji : j = i
    · subst j
      rw [splitDepth_same_child]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => f (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [Nat.add_comm 1,KernelTower.pairExpect]
      apply FiniteLaw.expect_congr
      intro z
      exact ih i (K z) a b (fun x y => f (z,x) (z,y))
    · rw [splitDepth_diff_child C i j (Ne.symm hji)]
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => f ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)) = _
      refine (FiniteLaw.expect_pi_pair
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j hji
        (fun x y => f (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2))).trans ?_
      erw [FiniteLaw.expect_bind]
      simp only [FiniteLaw.expect_bind,KernelTower.pairExpect]
      erw [KernelTower.law_succ_expect n (μ,K)]
      simp_rw [KernelTower.law_succ_expect n (μ,K)]
      apply FiniteLaw.expect_congr
      intro x
      rw [← leaf_marginal (C i) (K x) a]
      apply FiniteLaw.expect_congr
      intro y
      apply FiniteLaw.expect_congr
      intro z
      exact leaf_marginal (C j) (K z) b (fun w => f (x,(C i).pathAt a y) (z,w))

lemma pair_marginal_eq {n : ℕ} (S R : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (c d : R.Leaf) (h : splitDepth S a b = splitDepth R c d)
    (f : FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => f (S.pathAt a x) (S.pathAt b x)) =
      (R.sampleLaw T).expect (fun x => f (R.pathAt c x) (R.pathAt d x)) := by
  rw [pair_marginal,pair_marginal,h]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma expect_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (f : Ω → Λ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Successive projection of independent child vectors in a spatial
contraction. This is the actual product law; no decorrelation is assumed. -/
theorem product_contraction {N k : ℕ} {α : Fin k → Type*} [∀ i, Fintype (α i)]
    (P : (i : Fin k) → FiniteLaw (α i)) (X : (i : Fin k) → α i → Fin N → ℝ)
    (hX : ∀ i x v, |X i x v| ≤ 1) (B : Fin N → ℝ) (hB : ∀ v, |B v| ≤ 1) :
    (pi P).l2 (fun x => dot (fun v => (∏ i, X i (x i) v)-
      ∏ i, (P i).expect (fun y => X i y v)) B) ≤
      ∑ i, Real.sqrt (Real.sqrt ((P i).covarianceEnergy (X i))) := by
  classical
  induction k generalizing B with
  | zero => simp [dot,l2]
  | succ k ih =>
    let Q := pi (fun i : Fin k => P i.succ)
    let μ := fun v => (P 0).expect (fun y => X 0 y v)
    let C := fun (x : (i : Fin k) → α i.succ) v => B v * ∏ i, X i.succ (x i) v
    let f := fun (x : (i : Fin (k+1)) → α i) =>
      dot (fun v => X 0 (x 0) v-μ v) (C (fun i => x i.succ))
    let g := fun (x : (i : Fin (k+1)) → α i) =>
      dot (fun v => (∏ i : Fin k, X i.succ (x i.succ) v)-
        ∏ i : Fin k, (P i.succ).expect (fun y => X i.succ y v)) (fun v => B v*μ v)
    have hμ (v : Fin N) : |μ v| ≤ 1 := (P 0).abs_expect_le (fun y => hX 0 y v)
    have hC (x : (i : Fin k) → α i.succ) (v : Fin N) : |C x v| ≤ 1 := by
      dsimp only [C]
      rw [abs_mul,Finset.abs_prod]
      exact (mul_le_mul (hB v) (Finset.prod_le_one (fun _ _ => abs_nonneg _)
        (fun index _ => hX index.succ (x index) v)) (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) zero_le_one).trans_eq (one_mul 1)
    have hBμ (v : Fin N) : |B v*μ v| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (hB v) (hμ v) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have he (x : (i : Fin (k+1)) → α i) :
        dot (fun v => (∏ i, X i (x i) v)-∏ i, (P i).expect (fun y => X i y v)) B = f x+g x := by
      simp only [f,g,C,dot,Fin.prod_univ_succ]
      rw [← add_div,← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro v _
      dsimp only [μ]
      ring
    have hf : (pi P).l2 f ≤ Real.sqrt (Real.sqrt ((P 0).covarianceEnergy (X 0))) := by
      apply Real.sqrt_le_sqrt
      rw [expect_pi_cons P (fun x => f x^2)]
      change (P 0).expect (fun a => Q.expect (fun x =>
        (dot (fun v => X 0 a v-μ v) (C x))^2)) ≤ _
      rw [expect_comm]
      exact (P 0).independent_contraction_bound Q (X 0) C hC
    have hg : (pi P).l2 g ≤ ∑ i : Fin k,
        Real.sqrt (Real.sqrt ((P i.succ).covarianceEnergy (X i.succ))) := by
      have h := ih (fun i => P i.succ) (fun i => X i.succ)
        (fun i => hX i.succ) (fun v => B v*μ v) hBμ
      have heq : (pi P).l2 g = Q.l2 (fun x => dot
          (fun v => (∏ i : Fin k, X i.succ (x i) v)-
            ∏ i : Fin k, (P i.succ).expect (fun y => X i.succ y v)) (fun v => B v*μ v)) := by
        unfold l2
        rw [expect_pi_cons]
        simp only [g,Fin.cons_succ,expect_const,Q]
      rw [heq]
      exact h
    calc
      _ = (pi P).l2 (fun x => f x+g x) := by unfold l2; rw [FiniteLaw.expect_congr _ (fun x => congrArg (·^2) (he x))]
      _ ≤ (pi P).l2 f+(pi P).l2 g := (pi P).l2_add_le f g
      _ ≤ _ := by rw [Fin.sum_univ_succ]; exact add_le_add hf hg

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

/-- Product replacement on bounded spin coordinates, with its exact finite
sum of coordinate errors. -/
theorem bounded_product_difference {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i-g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hF := hf a (Finset.mem_insert_self a s)
    have hG : |∏ i ∈ s, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      _ = |f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))+(f a-g a)*(∏ i ∈ s, g i)| := by
        congr 1; ring
      _ ≤ |f a| * |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)|+|f a-g a| * |∏ i ∈ s, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))) ((f a-g a)*(∏ i ∈ s, g i))
      _ ≤ 1*(∑ i ∈ s, |f i-g i|)+|f a-g a| * 1 :=
        add_le_add (mul_le_mul hF (ih hf' hg') (abs_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ = _ := by ring

theorem bounded_product_difference_sq {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    ((∏ i, f i)-(∏ i, g i))^2 ≤ (Fintype.card ι : ℝ)*∑ i, (f i-g i)^2 := by
  have hb := bounded_product_difference Finset.univ f g (fun i _ => hf i) (fun i _ => hg i)
  have hn : 0 ≤ ∑ i, |f i-g i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |f i-g i|)
  simp only [Finset.card_univ,sq_abs] at hs
  have hsq : ((∏ i, f i)-(∏ i, g i))^2 ≤ (∑ i, |f i-g i|)^2 := by
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hn] using hb)
  exact hsq.trans hs

end DilutedSpinGlass

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

omit [Fintype Ω] in
theorem leafProduct_eq_prod {n : ℕ} (S : PrescribedTree n)
    (f : FinitePath Ω n → ℝ) (z : Sample Ω S) :
    leafProduct S f z = ∏ a : Leaf S, f (pathAt S a z) := by
  induction S with
  | leaf =>
    change f () = ∏ _ : Unit, f ()
    simp
  | @node n k C ih =>
    simp only [leafProduct]
    change _ = ∏ a : (i : Fin k) × Leaf (C i), f (pathAt (.node k C) a z)
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl (fun i _ => ih i (fun y => f ((z i).1,y)) (z i).2)

theorem treeMean_eq_expect {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (f : FinitePath Ω n → ℝ) : treeMean S T f = (sampleLaw S T).expect (leafProduct S f) := by
  induction S with
  | leaf =>
    change f () = KernelTower.unitLaw.expect (fun _ => f ())
    rw [FiniteLaw.expect_const]
  | @node n k C ih =>
    change FiniteLaw Ω × (Ω → KernelTower Ω n) at T
    rcases T with ⟨P,Q⟩
    change (Ω × FinitePath Ω n) → ℝ at f
    change (∏ i, P.expect (fun a => treeMean (C i) (Q a) (fun y => f (a,y)))) =
      (FiniteLaw.pi (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))).expect
        (fun z => ∏ i, leafProduct (C i) (fun y => f ((z i).1,y)) (z i).2)
    rw [FiniteLaw.expect_pi_product (fun i : Fin k => P.bind (fun a => sampleLaw (C i) (Q a)))
      (fun i (z : Ω × Sample Ω (C i)) => leafProduct (C i) (fun y => f (z.1,y)) z.2)]
    apply Finset.prod_congr rfl
    intro i _
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact ih i (Q a) (fun y => f (a,y))

omit [Fintype Ω] in
theorem leafProduct_bound {n : ℕ} (S : PrescribedTree n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) (z : Sample Ω S) :
    |leafProduct S f z| ≤ 1 := by
  rw [leafProduct_eq_prod,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun a _ => hf (pathAt S a z))

theorem treeMean_bound {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    {f : FinitePath Ω n → ℝ} (hf : ∀ x, |f x| ≤ 1) : |treeMean S T f| ≤ 1 := by
  rw [treeMean_eq_expect]
  exact (sampleLaw S T).abs_expect_le (leafProduct_bound S hf)

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Literal child-by-child projection of a prescribed-tree multioverlap.
Each factor is a spin product sampled from an actual independent child law.
This is the projection error used before signed-history charging. -/
theorem node_projection {n : ℕ} (k : ℕ+) (C : Fin k → PrescribedTree n)
    (T : KernelTower Ω (n+1)) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (hf : ∀ x v, |f x v| ≤ 1) (B : Fin N → ℝ) (hB : ∀ v, |B v| ≤ 1) :
    ((PrescribedTree.node k C).sampleLaw T).l2 (fun z => FiniteLaw.dot
      (fun v => (PrescribedTree.node k C).leafProduct (fun x => f x v) z -
        (PrescribedTree.node k C).treeMean T (fun x => f x v)) B) ≤
      ∑ i, Real.sqrt (Real.sqrt (childEnergy (C i) T f)) := by
  have hm (i : Fin k) (v : Fin N) :
      (T.1.bind (fun a => (C i).sampleLaw (T.2 a))).expect
        (fun z => (C i).leafProduct (fun y => f (z.1,y) v) z.2) =
      T.1.expect (fun a => (C i).treeMean (T.2 a) (fun y => f (a,y) v)) := by
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact (treeMean_eq_expect (C i) (T.2 a) (fun y => f (a,y) v)).symm
  have h := FiniteLaw.product_contraction
    (fun i : Fin k => T.1.bind (fun a => (C i).sampleLaw (T.2 a)))
    (fun i z v => (C i).leafProduct (fun y => f (z.1,y) v) z.2)
    (fun i z v => leafProduct_bound (C i) (fun y => hf (z.1,y) v) z.2) B hB
  simp_rw [hm] at h
  exact h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidableSplitDepthContinuity
lemma pairDivergence_coefficient {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    (pairDivergence S a d hd).coefficient m =
      m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    cases d with
    | zero => simp [pairDivergence,Divergence.coefficient]
    | succ d => exact ih a.1 a.2 d (by omega) (fun j => m j.succ)

lemma pairDivergence_old {n : ℕ} (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).oldAllowed b ↔ splitDepth S a b = d := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    cases d with
    | zero =>
      change j ∉ ({i} : Finset (Fin k)) ↔ _
      simp only [Finset.mem_singleton]
      by_cases h : i = j
      · subst j; rw [splitDepth_same_child]; simp
      · rw [splitDepth_diff_child C i j h]; simp [Ne.symm h]
    | succ d =>
      change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).oldAllowed (h ▸ b)) ↔ _
      by_cases h : j = i
      · subst j
        simp only [exists_const,splitDepth_same_child]
        rw [ih i a b d (by omega)]
        omega
      · rw [splitDepth_diff_child C i j (Ne.symm h)]
        constructor
        · rintro ⟨he,_⟩; exact (h he).elim
        · intro he; omega

lemma pairDivergence_fresh {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (v : S.Internal) (d : ℕ) (hd : d < n) :
    (pairDivergence S a d hd).freshAllowed v ↔ freshSplitDepth S v a = d := by
  induction S generalizing d with
  | leaf => exact v.elim
  | @node n k C ih =>
    rcases a with ⟨i,a⟩
    change Option ((j : Fin k) × (C j).Internal) at v
    cases d with
    | zero =>
      cases v with
      | none => change True ↔ 0 = 0; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change j ∉ ({i} : Finset (Fin k)) ↔ _
        simp only [Finset.mem_singleton]
        exact ne_comm.trans (freshSplitDepth_node_zero C j v ⟨i,a⟩).symm
    | succ d =>
      cases v with
      | none => change False ↔ 0 = d+1; simp
      | some v =>
        rcases v with ⟨j,v⟩
        change (∃ h : j = i, (pairDivergence (C i) a d (by omega)).freshAllowed (h ▸ v)) ↔ _
        by_cases h : j = i
        · subst j
          simp only [exists_const,freshSplitDepth_same_child]
          rw [ih i a v d (by omega)]
          omega
        · rw [freshSplitDepth_diff_child C j i (Ne.symm h)]
          constructor
          · rintro ⟨he,_⟩; exact (h he).elim
          · intro he; omega

/-- Exact signed total of every path splitting from the anchor at d. -/
theorem pair_choice_total {n : ℕ} (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) (hend : m (Fin.last n) = 1) :
    (∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0) +
      (∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
        then gamma S m v else 0) = m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩ := by
  simp_rw [splitDepth_symm (grow S _) (oldLeaf S _ a),splitDepth_new_old,
    ← pairDivergence_old S a _ d hd,← pairDivergence_fresh S a _ d hd]
  rw [divergence_choice_total _ m hend,pairDivergence_coefficient]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

lemma tailMean_bound (S : PrescribedTree n) (r : ℕ) (T : KernelTower Ω (n+r))
    (f : FinitePath Ω (n+r) → ℝ) (hf : ∀ x, |f x| ≤ 1) (x : FinitePath Ω (n+r)) :
    |tailMean S r T f x| ≤ 1 := by
  induction r with
  | zero => exact treeMean_bound S T hf
  | succ r ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X I Y : Type} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Y] {M : ℕ}

theorem measurable_packRoot
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2)) :
    Measurable (packRoot F) := by
  have hn (k : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × Sigma (RootPath I) =>
      F z.1.1 k z.1.2 z.2.1 z.2.2) := measurable_prodSigma (f := fun (z : RootPath Y M × RootPath X k) n y => F z.1 k z.2 n y) (hF k)
  have hk : Measurable (fun z : (RootPath Y M × Sigma (RootPath I)) × Sigma (RootPath X) =>
      F z.1.1 z.2.1 z.2.2 z.1.2.1 z.1.2.2) :=
    measurable_prodSigma (f := fun (z : RootPath Y M × Sigma (RootPath I)) k x => F z.1 k x z.2.1 z.2.2) (fun k => (hn k).comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
  exact hk.comp ((measurable_fst.prodMk measurable_snd.snd).prodMk measurable_snd.fst)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePiInjective
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι κ : Type*} {α : κ → Type*}

attribute [local instance] OAI.DilutedSpinGlass.FiniteLaw.instDecidable
lemma injectionFactor_apply (e : ι → κ) (he : Function.Injective e)
    (g : (i : ι) → α (e i) → ℝ) (i : ι) (x : α (e i)) :
    injectionFactor e g (e i) x = g i x := by
  classical
  unfold injectionFactor
  have h : ∃ j, e j = e i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  have ht : ∀ (j : ι) (hj : e j = e i), g j (hj.symm ▸ x) = g i x := by
    intro j hj
    have hji := he hj
    subst j
    rfl
  exact ht _ (Classical.choose_spec h)

lemma injectionFactor_outside (e : ι → κ) (g : (i : ι) → α (e i) → ℝ)
    (j : κ) (h : j ∉ Set.range e) (x : α j) : injectionFactor e g j x = 1 := by
  classical
  exact dite_eq_right h

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [∀ i, Fintype (α i)]

/-- A finite family of distinct child coordinates has the corresponding
product law, regardless of the unused coordinates in the full old tree. -/
lemma expect_pi_injective_product (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (g : (i : ι) → α (e i) → ℝ) :
    (pi P).expect (fun x => ∏ i, g i (x (e i))) = ∏ i, (P (e i)).expect (g i) := by
  have hx (x : (j : κ) → α j) : (∏ i, g i (x (e i))) =
      ∏ j, injectionFactor e g j (x j) :=
    Fintype.prod_of_injective e he _ _ (fun j hj => injectionFactor_outside e g j hj (x j))
      (fun i => (injectionFactor_apply e he g i (x (e i))).symm)
  rw [(pi P).expect_congr hx,expect_pi_product]
  symm
  apply Fintype.prod_of_injective e he
  · intro j hj
    exact ((P j).expect_congr (fun x => injectionFactor_outside e g j hj x)).trans
      ((P j).expect_const 1)
  · intro i
    exact (P (e i)).expect_congr (fun x => (injectionFactor_apply e he g i x).symm)

lemma product_point_indicator {β : ι → Type*} (x y : (i : ι) → β i) :
    (∏ i, (if x i = y i then (1:ℝ) else 0)) = (if x = y then 1 else 0) := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hh
      exact h (funext (fun i => not_not.mp (not_exists.mp hh i)))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma finite_indicator_expansion {β : ι → Type*} [∀ i, Fintype (β i)]
    (H : ((i : ι) → β i) → ℝ) (x : (i : ι) → β i) :
    H x = ∑ y, H y * ∏ i, (if x i = y i then (1:ℝ) else 0) := by
  classical
  simp_rw [product_point_indicator]
  simp

variable [DecidableEq ι]

lemma expect_pi_injective (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (H : ((i : ι) → α (e i)) → ℝ) :
    (pi P).expect (fun x => H (fun i => x (e i))) = (pi (fun i => P (e i))).expect H := by
  classical
  have hl : (pi P).expect (fun x => H (fun i => x (e i))) =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi P).expect_congr (fun x => finite_indicator_expansion H (fun i => x (e i)))]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_injective_product P e he
      (fun i x => if x = y i then (1:ℝ) else 0))
  have hr : (pi (fun i => P (e i))).expect H =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi (fun i => P (e i))).expect_congr (finite_indicator_expansion H)]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_product (fun i => P (e i))
      (fun i x => if x = y i then (1:ℝ) else 0))
  exact hl.trans hr.symm

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalIndex
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]


end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree.SplitMap
open scoped BigOperators
variable {Ω : Type}

lemma pathAt_pullSample {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (a : T.Leaf) (x : Sample Ω S) :
    T.pathAt a (f.pullSample x) = S.pathAt (f.leaf a) x := by
  induction T with
  | leaf => cases S; rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      rcases a with ⟨i,a⟩
      rw [f.leaf_eq_child i a]
      change ((x (f.childIndex i)).1,pathAt (C i) a ((f.child i).pullSample (x (f.childIndex i)).2)) =
        ((x (f.childIndex i)).1,pathAt (D (f.childIndex i)) ((f.child i).leaf a) (x (f.childIndex i)).2)
      rw [ih]

variable [Fintype Ω]

/-- Every exact prescribed splitting matrix has the same sampling law in
EVERY actual extension, jointly over its entire selected leaf family. -/
theorem expect_pullSample {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (K : KernelTower Ω n) (F : Sample Ω T → ℝ) :
    (S.sampleLaw K).expect (fun x => F (f.pullSample x)) = (T.sampleLaw K).expect F := by
  classical
  induction T with
  | leaf => cases S; rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      rcases K with ⟨μ,K⟩
      let P := fun j : Fin l => μ.bind (fun z => sampleLaw (D j) (K z))
      let Q := fun i : Fin k => μ.bind (fun z => sampleLaw (C i) (K z))
      let φ := fun (i : Fin k) (x : Ω × Sample Ω (D (f.childIndex i))) =>
        (x.1,(f.child i).pullSample x.2)
      change (FiniteLaw.pi P).expect (fun x => F (fun i => φ i (x (f.childIndex i)))) =
        (FiniteLaw.pi Q).expect F
      have hp := FiniteLaw.expect_pi_injective P f.childIndex f.childIndex_injective
        (fun x => F (fun i => φ i (x i)))
      refine hp.trans ?_
      have hφ : ∀ (i : Fin k) (g : Ω × Sample Ω (C i) → ℝ),
          (P (f.childIndex i)).expect (fun x => (1:ℝ)*g (φ i x)) =
          (Q i).expect (fun y => (1:ℝ)*g y) := by
        intro i g
        simp only [one_mul,P,Q,FiniteLaw.expect_bind]
        apply FiniteLaw.expect_congr
        intro z
        exact ih i (f.child i) (K z) (fun y => g (z,y))
      simpa only [Finset.prod_const_one,mul_one] using FiniteLaw.expect_pi_weighted_map
        (fun i => P (f.childIndex i)) Q φ (fun _ _ => (1:ℝ)) (fun _ _ => (1:ℝ)) hφ F

/-- Same joint marginal expressed directly in leaf paths, so terminal overlap
and projection-error observables can use it without any sample relabeling. -/
theorem expect_paths {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (K : KernelTower Ω n) (F : (T.Leaf → FinitePath Ω n) → ℝ) :
    (S.sampleLaw K).expect (fun x => F (fun a => S.pathAt (f.leaf a) x)) =
      (T.sampleLaw K).expect (fun x => F (fun a => T.pathAt a x)) := by
  have he := f.expect_pullSample K (fun x => F (fun a => T.pathAt a x))
  simpa only [pathAt_pullSample] using he

end DilutedSpinGlass.PrescribedTree.SplitMap
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistorySelector
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ}

lemma historyMass_mul (F : PrescribedTree L → ℝ) (E : ℝ) (k : ℕ)
    (S : PrescribedTree L) (a : ℕ) :
    historyMass (fun T => E*F T) k S a = E*historyMass F k S a := by
  induction k generalizing S a with
  | zero => rfl
  | succ k ih =>
    simp only [historyMass,ih]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v _
      ring

variable {Ω C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Every literal labeled extension contributes its actual absolute coefficient.
The domination retains all old tests rather than replacing the sampled law by
an unsigned or independently resampled one. -/
theorem labeledHistory_abs_le_mass (F : PrescribedTree L → ℝ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hV : ∀ S pos f, (∀ x, |f x| ≤ 1) → |V S pos f| ≤ F S)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤ historyMass F cs.length S U.card := by
  induction cs generalizing S U with
  | nil => exact hV S pos f hf
  | cons c cs ih =>
    simp only [labeledHistory,List.length_cons,historyMass]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · calc
        _ ≤ ∑ i ∈ U, |labeledHistory (grid L 0 L) V cs S (U.erase i) loc
            (Function.update pos c (loc i)) f| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ U, historyMass F cs.length S (U.card-1) := by
          apply Finset.sum_le_sum
          intro i hi
          have h := ih S (U.erase i) loc (Function.update pos c (loc i)) f hf
          simpa only [Finset.card_erase_of_mem hi] using h
        _ = _ := by simp [nsmul_eq_mul]
    · calc
        _ ≤ ∑ v : S.Internal, |gamma S (grid L 0 L) v *
            labeledHistory (grid L 0 L) V cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro v _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact ih (grow S v) U _ _ _ (fun x => hf (oldSample S v x))

/-- Charging estimate for an actual labeled terminal observable. Restricting
the allowed splitting matrices and inserting a uniformly bounded projection
error are both handled in this single estimate. -/
theorem labeledHistory_charging_bound (hL : 0 < L) (Q : Finset ℕ) (b : ℕ)
    (V : (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E) (cs : List C) (S : PrescribedTree L)
    (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S)
    (hV : ∀ T pos g, (∀ x, |g x| ≤ 1) → |V T pos g| ≤ E *
      (if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0)) :
    |labeledHistory (grid L 0 L) V cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length b * (L:ℝ)⁻¹^b) := by
  have h := labeledHistory_abs_le_mass
    (fun T => E*(if branchingCount S (· ∈ Q)+b ≤ branchingCount T (· ∈ Q) then 1 else 0))
    V hV cs S U loc pos f hf
  rw [historyMass_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (charging_final_shape hL Q cs.length b U.card S hU) hE)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω C : Type} [Fintype Ω] {n : ℕ}

/-- Complete positional splitting matrices determine the full joint path law,
not just pair overlaps. The enumerating colors may repeat leaf positions. -/
theorem matrix_paths_expect (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (F : (C → FinitePath Ω n) → ℝ) :
    (S.sampleLaw K).expect (fun x => F (fun c => S.pathAt (pos c) x)) =
      (T.sampleLaw K).expect (fun x => F (fun c => T.pathAt (q c) x)) := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  have he (c : C) : e.leaf (q c) = pos c := by
    apply (splitDepth_eq_height S _ _).mp
    exact (h (Function.surjInv hq (q c)) c).trans
      ((congrArg (fun z => splitDepth T z (q c)) (Function.surjInv_eq hq (q c))).trans
        (splitDepth_self T (q c)))
  have hm := e.expect_paths K (fun x => F (fun c => x (q c)))
  simpa only [he] using hm

/-- An arbitrary correlated old test bounded by one costs at most the actual
single-target L2 error, since the entire target marginal is fixed. -/
theorem matrix_weighted_error (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (K : KernelTower Ω n) (D : (C → FinitePath Ω n) → ℝ)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(S.sampleLaw K).expect (fun x => f x * D (fun c => S.pathAt (pos c) x))| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) := by
  let P := S.sampleLaw K
  let g := fun x : Sample Ω S => D (fun c => S.pathAt (pos c) x)
  have hsq := P.expect_mul_sq_le f g
  have hf2 : P.expect (fun x => f x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        have hx : f x^2 ≤ (1:ℝ)^2 := sq_le_sq.mpr (by simpa using hf x)
        simpa using hx)
      _ = _ := P.expect_const 1
  have he : P.expect (fun x => g x^2) =
      (T.sampleLaw K).expect (fun x => D (fun c => T.pathAt (q c) x)^2) :=
    matrix_paths_expect T S q hq pos h K (fun x => D x^2)
  have hd := (T.sampleLaw K).l2_nonneg (fun x => D (fun c => T.pathAt (q c) x))
  apply (sq_le_sq₀ (abs_nonneg _) hd).mp
  rw [sq_abs,FiniteLaw.l2_sq,← he]
  exact hsq.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (g x))])

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype C] [DecidableEq C] in
/-- A shape specified by a complete labeled splitting matrix contains each
of the target's branching vertices, with its vertex multiplicity intact. -/
lemma branchingCount_of_matrix (T S : PrescribedTree L) (q : C → T.Leaf)
    (hq : Function.Surjective q) (pos : C → S.Leaf)
    (h : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  let e : SplitMap T S := {
    leaf := fun a => pos (Function.surjInv hq a)
    split := fun a b => (h _ _).trans
      (congrArg₂ (splitDepth T) (Function.surjInv_eq hq a) (Function.surjInv_eq hq b)) }
  exact e.branchingCount_le P

/-- Absolute projection-error cost for the ACTUAL exact-matrix history. This
is the charging step in the shifted-two-copy argument: take Q to be shifted
depths, so the old tree has no branching in Q. The exponent counts vertices,
not distinct depths, hence aligned copies are charged separately. -/
theorem prescribed_history_charging_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0)
    (W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (E : ℝ) (hE : 0 ≤ E)
    (hW : ∀ R pos g, (∀ x, |g x| ≤ 1) →
      (∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)) → |W R pos g| ≤ E)
    (cs : List C) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (f : Sample Ω S → ℝ) (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then W R pos g else 0) cs S U loc pos f| ≤
      E * (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
        cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  classical
  apply labeledHistory_charging_bound hL Q (branchingCount T (· ∈ Q)) _ E hE cs S
    U loc pos f hf hU
  intro R loc g hg
  by_cases h : ∀ a b, splitDepth R (loc a) (loc b) = splitDepth T (q a) (q b)
  · rw [ite_eq_left h]
    have hc := branchingCount_of_matrix T R q hq loc h (· ∈ Q)
    rw [hS,zero_add,ite_eq_left hc,mul_one]
    exact hW R loc g hg h
  · rw [ite_eq_right h,abs_zero]
    exact mul_nonneg hE (by split_ifs <;> norm_num)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TripleMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

omit [Fintype Ω] in
lemma labeledHistory_mul_left (m : Fin (n+1) → ℝ) (t : ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun S pos f => t * V S pos f) cs S U loc pos f =
      t * labeledHistory m V cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators Classical
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype Ω] [Fintype C] in
lemma labeledHistory_sub (m : Fin (L+1) → ℝ)
    (V W : (R : PrescribedTree L) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ)
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos g-W R pos g) cs S U loc pos f =
      labeledHistory m V cs S U loc pos f-labeledHistory m W cs S U loc pos f := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    simp only [labeledHistory,ih,mul_sub,Finset.sum_sub_distrib]
    ring

/-- The genuine signed history of an L2 projection error has the exact
small-L charging cost. The target error need only be small under its own
single-copy law; it may be correlated with every old path and old test. -/
theorem projection_history_cost (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (D : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*D (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => D (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  refine prescribed_history_charging_bound hL Q T S q hq hS _ _
    (FiniteLaw.l2_nonneg _ _) ?_ cs U loc pos f hf hU
  intro R pos g hg h
  exact matrix_weighted_error T R q hq pos h K D g hg

/-- Direct comparison of an actual target overlap with its projected
observable inside the full signed ordered extension sum. -/
theorem projection_history_difference (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Surjective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (A B : (C → FinitePath Ω L) → ℝ) (cs : List C) (U : Finset ι)
    (loc : ι → S.Leaf) (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hU : U.card ≤ leaves S) :
    |labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f -
     labeledHistory (grid L 0 L)
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f| ≤
      (T.sampleLaw K).l2 (fun x => A (fun c => T.pathAt (q c) x)-B (fun c => T.pathAt (q c) x)) *
        (chargeBound (2*(leaves S+cs.length:ℕ)) ((Q.card:ℝ)*(leaves S+cs.length:ℕ))
          cs.length (branchingCount T (· ∈ Q)) * (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))) := by
  rw [← labeledHistory_sub]
  have he : (fun (R : PrescribedTree L) (pos : C → R.Leaf) (g : Sample Ω R → ℝ) =>
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*A (fun c => R.pathAt (pos c) x)) else 0)-
      (if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*B (fun c => R.pathAt (pos c) x)) else 0)) =
      (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
        then (R.sampleLaw K).expect (fun x => g x*(A (fun c => R.pathAt (pos c) x)-
          B (fun c => R.pathAt (pos c) x))) else 0) := by
    funext R pos g
    split_ifs <;> simp only [sub_self,mul_sub,FiniteLaw.expect_sub]
  rw [he]
  exact projection_history_cost hL Q T S q hq hS K (fun x => A x-B x) cs U loc pos f hf hU

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
lemma expect_pi_three (P : (i : ι) → FiniteLaw (α i)) (i j k : ι)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j) (f : α i → α j → α k → ℝ) :
    (pi P).expect (fun x => f (x i) (x j) (x k)) =
      (P i).expect (fun x => (P j).expect (fun y => (P k).expect (f x y))) := by
  rw [expect_pi_split P i]
  apply expect_congr
  intro x
  simp only [Equiv.piSplitAt_symm_apply,dite_true,dite_eq_right hji,dite_eq_right hki]
  exact expect_pi_pair (fun t : {t // t ≠ i} => P t) ⟨j,hji⟩ ⟨k,hki⟩
    (fun he => hkj (congrArg Subtype.val he)) (f x)
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
lemma branch_leaf_marginal {n : ℕ} (C : PrescribedTree n) (μ : FiniteLaw Ω)
    (K : Ω → KernelTower Ω n) (a : C.Leaf) (F : FinitePath Ω (n+1) → ℝ) :
    (μ.bind (fun z => C.sampleLaw (K z))).expect
      (fun x => F (x.1,C.pathAt a x.2)) = (KernelTower.law (n+1) (μ,K)).expect F := by
  erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect n (μ,K)]
  exact μ.expect_congr (fun z => leaf_marginal C (K z) a (fun y => F (z,y)))

/-- Every uncontracted tree with three positional pairwise split depths equal
to d has the genuine three-copy conditional marginal. All other branches are
integrated out, irrespective of their number or depths. -/
theorem triple_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b c : S.Leaf) (d : ℕ) (hd : d < n)
    (hab : splitDepth S a b = d) (hac : splitDepth S a c = d)
    (hbc : splitDepth S b c = d)
    (F : FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => F (S.pathAt a x) (S.pathAt b x) (S.pathAt c x)) =
      KernelTower.tripleExpectAt n T d F := by
  induction S generalizing d with
  | leaf => omega
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    rcases c with ⟨l,c⟩
    cases d with
    | zero =>
      have hji : j ≠ i := by
        intro hj; subst j
        rw [splitDepth_same_child] at hab
        omega
      have hli : l ≠ i := by
        intro hl; subst l
        rw [splitDepth_same_child] at hac
        omega
      have hlj : l ≠ j := by
        intro hl; subst l
        rw [splitDepth_same_child] at hbc
        omega
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x j).1,(C j).pathAt b (x j).2)
          ((x l).1,(C l).pathAt c (x l).2)) = _
      refine (FiniteLaw.expect_pi_three
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i j l hji hli hlj
        (fun x y z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2)
          (z.1,(C l).pathAt c z.2))).trans ?_
      change _ = (KernelTower.law (n+1) (μ,K)).expect (fun x =>
        (KernelTower.law (n+1) (μ,K)).expect (fun y =>
          (KernelTower.law (n+1) (μ,K)).expect (F x y)))
      calc
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (μ.bind (fun z => sampleLaw (C j) (K z))).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z =>
              F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z))) := by
          apply FiniteLaw.expect_congr; intro x
          apply FiniteLaw.expect_congr; intro y
          exact branch_leaf_marginal (C l) μ K c
            (fun z => F (x.1,(C i).pathAt a x.2) (y.1,(C j).pathAt b y.2) z)
        _ = (μ.bind (fun z => sampleLaw (C i) (K z))).expect (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))) := by
          apply FiniteLaw.expect_congr; intro x
          exact branch_leaf_marginal (C j) μ K b (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (fun z => F (x.1,(C i).pathAt a x.2) y z))
        _ = _ := branch_leaf_marginal (C i) μ K a (fun x =>
          (KernelTower.law (n+1) (μ,K)).expect (fun y =>
            (KernelTower.law (n+1) (μ,K)).expect (F x y)))
    | succ d =>
      have hji : j = i := by
        by_contra hj
        rw [splitDepth_diff_child C i j (Ne.symm hj)] at hab
        omega
      have hli : l = i := by
        by_contra hl
        rw [splitDepth_diff_child C i l (Ne.symm hl)] at hac
        omega
      subst j; subst l
      rw [splitDepth_same_child] at hab hac hbc
      change (FiniteLaw.pi (fun t => μ.bind (fun z => sampleLaw (C t) (K z)))).expect
        (fun x => F ((x i).1,(C i).pathAt a (x i).2) ((x i).1,(C i).pathAt b (x i).2)
          ((x i).1,(C i).pathAt c (x i).2)) = _
      refine (FiniteLaw.expect_pi_marginal
        (fun t => μ.bind (fun z => sampleLaw (C t) (K z))) i
        (fun x => F (x.1,(C i).pathAt a x.2) (x.1,(C i).pathAt b x.2)
          (x.1,(C i).pathAt c x.2))).trans ?_
      rw [FiniteLaw.expect_bind]
      exact μ.expect_congr (fun z => ih i (K z) a b c d (by omega) (by omega) (by omega)
        (by omega) (fun x y w => F (z,x) (z,y) (z,w)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryDistinct
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

lemma HistoryValid.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryValid S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (h.disjoint i hi b hb hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (h.disjoint i hi a ha hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb hab
  · intro j hj a ha
    rcases Finset.mem_erase.mp hj with ⟨hji,hj⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (fun e => hji (h.loc_inj e))
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simpa only [Function.update_of_ne hac] using h.disjoint j hj a ha

omit [DecidableEq ι] in
lemma HistoryValid.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryValid S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryValid (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨(oldLeaf_injective S v).comp h.loc_inj,?_,?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; rfl
    · subst a
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_self,Function.update_of_ne hbc] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos b) hab)
    · subst b
      have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_self,Function.update_of_ne hac] at hab
      exact False.elim (newLeaf_ne_oldLeaf S v (pos a) hab.symm)
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      have hbc : b ≠ c := fun e => hc (e ▸ hb)
      simp only [Function.update_of_ne hac,Function.update_of_ne hbc] at hab
      exact h.pos_inj ha hb (oldLeaf_injective S v hab)
  · intro i hi a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simpa only [Function.update_self] using (newLeaf_ne_oldLeaf S v (loc i)).symm
    · have hac : a ≠ c := fun e => hc (e ▸ ha)
      simp only [Function.update_of_ne hac]
      exact fun e => h.disjoint i hi a ha (oldLeaf_injective S v e)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProfileHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ} {C ι : Type} [DecidableEq C] [DecidableEq ι]

/-- Growth adds exactly one new positional leaf, not just one spin value. -/
theorem grow_leaf_cases (S : PrescribedTree n) (v : S.Internal) (b : (grow S v).Leaf) :
    b = newLeaf S v ∨ ∃ a, b = oldLeaf S v a := by
  classical
  let F : Option S.Leaf → (grow S v).Leaf := Option.elim' (newLeaf S v) (oldLeaf S v)
  have hinj : Function.Injective F := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h)
    · exact False.elim (newLeaf_ne_oldLeaf S v _ h.symm)
    · exact congrArg some (oldLeaf_injective S v h)
  have hcard : Fintype.card (Option S.Leaf) = Fintype.card (grow S v).Leaf := by
    simp only [Fintype.card_option,card_leaf,leaves_grow]
  have hs := ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj,hcard⟩).2
  obtain ⟨a,rfl⟩ := hs b
  cases a with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a,rfl⟩

lemma HistoryCover.pick_old {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) {i : ι} (hi : i ∈ U) :
    HistoryCover S (U.erase i) loc (insert c P) (Function.update pos c (loc i)) := by
  refine ⟨h.toHistoryValid.pick_old hc hi,?_⟩
  intro b
  rcases h.cover b with ⟨j,hj,rfl⟩ | ⟨d,hd,rfl⟩
  · by_cases hji : j = i
    · subst j
      exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
    · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,rfl⟩
  · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
    simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

omit [DecidableEq ι] in
lemma HistoryCover.pick_fresh {S : PrescribedTree n} {U : Finset ι} {loc : ι → S.Leaf}
    {P : Finset C} {pos : C → S.Leaf} (h : HistoryCover S U loc P pos)
    {c : C} (hc : c ∉ P) (v : S.Internal) :
    HistoryCover (grow S v) U (fun i => oldLeaf S v (loc i)) (insert c P)
      (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v)) := by
  refine ⟨h.toHistoryValid.pick_fresh hc v,?_⟩
  intro b
  rcases grow_leaf_cases S v b with rfl | ⟨a,rfl⟩
  · exact Or.inr ⟨c,Finset.mem_insert_self _ _,by simp only [Function.update_self]⟩
  · rcases h.cover a with ⟨i,hi,rfl⟩ | ⟨d,hd,rfl⟩
    · exact Or.inl ⟨i,hi,rfl⟩
    · refine Or.inr ⟨d,Finset.mem_insert_of_mem hd,?_⟩
      simp only [Function.update_of_ne (fun he : d = c => hc (he ▸ hd))]

omit [DecidableEq C] [DecidableEq ι] in
/-- Available-old sums equal unrestricted old-leaf sums for any observable
that vanishes on the protected references. No probability calculation occurs. -/
lemma HistoryCover.sum_available {S : PrescribedTree n} {U : Finset ι}
    {loc : ι → S.Leaf} {P : Finset C} {pos : C → S.Leaf}
    (h : HistoryCover S U loc P pos) (F : S.Leaf → ℝ)
    (hF : ∀ c ∈ P, F (pos c) = 0) :
    (∑ i ∈ U, F (loc i)) = ∑ b : S.Leaf, F b := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => h.loc_inj hij)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  rcases h.cover b with ⟨i,hi,rfl⟩ | ⟨c,hc,rfl⟩
  · exact False.elim (hb (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
  · exact hF c hc

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixHistoryDecidable_re47a78_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma matrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    matrixHistory T q K m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, matrixHistory T q K m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : matrixHistory T q K m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem matrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (K : KernelTower Ω n) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    matrixHistory T q K m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * matrixHistory T q K m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) else 0 := by
  have hc' : c ∉ cs := fun h => hdis c h (Finset.mem_insert_self _ _)
  have hd' : ∀ d ∈ P, d ∉ cs := fun d hd h => hdis d h (Finset.mem_insert_of_mem hd)
  change (_ + _) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      apply matrixHistory_mismatch T q K m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : matrixHistory T q K m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [matrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply matrixHistory_mismatch T q K m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance kappaRegularDecidable_re47a78_1 (p : Prop) : Decidable p :=
  Classical.propDecidable p
lemma branchProduct_ne_zero {x y : ℝ} (hxy : x < y) (hy : 0 ≤ y) (k : ℕ) :
    branchProduct x y k ≠ 0 := by
  unfold branchProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply ne_of_lt
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hmul := mul_nonneg hj hy
  nlinarith

theorem partialKappa_ne_zero {n : ℕ} (S : PrescribedTree n)
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (P : Finset S.Leaf) :
    partialKappa S m P ≠ 0 := by
  induction S with
  | leaf => exact one_ne_zero
  | @node n k C ih =>
    apply mul_ne_zero
    · exact branchProduct_ne_zero (hm (by simp : (0 : Fin (n+1+1)) < 1)) (hp 1) _
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => ih i _
        (fun a b h => hm (Fin.succ_lt_succ_iff.mpr h)) (fun j => hp j.succ) _)

variable {n : ℕ} {C ι : Type} [Fintype C] [DecidableEq C] [DecidableEq ι]

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.kappaRegularLeafDecidableEq
omit [DecidableEq ι] in
/-- The actual one-step protected extension total is the ratio of the two
unordered branching products. Complete split constraints, not a surrogate
probability mechanism, determine this coefficient. -/
theorem matrix_choice_kappa (T S : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (P : Finset C) (hP : P.Nonempty)
    (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (U : Finset ι) (loc : ι → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (m : Fin (n+1) → ℝ) (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) :
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then (1:ℝ) else 0) +
    (∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v else 0) =
    partialKappa T m ((insert c P).image q) / partialKappa T m (P.image q) := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image P (fun a => splitDepth T (q c) (q a)) hP
  let r : P → S.Leaf := fun a => pos a
  let s : P → T.Leaf := fun a => q a
  have himage : Finset.univ.image s = P.image q := by
    ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨b,hb⟩
      exact ⟨b,b.property,hb⟩
    · rintro ⟨b,hb,he⟩
      exact ⟨⟨b,hb⟩,he⟩
  have hqa : q c ≠ q a := fun h => hc (hq h ▸ ha)
  have hn : q c ∉ P.image q := by
    rintro h
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp h
    exact hc (hq he ▸ hd)
  have he := labeled_choice_total S T r s (q c) ⟨a,ha⟩
    (fun a b => hsplit a a.property b b.property) hqa (fun b => hmax b b.property) m hend
  have ho (b : S.Leaf) : labeledOldMatch S T r s (q c) b ↔
      ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledOldMatch,r,s,Subtype.forall]
  have hf (v : S.Internal) : labeledFreshMatch S T r s (q c) v ↔
      ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d) := by
    simp only [labeledFreshMatch,r,s,Subtype.forall]
  simp_rw [ho,hf] at he
  have hav := hcover.sum_available
    (fun b => if ∀ d ∈ P, splitDepth S b (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0)
    (by
      intro d hd
      apply ite_eq_right
      intro h
      have hh := h d hd
      rw [splitDepth_self] at hh
      exact hc (hq ((splitDepth_eq_height T (q c) (q d)).mp hh.symm) ▸ hd))
  rw [hav,he]
  have hk := partialKappa_insert T m (P.image q) (q a) (q c)
    (Finset.mem_image.mpr ⟨a,ha,rfl⟩) hn
    (by rintro t ht; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ht; exact hmax d hd)
  rw [Finset.image_insert,hk]
  rw [mul_div_cancel_right₀ _ (partialKappa_ne_zero T m hm hp _)]
  simp only [himage,s]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GlobalSelectedAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairObservableHistoryDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pair_univ_erase (S : PrescribedTree n) (a : S.Leaf) (d : ℕ) (hd : d < n) :
    (∑ b ∈ Finset.univ.erase a, if splitDepth S a b = d then (1:ℝ) else 0) =
      ∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0 := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset S.Leaf)
    (fun b => if splitDepth S a b = d then (1:ℝ) else 0) (Finset.mem_univ a)
  simpa only [splitDepth_self,ite_eq_right (Ne.symm (Nat.ne_of_lt hd)),add_zero] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance pairSquareDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma pairFreshCost_nonneg (S : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (a : S.Leaf) (d : ℕ) (v : S.Internal) :
    0 ≤ pairFreshCost S m a d v := by
  unfold pairFreshCost
  split_ifs
  · exact neg_nonneg.mpr (gamma_nonpos S m hm hp v)
  · rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

/-- Measurability of every finite prescribed-tree probability for the actual
recursively tilted conditional kernels. -/
theorem measurable_tilt_sample_weight {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (a : S.Sample Ω) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).weight a) := by
  induction S with
  | leaf => exact measurable_const
  | @node n k C ih =>
    change Measurable (fun x => ∏ i : Fin k,
      (T.1.tilt (m 0) (fun z => KernelTower.backwardLog n (T.2 z)
        (fun j => m j.succ) (fun y => f x (z,y)))).weight (a i).1 *
      ((C i).sampleLaw (KernelTower.tilt n (T.2 (a i).1)
        (fun j => m j.succ) (fun y => f x ((a i).1,y)))).weight (a i).2)
    apply Finset.measurable_prod
    intro i _
    exact (T.1.measurable_tilt_weight (m 0)
      (fun z => KernelTower.measurable_backwardLog n (T.2 z) (fun j => m j.succ)
        (fun y => hf (z,y))) (a i).1).mul
      (ih i (T.2 (a i).1) (fun j => m j.succ) (fun y => hf ((a i).1,y)) (a i).2)

theorem measurable_tilt_sample_expect {n : ℕ} (S : PrescribedTree n)
    (T : KernelTower Ω n) (m : Fin n → ℝ) {f : X → FinitePath Ω n → ℝ}
    {g : X → S.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun x => f x y)) (hg : ∀ a, Measurable (fun x => g x a)) :
    Measurable (fun x => (S.sampleLaw (KernelTower.tilt n T m (f x))).expect (g x)) := by
  apply Finset.measurable_sum
  intro a _
  exact (measurable_tilt_sample_weight S T m hf a).mul (hg a)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralPairSquare
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance generalPairSquareDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- The exact nonnegative-square identity before root averaging. It follows
from actual two-path marginals and complete old-law projectivity. -/
theorem pair_square_identity_general (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a b : S.Leaf)
    (d : ℕ) (hd : d < n) (hsplit : splitDepth S a b = d)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      R (S.pathAt a x) (S.pathAt c x) = R (S.pathAt a x) (S.pathAt b x)) :
    (1/2:ℝ) * ∑ v : S.Internal, pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x =>
        (R (S.pathAt a (oldSample S v x)) (S.pathAt b (oldSample S v x)) -
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))^2) =
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x => R (S.pathAt a x) (S.pathAt b x)^2) +
      pairObservableHistory T m S a d R (fun x => R (S.pathAt a x) (S.pathAt b x)) := by
  classical
  let X := fun x : Sample Ω S => R (S.pathAt a x) (S.pathAt b x)
  let Y := fun (v : S.Internal) (x : Sample Ω (grow S v)) =>
    R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)
  let A := (S.sampleLaw T).expect (fun x => X x^2)
  let Q := fun v : S.Internal => ((grow S v).sampleLaw T).expect
    (fun x => X (oldSample S v x)*Y v x)
  let e := m ⟨d,by omega⟩-m ⟨d+1,by omega⟩
  let q : ℝ := ∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
    if splitDepth S a c = d then 1 else 0
  have hsum : (∑ v : S.Internal, pairFreshCost S m a d v) = q-e := by
    have hh := pair_choice_total S a d hd m hend
    rw [← pair_univ_erase S a d hd] at hh
    have hn (v : S.Internal) : pairFreshCost S m a d v =
        -(if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then gamma S m v else 0) := by
      unfold pairFreshCost; split_ifs <;> simp
    simp_rw [hn,Finset.sum_neg_distrib]
    dsimp only [e]
    linarith
  have hsq (v : S.Internal)
      (hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d) :
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
        2*A-2*Q v := by
    have hy : ((grow S v).sampleLaw T).expect (fun x => Y v x^2) = A := by
      exact pair_marginal_eq (grow S v) S T (oldLeaf S v a) (newLeaf S v) a b
        (hv.trans hsplit.symm) (fun x y => R x y^2)
    calc
      _ = ((grow S v).sampleLaw T).expect (fun x =>
        X (oldSample S v x)^2 - 2*(X (oldSample S v x)*Y v x) + Y v x^2) :=
          FiniteLaw.expect_congr _ (fun _ => by ring)
      _ = _ := by
        rw [FiniteLaw.expect_add,FiniteLaw.expect_sub,FiniteLaw.expect_mul_left,
          grow_projectivity S T v (fun x => X x^2),hy]
        change A-2*Q v+A = 2*A-2*Q v
        ring
  have hterm (v : S.Internal) : pairFreshCost S m a d v *
      ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2) =
      2*(pairFreshCost S m a d v*A) - 2*(pairFreshCost S m a d v*Q v) := by
    by_cases hv : splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d
    · rw [hsq v hv]; ring
    · simp only [pairFreshCost,hv,ite_false,zero_mul,mul_zero,sub_zero]
  have hhist : pairObservableHistory T m S a d R X = q*A - ∑ v : S.Internal,
      pairFreshCost S m a d v*Q v := by
    unfold pairObservableHistory
    have ha : (∑ c ∈ (Finset.univ : Finset S.Leaf).erase a,
        if splitDepth S a c = d then (S.sampleLaw T).expect
          (fun x => X x * R (S.pathAt a x) (S.pathAt c x)) else 0) = q*A := by
      dsimp only [q]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs with hs
      · rw [one_mul]
        apply FiniteLaw.expect_congr
        intro x
        rw [hOld c hs x]
        change X x * X x = X x^2
        ring
      · simp
    rw [ha,sub_eq_add_neg,← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    unfold pairFreshCost
    split_ifs
    · change gamma S m v * Q v = -(-gamma S m v * Q v)
      ring
    · simp
  have hminus : m ⟨d+1,by omega⟩ - m ⟨d,by omega⟩ = -e := by dsimp [e]; ring
  rw [hminus]
  change (1/2:ℝ)*(∑ v, pairFreshCost S m a d v *
    ((grow S v).sampleLaw T).expect (fun x => (X (oldSample S v x)-Y v x)^2)) =
    (-e)*A+pairObservableHistory T m S a d R X
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,hsum,hhist]
  ring


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixNormalization
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixNormalizationDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype C] in
lemma splitOn_pick_old (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (x : S.Leaf)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hx : ∀ a ∈ P, splitDepth S x (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth S (Function.update pos c x a) (Function.update pos c x b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hx b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha))] using hx a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb))] using hsplit a ha b hb

omit [Fintype C] in
lemma splitOn_pick_fresh (T S : PrescribedTree n) (q : C → T.Leaf)
    (P : Finset C) (c : C) (hc : c ∉ P) (pos : C → S.Leaf) (v : S.Internal)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (hv : ∀ a ∈ P, freshSplitDepth S v (pos a) = splitDepth T (q c) (q a)) :
    ∀ a ∈ insert c P, ∀ b ∈ insert c P,
      splitDepth (grow S v)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) a)
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v) b) =
        splitDepth T (q a) (q b) := by
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with hac | ha <;> rcases Finset.mem_insert.mp hb with hbc | hb
  · subst a; subst b
    simp only [splitDepth_self]
  · subst a
    simpa only [Function.update_self,Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),
      splitDepth_new_old] using hv b hb
  · subst b
    rw [splitDepth_symm,splitDepth_symm T (q a)]
    simpa only [Function.update_self,Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      splitDepth_new_old] using hv a ha
  · simpa only [Function.update_of_ne (fun he : a = c => hc (he ▸ ha)),
      Function.update_of_ne (fun he : b = c => hc (he ▸ hb)),splitDepth_old_old] using hsplit a ha b hb

/-- Exact normalization of the ACTUAL complete-matrix protected history,
retaining an arbitrary old test. This bridges the analytic history to the
unordered kappa product, without assuming a reference-history identity. -/
theorem matrixHistory_normalization (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    matrixHistory T q K m cs S U loc pos f =
      (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
        (S.sampleLaw K).expect f := by
  classical
  induction cs generalizing P S U with
  | nil =>
    have he : P = Finset.univ := by simpa using hfull
    have hall : ∀ a b, splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b) := by
      intro a b
      apply hsplit a (by simp [he]) b (by simp [he])
    simp only [matrixHistory,labeledHistory,ite_eq_left hall,he,
      div_self (partialKappa_ne_zero T m hm hp _),one_mul]
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hcs' := (List.nodup_cons.mp hcs).2
    have hdis' : ∀ d ∈ cs, d ∉ insert c P := by
      intro d hd hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact (List.nodup_cons.mp hcs).1 hd
      · exact hdis d (by simp [hd]) hh
    have hfull' : insert c P ∪ cs.toFinset = Finset.univ := by
      simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hfull
    let A := partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c P).image q)
    have ho (i : ι) (hi : i ∈ U) :
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d) then (1:ℝ) else 0) *
          (A * (S.sampleLaw K).expect f) := by
      split_ifs with hx
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' S (U.erase i) loc _
          (hcover.pick_old hc hi) (splitOn_pick_old T S q P c hc pos (loc i) hsplit hx) f]
        exact (one_mul _).symm
      · simp only [zero_mul]
    have hfresh (v : S.Internal) :
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v * matrixHistory T q K m cs (grow S v) U
            (fun i => oldLeaf S v (loc i))
            (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
            (fun x => f (oldSample S v x)) else 0) =
        (if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
          then gamma S m v else 0) * (A * (S.sampleLaw K).expect f) := by
      split_ifs with hv
      · rw [ih hcs' (insert c P) (Finset.insert_nonempty _ _) hdis' hfull' (grow S v) U _ _
          (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc pos v hsplit hv) _,grow_projectivity]
      · simp only [zero_mul]
    rw [matrixHistory_step T q K m c cs P hc hdis']
    have hh : (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then matrixHistory T q K m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) =
        ∑ i ∈ U, (if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
          then (1:ℝ) else 0) * (A * (S.sampleLaw K).expect f) := Finset.sum_congr rfl ho
    rw [hh]
    simp_rw [hfresh]
    rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,
      matrix_choice_kappa T S q hq P hP c hc pos U loc hcover hsplit m hm hp hend]
    dsimp only [A]
    rw [← mul_assoc, div_mul_div_cancel₀'
      (partialKappa_ne_zero T m hm hp ((insert c P).image q))]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [Fintype C] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance weightedMatrixHistoryDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] in
/-- Once two assigned colors have the wrong split, no future legal extension
can repair it. This justifies enforcing the matrix constraints successively. -/
lemma weightedMatrixHistory_mismatch (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (cs : List C)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ)
    (a b : C) (ha : a ∉ cs) (hb : b ∉ cs)
    (he : splitDepth S (pos a) (pos b) ≠ splitDepth T (q a) (q b)) :
    weightedMatrixHistory T q V m cs S U loc pos f = 0 := by
  induction cs generalizing S U with
  | nil =>
    exact ite_eq_right (fun h => he (h a b))
  | cons c cs ih =>
    have hac : a ≠ c := fun h => ha (by simp [h])
    have hbc : b ≠ c := fun h => hb (by simp [h])
    have ha' : a ∉ cs := fun h => ha (by simp [h])
    have hb' : b ∉ cs := fun h => hb (by simp [h])
    change (∑ i ∈ U, weightedMatrixHistory T q V m cs S (U.erase i) loc
      (Function.update pos c (loc i)) f) +
      ∑ v : S.Internal, gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0
    have ho (i : ι) : weightedMatrixHistory T q V m cs S (U.erase i) loc
        (Function.update pos c (loc i)) f = 0 := by
      apply ih S (U.erase i) loc _ f ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc] using he
    have hfresh (v : S.Internal) : weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) = 0 := by
      apply ih (grow S v) U _ _ _ ha' hb'
      simpa only [Function.update_of_ne hac,Function.update_of_ne hbc,splitDepth_old_old] using he
    simp only [ho,hfresh,mul_zero,Finset.sum_const_zero,add_zero]

omit [Fintype Ω] in
/-- Exact sequential enforcement of the full split matrix inside the
protected signed history. Impossible branches vanish, rather than being
silently dropped or replaced by a reference law. -/
theorem weightedMatrixHistory_step (T : PrescribedTree n) (q : C → T.Leaf)
    (V : (R : PrescribedTree n) → (C → R.Leaf) → (Sample Ω R → ℝ) → ℝ) (m : Fin (n+1) → ℝ) (c : C) (cs : List C)
    (P : Finset C) (hc : c ∉ P) (hdis : ∀ d ∈ cs, d ∉ insert c P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q V m (c::cs) S U loc pos f =
    (∑ i ∈ U, if ∀ d ∈ P, splitDepth S (loc i) (pos d) = splitDepth T (q c) (q d)
      then weightedMatrixHistory T q V m cs S (U.erase i) loc (Function.update pos c (loc i)) f else 0) +
    ∑ v : S.Internal, if ∀ d ∈ P, freshSplitDepth S v (pos d) = splitDepth T (q c) (q d)
      then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) U
        (fun i => oldLeaf S v (loc i))
        (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
        (fun x => f (oldSample S v x)) else 0 := by
  have hc' : c ∉ cs := fun h => hdis c h (Finset.mem_insert_self _ _)
  have hd' : ∀ d ∈ P, d ∉ cs := fun d hd h => hdis d h (Finset.mem_insert_of_mem hd)
  change (_ + _) = _
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      apply weightedMatrixHistory_mismatch T q V m cs S (U.erase i) loc _ f c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd))] using he
  · apply Finset.sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · push Not at h
      obtain ⟨d,hd,he⟩ := h
      suffices hh : weightedMatrixHistory T q V m cs (grow S v) U
          (fun i => oldLeaf S v (loc i))
          (Function.update (fun d => oldLeaf S v (pos d)) c (newLeaf S v))
          (fun x => f (oldSample S v x)) = 0 by
        simpa only [weightedMatrixHistory,mul_zero] using congrArg (gamma S m v * ·) hh
      apply weightedMatrixHistory_mismatch T q V m cs (grow S v) U _ _ _ c d hc' (hd' d hd)
      simpa only [Function.update_self,Function.update_of_ne (fun e : d = c => hc (e ▸ hd)),
        splitDepth_new_old] using he

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HistoryRetained
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

omit [Fintype Ω] in
/-- A function of protected paths is transported jointly with the full old
test through EVERY fresh extension. This is an identity of signed histories. -/
theorem labeledHistory_protected_function (m : Fin (n+1) → ℝ)
    (V : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (P : Finset C) (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (cs : List C) (hdis : ∀ c ∈ cs, c ∉ P)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => V R pos (fun x => g x * G (fun c => R.pathAt (pos c) x)))
      cs S U loc pos f =
    labeledHistory m V cs S U loc pos (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  induction cs generalizing S U with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ∉ P := hdis c (by simp)
    have hdis' : ∀ d ∈ cs, d ∉ P := fun d hd => hdis d (by simp [hd])
    simp only [labeledHistory]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd))]
    · apply Finset.sum_congr rfl
      intro v _
      congr 1
      rw [ih hdis']
      congr 1
      funext x
      congr 1
      apply hG
      intro d hd
      rw [Function.update_of_ne (fun h : d = c => hc (h ▸ hd)),pathAt_oldLeaf]

variable [Fintype C]

noncomputable local instance historyRetainedPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
/-- Complete-matrix normalization WITH any observable of the already assigned
paths. Its joint dependence on the old test and the original samples is kept. -/
theorem matrixHistory_retained (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (cs : List C) (hcs : cs.Nodup) (P : Finset C) (hP : P.Nonempty)
    (hdis : ∀ c ∈ cs, c ∉ P) (hfull : P ∪ cs.toFinset = Finset.univ)
    (G : (C → FinitePath Ω n) → ℝ)
    (hG : ∀ x y, (∀ c ∈ P, x c = y c) → G x = G y)
    (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf)
    (hcover : HistoryCover S U loc P pos)
    (hsplit : ∀ a ∈ P, ∀ b ∈ P,
      splitDepth S (pos a) (pos b) = splitDepth T (q a) (q b))
    (f : Sample Ω S → ℝ) :
    labeledHistory m (fun R pos g => if ∀ a b,
      splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect (fun x => g x*G (fun c => R.pathAt (pos c) x)) else 0)
      cs S U loc pos f =
    (partialKappa T m (Finset.univ.image q) / partialKappa T m (P.image q)) *
      (S.sampleLaw K).expect (fun x => f x*G (fun c => S.pathAt (pos c) x)) := by
  rw [labeledHistory_protected_function m
    (fun R pos g => if ∀ a b, splitDepth R (pos a) (pos b) = splitDepth T (q a) (q b)
      then (R.sampleLaw K).expect g else 0) P G hG cs hdis]
  exact matrixHistory_normalization T q hq K m hm hp hend cs hcs P hP hdis hfull
    S U loc pos hcover hsplit _

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixPair
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

noncomputable local instance matrixPairPropDecidable_re47a78_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype C] [DecidableEq C] in
lemma singleton_history_cover (S : PrescribedTree n) (x : S.Leaf) (a : C) :
    HistoryCover S (Finset.univ.erase x) id ({a} : Finset C) (fun _ => x) := by
  classical
  refine ⟨⟨Function.injective_id,?_,?_⟩,?_⟩
  · intro c hc d hd _
    simp only [Finset.mem_coe,Finset.mem_singleton] at hc hd
    exact hc.trans hd.symm
  · intro y hy c _
    exact (Finset.mem_erase.mp hy).1
  · intro y
    by_cases h : y = x
    · exact Or.inr ⟨a,by simp,h⟩
    · exact Or.inl ⟨y,by simp [h],rfl⟩

/-- The actual full prescribed split-matrix history, retaining just the anchor
and the first newly assigned path, is its exact kappa ratio times the literal
one-color pair history. All unused old replicas and their joint test remain.
This is not a reference-history assumption. -/
theorem matrixHistory_first_pair (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect
        (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f =
    (partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)) *
      pairObservableHistory K m S x (splitDepth T (q a) (q c)) R f := by
  classical
  let P : Finset C := {a}
  have hc : c ∉ P := by simpa only [P,Finset.mem_singleton] using hac.symm
  have hcover := singleton_history_cover S x a
  have hsplit : ∀ b ∈ P, ∀ d ∈ P,
      splitDepth S ((fun _ : C => x) b) ((fun _ : C => x) d) = splitDepth T (q b) (q d) := by
    intro b hb d hd
    have hb' : b = a := Finset.mem_singleton.mp hb
    have hd' : d = a := Finset.mem_singleton.mp hd
    subst b; subst d
    simp only [splitDepth_self]
  let G : (C → FinitePath Ω n) → ℝ := fun y => R (y a) (y c)
  have hG : ∀ y z, (∀ b ∈ insert c P, y b = z b) → G y = G z := by
    intro y z h
    dsimp only [G]
    rw [h a (by simp [P]),h c (by simp)]
  let A := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c P).image q)
  let V := fun (D : PrescribedTree n) (pos : C → D.Leaf) (g : Sample Ω D → ℝ) =>
    (D.sampleLaw K).expect (fun z => g z * R (D.pathAt (pos a) z) (D.pathAt (pos c) z))
  have old (y : S.Leaf) (hy : y ∈ Finset.univ.erase x)
      (hs : splitDepth S x y = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
        (Function.update (fun _ => x) c y) f =
      A * (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) := by
    have hs' : ∀ b ∈ P, splitDepth S (id y) ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG S ((Finset.univ.erase x).erase y) id _
      (hcover.pick_old hc hy) (splitOn_pick_old T S q P c hc _ y hsplit hs') f
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  have fresh (v : S.Internal)
      (hs : splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)) :
      weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
        (fun y => oldLeaf S v (id y))
        (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
        (fun z => f (oldSample S v z)) =
      A * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
        R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) := by
    have hs' : ∀ b ∈ P, freshSplitDepth S v ((fun _ : C => x) b) = splitDepth T (q c) (q b) := by
      intro b hb
      have hb' : b = a := Finset.mem_singleton.mp hb
      subst b
      simpa only [splitDepth_symm (grow S v) (oldLeaf S v x),splitDepth_new_old,
        splitDepth_symm T (q a) (q c)] using hs
    have h := matrixHistory_retained T q hq K m hm hp hend cs hcs (insert c P)
      (Finset.insert_nonempty _ _) hdis hfull G hG (grow S v) (Finset.univ.erase x) _ _
      (hcover.pick_fresh hc v) (splitOn_pick_fresh T S q P c hc _ v hsplit hs')
      (fun z => f (oldSample S v z))
    simpa only [weightedMatrixHistory,V,G,A,id_eq,Function.update_self,Function.update_of_ne hac] using h
  change weightedMatrixHistory T q V m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f = _
  rw [weightedMatrixHistory_step T q V m c cs P hc hdis]
  have ho (y : S.Leaf) (hy : y ∈ Finset.univ.erase x) :
      (if ∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then weightedMatrixHistory T q V m cs S ((Finset.univ.erase x).erase y) id
          (Function.update (fun _ => x) c (id y)) f else 0) =
      A * (if splitDepth S x y = splitDepth T (q a) (q c)
        then (S.sampleLaw K).expect (fun z => f z * R (S.pathAt x z) (S.pathAt y z)) else 0) := by
    have he : (∀ d ∈ P, splitDepth S (id y) ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth S x y = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,id_eq,splitDepth_symm S y x,splitDepth_symm T (q c) (q a)]
    simp only [he]
    split_ifs with hs
    · exact old y hy hs
    · exact (mul_zero A).symm
  have hv (v : S.Internal) :
      (if ∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)
        then gamma S m v * weightedMatrixHistory T q V m cs (grow S v) (Finset.univ.erase x)
          (fun y => oldLeaf S v (id y))
          (Function.update (fun _ => oldLeaf S v x) c (newLeaf S v))
          (fun z => f (oldSample S v z)) else 0) =
      A * (if splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c)
        then gamma S m v * ((grow S v).sampleLaw K).expect (fun z => f (oldSample S v z) *
          R ((grow S v).pathAt (oldLeaf S v x) z) ((grow S v).pathAt (newLeaf S v) z)) else 0) := by
    have he : (∀ d ∈ P, freshSplitDepth S v ((fun _ : C => x) d) = splitDepth T (q c) (q d)) ↔
        splitDepth (grow S v) (oldLeaf S v x) (newLeaf S v) = splitDepth T (q a) (q c) := by
      simp only [P,Finset.mem_singleton,forall_eq,splitDepth_symm (grow S v) (oldLeaf S v x),
        splitDepth_new_old,splitDepth_symm T (q a) (q c)]
    simp only [he]
    split_ifs with hs
    · rw [fresh v hs]; ring
    · exact (mul_zero A).symm
  have he := Finset.sum_congr rfl ho
  rw [he]
  simp_rw [hv]
  rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add]
  rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω]
lemma abs_expect_mul_le_l2 (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (hg : ∀ x, |g x| ≤ 1) : |P.expect (fun x => f x*g x)| ≤ P.l2 f := by
  have hs := P.expect_mul_sq_le f g
  have hg2 : P.expect (fun x => g x^2) ≤ 1 := by
    calc
      _ ≤ P.expect (fun _ => 1) := P.expect_mono (fun x => by
        simpa using (sq_le_sq.mpr (show |g x| ≤ |(1:ℝ)| by simpa using hg x)))
      _ = _ := P.expect_const 1
  apply (sq_le_sq₀ (abs_nonneg _) (P.l2_nonneg _)).mp
  rw [sq_abs,l2_sq]
  exact hs.trans (by nlinarith [P.expect_nonneg (fun x => sq_nonneg (f x))])
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

noncomputable local instance singletonRootPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma grow_l2 (S : PrescribedTree n) (v : S.Internal) (K : KernelTower Ω n)
    (f : Sample Ω S → ℝ) :
    ((grow S v).sampleLaw K).l2 (fun x => f (oldSample S v x)) = (S.sampleLaw K).l2 f := by
  unfold FiniteLaw.l2
  exact congrArg Real.sqrt (grow_projectivity S K v (fun x => f x^2))

lemma pairObservableHistory_sub_test (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f g : Sample Ω S → ℝ) :
    pairObservableHistory K m S a d R (fun x => f x-g x) =
      pairObservableHistory K m S a d R f-pairObservableHistory K m S a d R g := by
  unfold pairObservableHistory
  simp only [sub_mul,FiniteLaw.expect_sub,mul_sub]
  have p (b : S.Leaf) :
      (if splitDepth S a b = d then
        (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) -
        (S.sampleLaw K).expect (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) =
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0) -
      (if splitDepth S a b = d then (S.sampleLaw K).expect
        (fun x => g x*R (S.pathAt a x) (S.pathAt b x)) else 0) := by split_ifs <;> ring
  have q (v : S.Internal) :
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x))-
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) =
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0)-
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => g (oldSample S v x)*R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) := by split_ifs <;> ring
  simp_rw [p,q]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Changing the old test has its original L2 cost, not a sup norm cost; fresh
branches preserve its entire old marginal. -/
theorem pairObservableHistory_l2 (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ)
    (hR : ∀ x y, |R x y| ≤ 1) :
    |pairObservableHistory K m S a d R f| ≤ pairHistoryMass S m a*(S.sampleLaw K).l2 f := by
  let B := (S.sampleLaw K).l2 f
  have hB : 0 ≤ B := FiniteLaw.l2_nonneg _ _
  unfold pairObservableHistory pairHistoryMass
  calc
    _ ≤ (∑ b ∈ (Finset.univ : Finset S.Leaf).erase a,
      |if splitDepth S a b = d then (S.sampleLaw K).expect (fun x => f x*R (S.pathAt a x) (S.pathAt b x)) else 0|) +
      ∑ v : S.Internal, |if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw K).expect (fun x => f (oldSample S v x)*
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ (∑ _b ∈ (Finset.univ : Finset S.Leaf).erase a, B) + ∑ v : S.Internal, |gamma S m v| * B := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro b _
        split_ifs
        · exact FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)
        · simpa using hB
      · apply Finset.sum_le_sum; intro v _
        split_ifs
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact (FiniteLaw.abs_expect_mul_le_l2 _ _ _ (fun x => hR _ _)).trans_eq (grow_l2 S v K f)
        · simpa using mul_nonneg (abs_nonneg (gamma S m v)) hB
    _ = _ := by simp [B,← Finset.sum_mul,add_mul]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
lemma abs_dot_le_one {N : ℕ} (x y : Fin N → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) : |dot x y| ≤ 1 := by
  by_cases hN : N = 0
  · subst N; simp [dot]
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [dot,abs_div,abs_of_pos hp,div_le_iff₀ hp,one_mul]
  calc
    _ ≤ ∑ i, |x i*y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hy i))
    _ = _ := by simp
end DilutedSpinGlass.FiniteLaw

end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0) (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma measurable_rootTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (rootTreeMean S T Q m base old f) := by
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine PrescribedTree.measurable_tilt_sample_expect S (tower (rootArray n y) L T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootTreeMean_bound {B : ℝ} (hf : ∀ x, |f x| ≤ B) (z : FullRootState Y X I M) :
    |rootTreeMean S T Q m base old f z| ≤ B :=
  FiniteLaw.abs_expect_le _ (fun _ => hf _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (d : ℕ) (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma integrable_rootTreeMean (S : PrescribedTree L) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) : Integrable (rootTreeMean S T Q m base old f) μ := by
  apply Integrable.of_bound (measurable_rootTreeMean S T Q m base old f hb).aestronglyMeasurable B
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (rootTreeMean_bound S T Q m base old f hf z))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixConstant
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C ι : Type} [Fintype Ω] [DecidableEq C] [DecidableEq ι] {n : ℕ}

noncomputable local instance matrixConstantDecidable_re47a78_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype Ω] in
lemma labeledHistory_congr_one (m : Fin (n+1) → ℝ)
    (V W : (S : PrescribedTree n) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (h : ∀ S pos, V S pos (fun _ => 1) = W S pos (fun _ => 1))
    (cs : List C) (S : PrescribedTree n) (U : Finset ι) (loc : ι → S.Leaf) (pos : C → S.Leaf) :
    labeledHistory m V cs S U loc pos (fun _ => 1) =
      labeledHistory m W cs S U loc pos (fun _ => 1) := by
  induction cs generalizing S U with
  | nil => exact h S pos
  | cons c cs ih => simp only [labeledHistory,ih]

variable [Fintype C]
/-- The anchor-alone complete matrix history is its exact signed kappa times
the single-target marginal observable. In fact the same identity holds with
any unused old tree, as long as its test is one. -/
theorem weightedMatrixHistory_one (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a : C) (cs : List C) (hcs : cs.Nodup) (hdis : ∀ c ∈ cs, c ≠ a)
    (hfull : ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf) (A : (C → FinitePath Ω n) → ℝ) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)))
      m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
    partialKappa T m (Finset.univ.image q) *
      (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z)) := by
  let B := (T.sampleLaw K).expect (fun z => A (fun c => T.pathAt (q c) z))
  have he := labeledHistory_congr_one m
    (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect (fun z => g z*A (fun c => D.pathAt (pos c) z)) else 0)
    (fun D pos g => B * (if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0))
    (by
      intro D pos
      split_ifs with h
      · simp only [one_mul,FiniteLaw.expect_const,mul_one]
        exact matrix_paths_expect T D q hq.2 pos h K A
      · exact (mul_zero B).symm)
    cs S (Finset.univ.erase x) id (fun _ => x)
  unfold weightedMatrixHistory
  rw [he,labeledHistory_mul_left]
  rw [show labeledHistory m (fun D pos g => if ∀ a b, splitDepth D (pos a) (pos b) = splitDepth T (q a) (q b)
      then (D.sampleLaw K).expect g else 0) cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) =
      matrixHistory T q K m cs S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) from rfl]
  rw [matrixHistory_normalization T q hq.1 K m hm hp hend cs hcs {a}
    (Finset.singleton_nonempty _) (by simpa only [Finset.mem_singleton] using hdis) hfull
    S (Finset.univ.erase x) id (fun _ => x) (singleton_history_cover S x a)
    (by intro b hb d hd; have hb' := Finset.mem_singleton.mp hb; have hd' := Finset.mem_singleton.mp hd
        subst b; subst d; simp only [splitDepth_self]) (fun _ => 1)]
  simp only [Finset.image_singleton,partialKappa_singleton,div_one,FiniteLaw.expect_const,mul_one]
  exact mul_comm _ _

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance partialKappaPairDecidable_re47a78_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
lemma partialKappa_pair (T : PrescribedTree n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a b : T.Leaf) (hab : a ≠ b) :
    partialKappa T m {b,a} =
      m ⟨splitDepth T a b,by have := splitDepth_lt_of_ne T a b hab; omega⟩-
      m ⟨splitDepth T a b+1,by have := splitDepth_lt_of_ne T a b hab; omega⟩ := by
  classical
  have h := matrix_choice_kappa T T id Function.injective_id {a} (Finset.singleton_nonempty _)
    b (by simpa using hab.symm) (fun _ => a) (Finset.univ.erase a) id
    (singleton_history_cover T a a)
    (by intro c hc d hd; have hc' := Finset.mem_singleton.mp hc; have hd' := Finset.mem_singleton.mp hd
        subst c; subst d; rfl) m hm hp hend
  simp only [Finset.mem_singleton,forall_eq,id_eq,Finset.image_id,partialKappa_singleton,div_one] at h
  simp_rw [splitDepth_symm T _ a] at h
  have he (v : T.Internal) : freshSplitDepth T v a = splitDepth (grow T v) (oldLeaf T v a) (newLeaf T v) := by
    rw [splitDepth_symm,splitDepth_new_old]
  simp_rw [he] at h
  rw [pair_univ_erase T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab),
    pair_choice_total T a (splitDepth T a b) (splitDepth_lt_of_ne T a b hab) m hend] at h
  exact h.symm

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixEnergyPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma grid_strictMono (hL : 0 < L) : StrictMono (grid L 0 L) := by
  intro i j hij
  dsimp only [grid]
  simp only [Nat.zero_add]
  exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij) (Nat.cast_pos.mpr hL)

lemma grid_nonneg : ∀ j, 0 ≤ grid L 0 L j := by
  intro j
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma grid_last (hL : 0 < L) : grid L 0 L (Fin.last L) = 1 := by
  simp [grid,ne_of_gt hL]

lemma signed_approximation {H HP J E : ℝ} (hJ : J ≠ 0) (h : |H-HP| ≤ E) :
    HP/J ≤ H/J+E/|J| := by
  have he : HP/J-H/J = (HP-H)/J := by ring
  have hh : HP/J-H/J ≤ E/|J| := by
    rw [he]
    calc
      _ ≤ |(HP-H)/J| := le_abs_self _
      _ = |H-HP|/|J| := by rw [abs_div,abs_sub_comm]
      _ ≤ E/|J| := div_le_div_of_nonneg_right h (le_of_lt (abs_pos.mpr hJ))
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {n : ℕ}

noncomputable local instance matrixEnergyCoefficientPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype C] in
lemma complete_list_nodup (a c : C) (hac : a ≠ c) (cs : List C)
    (hcs : cs.Nodup) (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C)) :
    (c::cs).Nodup ∧ (∀ d ∈ c::cs, d ≠ a) := by
  refine ⟨List.nodup_cons.mpr ⟨?_,hcs⟩,?_⟩
  · intro h; exact hdis c h (by simp)
  · intro d hd
    rcases List.mem_cons.mp hd with h|h
    · exact h ▸ hac.symm
    · intro he; subst d; exact hdis a h (by simp)

lemma complete_list_union (a c : C) (cs : List C)
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ) :
    ({a} : Finset C) ∪ (c::cs).toFinset = Finset.univ := by
  rw [List.toFinset_cons]
  simpa only [Finset.union_insert,Finset.insert_union,Finset.union_singleton,Finset.insert_comm] using hfull

lemma kappa_pair_quotient (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Injective q) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (d : ℕ) (hd : d < n)
    (hqd : splitDepth T (q a) (q c) = d) :
    partialKappa T m (Finset.univ.image q) /
      (partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c ({a} : Finset C)).image q)) =
      m ⟨d,by omega⟩-m ⟨d+1,by omega⟩ := by
  rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ (partialKappa_ne_zero T m hm hp _)]
  rw [Finset.image_insert,Finset.image_singleton,partialKappa_pair T m hm hp hend (q a) (q c)
    (fun h => hac (hq h))]
  simp only [hqd]

/-- Exact centering coefficient of an actual matrix-observable history. The
normalizer uses the protected PAIR, so one factor -delta remains. -/
theorem matrixHistory_one_div (T : PrescribedTree n) (q : C → T.Leaf)
    (hq : Function.Bijective q) (K : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (S : PrescribedTree n) (x : S.Leaf) (A : (C → FinitePath Ω n) → ℝ)
    (d : ℕ) (hd : d < n) (hqd : splitDepth T (q a) (q c) = d) :
    weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) (fun _ => 1) /
      (partialKappa T m (Finset.univ.image q) / partialKappa T m ((insert c ({a} : Finset C)).image q)) =
    (m ⟨d,by omega⟩-m ⟨d+1,by omega⟩) *
      (T.sampleLaw K).expect (fun z => A (fun b => T.pathAt (q b) z)) := by
  have hc := complete_list_nodup a c hac cs hcs hdis
  rw [weightedMatrixHistory_one T q hq K m hm hp hend a (c::cs) hc.1 hc.2
    (complete_list_union a c cs hfull) S x A, mul_div_right_comm,
    kappa_pair_quotient T q hq.1 m hm hp hend a c hac d hd hqd]

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- The nonnegative three-copy argument on an ARBITRARY old tree. Only the
geometric grouping of eligible paths is needed; all old paths and the test
are retained. This applies to the projected means of multi-leaf shapes. -/
theorem general_three_copy_bound_at (n d : ℕ) (hd : d < n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1)
    (S : PrescribedTree n) (a b : S.Leaf) (v : S.Internal)
    (hab : splitDepth S a b = d)
    (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (X : FinitePath Ω n → Fin N → ℝ)
    (hOld : ∀ c, splitDepth S a c = d → ∀ x : Sample Ω S,
      X (S.pathAt c x) = X (S.pathAt b x)) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n T d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) *
        (S.sampleLaw T).expect (fun x =>
          FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))^2) +
      pairObservableHistory T m S a d (fun x y => FiniteLaw.dot (X x) (X y))
        (fun x => FiniteLaw.dot (X (S.pathAt a x)) (X (S.pathAt b x))) := by
  classical
  let R := fun x y => FiniteLaw.dot (X x) (X y)
  let D := fun w : S.Internal => ((grow S w).sampleLaw T).expect (fun x =>
    (R (S.pathAt a (oldSample S w x)) (S.pathAt b (oldSample S w x)) -
      R ((grow S w).pathAt (oldLeaf S w a) x) ((grow S w).pathAt (newLeaf S w) x))^2)
  have hsum := pair_square_identity_general T m hend S a b d (by omega) hab R
    (fun c hc x => congrArg (FiniteLaw.dot (X (S.pathAt a x))) (hOld c hc x))
  have hnonneg (w : S.Internal) : 0 ≤ pairFreshCost S m a d w * D w :=
    mul_nonneg (pairFreshCost_nonneg S m hm hp a d w)
      (FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _))
  have hone : pairFreshCost S m a d v * D v ≤ ∑ w : S.Internal, pairFreshCost S m a d w * D w :=
    Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
  have hcost : pairFreshCost S m a d v = -gamma S m v := by
    unfold pairFreshCost
    rw [splitDepth_symm,splitDepth_new_old,hav,ite_eq_left rfl]
  have hD : D v = KernelTower.tripleExpectAt n T d
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
    have q := triple_marginal (grow S v) T (oldLeaf S v a) (oldLeaf S v b) (newLeaf S v)
      d (by omega) (by simpa only [splitDepth_old_old] using hab)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v a),splitDepth_new_old] using hav)
      (by simpa only [splitDepth_symm (grow S v) (oldLeaf S v b),splitDepth_new_old] using hbv)
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2)
    simpa only [D,R,pathAt_oldLeaf,pathAt_newLeaf] using q
  rw [hcost,hD] at hone

  change (1/2:ℝ)*(∑ w : S.Internal, pairFreshCost S m a d w * D w) = _ at hsum
  unfold KernelTower.halfTripleDifferenceAt
  linarith


end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixTripleDecidable_re47a78_1 (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition
omit [Fintype C] [DecidableEq C] in
/-- The old test may be the physical overlap, rather than the projected
one. Its replacement costs precisely its L2 projection error. -/
theorem pair_three_copy_test_bound (n d : ℕ) (hd : d < n) (K : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hp : ∀ j, 0 ≤ m j)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (x y : S.Leaf) (v : S.Internal)
    (hxy : splitDepth S x y = d) (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (f : Sample Ω S → ℝ) :
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
      pairObservableHistory K m S x d (fun z w => FiniteLaw.dot (X z) (X w)) f +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  have hR : ∀ z w, |R z w| ≤ 1 := fun z w => FiniteLaw.abs_dot_le_one _ _ (hX z) (hX w)
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hF : (S.sampleLaw K).expect (fun z => F z^2) ≤ 1 := by
    calc
      _ ≤ (S.sampleLaw K).expect (fun _ => 1) := FiniteLaw.expect_mono _ (fun z =>
        (sq_le_one_iff_abs_le_one _).mpr (hR _ _))
      _ = _ := FiniteLaw.expect_const _ _
  have henergy := general_three_copy_bound_at n d hd K m hm hp hend S x y v
    hxy hxv hyv X hOld
  have htest := pairObservableHistory_l2 K m S x d R (fun z => F z-f z) hR
  rw [pairObservableHistory_sub_test] at htest
  have htest' := (le_abs_self _).trans htest
  have hsq := mul_le_mul_of_nonneg_left hF hδ
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(S.sampleLaw K).expect (fun z => F z^2)+
      pairObservableHistory K m S x d R F at henergy
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt n K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  linarith

/-- Pointwise-in-the-root crux of the shifted-shape induction. The first term
is SIGNED (not the expectation of its absolute value), so the physical
perturbation identity can be used after root averaging. Every error is an
actual single-copy L2 error and has the literal protected-history charge. -/
theorem matrix_three_copy_pointwise (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (q : C → T.Leaf) (hq : Function.Bijective q)
    (hS : branchingCount S (· ∈ Q) = 0) (K : KernelTower Ω L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ d ∈ cs, d ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : FinitePath Ω L → Fin N → ℝ) (hX : ∀ z i, |X z i| ≤ 1)
    (hOld : ∀ z, splitDepth S x z = d → ∀ w : Sample Ω S, X (S.pathAt z w) = X (S.pathAt y w))
    (A : (C → FinitePath Ω L) → ℝ) (f : Sample Ω S → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
    let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-
      FiniteLaw.dot (X (T.pathAt (q a) z)) (X (T.pathAt (q c) z)))
    let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
    (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + H/J + E*B/|J| +
      pairHistoryMass S m x * (S.sampleLaw K).l2
        (fun z => FiniteLaw.dot (X (S.pathAt x z)) (X (S.pathAt y z))-f z) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
  let R := fun z w => FiniteLaw.dot (X z) (X w)
  let F := fun z : Sample Ω S => R (S.pathAt x z) (S.pathAt y z)
  let H := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*A (fun b => D.pathAt (pos b) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let HP := weightedMatrixHistory T q
      (fun D pos g => (D.sampleLaw K).expect (fun z => g z*R (D.pathAt (pos a) z) (D.pathAt (pos c) z)))
      m (c::cs) S (Finset.univ.erase x) id (fun _ => x) f
  let E := (T.sampleLaw K).l2 (fun z => A (fun b => T.pathAt (q b) z)-R (T.pathAt (q a) z) (T.pathAt (q c) z))
  let B := chargeBound (2*(leaves S+(c::cs).length:ℕ))
      ((Q.card:ℝ)*(leaves S+(c::cs).length:ℕ)) (c::cs).length (branchingCount T (· ∈ Q)) *
      (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  have henergy := pair_three_copy_test_bound L d hd K m hm.monotone hp hend S x y v
    hxy hxv hyv X hX hOld f
  have hU : (Finset.univ.erase x).card ≤ leaves S := by
    exact (Finset.card_erase_le).trans (by simp only [Finset.card_univ, card_leaf]; rfl)
  have hproj : |H-HP| ≤ E*B := by
    simpa only [H, HP, E, B, m, weightedMatrixHistory] using
      (projection_history_difference hL Q T S q hq.2 hS K A
        (fun z => R (z a) (z c)) (c::cs) (Finset.univ.erase x) id (fun _ => x) f hf hU)
  have hpair : HP = J*pairObservableHistory K m S x d R f := by
    have h := matrixHistory_first_pair T q hq.1 K m hm hp hend a c hac cs hcs hdis hfull S x R f
    simpa only [hqd] using h
  have happrox := signed_approximation hJ hproj
  rw [hpair,mul_div_cancel_left₀ _ hJ] at happrox
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+H/J+E*B/|J|+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z)
  change (-gamma S m v)*KernelTower.halfTripleDifferenceAt L K d X ≤
    (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+pairObservableHistory K m S x d R f+
      pairHistoryMass S m x*(S.sampleLaw K).l2 (fun z => F z-f z) at henergy
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators Classical
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

/-- The full shifted-matrix/three-copy estimate after root averaging. The
only analytic errors are actual target and old single-copy L2 projection
errors. The prescribed-tree identity appears as ONE centered root covariance,
not any stronger conditional or absolute pointwise concentration claim. -/
theorem root_matrix_three_copy {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (hL : 0 < L) (Q : Finset ℕ) (T S : PrescribedTree L)
    (q : C → T.Leaf) (hq : Function.Bijective q) (hS : branchingCount S (· ∈ Q) = 0)
    (K : (z : Z) → KernelTower (Ω z) L)
    (a c : C) (hac : a ≠ c) (cs : List C) (hcs : cs.Nodup)
    (hdis : ∀ b ∈ cs, b ∉ insert c ({a} : Finset C))
    (hfull : insert c ({a} : Finset C) ∪ cs.toFinset = Finset.univ)
    (x y : S.Leaf) (v : S.Internal) (d : ℕ) (hd : d < L)
    (hqd : splitDepth T (q a) (q c) = d) (hxy : splitDepth S x y = d)
    (hxv : freshSplitDepth S v x = d) (hyv : freshSplitDepth S v y = d)
    (X : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) (hX : ∀ z w i, |X z w i| ≤ 1)
    (hOld : ∀ z b, splitDepth S x b = d → ∀ w : Sample (Ω z) S,
      X z (S.pathAt b w) = X z (S.pathAt y w))
    (A : (z : Z) → (C → FinitePath (Ω z) L) → ℝ) (hA : ∀ z w, |A z w| ≤ 1)
    (f : (z : Z) → Sample (Ω z) S → ℝ) (hf : ∀ z w, |f z w| ≤ 1)
    (hE : Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ)
    (hH : Integrable (fun z => matrixObservableHistory T q (K z) (grid L 0 L) (c::cs) S x (A z) (f z)) μ)
    (hEt : Integrable (fun z => matrixProjectionError T q (K z) a c (A z) (X z)) μ)
    (hEo : Integrable (fun z => oldProjectionError S (K z) x y (f z) (X z)) μ)
    (hMean : Integrable (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w))) μ) :
    let m := grid L 0 L
    let J := partialKappa T m (Finset.univ.image q) /
      partialKappa T m ((insert c ({a} : Finset C)).image q)
    (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
      2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) +
        |matrixRootCovariance μ Ω T S q K m (c::cs) x A f|/|J| +
        (∫ z, matrixProjectionError T q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q T S (c::cs).length/|J| +
        pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (f z) (X z) ∂μ) := by
  dsimp only
  let m := grid L 0 L
  let J := partialKappa T m (Finset.univ.image q) /
    partialKappa T m ((insert c ({a} : Finset C)).image q)
  have hm := grid_strictMono hL
  have hp : ∀ j, 0 ≤ m j := grid_nonneg
  have hend : m (Fin.last L) = 1 := grid_last hL
  have hJ : J ≠ 0 := div_ne_zero (partialKappa_ne_zero T m hm hp _)
    (partialKappa_ne_zero T m hm hp _)
  apply root_matrix_error_bound μ
    (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z))
    (fun z => matrixObservableHistory T q (K z) m (c::cs) S x (A z) (f z))
    (fun z => matrixObservableHistory T q (K z) m (c::cs) S x (A z) (fun _ => 1))
    (fun z => (S.sampleLaw (K z)).expect (f z))
    (fun z => (T.sampleLaw (K z)).expect (fun w => A z (fun b => T.pathAt (q b) w)))
    (fun z => matrixProjectionError T q (K z) a c (A z) (X z))
    (fun z => oldProjectionError S (K z) x y (f z) (X z))
    J (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) (-gamma S m v)
    (shiftedCharge Q T S (c::cs).length) (pairHistoryMass S m x) hJ
    (sub_nonneg.mpr (hm.monotone (by simp)))
    (fun z => (S.sampleLaw (K z)).abs_expect_le (hf z))
    (fun z => (T.sampleLaw (K z)).abs_expect_le (fun w => hA z _))
    ?_ hE hH hMean hEt hEo ?_
  · intro z
    have he := matrixHistory_one_div T q hq (K z) m hm hp hend a c hac cs hcs hdis hfull S x (A z) d hd hqd
    simpa only [matrixObservableHistory, J, neg_sub] using he
  · intro z
    exact matrix_three_copy_pointwise hL Q T S q hq hS (K z) a c hac cs hcs hdis hfull
      x y v d hd hqd hxy hxv hyv (X z) (hX z) (hOld z) (A z) (f z) (hf z)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] {N : ℕ}

/-- Exact three-copy transfer for a coupled true vector and projected vector.
This prevents the invalid inference from only projected covariance energy. -/
theorem covariance_projection_transfer (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ) :
    P.covarianceEnergy X ≤
      P.expect (fun x => P.expect (fun y => P.expect (fun z =>
        (dot (Y x) (Y y)-dot (Y x) (Y z))^2)))+4*pairProjectionSq P X Y := by
  have hthree := P.three_copy_bound X
  have hthree' : 2*P.covarianceEnergy X ≤
      P.expect (fun x => P.expect (fun y => P.expect (fun z =>
        (dot (X x) (X y)-dot (X x) (X z))^2))) := by
    convert hthree using 1
    all_goals try with_reducible_and_instances rfl
    unfold covarianceEnergy
    ring
  have hp (x y z : Ω) :
      (dot (X x) (X y)-dot (X x) (X z))^2 ≤
        2*(dot (Y x) (Y y)-dot (Y x) (Y z))^2+
        4*(dot (X x) (X y)-dot (Y x) (Y y))^2+
        4*(dot (X x) (X z)-dot (Y x) (Y z))^2 := by
    nlinarith [sq_nonneg ((dot (X x) (X y)-dot (Y x) (Y y))+
        (dot (X x) (X z)-dot (Y x) (Y z))),
      sq_nonneg ((dot (X x) (X y)-dot (X x) (X z))-
        2*(dot (Y x) (Y y)-dot (Y x) (Y z)))]
  have h := P.expect_mono (fun x => P.expect_mono (fun y => P.expect_mono (fun z => hp x y z)))
  simp only [expect_add,expect_mul_left,expect_const] at h
  unfold pairProjectionSq
  linarith

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeProjectionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

/-- Pulling three independent copies of one sampled branch back to any one
leaf keeps exactly the three independent path law. -/
lemma branch_leaf_triple (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (F : FinitePath Ω (n+1) → FinitePath Ω (n+1) →
      FinitePath Ω (n+1) → ℝ) :
    (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
      (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun y =>
        (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun w =>
          F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) (w.1,C.pathAt a w.2)))) =
    KernelTower.tripleExpectAt (n+1) T 0 F := by
  change _ = (KernelTower.law (n+1) T).expect (fun x =>
    (KernelTower.law (n+1) T).expect (fun y => (KernelTower.law (n+1) T).expect (F x y)))
  calc
    _ = (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
      (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun y =>
        (KernelTower.law (n+1) T).expect (fun w =>
          F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) w))) := by
      apply FiniteLaw.expect_congr; intro x
      apply FiniteLaw.expect_congr; intro y
      exact branch_leaf_marginal C T.1 T.2 a (fun w =>
        F (x.1,C.pathAt a x.2) (y.1,C.pathAt a y.2) w)
    _ = (T.1.bind (fun z => C.sampleLaw (T.2 z))).expect (fun x =>
        (KernelTower.law (n+1) T).expect (fun y =>
          (KernelTower.law (n+1) T).expect (fun w => F (x.1,C.pathAt a x.2) y w))) := by
      apply FiniteLaw.expect_congr; intro x
      exact branch_leaf_marginal C T.1 T.2 a (fun y =>
        (KernelTower.law (n+1) T).expect (fun w => F (x.1,C.pathAt a x.2) y w))
    _ = _ := branch_leaf_marginal C T.1 T.2 a (fun x =>
      (KernelTower.law (n+1) T).expect (fun y => (KernelTower.law (n+1) T).expect (F x y)))

lemma branch_energy_projection_transfer (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (a : C.Leaf) (f Y : FinitePath Ω (n+1) → Fin N → ℝ) :
    childEnergy C T f ≤ 2*KernelTower.halfTripleDifferenceAt (n+1) T 0 Y +
      4*branchProjectionSq C T a f Y := by
  have h := FiniteLaw.covariance_projection_transfer
    (T.1.bind (fun z => C.sampleLaw (T.2 z)))
    (fun z i => C.leafProduct (fun w => f (z.1,w) i) z.2)
    (fun z => Y (z.1,C.pathAt a z.2))
  rw [branch_leaf_triple C T a (fun x y z =>
    (FiniteLaw.dot (Y x) (Y y)-FiniteLaw.dot (Y x) (Y z))^2)] at h
  simpa only [childEnergy,branchProjectionSq,KernelTower.halfTripleDifferenceAt,
    ← mul_assoc,show (2:ℝ)*(1/2)=1 by norm_num,one_mul] using h

/-- Three-copy transfer at an arbitrary prefix above a complete literal
multileaf shape. The shape's actual covariance is on the left. -/
theorem shape_energy_projection_transfer (C : PrescribedTree n) (a : C.Leaf)
    (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f Y : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    shapeEnergyAt C d T f ≤ 2*KernelTower.halfTripleDifferenceAt (n+1+d) T d Y +
      4*shapeProjectionSqAt C a d T f Y := by
  induction d with
  | zero => exact branch_energy_projection_transfer C T a f Y
  | succ d ih =>
    have h := T.1.expect_mono (fun z => ih (T.2 z) (fun y => f (z,y)) (fun y => Y (z,y)))
    convert h using 1
    · rfl
    · simp only [shapeProjectionSqAt,KernelTower.halfTripleDifferenceAt,
        KernelTower.tripleExpectAt,FiniteLaw.expect_add,FiniteLaw.expect_mul_left]
      rfl

lemma shapeEnergyAt_nonneg (C : PrescribedTree n) (d : ℕ) (T : KernelTower Ω (n+1+d))
    (f : FinitePath Ω (n+1+d) → Fin N → ℝ) : 0 ≤ shapeEnergyAt C d T f := by
  induction d with
  | zero => unfold shapeEnergyAt childEnergy FiniteLaw.covarianceEnergy; positivity
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => f (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedTree
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.shiftedTreeDecidable
lemma branchingCount_bottom {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (bottomUnary S) P = branchingCount S P := by
  classical
  induction S generalizing P with
  | leaf =>
    change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+(∑ _ : Fin 1, (0:ℕ)) = 0
    simp
  | @node n k C ih => simp only [bottomUnary,branchingCount,ih]

lemma branchingCount_unary {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (unary S) P = branchingCount S (fun d => P (d+1)) := by
  classical
  change (if P 0 ∧ 1 < (1:ℕ) then 1 else 0)+
    (∑ _ : Fin 1, branchingCount S (fun d => P (d+1))) = _
  simp

/-- Literal branching-vertex count as a sum. Distinct vertices at equal
depths occur separately; no count by distinct depth values is substituted. -/
lemma branchingCount_eq_vertexSum {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = ∑ v : S.Internal,
      if 1 < vertexArity S v ∧ P (vertexDepth S v) then 1 else 0 := by
  classical
  induction S generalizing P with
  | leaf =>
    change 0 = ∑ v : Empty, _
    simp
  | @node n k C ih =>
    change _ = ∑ v : Option ((i : Fin k) × Internal (C i)), _
    rw [Fintype.sum_option]
    simp only [vertexArity,vertexDepth,Fintype.sum_sigma,branchingCount,ih,and_comm]

lemma mem_branchingDepths {n : ℕ} (S : PrescribedTree n) (d : ℕ) :
    d ∈ branchingDepths S ↔ ∃ v : S.Internal, 1 < vertexArity S v ∧ vertexDepth S v=d := by
  classical
  simp only [branchingDepths,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]


lemma branchingCount_eq_zero_iff {n : ℕ} (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount S P = 0 ↔ ∀ d ∈ branchingDepths S, ¬P d := by
  classical
  rw [branchingCount_eq_vertexSum,Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · intro h d hd hp
    obtain ⟨v,hv,rfl⟩ := (mem_branchingDepths S d).mp hd
    have he := h v (Finset.mem_univ v)
    rw [ite_eq_left ⟨hv,hp⟩] at he
    contradiction
  · intro h v _
    by_cases hv : 1 < vertexArity S v
    · have hp := h (vertexDepth S v) ((mem_branchingDepths S _).mpr ⟨v,hv,rfl⟩)
      simp only [hv,hp,and_false,ite_false]
    · simp only [hv,false_and,ite_false]

lemma zero_not_mem_shiftedTwinDepths {n : ℕ} (S : PrescribedTree n) :
    0 ∉ shiftedTwinDepths S := by
  classical
  simp [shiftedTwinDepths]

lemma shifted_twin_old_count {n : ℕ} (S : PrescribedTree n) (hs : NoAdjacentBranchDepths S) :
    branchingCount (doubled (bottomUnary S)) (· ∈ shiftedTwinDepths S) = 0 := by
  classical
  have hC : branchingCount S (fun d => d+1 ∈ shiftedTwinDepths S)=0 := by
    apply (branchingCount_eq_zero_iff S _).mpr
    intro d hd h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    exact hs a ha d hd (by omega)
  simp only [doubled,branchingCount]

  simp only [zero_not_mem_shiftedTwinDepths,false_and,ite_false,branchingCount_bottom,hC,
    Finset.sum_const_zero,add_zero]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N n : ℕ}

lemma sampleLaw_unary_expect (S : PrescribedTree n) (T : KernelTower Ω (n+1))
    (F : Ω × Sample Ω S → ℝ) :
    ((unary S).sampleLaw T).expect (fun z => F (z 0)) =
      T.1.expect (fun a => (S.sampleLaw (T.2 a)).expect (fun w => F (a,w))) := by
  change (FiniteLaw.pi (fun _ : Fin 1 => T.1.bind (fun a => S.sampleLaw (T.2 a)))).expect
    (fun z => F (z 0)) = _
  rw [FiniteLaw.expect_pi_marginal,FiniteLaw.expect_bind]

lemma stemContractionSq_step (S : PrescribedTree n) (a : S.Leaf) (r : ℕ)
    (T : KernelTower Ω (n+r+1)) (f : FinitePath Ω (n+r+1) → Fin N → ℝ) (B : Fin N → ℝ) :
    stemContractionSq S a (r+1) T f B =
      T.1.expect (fun x => stemContractionSq S a r (T.2 x) (fun y => f (x,y)) B) := by
  unfold stemContractionSq
  let F := fun z : Ω × Sample Ω (stem S r) => (FiniteLaw.dot (fun i =>
    leafProduct (stem S r) (fun y => f (z.1,y) i) z.2-
      tailMean S r (T.2 z.1) (fun y => f (z.1,y) i)
        ((stem S r).pathAt (stemLeaf S r a) z.2)) B)^2
  refine Eq.trans ?_ (sampleLaw_unary_expect (stem S r) T F)
  apply FiniteLaw.expect_congr
  intro z
  apply congrArg (fun u : Fin N → ℝ => (FiniteLaw.dot u B)^2)
  funext i
  exact congrArg₂ (·-·) (leafProduct_unary (stem S r) (fun x => f x i) z) rfl

/-- Actual projection at an arbitrary later first split; child covariances
are averaged over the very same ancestral prefix. No decorrelation premise
is assumed. Constants are dimension-free, including zero spatial size. -/
theorem stem_node_contraction_sq_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r)) (f : FinitePath Ω (n+1+r) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) (B : Fin N → ℝ) (hB : ∀ i, |B i|≤1) :
    stemContractionSq (.node k C) a r T f B ≤
      (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) r T f) := by
  induction r with
  | zero =>
    have h := node_projection k C T f hf B hB
    have hs := mul_self_le_mul_self (FiniteLaw.l2_nonneg _ _) h
    rw [← pow_two,← pow_two,FiniteLaw.l2_sq] at hs
    have hc := @sq_sum_le_card_mul_sum_sq (Fin k) ℝ _ _ _ _ Finset.univ
      (fun i : Fin k => Real.sqrt (Real.sqrt (childEnergy (C i) T f)))
    simp only [Real.sq_sqrt (Real.sqrt_nonneg _),Finset.card_univ,Fintype.card_fin] at hc
    exact hs.trans hc
  | succ r ih =>
    rw [stemContractionSq_step]
    have h := T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg (C i) r (T.2 x) (fun y => f (x,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace ReducedTopology

attribute [local instance] OAI.DilutedSpinGlass.instDecidable_solutions
lemma admissible_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : lo ≤ q v := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.1
    | some v => exact h.1.trans ((Nat.le_succ _).trans (ih v.1 _ (h.2.2 v.1) v.2))

/-- Actual vertex multiplicities, with assigned *absolute* depths. Aligned
copies may repeat a coordinate but never merge their branching vertices. -/
theorem realize_branchingCount (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) (P : ℕ → Prop) :
    PrescribedTree.branchingCount (realize r d S q) (fun u => P (d+u)) =
      ∑ v : S.Vertex, if P (q v) then 1 else 0 := by
  classical
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => exact (Finset.sum_empty).symm
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.branchingCount_unary]
      have hh := ih (d+1) .leaf q trivial
      convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.branchingCount_unary]
        have ha : Admissible (.node k hk C) q (d+1) ((d+1)+r) :=
          ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
        have hh := ih (d+1) (.node k hk C) q ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]
      · have he : q none=d := by have := h.1; omega
        change _ = ∑ v : Option ((i : Fin k) × (C i).Vertex), _
        rw [Fintype.sum_option,Fintype.sum_sigma]
        simp only [PrescribedTree.branchingCount,Nat.add_zero,show 1<(k:ℕ) by omega,and_true,he]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have ha : Admissible (C i) (fun v => q (some ⟨i,v⟩)) (d+1) ((d+1)+r) := by
          simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i
        have hh := ih (d+1) (C i) (fun v => q (some ⟨i,v⟩)) ha
        convert hh using 1; simp [Nat.add_comm,Nat.add_left_comm]

end ReducedTopology
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω]

/-- Before its first scheduled branching, the realized topology is exactly
an initial unary stem; all later vertex assignments are unchanged. -/
lemma realize_stem (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d+r ≤ q v) :
    realize (n+r) d S q = PrescribedTree.stem (realize n (d+r) S q) r := by
  induction r generalizing d with
  | zero => rfl
  | succ r ih =>
    have hh : ∀ v, d+1+r ≤ q v := by intro v; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq v
    cases S with
    | leaf =>
      change PrescribedTree.unary (realize (n+r) (d+1) leaf q) =
        PrescribedTree.unary (PrescribedTree.stem (realize n (d+(r+1)) leaf q) r)
      congr 1
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh
    | node k hk C =>
      have hd : d<q none := by have := hq none; omega
      change realize (n+r+1) d (node k hk C) q = _
      rw [realize,ite_eq_left hd]
      change PrescribedTree.unary _ = PrescribedTree.unary _
      apply congrArg PrescribedTree.unary
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1) hh

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_VertexContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.realizeTranslationDecidable
/-- Bottom extension preserves all assigned internal depths, and supplies
precisely the old tree used opposite a delayed target in the matrix identity. -/
theorem realize_bottom (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) :
    realize (H+1) d S q=PrescribedTree.bottomUnary (realize H d S q) := by
  induction H generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := hq.1; have := hq.2.1; omega
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize,PrescribedTree.unary,PrescribedTree.bottomUnary]
      congr 1
      funext i
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      conv_lhs => rw [realize]
      conv_rhs => arg 1; rw [realize]
      split_ifs with hd
      · change PrescribedTree.node 1 _=PrescribedTree.node 1 _
        congr 1
        funext i
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2⟩
      · simp only [PrescribedTree.bottomUnary]
        congr 1
        funext i
        apply ih
        have he : q none=d := by have := hq.1; omega
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2.2 i

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShapeMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N k : ℕ}

noncomputable local instance shapeMatrixPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
omit [Fintype Ω] [DecidableEq C] in
lemma spatialProduct_bound [Fintype Ω] [DecidableEq C]
    (D : C → FinitePath Ω L → Fin N → ℝ)
    (hD : ∀ c x i, |D c x i| ≤ 1) (x : C → FinitePath Ω L) :
    |spatialProduct D x| ≤ 1 := by
  unfold spatialProduct
  simp only [abs_div, Nat.abs_cast]
  have hs : |∑ i : Fin N, ∏ c, D c (x c) i| ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ i : Fin N, |∏ c, D c (x c) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun c _ => hD c _ i))
      _ = _ := by simp
  by_cases hN : N = 0
  · subst N; simp
  · exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr (by simpa using hs)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_StemTwoSideProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] {N : ℕ}

/-- Pairwise projection retains both sampled vectors and their correlation
with any later old test. Only the separate sides are independent. -/
theorem pairProjectionSq_le_of_contractions (P : FiniteLaw Ω) (X Y : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) (A : ℝ)
    (hA : ∀ B : Fin N → ℝ, (∀ i, |B i|≤1) →
      P.expect (fun x => (dot (fun i => X x i-Y x i) B)^2) ≤ A) :
    pairProjectionSq P X Y ≤ 4*A := by
  let F := fun x y => dot (fun i => X y i-Y y i) (X x)
  let G := fun x y => dot (fun i => X x i-Y x i) (Y y)
  have he (x y : Ω) : dot (X x) (X y)-dot (Y x) (Y y)=F x y+G x y := by
    simp only [F,G,dot,← sub_div,← add_div,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hF : P.expect (fun x => P.expect (fun y => (F x y)^2)) ≤ A :=
    (P.expect_mono (fun x => hA (X x) (hX x))).trans_eq (P.expect_const _)
  have hG : P.expect (fun x => P.expect (fun y => (G x y)^2)) ≤ A := by
    rw [expect_comm]
    exact (P.expect_mono (fun y => hA (Y y) (hY y))).trans_eq (P.expect_const _)
  have hh := P.expect_mono (fun x => P.expect_mono (fun y =>
    show (dot (X x) (X y)-dot (Y x) (Y y))^2 ≤ 2*(F x y)^2+2*(G x y)^2 from by
      rw [he]
      nlinarith [sq_nonneg (F x y-G x y)]))
  simp only [expect_add,expect_mul_left] at hh
  exact hh.trans (by linarith)

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The actual projector uses only the sampled stem. It does not depend on
which old descendant leaf represents that stem. -/
lemma tailMean_path_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (z : Sample Ω (stem S r)) :
    tailMean S r T f ((stem S r).pathAt (stemLeaf S r a) z) =
      tailMean S r T f ((stem S r).pathAt (stemLeaf S r b) z) := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (T.2 (z 0).1) (fun y => f ((z 0).1,y)) (z 0).2

lemma tailMean_any_path_stem (S : PrescribedTree n) (r : ℕ) (a b : (stem S r).Leaf)
    (T : KernelTower Ω (n+r)) (f : FinitePath Ω (n+r) → ℝ)
    (z : Sample Ω (stem S r)) :
    tailMean S r T f ((stem S r).pathAt a z) =
      tailMean S r T f ((stem S r).pathAt b z) := by
  obtain ⟨a,rfl⟩ := (stemLeaf_bijective S r).2 a
  obtain ⟨b,rfl⟩ := (stemLeaf_bijective S r).2 b
  exact tailMean_path_stem S r a b T f z

/-- In the literal two-copy old tree, every leaf opposite the anchor has
exactly the same projected vector as the designated old-II leaf. This is
the geometric hOld premise of the full signed-matrix estimate. -/
theorem doubled_stem_projector_old_side (S : PrescribedTree n) (r : ℕ)
    (a b : (stem S r).Leaf) (T : KernelTower Ω (n+r+1))
    (f : FinitePath Ω (n+r+1) → Fin N → ℝ)
    (c : (doubled (stem S r)).Leaf)
    (hc : splitDepth (doubled (stem S r)) ⟨0,a⟩ c=0)
    (z : Sample Ω (doubled (stem S r))) :
    (fun i => tailMean S (r+1) T (fun x => f x i)
      ((doubled (stem S r)).pathAt c z)) =
    (fun i => tailMean S (r+1) T (fun x => f x i)
      ((doubled (stem S r)).pathAt ⟨1,b⟩ z)) := by
  rcases c with ⟨j,c⟩
  have hj : j ≠ 0 := by
    intro h
    subst j
    change splitDepth (.node 2 (fun _ => stem S r)) ⟨0,a⟩ ⟨0,c⟩=0 at hc
    rw [splitDepth_same_child] at hc
    omega
  have hj1 : j=1 := by
    apply Fin.ext
    have hh := j.isLt
    have hn : j.val ≠ 0 := fun h => hj (Fin.ext h)
    change j.val=1
    norm_num at hh
    omega
  subst j
  funext i
  exact tailMean_any_path_stem S r c b (T.2 (z 1).1) (fun y => f ((z 1).1,y) i) (z 1).2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_DoubledStemProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

omit [Fintype Ω] in
lemma doubledOverlap_eq (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (doubled S)) :
    doubledOverlap S f z=(∑ i, leafProduct (doubled S) (fun x => f x i) z)/(N:ℝ) := by
  unfold doubledOverlap FiniteLaw.dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = ∏ j : Fin 2, leafProduct S (fun x => f ((z j).1,x) i) (z j).2
  rw [Fin.prod_univ_two]
  rfl

/-- The old-tree projection error in the signed matrix bound, on the literal
doubled old tree, is controlled by the actual proper-child energies at its
later first split. No conditional concentration assumption is imposed. -/
theorem oldProjectionError_doubled_stem_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r+1)) (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    let S := PrescribedTree.node k C
    let X := fun x i => tailMean S (r+1) T (fun y => f y i) x
    oldProjectionError (doubled (stem S r)) T ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩
      (doubledOverlap (stem S r) f) X ≤
      2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f)) := by
  dsimp only
  let S := PrescribedTree.node k C
  let Q := T.1.bind (fun x => (stem S r).sampleLaw (T.2 x))
  let X := fun z : Ω × Sample Ω (stem S r) =>
    fun i => leafProduct (stem S r) (fun y => f (z.1,y) i) z.2
  let Y := fun z : Ω × Sample Ω (stem S r) =>
    fun i => tailMean S r (T.2 z.1) (fun y => f (z.1,y) i)
      ((stem S r).pathAt (stemLeaf S r a) z.2)
  have h := FiniteLaw.pairProjectionSq_le_of_contractions Q X Y
    (fun z i => leafProduct_bound _ (fun y => hf (z.1,y) i) z.2)
    (fun z i => tailMean_bound _ _ _ _ (fun y => hf (z.1,y) i) _) 
    ((k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f))
  have hc : ∀ B : Fin N → ℝ, (∀ i, |B i|≤1) →
      Q.expect (fun z => (FiniteLaw.dot (fun i => X z i-Y z i) B)^2) ≤
        (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by
    intro B hB
    rw [FiniteLaw.expect_bind]
    have hh := T.1.expect_mono (fun x => stem_node_contraction_sq_le k C a r (T.2 x)
      (fun y => f (x,y)) (fun y => hf (x,y)) B hB)
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => shapeEnergyAt_nonneg (C i) r (T.2 x) (fun y => f (x,y)))
  specialize h hc
  have he : (sampleLaw (doubled (stem S r)) T).expect (fun z =>
      (FiniteLaw.dot (Y (z 0)) (Y (z 1))-doubledOverlap (stem S r) f z)^2) =
        Q.pairProjectionSq X Y := by
    change (FiniteLaw.pi (fun _ : Fin 2 => Q)).expect _ = _
    refine Eq.trans ?_ (FiniteLaw.expect_pi_pair (fun _ : Fin 2 => Q) 0 1 (by decide)
      (fun x y => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (Y x) (Y y))^2))
    apply FiniteLaw.expect_congr
    intro z
    exact sub_sq_comm _ _
  unfold oldProjectionError FiniteLaw.l2
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by positivity
    rw [mul_pow,Real.sq_sqrt hn]
    change (sampleLaw (doubled (stem S r)) T).expect (fun z =>
      (FiniteLaw.dot (Y (z 0)) (Y (z 1))-doubledOverlap (stem S r) f z)^2) ≤ _
    rw [he]
    norm_num only [show (2:ℝ)^2=4 by norm_num]
    exact h

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

lemma splitDepth_stem (S : PrescribedTree n) (r : ℕ) (a b : S.Leaf) :
    splitDepth (stem S r) (stemLeaf S r a) (stemLeaf S r b)=splitDepth S a b+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change splitDepth (.node 1 (fun _ => stem S r)) ⟨0,stemLeaf S r a⟩ ⟨0,stemLeaf S r b⟩=_
    rw [splitDepth_same_child,ih]
    omega

lemma freshSplitDepth_stem (S : PrescribedTree n) (r : ℕ) (v : S.Internal) (a : S.Leaf) :
    freshSplitDepth (stem S r) (stemInternal S r v) (stemLeaf S r a)=freshSplitDepth S v a+r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 1+freshSplitDepth (stem S r) (stemInternal S r v) (stemLeaf S r a)=_
    rw [ih]
    omega

lemma splitProjector_bound (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (f : FinitePath Ω (n+r+1+d) → ℝ)
    (hf : ∀ x, |f x|≤1) (x : FinitePath Ω (n+r+1+d)) :
    |splitProjector S r d T f x|≤1 := by
  induction d with
  | zero => exact tailMean_bound S (r+1) T f hf x
  | succ d ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

/-- The old-side geometric premise of the full signed matrix identity at an
arbitrary evaluation depth d. All old leaves and sampled ancestors remain. -/
theorem stem_doubled_projector_old_side (S : PrescribedTree n) (r d : ℕ)
    (a b : (stem S r).Leaf) (T : KernelTower Ω (n+r+1+d))
    (f : FinitePath Ω (n+r+1+d) → Fin N → ℝ)
    (c : (stem (doubled (stem S r)) d).Leaf)
    (hc : splitDepth (stem (doubled (stem S r)) d)
      (stemLeaf (doubled (stem S r)) d ⟨0,a⟩) c=d)
    (z : Sample Ω (stem (doubled (stem S r)) d)) :
    (fun i => splitProjector S r d T (fun x => f x i)
      ((stem (doubled (stem S r)) d).pathAt c z)) =
    (fun i => splitProjector S r d T (fun x => f x i)
      ((stem (doubled (stem S r)) d).pathAt
        (stemLeaf (doubled (stem S r)) d ⟨1,b⟩) z)) := by
  induction d with
  | zero => exact doubled_stem_projector_old_side S r a b T f c hc z
  | succ d ih =>
    rcases c with ⟨j,c⟩
    have hj := Fin.eq_zero j
    subst j
    change splitDepth (.node 1 (fun _ => stem (doubled (stem S r)) d))
      ⟨0,stemLeaf (doubled (stem S r)) d ⟨0,a⟩⟩ ⟨0,c⟩=d+1 at hc
    rw [splitDepth_same_child] at hc
    have hc' : splitDepth (stem (doubled (stem S r)) d)
      (stemLeaf (doubled (stem S r)) d ⟨0,a⟩) c=d := by omega
    exact ih (T.2 (z 0).1) (fun y => f ((z 0).1,y)) c hc' (z 0).2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_StemCovarianceTransfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n N : ℕ}

/-- The old projection error and the physical two-copy projection energy
are exactly the same coupling, not only equal separate marginal errors. -/
lemma oldProjectionError_doubled_sq (S : PrescribedTree n) (a : S.Leaf)
    (T : KernelTower Ω (n+1)) (f X : FinitePath Ω (n+1) → Fin N → ℝ) :
    (oldProjectionError (doubled S) T ⟨0,a⟩ ⟨1,a⟩ (doubledOverlap S f) X)^2 =
      branchProjectionSq S T a f X := by
  unfold oldProjectionError
  rw [FiniteLaw.l2_sq]
  unfold branchProjectionSq FiniteLaw.pairProjectionSq
  change (FiniteLaw.pi (fun _ : Fin 2 => T.1.bind (fun x => S.sampleLaw (T.2 x)))).expect _ = _
  refine Eq.trans ?_ (FiniteLaw.expect_pi_pair
    (fun _ : Fin 2 => T.1.bind (fun x => S.sampleLaw (T.2 x))) 0 1 (by decide)
    (fun z w => (FiniteLaw.dot
      (fun i => leafProduct S (fun y => f (z.1,y) i) z.2)
      (fun i => leafProduct S (fun y => f (w.1,y) i) w.2)-
      FiniteLaw.dot (X (z.1,S.pathAt a z.2)) (X (w.1,S.pathAt a w.2)))^2))
  apply FiniteLaw.expect_congr
  intro z
  exact sub_sq_comm _ _

/-- The proper-child covariance estimate for the exact coupled projection
energy required by the three-copy transfer. -/
theorem branchProjectionSq_stem_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r : ℕ)
    (T : KernelTower Ω (n+1+r+1)) (f : FinitePath Ω (n+1+r+1) → Fin N → ℝ)
    (hf : ∀ x i, |f x i|≤1) :
    branchProjectionSq (stem (.node k C) r) T (stemLeaf (.node k C) r a) f
      (fun x i => tailMean (.node k C) (r+1) T (fun y => f y i) x) ≤
      4*(k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by
  rw [← oldProjectionError_doubled_sq]
  have hh := oldProjectionError_doubled_stem_le k C a r T f hf
  have hs := mul_self_le_mul_self (FiniteLaw.l2_nonneg _ _) hh
  have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (shapeEnergyAt (C i) (r+1) T f) := by positivity
  simpa only [oldProjectionError,← pow_two,mul_pow,Real.sq_sqrt hn,show (2:ℝ)^2=4 by norm_num,mul_assoc] using hs

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MatrixLeafProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [Fintype Ω] [DecidableEq I] in
/-- The physical color-indexed spatial product is exactly the product of
all actual target leaves whenever colors enumerate those leaves bijectively. -/
lemma spatialProduct_leafProduct (S : PrescribedTree n) (q : I → S.Leaf)
    (hq : Function.Bijective q) (f : FinitePath Ω n → Fin N → ℝ) (z : Sample Ω S) :
    spatialProduct (fun _ : I => f) (fun c => S.pathAt (q c) z) =
      (∑ i, leafProduct S (fun x => f x i) z)/(N:ℝ) := by
  unfold spatialProduct
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [leafProduct_eq_prod]
  exact Fintype.prod_bijective q hq _ _ (fun _ => rfl)

omit [Fintype I] [DecidableEq I] in
/-- Changing the target's projected means to the old projected means costs
their actual coupled L2 difference in the target law, uniformly over extension
histories after marginalization. -/
theorem matrixProjectionError_change (S : PrescribedTree n) (q : I → S.Leaf)
    (T : KernelTower Ω n) (a c : I) (A : (I → FinitePath Ω n) → ℝ)
    (X Y : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError S q T a c A X ≤ matrixProjectionError S q T a c A Y +
      (S.sampleLaw T).l2 (fun z => FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z))-
        FiniteLaw.dot (X (S.pathAt (q a) z)) (X (S.pathAt (q c) z))) := by
  have h := (S.sampleLaw T).l2_add_le
    (fun z => A (fun c => S.pathAt (q c) z)-FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z)))
    (fun z => FiniteLaw.dot (Y (S.pathAt (q a) z)) (Y (S.pathAt (q c) z))-
      FiniteLaw.dot (X (S.pathAt (q a) z)) (X (S.pathAt (q c) z)))
  simpa only [matrixProjectionError,sub_add_sub_cancel] using h

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CoordinateFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {N : ℕ}

lemma spatialSq_nonneg (x : Fin N → ℝ) : 0 ≤ spatialSq x :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

lemma spatial_mean_sq_le (x : Fin N → ℝ) : ((∑ i, x i)/(N:ℝ))^2 ≤ spatialSq x := by
  by_cases hN : N=0
  · subst N
    simp [spatialSq]
  · have hn : 0<(N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have h := @sq_sum_le_card_mul_sum_sq (Fin N) ℝ _ _ _ _ Finset.univ x
    simp only [Finset.card_univ,Fintype.card_fin] at h
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    calc
      _ ≤ (N:ℝ)*∑ i, (x i)^2 := h
      _ = spatialSq x*(N:ℝ)^2 := by
        unfold spatialSq
        field_simp

/-- The simultaneous change of both vectors in a contraction is controlled
by the two actual coupled spatial norms, regardless of correlation. -/
theorem dot_pair_change_sq (x y u v : Fin N → ℝ)
    (hx : ∀ i, |x i|≤1) (hy : ∀ i, |y i|≤1)
    (hu : ∀ i, |u i|≤1) (hv : ∀ i, |v i|≤1) :
    (dot x y-dot u v)^2 ≤ 2*spatialSq (fun i => x i-u i)+2*spatialSq (fun i => y i-v i) := by
  have hpt (i : Fin N) : (x i*y i-u i*v i)^2 ≤ 2*((x i-u i)^2+(y i-v i)^2) := by
    have h := bounded_product_difference_sq
      (fun j : Fin 2 => if j=0 then x i else y i)
      (fun j : Fin 2 => if j=0 then u i else v i)
      (fun j => by split_ifs <;> [exact hx i;exact hy i])
      (fun j => by split_ifs <;> [exact hu i;exact hv i])
    simpa only [Fintype.card_fin,Fin.prod_univ_two,Fin.sum_univ_two,ite_true,
      show ¬(1:Fin 2)=0 by decide,ite_false,Nat.cast_ofNat] using h
  have h := spatial_mean_sq_le (fun i => x i*y i-u i*v i)
  change ((∑ i, (x i*y i-u i*v i))/(N:ℝ))^2 ≤ _ at h
  change ((∑ i, x i*y i)/(N:ℝ)-(∑ i, u i*v i)/(N:ℝ))^2 ≤ _
  rw [← sub_div,← Finset.sum_sub_distrib]
  apply h.trans
  unfold spatialSq
  calc
    _ ≤ (∑ i, 2*((x i-u i)^2+(y i-v i)^2))/(N:ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hpt i)) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

/-- A target contraction change costs only the single-path marginal spatial
change. This is uniform over the entire target shape and does NOT assume
regularity of a union with any old tree. -/
theorem coupled_projection_change_l2 (S : PrescribedTree n) (T : KernelTower Ω n)
    (a b : S.Leaf) (X Y : FinitePath Ω n → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) :
    (S.sampleLaw T).l2 (fun z => FiniteLaw.dot (X (S.pathAt a z)) (X (S.pathAt b z))-
      FiniteLaw.dot (Y (S.pathAt a z)) (Y (S.pathAt b z))) ≤
      2*Real.sqrt ((KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))) := by
  let E := (KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))
  have hn : 0≤E := FiniteLaw.expect_nonneg _ (fun x => FiniteLaw.spatialSq_nonneg _)
  have h := (S.sampleLaw T).expect_mono (fun z => FiniteLaw.dot_pair_change_sq
    (X (S.pathAt a z)) (X (S.pathAt b z)) (Y (S.pathAt a z)) (Y (S.pathAt b z))
    (hX _) (hX _) (hY _) (hY _))
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul_left,FiniteLaw.expect_mul_left,
    leaf_marginal S T a (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i)),
    leaf_marginal S T b (fun x => FiniteLaw.spatialSq (fun i => X x i-Y x i))] at h
  unfold FiniteLaw.l2
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow,Real.sq_sqrt hn]
    change _ ≤ 2*E+2*E at h
    nlinarith [h]

omit [Fintype I] [DecidableEq I] in
/-- The full target matrix error splits into its genuine proper-child
projection and a shape-independent single-path coupled comparison. -/
theorem matrixProjectionError_change_spatial (S : PrescribedTree n) (q : I → S.Leaf)
    (T : KernelTower Ω n) (a c : I) (A : (I → FinitePath Ω n) → ℝ)
    (X Y : FinitePath Ω n → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) (hY : ∀ x i, |Y x i|≤1) :
    matrixProjectionError S q T a c A X ≤ matrixProjectionError S q T a c A Y +
      2*Real.sqrt ((KernelTower.law n T).expect (fun x => FiniteLaw.spatialSq (fun i => Y x i-X x i))) :=
  by
  have h := matrixProjectionError_change S q T a c A X Y
  have h2 := coupled_projection_change_l2 S T (q a) (q c) Y X hY hX
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PrefixProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [Fintype Ω] in
lemma treeOverlap_bound (S : PrescribedTree n) (f : FinitePath Ω n → Fin N → ℝ)
    (hf : ∀ x i, |f x i| ≤ 1) (z : Sample Ω S) : |treeOverlap S f z| ≤ 1 := by
  unfold treeOverlap
  have h := FiniteLaw.abs_dot_le_one (fun i => leafProduct S (fun x => f x i) z)
    (fun _ => (1:ℝ)) (fun i => leafProduct_bound S (fun x => hf x i) z) (fun _ => by norm_num)
  simpa only [FiniteLaw.dot,mul_one] using h

omit [Fintype Ω] in
lemma treeOverlap_unary (S : PrescribedTree n) (f : FinitePath Ω (n+1) → Fin N → ℝ)
    (z : Sample Ω (unary S)) :
    treeOverlap (unary S) f z=treeOverlap S (fun y => f ((z 0).1,y)) (z 0).2 := by
  simp only [treeOverlap,leafProduct_unary]

lemma descendantEnergyAt_nonneg (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    0 ≤ descendantEnergyAt C r d T f := by
  induction d with
  | zero => exact shapeEnergyAt_nonneg C (r+1) T f
  | succ d ih => exact T.1.expect_nonneg (fun x => ih (T.2 x) (fun y => f (x,y)))

/-- Exact identification of the old error in the signed identity with the
conditional two-copy error of the whole multileaf shape, at arbitrary d. -/
lemma oldProjectionError_prefixed_sq (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (f X : FinitePath Ω (n+1+d) → Fin N → ℝ) :
    (oldProjectionError (stem (doubled S) d) T (stemLeaf (doubled S) d ⟨0,a⟩)
      (stemLeaf (doubled S) d ⟨1,a⟩) (treeOverlap (stem (doubled S) d) f) X)^2 =
      shapeProjectionSqAt S a d T f X := by
  induction d with
  | zero =>
    have h := oldProjectionError_doubled_sq S a T f X
    have he : doubledOverlap S f=treeOverlap (doubled S) f := funext (doubledOverlap_eq S f)
    rw [he] at h
    exact h
  | succ d ih =>
    rw [oldProjectionError,FiniteLaw.l2_sq]
    let F := fun z : Ω × Sample Ω (stem (doubled S) d) =>
      (FiniteLaw.dot (X (z.1, (stem (doubled S) d).pathAt (stemLeaf (doubled S) d ⟨0,a⟩) z.2))
        (X (z.1, (stem (doubled S) d).pathAt (stemLeaf (doubled S) d ⟨1,a⟩) z.2))-
        treeOverlap (stem (doubled S) d) (fun y => f (z.1,y)) z.2)^2
    have he : (sampleLaw (stem (doubled S) (d+1)) T).expect (fun z =>
        (FiniteLaw.dot (X ((stem (doubled S) (d+1)).pathAt (stemLeaf (doubled S) (d+1) ⟨0,a⟩) z))
          (X ((stem (doubled S) (d+1)).pathAt (stemLeaf (doubled S) (d+1) ⟨1,a⟩) z))-
          treeOverlap (stem (doubled S) (d+1)) f z)^2)=
        T.1.expect (fun x => (sampleLaw (stem (doubled S) d) (T.2 x)).expect (fun z => F (x,z))) := by
      refine Eq.trans ?_ (sampleLaw_unary_expect (stem (doubled S) d) T F)
      apply FiniteLaw.expect_congr
      intro z
      dsimp only [F]
      rw [show treeOverlap (stem (doubled S) (d+1)) f z=
        treeOverlap (stem (doubled S) d) (fun y => f ((z 0).1,y)) (z 0).2 from treeOverlap_unary _ f z]
      rfl
    rw [he]
    apply FiniteLaw.expect_congr
    intro x
    have h := ih (T.2 x) (fun y => f (x,y)) (fun y => X (x,y))
    rw [oldProjectionError,FiniteLaw.l2_sq] at h
    exact h

/-- The projection energy uses only proper-child energies even when the
first evaluation depth is not the root. No prefix is discarded. -/
theorem prefixed_stem_projection_sq_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    shapeProjectionSqAt (stem (.node k C) r) (stemLeaf (.node k C) r a) d T f
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
      4*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
  induction d with
  | zero => exact branchProjectionSq_stem_le k C a r T f hf
  | succ d ih =>
    change T.1.expect (fun x => shapeProjectionSqAt (stem (.node k C) r)
      (stemLeaf (.node k C) r a) d (T.2 x) (fun y => f (x,y))
        (fun y i => splitProjector (.node k C) r d (T.2 x) (fun z => f (x,z) i) y)) ≤ _
    have h := T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_fintype_sum] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    exact T.1.expect_sqrt_le _ (fun x => descendantEnergyAt_nonneg (C i) r d (T.2 x) (fun y => f (x,y)))

/-- The exact actual whole-shape covariance with both evaluation and first
split at arbitrary depths, bounded by the full projected three-copy term. -/
theorem prefixed_stem_covariance_three_copy_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    shapeEnergyAt (stem (.node k C) r) d T f ≤
      2*KernelTower.halfTripleDifferenceAt (n+1+r+1+d) T d
        (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x)+
      16*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
  have h := shape_energy_projection_transfer (stem (.node k C) r)
    (stemLeaf (.node k C) r a) d T f
    (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x)
  have he := prefixed_stem_projection_sq_le k C a r d T f hf
  linarith

/-- The L2 old-test error in the prescribed-tree identity, not merely a
projected covariance, now has its explicit proper-child bound. -/
theorem prefixed_stem_old_error_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (a : (PrescribedTree.node k C).Leaf) (r d : ℕ) (T : KernelTower Ω (n+1+r+1+d))
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i| ≤ 1) :
    let S := stem (.node k C) r
    oldProjectionError (stem (doubled S) d) T (stemLeaf (doubled S) d ⟨0,stemLeaf (.node k C) r a⟩)
      (stemLeaf (doubled S) d ⟨1,stemLeaf (.node k C) r a⟩)
      (treeOverlap (stem (doubled S) d) f)
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
      2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by
  dsimp only
  have h := prefixed_stem_projection_sq_le k C a r d T f hf
  rw [← oldProjectionError_prefixed_sq] at h
  have hn : 0 ≤ (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by positivity
  have he : (2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)))^2=
      4*(k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f) := by
    rw [mul_pow,Real.sq_sqrt hn]
    ring
  have hn2 : 0 ≤ 2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by positivity
  nlinarith

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MultileafMatrixPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

lemma splitFrame_split (S : PrescribedTree n) (r d : ℕ) (a : S.Leaf) :
    splitDepth (splitFrame S r d) (splitFrameLeaf S r d 0 a) (splitFrameLeaf S r d 1 a)=d := by
  exact (splitDepth_stem (doubled (stem S r)) d
    ⟨0,stemLeaf S r a⟩ ⟨1,stemLeaf S r a⟩).trans
    (by
      exact (congrArg (fun x => x+d)
        (splitDepth_diff_child (fun _ : Fin (2:ℕ+) => stem S r) 0 1 (by decide)
          (a := stemLeaf S r a) (b := stemLeaf S r a))).trans (Nat.zero_add d))

lemma splitFrame_fresh_split (S : PrescribedTree n) (r d : ℕ) (j : Fin 2) (a : S.Leaf) :
    freshSplitDepth (splitFrame S r d) (splitFrameVertex S r d) (splitFrameLeaf S r d j a)=d := by
  exact (freshSplitDepth_stem (doubled (stem S r)) d none ⟨j,stemLeaf S r a⟩).trans (by exact Nat.zero_add d)

lemma splitFrame_gamma (S : PrescribedTree n) (r d : ℕ) (m : Fin (n+r+1+d+1) → ℝ) :
    gamma (splitFrame S r d) m (splitFrameVertex S r d)=
      m ⟨d,by omega⟩-2*m ⟨d+1,by omega⟩ := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih (fun j => m j.succ)

lemma splitFrame_gamma_grid (S : PrescribedTree n) (r d : ℕ) :
    -gamma (splitFrame S r d) (grid (n+r+1+d) 0 (n+r+1+d)) (splitFrameVertex S r d)=
      ((d:ℝ)+2)/(n+r+1+d:ℕ) := by
  rw [splitFrame_gamma]
  simp only [grid,zero_add,Nat.cast_add,Nat.cast_one]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootMultileafMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n N : ℕ}

omit [DecidableEq I] in
/-- Exact conversion of the color-indexed matrix projection to the old
all-leaf projection error in the SAME sampled tree. -/
lemma matrixProjectionError_treeOverlap (S : PrescribedTree n)
    (q : I → S.Leaf) (hq : Function.Bijective q) (T : KernelTower Ω n)
    (a c : I) (f X : FinitePath Ω n → Fin N → ℝ) :
    matrixProjectionError S q T a c (spatialProduct (fun _ : I => f)) X=
      oldProjectionError S T (q a) (q c) (treeOverlap S f) X := by
  unfold matrixProjectionError oldProjectionError FiniteLaw.l2
  congr 1
  apply FiniteLaw.expect_congr
  intro z
  have he := spatialProduct_leafProduct S q hq f z
  change spatialProduct (fun _ : I => f) (fun j => S.pathAt (q j) z)=treeOverlap S f z at he
  dsimp only
  rw [he]
  exact sub_sq_comm _ _

omit [DecidableEq I] in
/-- The target's actual own-projector error, for arbitrary initial prefix
and later first split, is controlled only by genuine proper children. -/
theorem matrixProjectionError_prefixed_le (k : ℕ+) (C : Fin k → PrescribedTree n)
    (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (q : I → (splitFrame (.node k C) r d).Leaf) (hq : Function.Bijective q)
    (T : KernelTower Ω (n+1+r+1+d)) (a c : I)
    (ha : q a=splitFrameLeaf (.node k C) r d 0 b)
    (hc : q c=splitFrameLeaf (.node k C) r d 1 b)
    (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    matrixProjectionError (splitFrame (.node k C) r d) q T a c
      (spatialProduct (fun _ : I => f))
      (fun x i => splitProjector (.node k C) r d T (fun y => f y i) x) ≤
       2*Real.sqrt ((k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d T f)) := by
  rw [matrixProjectionError_treeOverlap _ q hq T a c,ha,hc]
  exact prefixed_stem_old_error_le k C b r d T f hf

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

/-- The entire multileaf covariance, after averaging the genuine root law,
is controlled by the SAME signed centered matrix history and the literal
proper-child covariances. No conditional concentration is assumed. -/
theorem root_multileaf_matrix {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (k : ℕ+) (C : Fin k → PrescribedTree n) (b : (PrescribedTree.node k C).Leaf) (r d : ℕ)
    (Target : PrescribedTree (n+1+r+1+d)) (q : I → Target.Leaf) (hq : Function.Bijective q)
    (Q : Finset ℕ) (hS : branchingCount (splitFrame (.node k C) r d) (· ∈ Q)=0)
    (K : (z : Z) → KernelTower (Ω z) (n+1+r+1+d)) (a c : I) (hac : a≠c)
    (cs : List I) (hcs : cs.Nodup) (hdis : ∀ j ∈ cs, j ∉ insert c ({a}:Finset I))
    (hfull : insert c ({a}:Finset I) ∪ cs.toFinset=Finset.univ)
    (hqd : splitDepth Target (q a) (q c)=d)
    (f : (z : Z) → FinitePath (Ω z) (n+1+r+1+d) → Fin N → ℝ) (hf : ∀ z x i, |f z x i| ≤ 1) :
    let L := n+1+r+1+d
    let S := splitFrame (.node k C) r d
    let x := splitFrameLeaf (.node k C) r d 0 b
    let y := splitFrameLeaf (.node k C) r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert c ({a}:Finset I)).image q)
    let X := fun z x i => splitProjector (.node k C) r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    let W := fun z => (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d (K z) (f z))
    Integrable (fun z => shapeEnergyAt (stem (.node k C) r) d (K z) (f z)) μ →
    Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
    Integrable (fun z => matrixObservableHistory Target q (K z) m (c::cs) S x (A z) (treeOverlap S (f z))) μ →
    Integrable (fun z => matrixProjectionError Target q (K z) a c (A z) (X z)) μ →
    Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
    Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
    Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
        (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  let L := n+1+r+1+d
  let S := splitFrame (.node k C) r d
  let x := splitFrameLeaf (.node k C) r d 0 b
  let y := splitFrameLeaf (.node k C) r d 1 b
  let v := splitFrameVertex (.node k C) r d
  let m := grid L 0 L
  let J := partialKappa Target m (Finset.univ.image q)/
    partialKappa Target m ((insert c ({a}:Finset I)).image q)
  let X := fun z x i => splitProjector (.node k C) r d (K z) (fun y => f z y i) x
  let A := fun z => spatialProduct (fun _ : I => f z)
  let W := fun z => (k:ℝ)*∑ i, Real.sqrt (descendantEnergyAt (C i) r d (K z) (f z))
  intro hV hT hH hEt hEo hMean hW hSqrtW
  have hL : 0<L := by dsimp [L]; omega
  have hd : d<L := by dsimp [L]; omega
  have h := root_matrix_three_copy μ Ω hL Q Target S q hq hS K a c hac cs hcs hdis hfull
    x y v d hd hqd (splitFrame_split (.node k C) r d b)
    (splitFrame_fresh_split (.node k C) r d 0 b) (splitFrame_fresh_split (.node k C) r d 1 b)
    X (fun z w i => splitProjector_bound (.node k C) r d (K z) (fun w => f z w i)
      (fun w => hf z w i) w)
    (fun z w hz t => stem_doubled_projector_old_side (.node k C) r d
      (stemLeaf (.node k C) r b) (stemLeaf (.node k C) r b) (K z) (f z) w hz t)
    A (fun z w => spatialProduct_bound (fun _ : I => f z) (fun _ => hf z) w)
    (fun z => treeOverlap S (f z)) (fun z => treeOverlap_bound S (f z) (hf z))
    hT hH hEt hEo hMean
  dsimp only at h
  have hv : (∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
      2*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ)+16*(∫ z, W z ∂μ) := by
    have hh := integral_mono hV ((hT.const_mul 2).add (hW.const_mul 16)) (fun z =>
      (prefixed_stem_covariance_three_copy_le k C b r d (K z) (f z) (hf z)).trans_eq (by dsimp [W]; ring))
    simp only [Pi.add_apply] at hh
    rw [integral_add (hT.const_mul 2) (hW.const_mul 16),integral_const_mul,integral_const_mul] at hh
    exact hh
  have ho : (∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) ≤
      2*(∫ z, Real.sqrt (W z) ∂μ) := by
    have hh := integral_mono hEo (hSqrtW.const_mul 2) (fun z =>
      prefixed_stem_old_error_le k C b r d (K z) (f z) (hf z))
    rw [integral_const_mul] at hh
    exact hh
  have hc0 : 0 ≤ ((d:ℝ)+2)/(L:ℝ) := by positivity
  have hv' := mul_le_mul_of_nonneg_left hv hc0
  have hmass : 0 ≤ pairHistoryMass S m x := by unfold pairHistoryMass; positivity
  have ho' := mul_le_mul_of_nonneg_left ho hmass
  have hg : -gamma S m v=((d:ℝ)+2)/(L:ℝ) := splitFrame_gamma_grid (.node k C) r d
  have hdelta : m ⟨d+1,by omega⟩-m ⟨d,by omega⟩=(L:ℝ)⁻¹ := by
    dsimp [m,grid]
    push_cast
    ring
  change (-gamma S m v)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
    2*(m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)+
    |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
    (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|+
    pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) at h
  rw [hg,hdelta] at h
  let B := 2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (c::cs) x A (fun z => treeOverlap S (f z))|/|J|+
    (∫ z, matrixProjectionError Target q (K z) a c (A z) (X z) ∂μ)*shiftedCharge Q Target S (c::cs).length/|J|
  change ((d:ℝ)+2)/(L:ℝ)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ) ≤
    B+pairHistoryMass S m x*(∫ z, oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z) ∂μ) at h
  have hh := h.trans (add_le_add le_rfl ho')
  change ((d:ℝ)+2)/(L:ℝ)*(∫ z, shapeEnergyAt (stem (.node k C) r) d (K z) (f z) ∂μ) ≤
    2*(B+pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+((d:ℝ)+2)/(L:ℝ)*(16*(∫ z, W z ∂μ))
  calc
    _ ≤ ((d:ℝ)+2)/(L:ℝ)*(2*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ)+16*(∫ z, W z ∂μ)) := hv'
    _ = 2*(((d:ℝ)+2)/(L:ℝ)*(∫ z, KernelTower.halfTripleDifferenceAt L (K z) d (X z) ∂μ))+
        ((d:ℝ)+2)/(L:ℝ)*(16*(∫ z, W z ∂μ)) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num)) le_rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProperChildScheduleContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- Exact proper-child factorization of the conditional first-split mean;
the unary child transition is retained, not erased. -/
lemma tailMean_node_product (k : ℕ+) (C : Fin k → PrescribedTree n) (p : ℕ)
    (T : KernelTower Ω (n+1+p)) (f : FinitePath Ω (n+1+p) → ℝ)
    (x : FinitePath Ω (n+1+p)) :
    tailMean (.node k C) p T f x=∏ j, tailMean (unary (C j)) p T f x := by
  induction p with
  | zero => simp only [tailMean,treeMean,treeMean_unary]
  | succ p ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) x.2

/-- The projector used in the signed multileaf matrix identity is literally
the product of proper-child conditional means on the SAME sampled prefix. -/
lemma splitProjector_node_product (k : ℕ+) (C : Fin k → PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → ℝ)
    (x : FinitePath Ω (n+1+r+1+d)) :
    splitProjector (.node k C) r d T f x=∏ j, splitProjector (unary (C j)) r d T f x := by
  induction d with
  | zero => exact tailMean_node_product k C (r+1) T f x
  | succ d ih => exact ih (T.2 x.1) (fun y => f (x.1,y)) x.2

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ConditionalScheduledMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma conditionalScheduledMean_zero (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (x : FinitePath Ω H) :
    conditionalScheduledMean H d 0 S q T f x=PrescribedTree.treeMean (realize H d S q) T f := by
  cases H <;> rfl

lemma conditionalScheduledMean_bound (H d e : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x|≤1) (x : FinitePath Ω H) :
    |conditionalScheduledMean H d e S q T f x|≤1 := by
  induction H generalizing d e with
  | zero => exact PrescribedTree.treeMean_bound .leaf T hf
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.treeMean_bound _ T hf
    | succ e => exact ih (d+1) e (T.2 x.1) (fun y => f (x.1,y)) (fun y => hf (x.1,y)) x.2

/-- Exact tail-projector geometry, with the original prefix retained. -/
lemma conditionalScheduledMean_eq_tail (H p d : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → ℝ)
    (x : FinitePath Ω (H+p)) :
    conditionalScheduledMean (H+p) d p S q T f x=
      PrescribedTree.tailMean (realize H (d+p) S q) p T f x := by
  induction p generalizing d with
  | zero => exact conditionalScheduledMean_zero H d S q T f x
  | succ p ih =>
    change conditionalScheduledMean (H+p) (d+1) p S q (T.2 x.1) (fun y => f (x.1,y)) x.2=_
    have h := ih (d+1) (T.2 x.1) (fun y => f (x.1,y)) x.2
    simpa only [PrescribedTree.tailMean,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

lemma conditionalScheduledProduct_bound {ι : Type*} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (f : FinitePath Ω H → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (x : FinitePath Ω H) (i : Fin N) : |conditionalScheduledProduct H d e C q T f x i|≤1 := by
  unfold conditionalScheduledProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ =>
    conditionalScheduledMean_bound H d e (C j) (q j) T (fun y => f y i) (fun y => hf y i) x)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FirstSplitSchedule
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma realize_unary_of_later (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d<q v) :
    realize (H+1) d S q=PrescribedTree.unary (realize H (d+1) S q) := by
  cases S with
  | leaf => rfl
  | node k hk C => rw [realize,ite_eq_left (hq none)]

/-- Literal identification with the old/target projector in the matrix
identity, at arbitrary initial evaluation prefix and later first split. -/
lemma conditionalScheduledMean_eq_splitProjector (H r d a : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω (H+r+1+d))
    (f : FinitePath Ω (H+r+1+d) → ℝ) (x : FinitePath Ω (H+r+1+d)) :
    conditionalScheduledMean (H+r+1+d) a (r+1+d) S q T f x=
      PrescribedTree.splitProjector (realize H (a+(r+1+d)) S q) r d T f x := by
  induction d generalizing a with
  | zero => exact conditionalScheduledMean_eq_tail H (r+1) a S q T f x
  | succ d ih =>
    change conditionalScheduledMean (H+r+1+d) (a+1) (r+1+d) S q
      (T.2 x.1) (fun y => f (x.1,y)) x.2=_
    have h := ih (a+1) (T.2 x.1) (fun y => f (x.1,y)) x.2
    simpa only [PrescribedTree.splitProjector,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The actual first-split projector in the matrix observable is precisely
the scheduled conditional child product. This applies to the old or delayed
target schedule separately, without altering any branching assignment. -/
theorem scheduled_splitProjector_product (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+1+d<q j v) (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) :
    (fun x i => PrescribedTree.splitProjector
      (realize (H+1) (r+1+d) (.node k hk C) (rootSchedule (r+1+d) q)) r d T (fun y => f y i) x)=
      conditionalScheduledProduct (H+1+r+1+d) 0 (r+1+d) C q T f := by
  funext x i
  simp only [realize,rootSchedule,lt_self_iff_false,ite_false]
  rw [PrescribedTree.splitProjector_node_product]
  unfold conditionalScheduledProduct
  apply Finset.prod_congr rfl
  intro j _
  have h := conditionalScheduledMean_eq_splitProjector (H+1) r d 0 (C j) (q j) T (fun y => f y i) x
  rw [Nat.zero_add,realize_unary_of_later H (r+1+d) (C j) (q j) (hq j)] at h
  exact h.symm

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalPairConnection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PrescribedTree ConcreteReservoir
open scoped NNReal BigOperators
variable {Ω X Y : Type} [Fintype Ω] [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Fintype Ω] in
lemma readVector_bound (read : Site N → FinitePath Ω (L+1) → Spin) (x) (i) :
    |readVector read x i| ≤ 1 := by simp only [readVector,abs_spin,le_refl]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullCubeConditionalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p : ℕ}

lemma gridExponents_cons (L : ℕ) :
    Fin.cons 0 (gridExponents L) = grid (L+1) 0 (L+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [grid]
  · simp [grid,gridExponents,Fin.val_succ]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProjectionShiftError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]


omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_nonneg (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (Q : α → Fin L) :
    0≤projectionShiftError a C e T f Q := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- The universal shift error is valid in the literal matrix projection
error, before taking signed histories or any physical-root expectation. -/
theorem matrixProjectionError_shift_le {I : Type} [Fintype I] [DecidableEq I]
    (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Q : α → Fin L) (Target : PrescribedTree L) (q : I → Target.Leaf) (u v : I)
    (A : (I → FinitePath Ω L) → ℝ) :
    PrescribedTree.matrixProjectionError Target q T u v A
      (conditionalScheduledProduct L 0 (Q a).val C (fun j w => (Q (e j w)).val) T f) ≤
    PrescribedTree.matrixProjectionError Target q T u v A
      (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j w => (Q (e j w)).val+1) T f)+
      projectionShiftError a C e T f Q := by
  have h := PrescribedTree.matrixProjectionError_change_spatial Target q T u v A
    (conditionalScheduledProduct L 0 (Q a).val C (fun j w => (Q (e j w)).val) T f)
    (conditionalScheduledProduct L 0 ((Q a).val+1) C (fun j w => (Q (e j w)).val+1) T f)
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)
    (conditionalScheduledProduct_bound L 0 _ C _ T f hf)
  exact h

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionShiftError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}

/-- The actual delayed target's own projection is the shifted scheduled
proper-child product. No identification of independent pairs of assignments. -/
lemma delayed_target_projector (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+d+1≤q j v)
    (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) :
    (fun x i => PrescribedTree.splitProjector
      (.node k (fun j => realize H (r+1+d+1) (C j) (fun v => q j v+1)))
      r d T (fun y => f y i) x)=
    conditionalScheduledProduct (H+1+r+1+d) 0 (r+1+d) C (fun j v => q j v+1) T f := by
  have h := scheduled_splitProjector_product H r d k hk C (fun j v => q j v+1)
    (fun j v => by have := hq j v; omega) T f
  simpa only [realize,rootSchedule,lt_self_iff_false,ite_false] using h

omit [Fintype α] [DecidableEq α] in
/-- Bound the literal target error in the signed matrix identity by proper
children and the ONE extension-uniform h_N on the SAME full depth cube.
Target leaf labels may be any bijective spatial-multioverlap enumeration. -/
theorem delayed_target_projection_le (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+r+1+d)) (ha : (Q a).val=r+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+r+1+d))
    (f : FinitePath Ω (H+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    let Child := fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let S := PrescribedTree.node k Child
    let Target := PrescribedTree.splitFrame S r d
    ∀ (b : S.Leaf) (q : I → Target.Leaf), Function.Bijective q →
      ∀ (u v : I), q u=PrescribedTree.splitFrameLeaf S r d 0 b →
        q v=PrescribedTree.splitFrameLeaf S r d 1 b →
    PrescribedTree.matrixProjectionError Target q T u v
      (PrescribedTree.spatialProduct (fun _ : I => f))
      (conditionalScheduledProduct (H+1+r+1+d) 0 (Q a).val C
        (fun j w => (Q (e j w)).val) T f) ≤
      2*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (PrescribedTree.descendantEnergyAt (Child j) r d T f))+
        projectionShiftError a C e T f Q := by
  dsimp only
  intro b q hq u v hu hv
  let Child := fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let S := PrescribedTree.node k Child
  let Target := PrescribedTree.splitFrame S r d
  have hp := delayed_target_projector H r d k hk C (fun j w => (Q (e j w)).val)
    (fun j w => by rw [← ha]; exact hQ j w) T f
  have hown := PrescribedTree.matrixProjectionError_prefixed_le k Child b r d q hq T u v hu hv f hf
  change (fun x i => PrescribedTree.splitProjector S r d T (fun y => f y i) x)=_ at hp
  rw [hp] at hown
  have hdepth : r+1+d=(Q a).val+1 := by omega
  rw [hdepth] at hown
  let : NeZero (H+1+r+1+d) := ⟨by omega⟩
  exact (matrixProjectionError_shift_le a C e T f hf Q Target q u v
    (PrescribedTree.spatialProduct (fun _ : I => f))).trans (add_le_add hown le_rfl)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeightTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass

namespace PrescribedTree
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I] {n m N : ℕ}

lemma leafHeightCast_bijective (h : n=m) (S : PrescribedTree n) :
    Function.Bijective (leafHeightCast h S) := by cases h; exact Function.bijective_id

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableProjector
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z]

omit [Fintype Ω] in
lemma measurable_leafProduct {n : ℕ} (S : PrescribedTree n)
    {g : Z → FinitePath Ω n → ℝ} (hg : ∀ y, Measurable (fun z => g z y))
    (a : S.Sample Ω) : Measurable (fun z => leafProduct S (g z) a) := by
  simp_rw [leafProduct_eq_prod]
  exact Finset.measurable_prod _ (fun b _ => hg _)

lemma measurable_treeMean_tilt {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin n → ℝ) {f g : Z → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y)) :
    Measurable (fun z => treeMean S (KernelTower.tilt n T m (f z)) (g z)) := by
  simp_rw [treeMean_eq_expect]
  exact measurable_tilt_sample_expect S T m hf (measurable_leafProduct S hg)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_conditionalScheduledMean_tilt (H d e : ℕ) (S : ReducedTopology)
    (q : S.Vertex → ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f g : Z → FinitePath Ω H → ℝ} (hf : ∀ y, Measurable (fun z => f z y))
    (hg : ∀ y, Measurable (fun z => g z y)) (x : FinitePath Ω H) :
    Measurable (fun z => conditionalScheduledMean H d e S q (KernelTower.tilt H T m (f z)) (g z) x) := by
  induction H generalizing d e with
  | zero => exact hg ()
  | succ H ih =>
    cases e with
    | zero => exact PrescribedTree.measurable_treeMean_tilt _ T m hf hg
    | succ e =>
        exact ih (d+1) e (T.2 x.1) (fun j => m j.succ)
          (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

lemma measurable_conditionalScheduledProduct_tilt {ι : Type} [Fintype ι]
    (H d e : ℕ) (C : ι → ReducedTopology) (q : (j : ι) → (C j).Vertex → ℕ)
    (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {g : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (x : FinitePath Ω H) (i : Fin N) :
    Measurable (fun z => conditionalScheduledProduct H d e C q (KernelTower.tilt H T m (f z)) (g z) x i) := by
  unfold conditionalScheduledProduct
  exact Finset.measurable_prod _ (fun j _ =>
    measurable_conditionalScheduledMean_tilt H d e (C j) (q j) T m hf (fun y => hg y i) x)

lemma measurable_projectorChangeSq_tilt (H : ℕ) (T : KernelTower Ω H) (m : Fin H → ℝ)
    {f : Z → FinitePath Ω H → ℝ} {X Y : Z → FinitePath Ω H → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i))
    (hY : ∀ y i, Measurable (fun z => Y z y i)) :
    Measurable (fun z => projectorChangeSq (KernelTower.tilt H T m (f z)) (X z) (Y z)) := by
  apply KernelTower.measurable_path_expect H T m hf
  intro y
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => ((hX y i).sub (hY y i)).pow_const 2)

lemma projectorChangeSq_le_four {H : ℕ} (T : KernelTower Ω H)
    (X Y : FinitePath Ω H → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) (hY : ∀ y i, |Y y i|≤1) : projectorChangeSq T X Y≤4 := by
  apply ((KernelTower.law H T).expect_mono (fun y => show FiniteLaw.spatialSq (fun i => X y i-Y y i)≤4 from ?_)).trans_eq
    ((KernelTower.law H T).expect_const 4)
  by_cases hN : N=0
  · simp [FiniteLaw.spatialSq,hN]
  · unfold FiniteLaw.spatialSq
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
    calc
      _ ≤ ∑ _ : Fin N, (4:ℝ) := Finset.sum_le_sum (fun i _ => by
        have hx := abs_le.mp (hX y i)
        have hy := abs_le.mp (hY y i)
        nlinarith [sq_nonneg (2-(X y i-Y y i)),sq_nonneg (2+(X y i-Y y i)),
          mul_nonneg (show 0≤2-(X y i-Y y i) by linarith) (show 0≤2+(X y i-Y y i) by linarith)])
      _ = _ := by simp; ring

variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] {L : ℕ} [NeZero L]

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma measurable_projectionShiftError_tilt (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : Z → FinitePath Ω L → ℝ} {g : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y i, Measurable (fun z => g z y i))
    (Q : α → Fin L) :
    Measurable (fun z => projectionShiftError a C e (KernelTower.tilt L T m (f z)) (g z) Q) := by
  unfold projectionShiftError
  apply Measurable.const_mul
  apply Measurable.sqrt
  exact measurable_projectorChangeSq_tilt L T m hf
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)
    (measurable_conditionalScheduledProduct_tilt L 0 _ C _ T m hf hg)

omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma projectionShiftError_le_four (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ)
    (hf : ∀ y i, |f y i|≤1) (Q : α → Fin L) : projectionShiftError a C e T f Q≤4 := by
  have h := projectorChangeSq_le_four T _ _
    (conditionalScheduledProduct_bound L 0 ((Q a).val+1) C
      (fun j v => (Q (e j v)).val+1) T f hf)
    (conditionalScheduledProduct_bound L 0 (Q a).val C
      (fun j v => (Q (e j v)).val) T f hf)
  have h' := Real.sqrt_le_sqrt h
  norm_num at h'
  unfold projectionShiftError
  linarith

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableShapeEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma covarianceEnergy_le_four (P : FiniteLaw Ω) (X : Ω → Fin N → ℝ)
    (hX : ∀ x i, |X x i|≤1) : P.covarianceEnergy X≤4 := by
  by_cases hN : N=0
  · simp [covarianceEnergy,hN]
  · have hpos : 0<(N:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    unfold covarianceEnergy
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, (4:ℝ) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        have h1 : |P.expect (fun x => X x i*X x j)|≤1 := P.abs_expect_le (fun x => by
          rw [abs_mul]; exact (mul_le_mul (hX x i) (hX x j) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
        have h2 : |P.expect (fun x => X x i)*P.expect (fun x => X x j)|≤1 := by
          rw [abs_mul]
          exact (mul_le_mul (P.abs_expect_le (fun x => hX x i)) (P.abs_expect_le (fun x => hX x j))
            (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
        have h : |P.covariance (fun x => X x i) (fun x => X x j)|≤2 := by
          exact (abs_sub _ _).trans (by linarith)
        have hs := sq_le_sq.mpr (show |P.covariance (fun x => X x i) (fun x => X x j)|≤|(2:ℝ)| by simpa using h)
        norm_num at hs
        exact hs
      _ = _ := by simp; ring

end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {n N : ℕ}

lemma measurable_child_expect_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {g : Z → Ω × C.Sample Ω → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ a, Measurable (fun z => g z a)) :
    Measurable (fun z => ((KernelTower.tilt (n+1) T m (f z)).1.bind
      (fun a => C.sampleLaw ((KernelTower.tilt (n+1) T m (f z)).2 a))).expect (g z)) := by
  simp_rw [FiniteLaw.expect_bind]
  apply T.1.measurable_tilt_expect (m 0)
  · intro a
    exact KernelTower.measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
  · intro a
    exact measurable_tilt_sample_expect C (T.2 a) (fun j => m j.succ)
      (fun y => hf (a,y)) (fun y => hg (a,y))

lemma measurable_childEnergy_tilt (C : PrescribedTree n) (T : KernelTower Ω (n+1))
    (m : Fin (n+1) → ℝ) {f : Z → FinitePath Ω (n+1) → ℝ}
    {X : Z → FinitePath Ω (n+1) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => childEnergy C (KernelTower.tilt (n+1) T m (f z)) (X z)) := by
  have hY (a : Ω × C.Sample Ω) (i : Fin N) :
      Measurable (fun z => C.leafProduct (fun y => X z (a.1,y) i) a.2) :=
    measurable_leafProduct C (fun y => hX (a.1,y) i) a.2
  unfold childEnergy FiniteLaw.covarianceEnergy FiniteLaw.covariance
  apply Measurable.div_const
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  exact (measurable_child_expect_tilt C T m hf (fun a => (hY a i).mul (hY a j))).sub
    ((measurable_child_expect_tilt C T m hf (fun a => hY a i)).mul
      (measurable_child_expect_tilt C T m hf (fun a => hY a j)))

lemma measurable_shapeEnergyAt_tilt (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (m : Fin (n+1+d) → ℝ)
    {f : Z → FinitePath Ω (n+1+d) → ℝ} {X : Z → FinitePath Ω (n+1+d) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => shapeEnergyAt C d (KernelTower.tilt (n+1+d) T m (f z)) (X z)) := by
  induction d with
  | zero => exact measurable_childEnergy_tilt C T m hf hX
  | succ d ih =>
    apply T.1.measurable_tilt_expect (m 0)
    · intro a
      exact KernelTower.measurable_backwardLog (n+1+d) (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma shapeEnergyAt_le_four (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (X : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : shapeEnergyAt C d T X≤4 := by
  induction d with
  | zero =>
      unfold shapeEnergyAt childEnergy
      apply FiniteLaw.covarianceEnergy_le_four
      intro a i
      exact leafProduct_bound C (fun y => hX (a.1,y) i) a.2
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 4)

lemma measurable_descendantEnergyAt_tilt (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (m : Fin (n+1+r+1+d) → ℝ)
    {f : Z → FinitePath Ω (n+1+r+1+d) → ℝ} {X : Z → FinitePath Ω (n+1+r+1+d) → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => descendantEnergyAt C r d (KernelTower.tilt (n+1+r+1+d) T m (f z)) (X z)) := by
  induction d with
  | zero => exact measurable_shapeEnergyAt_tilt C (r+1) T m hf hX
  | succ d ih =>
    apply T.1.measurable_tilt_expect (m 0)
    · intro a
      exact KernelTower.measurable_backwardLog (n+1+r+1+d) (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
    · intro a
      exact ih (T.2 a) (fun j => m j.succ) (fun y => hf (a,y)) (fun y i => hX (a,y) i)

lemma descendantEnergyAt_le_four (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (X : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ)
    (hX : ∀ y i, |X y i|≤1) : descendantEnergyAt C r d T X≤4 := by
  induction d with
  | zero => exact shapeEnergyAt_le_four C (r+1) T X hX
  | succ d ih =>
      exact (T.1.expect_mono (fun a => ih (T.2 a) (fun y => X (a,y))
        (fun y i => hX (a,y) i))).trans_eq (T.1.expect_const 4)

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootShapeEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n : ℕ}

section Shape
variable (C : PrescribedTree n) (d : ℕ)
    (T : KernelTower Ω (n+1+d)) (Q : (i : I) → Fin (n+1+d) → FiniteLaw (A i))
    (m : Fin (n+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+d) → FinitePath (A i) (n+1+d) → ℝ)
    (V : FinitePath Ω (n+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootShapeEnergy : Measurable (fun z : FullRootState Y X I M =>
    shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) := by
  change Measurable (packRoot (fun h k x n y =>
    shapeEnergyAt C d (KernelTower.tilt _ (tower (rootArray n y) _ T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) _ w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_shapeEnergyAt_tilt C d (tower (rootArray n y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
lemma integrable_rootShapeEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      shapeEnergyAt C d (rootTower T Q m base old z) (rootVector V z)) μ := by
  apply Integrable.of_bound (measurable_rootShapeEnergy C d T Q m base old V hb).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (shapeEnergyAt_nonneg C d _ _)]
  exact shapeEnergyAt_le_four C d _ _ (fun y i => hV _ i)
end Shape

section Child
variable (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (Q : (i : I) → Fin (n+1+r+1+d) → FiniteLaw (A i))
    (m : Fin (n+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+1+r+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+1+r+1+d) → FinitePath (A i) (n+1+r+1+d) → ℝ)
    (V : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootDescendantEnergy : Measurable (fun z : FullRootState Y X I M =>
    descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z)) := by
  change Measurable (packRoot (fun h k x n y =>
    descendantEnergyAt C r d (KernelTower.tilt _ (tower (rootArray n y) _ T Q) m
      (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) _ w))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_descendantEnergyAt_tilt C r d (tower (rootArray n y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
lemma integrable_rootDescendantEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z)) μ := by
  apply Integrable.of_bound (measurable_rootDescendantEnergy C r d T Q m base old V hb).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (descendantEnergyAt_nonneg C r d _ _)]
  exact descendantEnergyAt_le_four C r d _ _ (fun y i => hV _ i)

include hb in
lemma integrable_sqrt_rootDescendantEnergy (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
      Real.sqrt (descendantEnergyAt C r d (rootTower T Q m base old z) (rootVector V z))) μ := by
  apply Integrable.of_bound (measurable_rootDescendantEnergy C r d T Q m base old V hb).sqrt.aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := Real.sqrt_le_sqrt (descendantEnergyAt_le_four C r d
    (rootTower T Q m base old z) (rootVector V z) (fun y i => hV _ i))
  norm_num at h
  exact h
end Child

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootChildSumIntegrability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

lemma measurable_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y)) :
    Measurable (fun z : FullRootState Y X I M => descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) := by
  subst L
  exact measurable_rootDescendantEnergy C r d T Q m base old V hb

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootChildSum : Measurable (rootChildSum k C r d h T Q m base old V) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb).sqrt)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootChildSum_nonneg (z : FullRootState Y X I M) :
    0 ≤ rootChildSum k C r d h T Q m base old V z := by
  unfold rootChildSum
  positivity

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootChildSum_bound (hV : ∀ x i, |V x i|≤1) (z : FullRootState Y X I M) :
    rootChildSum k C r d h T Q m base old V z ≤ 2*(k:ℝ)^2 := by
  have he (j : Fin k) : Real.sqrt (descendantEnergyAt (C j) r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) ≤ 2 := by
    have hb := Real.sqrt_le_sqrt (descendantEnergyAt_le_four (C j) r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))
       (fun _ index => hV _ index))
    norm_num at hb
    exact hb
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun j _ => he j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  unfold rootChildSum
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) k)
  nlinarith

include hb in
lemma integrable_rootChildSum (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ x i, |V x i|≤1) : Integrable (rootChildSum k C r d h T Q m base old V) μ := by
  apply Integrable.of_bound (measurable_rootChildSum k C r d h T Q m base old V hb).aestronglyMeasurable
    (2*(k:ℝ)^2)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (rootChildSum_nonneg k C r d h T Q m base old V z)]
  exact rootChildSum_bound k C r d h T Q m base old V hV z

include hb in
lemma integrable_sqrt_rootChildSum (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ x i, |V x i|≤1) : Integrable (fun z => Real.sqrt (rootChildSum k C r d h T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootChildSum k C r d h T Q m base old V hb).sqrt.aestronglyMeasurable
    (Real.sqrt (2*(k:ℝ)^2))
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (rootChildSum_bound k C r d h T Q m base old V hV z)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MeasurableProjectionError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {N : ℕ}
lemma measurable_dot {X Y : Z → Fin N → ℝ}
    (hX : ∀ i, Measurable (fun z => X z i)) (hY : ∀ i, Measurable (fun z => Y z i)) :
    Measurable (fun z => dot (X z) (Y z)) := by
  exact (Finset.measurable_sum _ (fun i _ => (hX i).mul (hY i))).div_const _

lemma l2_le_two {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ x, |f x|≤2) : P.l2 f≤2 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  exact (P.expect_mono (fun x => sq_le_sq.mpr (show |f x|≤|(2:ℝ)| by simpa using hf x))).trans_eq
    (P.expect_const _)
end DilutedSpinGlass.FiniteLaw
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z C : Type} [Fintype Ω] [MeasurableSpace Z] [Fintype C] [DecidableEq C] {n L N : ℕ}

lemma measurable_tailMean_tilt (S : PrescribedTree n) (r : ℕ)
    (T : KernelTower Ω (n+r)) (m : Fin (n+r) → ℝ)
    {f g : Z → FinitePath Ω (n+r) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (x : FinitePath Ω (n+r)) :
    Measurable (fun z => tailMean S r (KernelTower.tilt (n+r) T m (f z)) (g z) x) := by
  induction r with
  | zero => exact measurable_treeMean_tilt S T m hf hg
  | succ r ih =>
      exact ih (T.2 x.1) (fun j => m j.succ) (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

lemma measurable_splitProjector_tilt (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (m : Fin (n+r+1+d) → ℝ)
    {f g : Z → FinitePath Ω (n+r+1+d) → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (x : FinitePath Ω (n+r+1+d)) :
    Measurable (fun z => splitProjector S r d (KernelTower.tilt (n+r+1+d) T m (f z)) (g z) x) := by
  induction d with
  | zero => exact measurable_tailMean_tilt S (r+1) T m hf hg x
  | succ d ih =>
      exact ih (T.2 x.1) (fun j => m j.succ) (fun y => hf (x.1,y)) (fun y => hg (x.1,y)) x.2

omit [Fintype C] [DecidableEq C] in
lemma measurable_matrixProjectionError_tilt (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (m : Fin L → ℝ) (a c : C)
    {f : Z → FinitePath Ω L → ℝ} {A : Z → (C → FinitePath Ω L) → ℝ}
    {X : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hA : ∀ y, Measurable (fun z => A z y))
    (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => matrixProjectionError T q (KernelTower.tilt L K m (f z)) a c (A z) (X z)) := by
  unfold matrixProjectionError FiniteLaw.l2
  apply Measurable.sqrt
  exact measurable_tilt_sample_expect T K m hf
    (fun y => ((hA _).sub (FiniteLaw.measurable_dot (hX _) (hX _))).pow_const 2)

lemma measurable_oldProjectionError_tilt (S : PrescribedTree L) (a b : S.Leaf)
    (K : KernelTower Ω L) (m : Fin L → ℝ)
    {f : Z → FinitePath Ω L → ℝ} {g : Z → Sample Ω S → ℝ}
    {X : Z → FinitePath Ω L → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hg : ∀ y, Measurable (fun z => g z y))
    (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => oldProjectionError S (KernelTower.tilt L K m (f z)) a b (g z) (X z)) := by
  unfold oldProjectionError FiniteLaw.l2
  apply Measurable.sqrt
  exact measurable_tilt_sample_expect S K m hf
    (fun y => ((FiniteLaw.measurable_dot (hX _) (hX _)).sub (hg y)).pow_const 2)

omit [Fintype C] [DecidableEq C] in
lemma matrixProjectionError_le_two (T : PrescribedTree L) (q : C → T.Leaf)
    (K : KernelTower Ω L) (a c : C) (A : (C → FinitePath Ω L) → ℝ)
    (X : FinitePath Ω L → Fin N → ℝ) (hA : ∀ y, |A y|≤1) (hX : ∀ y i, |X y i|≤1) :
    matrixProjectionError T q K a c A X≤2 := by
  apply FiniteLaw.l2_le_two
  intro y
  have ha := hA (fun b => T.pathAt (q b) y)
  have hx := FiniteLaw.abs_dot_le_one _ _ (hX (T.pathAt (q a) y)) (hX (T.pathAt (q c) y))
  exact (abs_sub _ _).trans (by linarith)

lemma oldProjectionError_le_two (S : PrescribedTree L) (K : KernelTower Ω L) (a b : S.Leaf)
    (g : Sample Ω S → ℝ) (X : FinitePath Ω L → Fin N → ℝ)
    (hg : ∀ y, |g y|≤1) (hX : ∀ y i, |X y i|≤1) : oldProjectionError S K a b g X≤2 := by
  apply FiniteLaw.l2_le_two
  intro y
  have ha := hg y
  have hx := FiniteLaw.abs_dot_le_one _ _ (hX (S.pathAt a y)) (hX (S.pathAt b y))
  exact (abs_sub _ _).trans (by linarith)

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.KernelTower
open _root_.MeasureTheory
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N : ℕ}

lemma measurable_tripleExpectAt_tilt (n d : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ}
    {F : Z → FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y))
    (hF : ∀ x y w, Measurable (fun z => F z x y w)) :
    Measurable (fun z => tripleExpectAt n (tilt n T m (f z)) d (F z)) := by
  induction n generalizing d with
  | zero => exact hF () () ()
  | succ n ih =>
    cases d with
    | zero => exact measurable_path_expect (n+1) T m hf (fun x =>
        measurable_path_expect (n+1) T m hf (fun y => measurable_path_expect (n+1) T m hf (hF x y)))
    | succ d =>
      apply T.1.measurable_tilt_expect (m 0)
      · intro a
        exact measurable_backwardLog n (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
      · intro a
        exact ih d (T.2 a) (fun j => m j.succ) (fun y => hf (a,y))
          (fun x y w => hF (a,x) (a,y) (a,w))

lemma abs_tripleExpectAt_le (n d : ℕ) (T : KernelTower Ω n)
    (F : FinitePath Ω n → FinitePath Ω n → FinitePath Ω n → ℝ)
    {B : ℝ} (hF : ∀ x y w, |F x y w|≤B) : |tripleExpectAt n T d F|≤B := by
  induction n generalizing d with
  | zero => exact hF () () ()
  | succ n ih =>
    cases d with
    | zero => exact (law (n+1) T).abs_expect_le (fun x =>
        (law (n+1) T).abs_expect_le (fun y => (law (n+1) T).abs_expect_le (hF x y)))
    | succ d => exact T.1.abs_expect_le (fun a => ih d (T.2 a) _
        (fun x y w => hF (a,x) (a,y) (a,w)))

lemma measurable_halfTripleDifferenceAt_tilt (n d : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    {f : Z → FinitePath Ω n → ℝ} {X : Z → FinitePath Ω n → Fin N → ℝ}
    (hf : ∀ y, Measurable (fun z => f z y)) (hX : ∀ y i, Measurable (fun z => X z y i)) :
    Measurable (fun z => halfTripleDifferenceAt n (tilt n T m (f z)) d (X z)) := by
  apply Measurable.const_mul
  exact measurable_tripleExpectAt_tilt n d T m hf (fun x y w =>
    ((FiniteLaw.measurable_dot (hX x) (hX y)).sub (FiniteLaw.measurable_dot (hX x) (hX w))).pow_const 2)

lemma abs_halfTripleDifferenceAt_le_two (n d : ℕ) (T : KernelTower Ω n)
    (X : FinitePath Ω n → Fin N → ℝ) (hX : ∀ x i, |X x i|≤1) : |halfTripleDifferenceAt n T d X|≤2 := by
  have h : |tripleExpectAt n T d (fun x y w => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X w))^2)|≤4 := by
    apply abs_tripleExpectAt_le
    intro x y w
    rw [abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_le.mp (FiniteLaw.abs_dot_le_one _ _ (hX x) (hX y))
    have h2 := abs_le.mp (FiniteLaw.abs_dot_le_one _ _ (hX x) (hX w))
    nlinarith [sq_nonneg (FiniteLaw.dot (X x) (X y)+FiniteLaw.dot (X x) (X w))]
  unfold halfTripleDifferenceAt
  rw [abs_mul]
  norm_num
  linarith

end DilutedSpinGlass.KernelTower
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z C ι : Type} [Fintype Ω] [MeasurableSpace Z] [Fintype C]
    [DecidableEq C] [DecidableEq ι] {L : ℕ}

omit [Fintype Ω] [Fintype C] in
lemma measurable_labeledHistory (m : Fin (L+1) → ℝ)
    (V : Z → (S : PrescribedTree L) → (C → S.Leaf) → (Sample Ω S → ℝ) → ℝ)
    (hV : ∀ S pos (g : Z → Sample Ω S → ℝ),
      (∀ x, Measurable (fun z => g z x)) → Measurable (fun z => V z S pos (g z)))
    (cs : List C) (S : PrescribedTree L) (U : Finset ι) (loc : ι → S.Leaf)
    (pos : C → S.Leaf) (f : Z → Sample Ω S → ℝ)
    (hf : ∀ x, Measurable (fun z => f z x)) :
    Measurable (fun z => labeledHistory m (V z) cs S U loc pos (f z)) := by
  induction cs generalizing S U with
  | nil => exact hV S pos f hf
  | cons c cs ih =>
    unfold labeledHistory
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun i _ => ih S (U.erase i) loc _ f hf)
    · exact Finset.measurable_sum _ (fun v _ =>
        (ih (grow S v) U _ _ _ (fun x => hf (oldSample S v x))).const_mul _)

lemma measurable_matrixObservableHistory_tilt (K : KernelTower Ω L) (m : Fin L → ℝ)
    (m' : Fin (L+1) → ℝ) (T S : PrescribedTree L) (q : C → T.Leaf) (cs : List C) (a : S.Leaf)
    {f : Z → FinitePath Ω L → ℝ} {A : Z → (C → FinitePath Ω L) → ℝ}
    {g : Z → Sample Ω S → ℝ}
    (hf : ∀ x, Measurable (fun z => f z x))
    (hA : ∀ x, Measurable (fun z => A z x)) (hg : ∀ x, Measurable (fun z => g z x)) :
    Measurable (fun z => matrixObservableHistory T q (KernelTower.tilt L K m (f z)) m' cs S a (A z) (g z)) := by
  classical
  unfold matrixObservableHistory weightedMatrixHistory
  apply measurable_labeledHistory
  · intro R pos g' hg'
    by_cases h : ∀ a b, splitDepth R (pos a) (pos b)=splitDepth T (q a) (q b)
    · simp only [ite_eq_left h]
      exact measurable_tilt_sample_expect R K m hf (fun x => (hg' x).mul (hA _))
    · simp only [ite_eq_right h]
      exact measurable_const
  · exact hg

/-- A crude finite mass bound used ONLY for integrability. It is not a
replacement for the signed centered covariance or the depth charging bound. -/
lemma matrixObservableHistory_bound (K : KernelTower Ω L) (T S : PrescribedTree L)
    (q : C → T.Leaf) (cs : List C) (a : S.Leaf)
    (A : (C → FinitePath Ω L) → ℝ) (g : Sample Ω S → ℝ)
    (hA : ∀ x, |A x|≤1) (hg : ∀ x, |g x|≤1) :
    |matrixObservableHistory T q K (grid L 0 L) cs S a A g|≤
      historyMass (fun _ => 1) cs.length S ((Finset.univ.erase a).card) := by
  classical
  unfold matrixObservableHistory weightedMatrixHistory
  apply labeledHistory_abs_le_mass (fun _ => 1)
  · intro R pos g' hg'
    by_cases h : ∀ a b, splitDepth R (pos a) (pos b)=splitDepth T (q a) (q b)
    · rw [ite_eq_left h]
      apply FiniteLaw.abs_expect_le
      intro x
      rw [abs_mul]
      exact (mul_le_mul (hg' x) (hA _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · rw [ite_eq_right h,abs_zero]
      norm_num
  · exact hg

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProjectionIntegrability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω Z : Type} [Fintype Ω] [MeasurableSpace Z] {N L : ℕ}
omit [Fintype Ω] in
lemma treeOverlap_eq_spatialProduct (S : PrescribedTree L) (f : FinitePath Ω L → Fin N → ℝ)
    (x : Sample Ω S) : treeOverlap S f x=spatialProduct (fun _ : S.Leaf => f) (fun b => S.pathAt b x) := by
  simp only [treeOverlap,spatialProduct,leafProduct_eq_prod]
end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y C : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [DecidableEq C] {M N n : ℕ}
attribute [local irreducible] PrescribedTree.matrixProjectionError PrescribedTree.oldProjectionError
    KernelTower.halfTripleDifferenceAt PrescribedTree.splitProjector

variable (S : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+r+1+d)) (Q : (i : I) → Fin (n+r+1+d) → FiniteLaw (A i))
    (m : Fin (n+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (n+r+1+d) → ℝ)
    (old : (i : I) → FinitePath Ω (n+r+1+d) → FinitePath (A i) (n+r+1+d) → ℝ)
    (V : FinitePath Ω (n+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootProjectedTriple : Measurable (fun z : FullRootState Y X I M =>
    KernelTower.halfTripleDifferenceAt (n+r+1+d) (rootTower T Q m base old z) d
      (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    KernelTower.halfTripleDifferenceAt _
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) d
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine KernelTower.measurable_halfTripleDifferenceAt_tilt _ d (tower (rootArray nt y) _ T Q) m ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootSplitProjector_bound (hV : ∀ y i, |V y i|≤1) (z : FullRootState Y X I M)
    (x : FinitePath (rootAlphabet (Ω := Ω) (A := A) z) (n+r+1+d)) (i : Fin N) :
    |rootSplitProjector S r d T Q m base old V z x i|≤1 :=
  splitProjector_bound S r d _ _ (fun _ => hV _ i) x

include hb in
lemma integrable_rootProjectedTriple (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) : Integrable (fun z : FullRootState Y X I M =>
    KernelTower.halfTripleDifferenceAt (n+r+1+d) (rootTower T Q m base old z) d
      (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootProjectedTriple S r d T Q m base old V hb).aestronglyMeasurable 2
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs]
    exact KernelTower.abs_halfTripleDifferenceAt_le_two _ d _ _
      (rootSplitProjector_bound S r d T Q m base old V hV z))

include hb in
omit [Fintype C] [DecidableEq C] in
lemma measurable_rootTargetError (R : PrescribedTree (n+r+1+d)) (q : C → R.Leaf) (a c : C)
    (F : (C → FinitePath Ω (n+r+1+d)) → ℝ) :
    Measurable (fun z : FullRootState Y X I M =>
      matrixProjectionError R q (rootTower T Q m base old z) a c
        (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
        (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    matrixProjectionError R q
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) a c
      (fun w => F (fun b => physical (rootArray nt y) _ (w b)))
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_matrixProjectionError_tilt R q (tower (rootArray nt y) _ T Q) m a c ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

include hb in
omit [Fintype C] [DecidableEq C] in
lemma integrable_rootTargetError (R : PrescribedTree (n+r+1+d)) (q : C → R.Leaf) (a c : C)
    (F : (C → FinitePath Ω (n+r+1+d)) → ℝ)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) (hF : ∀ x, |F x|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      matrixProjectionError R q (rootTower T Q m base old z) a c
        (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
        (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootTargetError S r d T Q m base old V hb R q a c F).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ matrixProjectionError R q (rootTower T Q m base old z) a c
    (fun x => F (fun b => physical (rootArray z.2.2.1 z.2.2.2) _ (x b)))
    (rootSplitProjector S r d T Q m base old V z) from by
      unfold matrixProjectionError; exact FiniteLaw.l2_nonneg _ _)]
  exact matrixProjectionError_le_two R q _ a c _ _ (fun x => hF _)
    (rootSplitProjector_bound S r d T Q m base old V hV z)

include hb in
lemma measurable_rootOldError (R : PrescribedTree (n+r+1+d)) (a b : R.Leaf) :
    Measurable (fun z : FullRootState Y X I M =>
      oldProjectionError R (rootTower T Q m base old z) a b (treeOverlap R (rootVector V z))
        (rootSplitProjector S r d T Q m base old V z)) := by
  change Measurable (packRoot (fun h k x nt y =>
    oldProjectionError R
      (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
        (logWeight (base h k x) (rootArray nt y) old)) a b
      (treeOverlap R (fun w => V (physical (rootArray nt y) _ w)))
      (fun w i => splitProjector S r d
        (KernelTower.tilt _ (tower (rootArray nt y) _ T Q) m
          (logWeight (base h k x) (rootArray nt y) old))
        (fun w => V (physical (rootArray nt y) _ w) i) w)))
  apply measurable_packRoot
  intro k nt
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_oldProjectionError_tilt R a b (tower (rootArray nt y) _ T Q) m ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · intro w i
    refine measurable_splitProjector_tilt S r d (tower (rootArray nt y) _ T Q) m ?_ ?_ w
    · exact fun w => (hb k _).add measurable_const
    · exact fun _ => measurable_const

include hb in
lemma integrable_rootOldError (R : PrescribedTree (n+r+1+d)) (a b : R.Leaf)
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ]
    (hV : ∀ y i, |V y i|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      oldProjectionError R (rootTower T Q m base old z) a b (treeOverlap R (rootVector V z))
        (rootSplitProjector S r d T Q m base old V z)) μ := by
  apply Integrable.of_bound (measurable_rootOldError S r d T Q m base old V hb R a b).aestronglyMeasurable 2
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ oldProjectionError R (rootTower T Q m base old z) a b
    (treeOverlap R (rootVector V z)) (rootSplitProjector S r d T Q m base old V z) from by
      unfold oldProjectionError; exact FiniteLaw.l2_nonneg _ _)]
  exact oldProjectionError_le_two R _ a b _ _ (treeOverlap_bound R _ (fun x i => hV _ i))
    (rootSplitProjector_bound S r d T Q m base old V hV z)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y C : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype C] [DecidableEq C] {L M : ℕ}
attribute [local irreducible] PrescribedTree.matrixObservableHistory

variable (R S : PrescribedTree L) (q : C → R.Leaf) (cs : List C) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (F : (C → FinitePath Ω L) → ℝ) (g : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootMatrixObservableHistory (m' : Fin (L+1) → ℝ) :
    Measurable (fun z : FullRootState Y X I M =>
      matrixObservableHistory R q (rootTower T Q m base old z) m' cs S a
        (fun x => F (fun c => physical (rootArray z.2.2.1 z.2.2.2) L (x c)))
        (fun x => g (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))) := by
  change Measurable (packRoot (fun h k x n y =>
    matrixObservableHistory R q
      (KernelTower.tilt L (tower (rootArray n y) L T Q) m
        (logWeight (base h k x) (rootArray n y) old)) m' cs S a
      (fun x => F (fun c => physical (rootArray n y) L (x c)))
      (fun x => g (fun b => physical (rootArray n y) L (S.pathAt b x)))))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_matrixObservableHistory_tilt (tower (rootArray n y) L T Q) m m' R S q cs a ?_ ?_ ?_
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ => measurable_const
  · exact fun _ => measurable_const

include hb in
/-- Ordinary integrability of the literal signed multileaf history at the
actual variable-alphabet root. This does NOT take its absolute value in the
concentration identity: the crude bound is used only to justify integration. -/
lemma integrable_rootMatrixObservableHistory (μ : Measure (FullRootState Y X I M))
    [IsFiniteMeasure μ] (hF : ∀ x, |F x|≤1) (hg : ∀ x, |g x|≤1) :
    Integrable (fun z : FullRootState Y X I M =>
      matrixObservableHistory R q (rootTower T Q m base old z) (grid L 0 L) cs S a
        (fun x => F (fun c => physical (rootArray z.2.2.1 z.2.2.2) L (x c)))
        (fun x => g (fun b => physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b x)))) μ := by
  classical
  apply Integrable.of_bound (measurable_rootMatrixObservableHistory R S q cs a T Q m base old F g hb
    (grid L 0 L)).aestronglyMeasurable (historyMass (fun _ => 1) cs.length S ((Finset.univ.erase a).card))
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  exact matrixObservableHistory_bound _ R S q cs a _ _ (fun x => hF _) (fun x => hg _)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootShiftIntegrability
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ReducedTopology
open scoped BigOperators
attribute [local irreducible] ReducedTopology.projectionShiftError
variable {Ω I X Y α ι : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [Fintype α] [DecidableEq α] [Fintype ι]
    {L M N : ℕ} [NeZero L]

variable (a : α) (C : ι → ReducedTopology)
    (e : (j : ι) → (C j).Vertex → {j : α // j≠a})
    (T : KernelTower Ω L) (P : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
/-- The exact single-copy shift error is measurable at the physical root,
including all Poisson counts and its countable variable marker alphabet. -/
lemma measurable_root_projectionShiftError (Q : α → Fin L) :
    Measurable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) := by
  change Measurable (packRoot (fun h k x n y =>
    projectionShiftError a C e
      (KernelTower.tilt L (tower (rootArray n y) L T P) m
        (logWeight (base h k x) (rootArray n y) old))
      (fun w => V (physical (rootArray n y) L w)) Q))
  apply measurable_packRoot
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  refine measurable_projectionShiftError_tilt a C e (tower (rootArray n y) L T P) m ?_ ?_ Q
  · exact fun w => (hb k _).add measurable_const
  · exact fun _ _ => measurable_const

include hb in
omit [Fintype α] [DecidableEq α] [NeZero L] in
lemma integrable_root_projectionShiftError (μ : Measure (FullRootState Y X I M))
    [IsFiniteMeasure μ] (hV : ∀ y i, |V y i|≤1) (Q : α → Fin L) :
    Integrable (fun z : FullRootState Y X I M =>
      projectionShiftError a C e (rootTower T P m base old z) (rootVector V z) Q) μ := by
  apply Integrable.of_bound (measurable_root_projectionShiftError a C e T P m base old V hb Q).aestronglyMeasurable 4
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (projectionShiftError_nonneg a C e _ _ Q)]
  exact projectionShiftError_le_four a C e _ _ (fun y i => hV _ i) Q

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledFrameError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}


/-- Complete target projection comparison at the SAME height as the old
frame. Both projectors and both entire target sides are the literal
scheduled trees. No desired covariance estimate is an input. -/
theorem scheduled_frame_target_error_le (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+1+r+1+d))
    (f : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let RawTarget := PrescribedTree.splitFrame (.node k NewChild) (r+1) d
    let Target := PrescribedTree.heightCast ht RawTarget
    let T' := kernelHeightCast ht.symm T
    let f' := vectorHeightCast ht.symm f
    ∀ (b : (PrescribedTree.node k NewChild).Leaf) (q0 : I → RawTarget.Leaf),
      Function.Bijective q0 → ∀ (u v : I),
      q0 u=PrescribedTree.splitFrameLeaf (.node k NewChild) (r+1) d 0 b →
      q0 v=PrescribedTree.splitFrameLeaf (.node k NewChild) (r+1) d 1 b →
    let q := fun j => PrescribedTree.leafHeightCast ht RawTarget (q0 j)
    PrescribedTree.matrixProjectionError Target q T u v
      (PrescribedTree.spatialProduct (fun _ : I => f))
      (fun x i => PrescribedTree.splitProjector (.node k OldChild) r d T (fun y => f y i) x) ≤
      2*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (PrescribedTree.descendantEnergyAt (NewChild j) (r+1) d T' f'))+
        projectionShiftError a C e T f Q := by
  dsimp only
  intro b q0 hq u v hu hv
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let L' := H+1+(r+1)+1+d
  let Q' : α → Fin L' := fun j => Fin.cast ht.symm (Q j)
  let T' := kernelHeightCast ht.symm T
  let f' := vectorHeightCast ht.symm f
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let RawTarget := PrescribedTree.splitFrame (.node k NewChild) (r+1) d
  have hf' : ∀ x i, |f' x i|≤1 := fun x i => hf (pathHeightCast ht x) i
  have hnew := delayed_target_projection_le (I := I) H (r+1) d k hk a C e Q'
    (by simpa only [Q',Fin.val_cast] using ha)
    (fun j v => by simpa only [Q',Fin.val_cast] using hQ j v) T' f' hf'
  dsimp only at hnew
  simp only [Q',Fin.val_cast] at hnew
  have he := hnew b q0 hq u v hu hv
  have hp := scheduled_splitProjector_product (H+1) r d k hk C
    (fun j w => (Q (e j w)).val)
    (fun j w => by have := hQ j w; omega) T f
  simp only [realize,rootSchedule,lt_self_iff_false,ite_false] at hp
  rw [hp]
  have hcast := PrescribedTree.matrixProjectionError_heightCast ht RawTarget q0 T' u v f'
    (conditionalScheduledProduct L' 0 (Q a).val C (fun j w => (Q (e j w)).val) T' f')
  rw [conditionalScheduledProduct_heightCast] at hcast
  dsimp only [T',f'] at hcast
  simp only [kernelHeightCast_inv,vectorHeightCast_inv] at hcast
  simp only [ha] at hcast he
  rw [hcast]
  have hh := projectionShiftError_heightCast ht.symm a C e T f Q
  change projectionShiftError a C e T' f' Q'=projectionShiftError a C e T f Q at hh
  change _ ≤ _+projectionShiftError a C e T' f' (fun j => Q' j) at he
  rw [hh] at he
  exact he

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass
variable {Ω : Type} [Fintype Ω] {n m N : ℕ}

namespace PrescribedTree
/-- A proper-child covariance is the SAME single-copy covariance evaluated at
the child's retained evaluation coordinate. Its two successive prefix averages
are just one original-kernel prefix, not an independent pair of copies. -/
lemma descendantEnergyAt_eq_shapeEnergyAt (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    descendantEnergyAt C r d T f = shapeEnergyAt C (r+1+d)
      (kernelHeightCast (by omega) T) (vectorHeightCast (by omega) f) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [descendantEnergyAt,shapeEnergyAt,kernelHeightCast_succ_fst,
      kernelHeightCast_succ_snd,vectorHeightCast_succ_pair]
    apply FiniteLaw.expect_congr
    intro x
    exact ih (T.2 x) (fun y => f (x,y))

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

lemma scheduledShapeEnergy_eq_realize (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : L=n+1+d) (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    scheduledShapeEnergy L d S q T f =
      shapeEnergyAt (realize n (d+1) S q) d (kernelHeightCast h T) (vectorHeightCast h f) := by
  subst L
  unfold scheduledShapeEnergy
  rw [dite_eq_left (by omega : d<n+1+d)]
  have he (n' : ℕ) (hn : n'=n) (hc : n+1+d=n'+1+d) :
      shapeEnergyAt (realize n' (d+1) S q) d (kernelHeightCast hc T) (vectorHeightCast hc f) =
        shapeEnergyAt (realize n (d+1) S q) d T f := by
    subst n'
    rfl
  exact he _ (by omega) _

/-- Exact retained-coordinate identification used by the fiber estimate. The
child covariance at the later first split is precisely this same energy family,
not a separately selected experiment and not a two-copy depth average. -/
lemma descendantEnergyAt_eq_scheduled (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    descendantEnergyAt (realize n (r+1+d+1) S q) r d T f =
      scheduledShapeEnergy (n+1+r+1+d) (r+1+d) S q T f := by
  rw [scheduledShapeEnergy_eq_realize n (r+1+d) S q (by omega)]
  exact descendantEnergyAt_eq_shapeEnergyAt _ r d T f

/-- The left side of the multileaf step belongs to the same literal scheduled
covariance family as its proper-child energies. -/
lemma scheduledShapeEnergy_node (n r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+1+d+1≤q j v)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    scheduledShapeEnergy (n+1+r+1+d) d (.node k hk C) (rootSchedule (r+1+d) q) T f =
      shapeEnergyAt (stem (.node k (fun j => realize n (r+1+d+1) (C j) (q j))) r) d T f := by
  rw [scheduledShapeEnergy_eq_realize (n+1+r) d _ _ rfl]
  have hlow : ∀ v : (ReducedTopology.node k hk C).Vertex, d+1+r ≤ rootSchedule (r+1+d) q v := by
    intro v
    cases v with
    | none => simp only [rootSchedule]; omega
    | some v => have hh := hq v.1 v.2; dsimp only [rootSchedule]; omega
  rw [realize_stem (n+1) r (d+1) _ _ hlow]
  simp only [realize,rootSchedule,show ¬d+1+r < r+1+d by omega,ite_false,
    show d+1+r+1=r+1+d+1 by omega]
  rfl

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledRootMultileaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory
open scoped BigOperators
open PrescribedTree
variable {α I : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I] {N : ℕ}

/-- Root-averaged genuine old/delayed multileaf induction. The only signed
term is ONE centered root matrix covariance, exactly the term controlled
by physical_matrix_selection. All remaining errors are actual proper
children or the single-copy h_N; the target projection error is eliminated. -/
theorem scheduled_root_multileaf {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (K : (z : Z) → KernelTower (Ω z) (H+1+1+r+1+d))
    (f : (z : Z) → FinitePath (Ω z) (H+1+1+r+1+d) → Fin N → ℝ)
    (hf : ∀ z x i, |f z x i|≤1) :
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
    let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let X := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let y := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    Integrable (fun z => shapeEnergyAt (stem OldNode r) d (K z) (f z)) μ →
    Integrable (fun z => KernelTower.halfTripleDifferenceAt L (K z) d (X z)) μ →
    Integrable (fun z => matrixObservableHistory Target q (K z) m (v::cs) S x (A z) (treeOverlap S (f z))) μ →
    Integrable (fun z => matrixProjectionError Target q (K z) u v (A z) (X z)) μ →
    Integrable (fun z => oldProjectionError S (K z) x y (treeOverlap S (f z)) (X z)) μ →
    Integrable (fun z => (Target.sampleLaw (K z)).expect (fun w => A z (fun j => Target.pathAt (q j) w))) μ →
    Integrable W μ → Integrable (fun z => Real.sqrt (W z)) μ →
    Integrable (fun z => Real.sqrt (W' z)) μ → Integrable h μ →
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ Ω Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
    hV hTriple hHistory hTarget hOld hMean hW hSqrtW hSqrtNew hShift
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let RawTarget := splitFrame (.node k NewChild) (r+1) d
  let Target := heightCast ht RawTarget
  let q := fun j => leafHeightCast ht RawTarget (q0 j)
  let S := splitFrame (.node k OldChild) r d
  let X := fun z x i => splitProjector (.node k OldChild) r d (K z) (fun y => f z y i) x
  let A := fun z => spatialProduct (fun _ : I => f z)
  let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d
    (kernelHeightCast ht.symm (K z)) (vectorHeightCast ht.symm (f z)))
  let h := fun z => projectionShiftError a C e (K z) (f z) Q
  have hq' : Function.Bijective q := (leafHeightCast_bijective ht RawTarget).comp hq
  have hqd : splitDepth Target (q u) (q v)=d := by
    rw [splitDepth_heightCast,hu,hv]
    exact splitFrame_split (.node k NewChild) (r+1) d b'
  have hbase := root_multileaf_matrix μ Ω k OldChild b r d Target q hq' B hS K u v huv
    cs hcs hdis hfull hqd f hf hV hTriple hHistory hTarget hOld hMean hW hSqrtW
  have hproj : (∫ z, matrixProjectionError Target q (K z) u v (A z) (X z) ∂μ) ≤
      2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ) := by
    have hle := integral_mono hTarget ((hSqrtNew.const_mul 2).add hShift) (fun z =>
      scheduled_frame_target_error_le H r d k hk a C e Q ha hQ (K z) (f z) (hf z) b' q0 hq u v hu hv)
    change (∫ z, matrixProjectionError Target q (K z) u v (A z) (X z) ∂μ) ≤
      (∫ z, 2*Real.sqrt (W' z)+h z ∂μ) at hle
    rw [integral_add (hSqrtNew.const_mul 2) hShift,integral_const_mul] at hle
    exact hle
  have hcharge : 0 ≤ shiftedCharge B Target S (v::cs).length := by
    unfold shiftedCharge
    exact mul_nonneg (chargeBound_nonneg (by positivity) (by positivity) _ _) (by positivity)
  have hproj' := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hproj hcharge)
    (abs_nonneg (partialKappa Target (grid L 0 L) (Finset.univ.image q)/
      partialKappa Target (grid L 0 L) ((insert v ({u}:Finset I)).image q)))
  exact hbase.trans (add_le_add (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl hproj') le_rfl) (by norm_num)) le_rfl)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalScheduledMultileaf
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree HeterogeneousMarks
open scoped BigOperators
variable {α I Ω J X Y : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype Ω] {Mark : J → Type} [∀ j, Fintype (Mark j)] [Countable J]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace X] [MeasurableSpace Y]
    {M N : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- Actual physical-root multileaf induction, with ALL ordinary integrability
premises discharged for finite alphabets and countably many marker types.
The signed root covariance remains a single centered term, not a pointwise
absolute value. This is a dependency of decorrelation, not the main formula. -/
theorem physical_scheduled_root_multileaf (μ : Measure (FullRootState Y X J M))
    [IsProbabilityMeasure μ]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+1+r+1+d)) (P : (j : J) → Fin (H+1+1+r+1+d) → FiniteLaw (Mark j))
    (m : Fin (H+1+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (H+1+1+r+1+d) → ℝ)
    (old : (j : J) → FinitePath Ω (H+1+1+r+1+d) → FinitePath (Mark j) (H+1+1+r+1+d) → ℝ)
    (V : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i|≤1) :
    let K := rootTower T P m base old
    let f := rootVector V (I := J) (A := Mark) (X := X) (Y := Y) (M := M)
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (OldChild j) r d (K z) (f z))
    let W' := fun z => (k:ℝ)*∑ j, Real.sqrt (descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z))
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let _ := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let _ := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ (rootAlphabet (Ω := Ω) (A := Mark)) Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*(∫ z, Real.sqrt (W' z) ∂μ)+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*(∫ z, Real.sqrt (W z) ∂μ)))+
      (((d:ℝ)+2)/(L:ℝ))*(16*(∫ z, W z ∂μ)) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let OldNode := PrescribedTree.node k OldChild
  let NewNode := PrescribedTree.node k NewChild
  let RawTarget := splitFrame NewNode (r+1) d
  let Target := heightCast ht RawTarget
  let q := fun j => leafHeightCast ht RawTarget (q0 j)
  let S := splitFrame OldNode r d
  let x := splitFrameLeaf OldNode r d 0 b
  let y := splitFrameLeaf OldNode r d 1 b
  apply scheduled_root_multileaf μ (rootAlphabet (Ω := Ω) (A := Mark)) H r d k hk a C e Q ha hQ
    (rootTower T P m base old) (rootVector V) (fun z y i => hV _ i)
    b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  · exact integrable_rootShapeEnergy (stem OldNode r) d T P m base old V hb μ hV
  · exact integrable_rootProjectedTriple OldNode r d T P m base old V hb μ hV
  · have hh := integrable_rootMatrixObservableHistory Target S q (v::cs) x T P m base old
      (spatialProduct (fun _ : I => V)) (spatialProduct (fun _ : S.Leaf => V)) hb μ
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
    have hg (z : FullRootState Y X J M) : treeOverlap S (rootVector (A := Mark) V z) =
        (fun w => spatialProduct (fun _ : S.Leaf => V)
          (fun c => physical (rootArray z.2.2.1 z.2.2.2) _ (S.pathAt c w))) := by
      funext w
      exact treeOverlap_eq_spatialProduct S (rootVector (A := Mark) V z) w
    change Integrable (fun z => matrixObservableHistory Target q (rootTower T P m base old z)
      (grid L 0 L) (v::cs) S x (spatialProduct (fun _ : I => rootVector (A := Mark) V z))
      (treeOverlap S (rootVector (A := Mark) V z))) μ
    simp_rw [hg]
    exact hh
  · exact integrable_rootTargetError OldNode r d T P m base old V hb Target q u v
      (spatialProduct (fun _ : I => V)) μ hV
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) w)
  · exact integrable_rootOldError OldNode r d T P m base old V hb S x y μ hV
  · exact integrable_rootTreeMean T P m base old hb Target
      (fun w => spatialProduct (fun _ : I => V) (fun j => w (q j))) μ
      (fun w => spatialProduct_bound _ (fun _ w i => hV w i) _)
  · exact integrable_rootChildSum k OldChild r d rfl T P m base old V hb μ hV
  · exact integrable_sqrt_rootChildSum k OldChild r d rfl T P m base old V hb μ hV
  · exact integrable_sqrt_rootChildSum k NewChild (r+1) d ht.symm T P m base old V hb μ hV
  · exact integrable_root_projectionShiftError a C e T P m base old V hb μ hV Q

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootChildMoment
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped BigOperators

/-- Probability-root Jensen for the square root, proved directly from the
nonnegative centered square. It is used twice in the multileaf induction. -/
lemma integral_sqrt_le_sqrt_integral {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → ℝ)
    (hf : Integrable f μ) (hs : Integrable (fun z => Real.sqrt (f z)) μ)
    (h : ∀ z, 0≤f z) : (∫ z, Real.sqrt (f z) ∂μ)≤Real.sqrt (∫ z, f z ∂μ) := by
  let t := ∫ z, Real.sqrt (f z) ∂μ
  have ht : 0≤t := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have he (z : Z) : (Real.sqrt (f z)-t)^2=f z-(2*t)*Real.sqrt (f z)+t^2 := by
    have hs := Real.sq_sqrt (h z)
    nlinarith
  have hp : 0≤∫ z, (Real.sqrt (f z)-t)^2 ∂μ := integral_nonneg (fun z => sq_nonneg _)
  simp_rw [he] at hp
  have hm : Integrable (fun z => (2*t)*Real.sqrt (f z)) μ := hs.const_mul (2*t)
  have hd : Integrable (fun z => f z-(2*t)*Real.sqrt (f z)) μ := hf.sub hm
  rw [integral_add hd (integrable_const (t^2)),
    integral_sub hf hm,integral_const_mul,integral_const] at hp
  simp only [probReal_univ,one_smul] at hp
  have hsq : t^2 ≤ ∫ z, f z ∂μ := by dsimp only [t] at *; nlinarith
  exact (Real.sqrt_sq ht).symm.le.trans (Real.sqrt_le_sqrt hsq)

namespace HeterogeneousMarks
open PrescribedTree
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {M N n L : ℕ}

lemma integrable_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ] (hV : ∀ x i, |V x i|≤1) :
    Integrable (fun z : FullRootState Y X I M => descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z))) μ := by
  subst L
  exact integrable_rootDescendantEnergy C r d T Q m base old V hb μ hV

lemma integrable_sqrt_rootDescendantEnergy_cast (C : PrescribedTree n) (r d : ℕ)
    (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsFiniteMeasure μ] (hV : ∀ x i, |V x i|≤1) :
    Integrable (fun z : FullRootState Y X I M => Real.sqrt (descendantEnergyAt C r d
      (kernelHeightCast h (rootTower T Q m base old z)) (vectorHeightCast h (rootVector V z)))) μ := by
  subst L
  exact integrable_sqrt_rootDescendantEnergy C r d T Q m base old V hb μ hV

variable (k : ℕ) (C : Fin k → PrescribedTree n) (r d : ℕ) (h : L=n+1+r+1+d)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]

include hb in
lemma integral_rootChildSum_le (hV : ∀ x i, |V x i|≤1) :
    (∫ z, rootChildSum k C r d h T Q m base old V z ∂μ) ≤
      rootChildMeanSum k C r d h T Q m base old V μ := by
  unfold rootChildSum rootChildMeanSum
  rw [integral_const_mul,integral_finsetSum _ (fun j _ =>
    integrable_sqrt_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  apply Finset.sum_le_sum
  intro j _
  exact integral_sqrt_le_sqrt_integral μ _
    (integrable_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)
    (integrable_sqrt_rootDescendantEnergy_cast (C j) r d h T Q m base old V hb μ hV)
    (fun z => descendantEnergyAt_nonneg (C j) r d _ _)

include hb in
lemma integral_sqrt_rootChildSum_le (hV : ∀ x i, |V x i|≤1) :
    (∫ z, Real.sqrt (rootChildSum k C r d h T Q m base old V z) ∂μ) ≤
      Real.sqrt (rootChildMeanSum k C r d h T Q m base old V μ) := by
  exact (integral_sqrt_le_sqrt_integral μ _
    (integrable_rootChildSum k C r d h T Q m base old V hb μ hV)
    (integrable_sqrt_rootChildSum k C r d h T Q m base old V hb μ hV)
    (rootChildSum_nonneg k C r d h T Q m base old V)).trans
    (Real.sqrt_le_sqrt (integral_rootChildSum_le k C r d h T Q m base old V hb μ hV))

end HeterogeneousMarks
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalMultileafMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree HeterogeneousMarks
open scoped BigOperators
variable {α I Ω J X Y : Type} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype Ω] {Mark : J → Type} [∀ j, Fintype (Mark j)] [Countable J]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace X] [MeasurableSpace Y]
    {M N : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- Root-moment form of the genuine multileaf induction. Projection costs
are now functions of the ROOT conditional covariance of proper children;
there are no caller integrability or projection-error hypotheses. -/
theorem physical_scheduled_root_multileaf_moments (μ : Measure (FullRootState Y X J M))
    [IsProbabilityMeasure μ]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+1+r+1+d)) (P : (j : J) → Fin (H+1+1+r+1+d) → FiniteLaw (Mark j))
    (m : Fin (H+1+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (H+1+1+r+1+d) → ℝ)
    (old : (j : J) → FinitePath Ω (H+1+1+r+1+d) → FinitePath (Mark j) (H+1+1+r+1+d) → ℝ)
    (V : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i|≤1) :
    let K := rootTower T P m base old
    let f := rootVector V (I := J) (A := Mark) (X := X) (Y := Y) (M := M)
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r d (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let _ := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : I => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : I → RawTarget.Leaf), Function.Bijective q0 →
      ∀ (u v : I), u≠v → q0 u=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 v=splitFrameLeaf NewNode (r+1) d 1 b' →
    ∀ (B : Finset ℕ), branchingCount S (· ∈ B)=0 →
    ∀ (cs : List I), cs.Nodup → (∀ j ∈ cs, j ∉ insert v ({u}:Finset I)) →
      insert v ({u}:Finset I) ∪ cs.toFinset=Finset.univ →
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let _ := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({u}:Finset I)).image q)
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ (rootAlphabet (Ω := Ω) (A := Mark)) Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  have hh := physical_scheduled_root_multileaf μ H r d k hk a C e Q ha hQ T P m base old V hb hV
    b b' q0 hq u v huv hu hv B hS cs hcs hdis hfull
  have hW := integral_rootChildSum_le k OldChild r d rfl T P m base old V hb μ hV
  have hOld := integral_sqrt_rootChildSum_le k OldChild r d rfl T P m base old V hb μ hV
  have hNew := integral_sqrt_rootChildSum_le k NewChild (r+1) d ht.symm T P m base old V hb μ hV
  apply hh.trans
  have hmass : 0 ≤ pairHistoryMass (splitFrame (.node k OldChild) r d) (grid L 0 L)
      (splitFrameLeaf (.node k OldChild) r d 0 b) := by unfold pairHistoryMass; positivity
  have hcharge : 0 ≤ shiftedCharge B (heightCast ht (splitFrame (.node k NewChild) (r+1) d))
      (splitFrame (.node k OldChild) r d) (v::cs).length := by
    unfold shiftedCharge
    exact mul_nonneg (chargeBound_nonneg (by positivity) (by positivity) _ _) (by positivity)
  gcongr
  all_goals first | exact hW | exact hOld | exact hNew

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ShiftedFrameGeometry
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n : ℕ}

noncomputable local instance shiftedFrameGeometryPropDecidable_re47a78_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
lemma branchingCount_stem (S : PrescribedTree n) (r : ℕ) (P : ℕ → Prop) :
    branchingCount (stem S r) P=branchingCount S (fun u => P (u+r)) := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
    change branchingCount (unary (stem S r)) P=_
    rw [branchingCount_unary,ih]
    simp only [Nat.add_assoc]

lemma mem_shiftedPrefixDepths (S : PrescribedTree n) (d u : ℕ) :
    u+d ∈ shiftedPrefixDepths S d ↔ u ∈ shiftedTwinDepths S := by
  classical
  simp [shiftedPrefixDepths]

/-- No old branch can pay a charged target factor, even below a retained
shared prefix. Equal-depth occurrences in the twins remain separate. -/
theorem shifted_prefix_old_count (S : PrescribedTree n) (d : ℕ)
    (hS : NoAdjacentBranchDepths S) :
    branchingCount (stem (doubled (bottomUnary S)) d) (· ∈ shiftedPrefixDepths S d)=0 := by
  rw [branchingCount_stem]
  simpa only [mem_shiftedPrefixDepths] using shifted_twin_old_count S hS

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledFrameGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n m : ℕ}

lemma branchingCount_splitFrame_bottom (S : PrescribedTree n) (r d : ℕ) (P : ℕ → Prop) :
    branchingCount (splitFrame (bottomUnary S) r d) P =
      branchingCount (stem (doubled (bottomUnary (stem S r))) d) P := by
  simp only [splitFrame,branchingCount_stem,doubled,branchingCount,branchingCount_bottom]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The scheduled old frame has no charged internal branching vertex.
No regularity of a union of old and target trees is postulated. -/
theorem scheduled_frame_old_count (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d))
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    (hno : NoAdjacentBranchDepths
      (stem (PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))) r)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    branchingCount (splitFrame Old r d) (· ∈ shiftedPrefixDepths (stem Base r) d)=0 := by
  dsimp only
  have he : (PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j)
      (fun v => (Q (e j v)).val))) =
      bottomUnary (PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j)
        (fun v => (Q (e j v)).val))) := by
    change PrescribedTree.node k _=PrescribedTree.node k _
    congr 1
    funext j
    exact realize_bottom H (r+1+d+1) (C j) _ (had j)
  rw [he,branchingCount_splitFrame_bottom]
  exact shifted_prefix_old_count _ d hno

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

lemma canonicalMatrixHistory (t : ℕ) :
    (List.ofFn (fun j : Fin (t+1) => (some j : Option (Fin (t+1))))).reverse =
      some (Fin.last t) :: canonicalMatrixTail t := by
  rw [List.ofFn_succ_last, List.reverse_append]
  rfl

lemma canonicalMatrixTail_nodup (t : ℕ) : (canonicalMatrixTail t).Nodup := by
  apply List.nodup_reverse.mpr
  exact List.nodup_ofFn.mpr (fun i j h => Fin.castSucc_injective t (Option.some_injective _ h))

lemma canonicalMatrixTail_not_mem (t : ℕ) (x : Option (Fin (t+1)))
    (hx : x ∈ canonicalMatrixTail t) :
    x ∉ insert (some (Fin.last t)) ({none} : Finset (Option (Fin (t+1)))) := by
  simp only [canonicalMatrixTail, List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, Option.some_ne_none,
    or_false]
  exact Fin.castSucc_ne_last j

lemma canonicalMatrixTail_full (t : ℕ) :
    insert (some (Fin.last t)) ({none} : Finset (Option (Fin (t+1)))) ∪
      (canonicalMatrixTail t).toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  cases x with
  | none => simp
  | some j =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · apply Finset.mem_union.mpr (Or.inr _)
      simp only [List.mem_toFinset, canonicalMatrixTail, List.mem_reverse, List.mem_ofFn]
      exact ⟨i,rfl⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ScheduledRegularFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

omit [Fintype α] [DecidableEq α] in
lemma regular_no_adjacent_values (q : α → Fin L) {η : ℝ}
    (hlarge : 1<η*(L:ℝ)) (hr : Regular η q) (a b : α) :
    (q a).val+1≠(q b).val := by
  intro he
  have hab : a≠b := by intro h; subst b; omega
  have hsep := hr.2 a b hab
  have hL : (0:ℝ)<L := Nat.cast_pos.mpr (NeZero.pos L)
  have he' : ((q a).val:ℝ)+1=((q b).val:ℝ) := by exact_mod_cast he
  have habs : |normalized (q a)-normalized (q b)|=1/(L:ℝ) := by
    unfold normalized
    rw [← sub_div,abs_div,abs_of_pos hL]
    have h : ((q a).val:ℝ)-((q b).val:ℝ) = -1 := by linarith
    rw [h]
    norm_num
  rw [habs] at hsep
  have hlt : 1/(L:ℝ)<η := (div_lt_iff₀ hL).mpr hlarge
  linarith
end DilutedSpinGlass.DepthAverage

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators

lemma branching_depth_assigned_at (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) (a : ℕ)
    (ha : a ∈ branchingDepths (realize H d S q)) : ∃ v, q v=d+a := by
  classical
  by_contra! h
  have hz : branchingCount (realize H d S q) (fun u => d+u=d+a)=0 := by
    rw [realize_branchingCount H d S q hq (fun u => u=d+a)]
    simp only [h,ite_false,Finset.sum_const_zero]
  exact ((branchingCount_eq_zero_iff _ _).mp hz a ha) rfl

lemma realize_no_adjacent_at (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) (hsep : ∀ u v, q u+1≠q v) :
    NoAdjacentBranchDepths (realize H d S q) := by
  intro a ha b hb he
  obtain ⟨u,hu⟩ := branching_depth_assigned_at H d S q hq a ha
  obtain ⟨v,hv⟩ := branching_depth_assigned_at H d S q hq b hb
  exact hsep u v (by omega)

/-- Genuine interior regular assignments discharge the old frame's charging
geometry, including arbitrary retained evaluation prefixes and terminal reserve. -/
theorem scheduled_regular_old_count {α : Type} [Fintype α] [DecidableEq α]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+d:ℕ)) (hr : DepthAverage.Regular η Q) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    branchingCount (splitFrame Old r d) (· ∈ shiftedPrefixDepths (stem Base r) d)=0 := by
  apply scheduled_frame_old_count H r d k a C e Q had
  let R : ReducedTopology := .node k hk C
  let q : R.Vertex → ℕ := rootSchedule (hk := hk) (r+1+d) (fun j v => (Q (e j v)).val)
  have hq : Admissible R q (d+1) (d+1+(H+1+r)) := by
    change d+1 ≤ r+1+d ∧ r+1+d<d+1+(H+1+r) ∧ _
    refine ⟨by omega,by omega,?_⟩
    intro j
    simpa only [q,rootSchedule,show d+1+(H+1+r)=r+1+d+1+H by omega] using had j
  have hv (v : R.Vertex) : ∃ x : α, q v=(Q x).val := by
    cases v with
    | none => exact ⟨a,ha.symm⟩
    | some v => exact ⟨e v.1 v.2,rfl⟩
  have hno : NoAdjacentBranchDepths (realize (H+1+r) (d+1) R q) := by
    apply realize_no_adjacent_at _ _ _ _ hq
    intro u v
    obtain ⟨x,hx⟩ := hv u
    obtain ⟨y,hy⟩ := hv v
    rw [hx,hy]
    let : NeZero (H+1+1+r+1+d) := ⟨by omega⟩
    exact DepthAverage.regular_no_adjacent_values Q hlarge hr x y
  have hlower : ∀ v, d+1+r≤q v := by
    intro v
    cases v with
    | none => change d+1+r ≤ r+1+d; omega
    | some v =>
      have h := admissible_lower (C v.1) (fun w => (Q (e v.1 w)).val) (had v.1) v.2
      change d+1+r≤(Q (e v.1 v.2)).val
      omega
  rw [realize_stem (H+1) r (d+1) R q hlower] at hno
  change NoAdjacentBranchDepths (stem (realize (H+1) (d+1+r) (.node k hk C) q) r) at hno
  simp only [realize,q,rootSchedule,show ¬d+1+r < r+1+d by omega,ite_false] at hno
  simpa only [show d+1+r+1=r+1+d+1 by omega] using hno

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CanonicalRegularMultileaf
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory PrescribedTree HeterogeneousMarks
open scoped BigOperators
variable {α Ω J X Y : Type} [Fintype α] [DecidableEq α]
    [Fintype Ω] {Mark : J → Type} [∀ j, Fintype (Mark j)] [Countable J]
    [MeasurableSpace J] [MeasurableSingletonClass J] [MeasurableSpace X] [MeasurableSpace Y]
    {M N t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

 
theorem canonical_regular_root_multileaf (μ : Measure (FullRootState Y X J M))
    [IsProbabilityMeasure μ]
    (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+d:ℕ)) (hr : DepthAverage.Regular η Q)
    (T : KernelTower Ω (H+1+1+r+1+d)) (P : (j : J) → Fin (H+1+1+r+1+d) → FiniteLaw (Mark j))
    (m : Fin (H+1+1+r+1+d) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (H+1+1+r+1+d) → ℝ)
    (old : (j : J) → FinitePath Ω (H+1+1+r+1+d) → FinitePath (Mark j) (H+1+1+r+1+d) → ℝ)
    (V : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i|≤1) :
    let K := rootTower T P m base old
    let f := rootVector V (I := J) (A := Mark) (X := X) (Y := Y) (M := M)
    let L := H+1+1+r+1+d
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) d
    let S := splitFrame OldNode r d
    let RawTarget := splitFrame NewNode (r+1) d
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r d (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) d (K' z) (f' z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    let _ := fun z x i => splitProjector OldNode r d (K z) (fun y => f z y i) x
    let A := fun z => spatialProduct (fun _ : Option (Fin (t+1)) => f z)
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) d 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) d 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r d 0 b
    let _ := splitFrameLeaf OldNode r d 1 b
    let m := grid L 0 L
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    (((d:ℝ)+2)/(L:ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) d (K z) (f z) ∂μ) ≤
      2*(2*(L:ℝ)⁻¹ + |matrixRootCovariance μ (rootAlphabet (Ω := Ω) (A := Mark)) Target S q K m (v::cs) x A
          (fun z => treeOverlap S (f z))|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      (((d:ℝ)+2)/(L:ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  have hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val := by
    intro j v
    rw [ha]
    exact admissible_lower (C j) _ (had j) v
  let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
  let B := shiftedPrefixDepths (stem BaseNode r) d
  have hS := scheduled_regular_old_count H r d k hk a C e Q ha had hlarge hr
  exact physical_scheduled_root_multileaf_moments μ H r d k hk a C e Q ha hQ T P m base old V hb hV
    b b' q0 hq none (some (Fin.last t)) (by simp) hu hv B hS
    (canonicalMatrixTail t) (canonicalMatrixTail_nodup t) (canonicalMatrixTail_not_mem t)
    (canonicalMatrixTail_full t)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalTreeMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set
open scoped NNReal BigOperators Topology
variable {L p k : ℕ}

/-- The canonical insertion history really has the precise head/tail
required by the integrated proper-child inequality. -/
lemma physicalTreeMatrixCovariance_history (m : Fin (L+1) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (M : Model p) (C H : ℝ)
    (N : ℕ) (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) (q : Option (Fin (k+1)) → T.Leaf) :
    physicalTreeMatrixCovariance m S a M C H N u T q =
      matrixRootCovariance
        (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
          (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
        (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) T S q
        (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
          (fun i => prior i.1.1) m (physicalBase M C H N)
          (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
        (Fin.cons 0 m) (some (Fin.last k)::canonicalMatrixTail k) a
        (fun z => spatialProduct (fun _ => rootVector
          (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z))
        (fun z => treeOverlap S (rootVector
          (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)) z)) := by
  unfold physicalTreeMatrixCovariance
  rw [canonicalMatrixHistory]

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalGridMultileaf
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {p t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

/-- Physical specialization of the non-singleton induction step. The only
signed history is literally the covariance controlled by joint_grid_selection;
all other errors are the single-copy shift error and proper-child root energies.
The evaluation depth is positive, as it is on the regular depth domain. -/
theorem physical_grid_root_multileaf (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
    (u : Spec (H+1+1+r+1+d) × ℕ → ℝ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+(d+1))) (ha : (Q a).val=r+1+(d+1))
    (had : ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) (r+1+(d+1)+1) (r+1+(d+1)+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+(d+1):ℕ)) (hr : DepthAverage.Regular η Q) :
    let L₀ := H+1+1+r+1+d
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
      (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
      (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    let ht := shiftedFrameHeight H r (d+1)
    let OldChild := fun j => realize (H+1) (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) (d+1)
    let S := splitFrame OldNode r (d+1)
    let RawTarget := splitFrame NewNode (r+1) (d+1)
    let Target := heightCast ht RawTarget
    let K' := fun z => kernelHeightCast ht.symm (K z)
    let f' := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (OldChild j) r (d+1) (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, descendantEnergyAt (NewChild j) (r+1) (d+1) (K' z) (f' z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) (d+1) 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) (d+1) 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r (d+1) 0 b
    let m := Fin.cons 0 (gridExponents L₀)
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, shapeEnergyAt (stem OldNode r) (d+1) (K z) (f z) ∂μ) ≤
      2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  let L₀ := H+1+1+r+1+d
  have hh := canonical_regular_root_multileaf
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)) H r (d+1) k hk a C e Q ha had hlarge hr
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
    (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
    (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
    (measurable_physicalBase M θB hB N) (readVector_bound _) b b' q0 hq hu hv
  dsimp only at hh
  have hg : grid (H+1+1+r+1+(d+1)) 0 (H+1+1+r+1+(d+1)) =
      Fin.cons 0 (gridExponents L₀) := (gridExponents_cons L₀).symm
  simp only [hg] at hh
  rw [physicalTreeMatrixCovariance_history]
  exact hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalScheduledStep
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology
open scoped NNReal BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {p t : ℕ}
attribute [local irreducible] projectionShiftError matrixProjectionError oldProjectionError
    matrixObservableHistory KernelTower.halfTripleDifferenceAt splitProjector

 
theorem physical_grid_scheduled_step_oai (M : Model p) (θB hB : ℝ) (N H r d : ℕ)
    (u : Spec (H+1+1+r+1+d) × ℕ → ℝ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+(d+1))) (ha : (Q a).val=r+1+(d+1))
    (had : ∀ j, ReducedTopology.Admissible (C j) (fun v => (Q (e j v)).val) (r+1+(d+1)+1) (r+1+(d+1)+1+H))
    {η : ℝ} (hlarge : 1<η*(H+1+1+r+1+(d+1):ℕ)) (hr : DepthAverage.Regular η Q) :
    let L₀ := H+1+1+r+1+d
    let μ := fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L₀) N) (M.alpha*N) (scoreRate N)
    let K := rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L₀)
      (fun i : Labels L₀ (Site N) => prior i.1.1) (gridExponents L₀) (physicalBase M θB hB N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
    let f := rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L₀ x) v))
      (I := Labels L₀ (Site N)) (A := fun i => Alphabet i.1.1) (X := Bond p N) (Y := ℝ) (M := N)
    let ht := shiftedFrameHeight H r (d+1)
    let OldChild := fun j => realize (H+1) (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val+1)
    let OldNode := PrescribedTree.node k OldChild
    let NewNode := PrescribedTree.node k NewChild
    let BaseNode := PrescribedTree.node k (fun j => realize H (r+1+(d+1)+1) (C j) (fun v => (Q (e j v)).val))
    let B := shiftedPrefixDepths (stem BaseNode r) (d+1)
    let S := splitFrame OldNode r (d+1)
    let RawTarget := splitFrame NewNode (r+1) (d+1)
    let Target := heightCast ht RawTarget
    let _ := fun z => kernelHeightCast ht.symm (K z)
    let _ := fun z => vectorHeightCast ht.symm (f z)
    let W := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+(d+1)) (C j) (fun v => (Q (e j v)).val) (K z) (f z) ∂μ)
    let W' := (k:ℝ)*∑ j, Real.sqrt (∫ z, scheduledShapeEnergy (L₀+1) (r+1+1+(d+1)) (C j) (fun v => (Q (e j v)).val+1) (K z) (f z) ∂μ)
    let h := fun z => projectionShiftError a C e (K z) (f z) Q
    ∀ (b : OldNode.Leaf) (b' : NewNode.Leaf) (q0 : Option (Fin (t+1)) → RawTarget.Leaf),
      Function.Bijective q0 → q0 none=splitFrameLeaf NewNode (r+1) (d+1) 0 b' →
        q0 (some (Fin.last t))=splitFrameLeaf NewNode (r+1) (d+1) 1 b' →
    let v := some (Fin.last t)
    let cs := canonicalMatrixTail t
    let q := fun j => leafHeightCast ht RawTarget (q0 j)
    let x := splitFrameLeaf OldNode r (d+1) 0 b
    let m := Fin.cons 0 (gridExponents L₀)
    let J := partialKappa Target m (Finset.univ.image q)/
      partialKappa Target m ((insert v ({none}:Finset (Option (Fin (t+1))))).image q)
    ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(∫ z, scheduledShapeEnergy (L₀+1) (d+1) (.node k hk C) (rootSchedule (r+1+(d+1)) (fun j v => (Q (e j v)).val)) (K z) (f z) ∂μ) ≤
      2*(2*((L₀+1:ℕ):ℝ)⁻¹ + |physicalTreeMatrixCovariance (gridExponents L₀) S x M θB hB N u Target q|/|J|+
        (2*Real.sqrt W'+(∫ z, h z ∂μ))*shiftedCharge B Target S (v::cs).length/|J|+
        pairHistoryMass S m x*(2*Real.sqrt W))+
      ((((d+1:ℕ):ℝ)+2)/((L₀+1:ℕ):ℝ))*(16*W) := by
  dsimp only
  intro b b' q0 hq hu hv
  have hh := physical_grid_root_multileaf M θB hB N H r d u k hk a C e Q ha had hlarge hr b b' q0 hq hu hv
  dsimp only at hh
  have hQ : ∀ j v, r+1+(d+1)+1≤(Q (e j v)).val := by
    intro j v
    exact admissible_lower (C j) _ (had j) v
  conv_lhs =>
    arg 2
    arg 2
    ext z
    exact scheduledShapeEnergy_node (H+1) r (d+1) k hk C _ hQ _ _
  simp_rw [descendantEnergyAt_eq_scheduled] at hh
  simp only [scheduledShapeEnergy_heightCast] at hh
  exact hh

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step_oai := @OAI.DilutedSpinGlass.UniversalDictionary.physical_grid_scheduled_step_oai
