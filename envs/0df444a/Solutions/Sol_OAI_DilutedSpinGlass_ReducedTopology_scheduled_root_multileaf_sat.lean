-- Prove2me | solution 1 for OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:37:58.663293+00:00
-- url     : https://prove2.me/submissions/896048b0-7e09-491a-a32c-78efc799f922

import Mathlib
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_root_matrix_three_copy_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProducts
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.instDecidable_11
theorem chargeBound_nonneg {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (k b : ℕ) :
    0 ≤ chargeBound C D k b := by
  induction k generalizing b with
  | zero => simp only [chargeBound]; split <;> norm_num
  | succ k ih =>
    cases b with
    | zero => exact mul_nonneg hC (ih 0)
    | succ b => exact add_nonneg (mul_nonneg hC (ih _)) (mul_nonneg hD (ih _))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeEmbedding
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_LabeledColorHistory
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeterogeneousProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SplitDepthContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TripleMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]
lemma branch_leaf_marginal {n : ℕ} (C : PrescribedTree n) (μ : FiniteLaw Ω)
    (K : Ω → KernelTower Ω n) (a : C.Leaf) (F : FinitePath Ω (n+1) → ℝ) :
    (μ.bind (fun z => C.sampleLaw (K z))).expect
      (fun x => F (x.1,C.pathAt a x.2)) = (KernelTower.law (n+1) (μ,K)).expect F := by
  erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect n (μ,K)]
  exact μ.expect_congr (fun z => leaf_marginal C (K z) a (fun y => F (z,y)))

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootMatrixTriple
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeProjectionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShiftedTree
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMatrix
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

noncomputable local instance shapeMatrixPropDecidable_r48e9dc_1 (proposition : Prop) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_StemTwoSideProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_DoubledStemProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_StemCovarianceTransfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixLeafProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CoordinateFiber
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_PrefixProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MultileafMatrixPointwise
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootMultileafMatrix
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
  have h := root_matrix_three_copy_sat μ Ω hL Q Target S q hq hS K a c hac cs hcs hdis hfull
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProperChildScheduleContinuity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConditionalScheduledMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FirstSplitSchedule
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ProjectionShiftError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance projectionShiftErrorPropDecidable_r48e9dc_1 (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω α ι : Type} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype ι]
  {L N : ℕ} [NeZero L]


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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProjectionShiftError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_HeightTransport
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledFrameError
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledRootMultileaf
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
theorem scheduled_root_multileaf_sat_oai {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
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

theorem solution : type_of% @OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat_oai := @OAI.DilutedSpinGlass.ReducedTopology.scheduled_root_multileaf_sat_oai
