-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:04.066271+00:00
-- url     : https://prove2.me/submissions/b3f0529a-955c-480c-9687-1241149203e2

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalSubtree_limsup_tendsto

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

variable {n : ℕ}

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

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeDerivatives
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

/-- Lipschitz sequences have a square-integrable Poisson law. -/
theorem poisson_memLp_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    MemLp f 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
  apply poisson_integrable_quadratic r (A := 2*(f 0)^2) (B := 2*C^2)
  intro n
  have h := hL n 0
  simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  have hh : |f n| ≤ C*(n : ℝ)+|f 0| := by
    calc |f n| = |(f n-f 0)+f 0| := by rw [sub_add_cancel]
         _ ≤ |f n-f 0| + |f 0| := abs_add_le _ _
         _ ≤ C*(n : ℝ)+|f 0| := by linarith
  have hb : 0 ≤ C*(n : ℝ)+|f 0| := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f n), sq_abs (f 0),
    sq_nonneg (C*(n : ℝ)-|f 0|), mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hb (abs_nonneg (f n)))]

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- Adding one root coordinate gives the full Lipschitz bound in the count. -/
theorem nat_lipschitz_of_step {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ n, |f (n+1)-f n| ≤ C) : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)| := by
  have hle : ∀ n m, n ≤ m → |f m-f n| ≤ C*((m : ℝ)-(n : ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have ha : |f (m+1)-f n| ≤ |f (m+1)-f m|+|f m-f n| := by
        calc
          |f (m+1)-f n| = |(f (m+1)-f m)+(f m-f n)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      push_cast
      nlinarith [h m]
  intro n m
  rcases le_total n m with hnm | hmn
  · rw [abs_sub_comm (f n), abs_sub_comm (n : ℝ), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ m))]
    exact hle n m hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ n))]
    exact hle m n hmn

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConvexBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 
theorem integral_abs_le_sqrt_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have hn := variance_nonneg (fun x => ‖f x‖) μ
  rw [variance_eq_sub hf.norm] at hn
  simp only [Real.norm_eq_abs, Pi.pow_apply, sq_abs] at hn
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ActualCharging
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology BigOperators

/-- First take each fixed-grid limsup, then the grid limit, and only then
let the arbitrary regularity cutoff tend to zero. -/
lemma squeeze_triangle_grid_zero (a : ℕ → ℝ) (C : ℝ) (ha : ∀ n, 0 ≤ a n)
    (hC : 0 ≤ C) (b : ℝ → ℕ → ℝ)
    (hb : ∀ η, 0<η → Tendsto (b η) atTop (𝓝 (C*η)))
    (hbound : ∀ η, 0<η → ∀ n, a n ≤ b η n) :
    Tendsto a atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(2*(C+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hcut : C*η<ε := by
    dsimp [η]
    have h : C/(2*(C+1))<1 := (div_lt_one (by positivity)).mpr (by linarith)
    calc
      C*(ε/(2*(C+1))) = ε*(C/(2*(C+1))) := by ring
      _ < ε*1 := mul_lt_mul_of_pos_left h hε
      _ = ε := mul_one ε
  obtain ⟨n,hn⟩ := (eventually_atTop.mp ((hb η hη).eventually (Iio_mem_nhds hcut)))
  refine ⟨n,fun m hm => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (ha m)]
  exact (hbound η hη m).trans_lt (hn m hm)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_DeviationLimitTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma limsup_affine_bound (a b : ℕ → ℝ) (c d : ℝ) (hc : 0 ≤ c)
    (ha : ∀ n, 0≤a n) (hb : IsBoundedUnder (·≤·) atTop b)
    (h : ∀ n, a n ≤ c*b n+d) : limsup a atTop ≤ c*limsup b atTop+d := by
  have he (ε : ℝ) (hε : 0<ε) : limsup a atTop ≤ c*(limsup b atTop+ε)+d := by
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha).frequently))
    filter_upwards [eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) hb] with n hn
    exact (h n).trans (add_le_add (mul_le_mul_of_nonneg_left hn.le hc) le_rfl)
  have ht : Tendsto (fun ε : ℝ => c*(limsup b atTop+ε)+d) (𝓝[>] 0)
      (𝓝 (c*limsup b atTop+d)) := by
    have hh : ContinuousAt (fun ε : ℝ => c*(limsup b atTop+ε)+d) 0 := by fun_prop
    simpa using hh.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall he)

lemma doubleLimit_young (a b : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0≤C)
    (ha : ∀ L n, 0≤a L n) (hb : ∀ L, IsBoundedUnder (·≤·) atTop (b L))
    (hbound : ∀ t, 0<t → ∀ L n, a L n≤C*(b L n/(2*t)+t/2))
    (hdecay : Tendsto (fun L => limsup (b L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have hupper (t : ℝ) (ht : 0<t) (L : ℕ) :
      limsup (a L) atTop≤C*(limsup (b L) atTop/(2*t)+t/2) := by
    have hh := limsup_affine_bound (a L) (b L) (C/(2*t)) (C*t/2)
      (by positivity) (ha L) (hb L) (fun n => (hbound t ht L n).trans_eq (by ring))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hnonneg (L : ℕ) : 0≤limsup (a L) atTop := by
    obtain ⟨B,hB⟩ := hb L
    have hB' : ∀ᶠ n in atTop, b L n≤B := hB
    have ha' : IsBoundedUnder (·≤·) atTop (a L) := by
      apply isBoundedUnder_of_eventually_le (a := C*(B/2+1/2))
      filter_upwards [hB'] with n hn
      apply (hbound 1 (by norm_num) L n).trans
      apply mul_le_mul_of_nonneg_left _ hC
      norm_num
      linarith
    apply le_limsup_of_le ha'
    intro x hx
    obtain ⟨n,hn⟩ := hx.exists
    exact (ha L n).trans hn
  apply squeeze_triangle_grid_zero _ (C/2) hnonneg (by positivity)
    (fun t L => C*(limsup (b L) atTop/(2*t)+t/2)) _ (fun t ht L => hupper t ht L)
  intro t ht
  convert ((hdecay.div_const (2*t)).add_const (t/2)).const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  simp
  ring

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeEmbedding
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

namespace SplitMap
variable {n : ℕ} {T S : PrescribedTree n}

lemma injective (f : SplitMap T S) : Function.Injective f.leaf := by
  intro a b h
  apply (splitDepth_eq_height T a b).mp
  rw [← f.split,h,splitDepth_self]

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

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.edgeFintype _root_.OAI.DilutedSpinGlass.PrescribedTree.leafDecidableEq _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

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

end DilutedSpinGlass.PrescribedTree

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_JointRootLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePiInjective
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShapeMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_TreeMeasurable
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_SingletonRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_ParameterRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_MatrixEnergy
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
variable {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C] {L N : ℕ}

noncomputable local instance matrixEnergyPropDecidable_r13125a_1 (proposition : Prop) :
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

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ShiftedTree
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

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.shiftedTreeDecidable
lemma leaves_unary {n : ℕ} (S : PrescribedTree n) : leaves (unary S) = leaves S := by
  change (∑ _ : Fin 1, leaves S) = _
  simp

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ScheduledTopology
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
lemma admissible_mono_lower (S : ReducedTopology) (q : S.Vertex → ℕ)
    {lo lo' hi : ℕ} (hlo : lo'≤lo) (h : Admissible S q lo hi) : Admissible S q lo' hi := by
  cases S with
  | leaf => trivial
  | node k hk C => exact ⟨hlo.trans h.1,h.2⟩

lemma admissible_lower (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : lo ≤ q v := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.1
    | some v => exact h.1.trans ((Nat.le_succ _).trans (ih v.1 _ (h.2.2 v.1) v.2))

lemma admissible_upper (S : ReducedTopology) (q : S.Vertex → ℕ) {lo hi : ℕ}
    (h : Admissible S q lo hi) (v : S.Vertex) : q v < hi := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none => exact h.2.1
    | some v => exact ih v.1 _ (h.2.2 v.1) v.2

lemma realize_leaves (r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : Admissible S q d (d+r)) :
    PrescribedTree.leaves (realize r d S q) = Fintype.card S.Leaf := by
  induction r generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := h.2.1; have := h.1; omega
  | succ r ih =>
    cases S with
    | leaf =>
      rw [realize,PrescribedTree.leaves_unary]
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      rw [realize]
      split_ifs with hd
      · rw [PrescribedTree.leaves_unary]
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩
      · have he : q none=d := by have := h.1; omega
        simp only [PrescribedTree.leaves]
        change _ = Fintype.card ((i : Fin k) × (C i).Leaf)
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro i _
        apply ih
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2.2 i

end ReducedTopology
end DilutedSpinGlass
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

noncomputable local instance shapeMatrixPropDecidable_r13125a_1 (proposition : Prop) :
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_StemCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

lemma leaf_card_pos (S : ReducedTopology) : 0<Fintype.card S.Leaf := by
  induction S with
  | leaf => exact Nat.zero_lt_one
  | node k hk C ih =>
    change 0<Fintype.card ((j : Fin k) × (C j).Leaf)
    rw [Fintype.card_sigma]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨⟨0,k.property⟩,Finset.mem_univ _,ih _⟩

/-- Every proper child consumes strictly fewer leaves, without suppressing
or identifying distinct child occurrences with the same topology. -/
lemma child_leaf_card_lt (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    (j : Fin k) : Fintype.card (C j).Leaf <
      Fintype.card (ReducedTopology.node k hk C).Leaf := by
  classical
  have hi : ∃ i : Fin k, i≠j := by
    by_cases hj : j=⟨0,k.property⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      intro h
      have hh := congrArg Fin.val (h.trans hj)
      change (1:ℕ)=0 at hh
      omega
    · exact ⟨⟨0,k.property⟩,Ne.symm hj⟩
  obtain ⟨i,hij⟩ := hi
  change _ < Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma,← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  apply Nat.lt_add_of_pos_right
  exact (leaf_card_pos (C i)).trans_le
    (Finset.single_le_sum (f := fun x : Fin k => Fintype.card (C x).Leaf) (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩))

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FirstSplitSchedule
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
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma realize_unary_of_later (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d<q v) :
    realize (H+1) d S q=PrescribedTree.unary (realize H (d+1) S q) := by
  cases S with
  | leaf => rfl
  | node k hk C => rw [realize,ite_eq_left (hq none)]

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalPairConnection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProjectionIntegrability
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonSmoothing
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Poisson's add-one identity gives a *smoothing* estimate for every bounded
 test, without any regularity in the count. This is the needed large-rate
 transfer for the cavity reservoir, not the O(1) unmatched-points estimate. -/
lemma poisson_bounded_shift (r : ℝ≥0) (hr : 0 < r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)| ≤
      B / Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  have hreal : (0:ℝ) < r := hr
  have hi : Integrable f (poissonMeasure r) := (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hi' : Integrable (fun n => f (n+1)) (poissonMeasure r) :=
    (bounded_memLp (Measurable.of_discrete) (fun n => hf (n+1)) 1).integrable le_rfl
  have hn : MemLp (fun n : ℕ => (n:ℝ)) 2 (poissonMeasure r) :=
    poisson_memLp_lipschitz r (by norm_num : (0:ℝ)≤1) (fun _ _ => by simp)
  have hc := hn.sub (memLp_const (r:ℝ))
  have hcs : (∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r)≤Real.sqrt r := by
    simpa only [Pi.sub_apply,poisson_variance] using integral_abs_le_sqrt_sq (poissonMeasure r) hc
  have hnf : Integrable (fun n : ℕ => (n:ℝ)*f n) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := B)
    intro n
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    simpa only [zero_add,mul_comm] using mul_le_mul_of_nonneg_left (hf n) (Nat.cast_nonneg n)
  have hid : Integrable (fun n : ℕ => ((n:ℝ)-r)*f n) (poissonMeasure r) := by
    have heq : (fun n : ℕ => ((n:ℝ)-r)*f n)=
        (fun n : ℕ => (n:ℝ)*f n)-(fun n => (r:ℝ)*f n) := by
      funext n
      change ((n:ℝ)-r)*f n=(n:ℝ)*f n-(r:ℝ)*f n
      ring
    rw [heq]
    exact hnf.sub (hi.const_mul r)
  have he : (r:ℝ)*((∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)) =
      ∫ n : ℕ, ((n:ℝ)-r)*f n ∂poissonMeasure r := by
    simp_rw [sub_mul]
    rw [integral_sub hnf (hi.const_mul r),integral_const_mul,poisson_add_one r f hi',mul_sub]
  have hab := abs_integral_le_integral_abs (f := fun n : ℕ => ((n:ℝ)-r)*f n) (μ := poissonMeasure r)
  have hm : (∫ n : ℕ, |((n:ℝ)-r)*f n| ∂poissonMeasure r) ≤
      B * Real.sqrt r := by
    calc
      _ ≤ ∫ n : ℕ, |(n:ℝ)-r| * B ∂poissonMeasure r := by
        apply integral_mono hid.abs ((hc.integrable (by norm_num)).abs.mul_const B)
        intro n
        change |((n:ℝ)-r)*f n| ≤ |(n:ℝ)-r| * B
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hf n) (abs_nonneg _)
      _ = B*(∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r) := by rw [integral_mul_const,mul_comm]
      _ ≤ B*Real.sqrt r := mul_le_mul_of_nonneg_left hcs hB
  rw [← he,abs_mul,abs_of_pos hreal] at hab
  have hs : 0<Real.sqrt (r:ℝ) := Real.sqrt_pos.2 hreal
  have hsq := Real.sq_sqrt (le_of_lt hreal)
  rw [le_div_iff₀ hs]
  nlinarith [hab.trans hm]

lemma poisson_bounded_rate_add (r s : ℝ≥0) (hr : 0 < r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤
      B*(s:ℝ)/Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  let g (k : ℕ) := ∫ n, f (n+k) ∂poissonMeasure r
  have hg (k : ℕ) : |g (k+1)-g k|≤B/Real.sqrt r := by
    simpa only [g,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      poisson_bounded_shift r hr (f := fun n => f (n+k)) (fun n => hf (n+k))
  have hl := nat_lipschitz_of_step (div_nonneg hB (Real.sqrt_nonneg r)) hg
  have hgi : Integrable g (poissonMeasure s) :=
    (bounded_memLp (Measurable.of_discrete) (fun k => abs_integral_le_bound (μ := poissonMeasure r) (fun n => hf (n+k))) 1).integrable le_rfl
  have hc : |(∫ k, g k ∂poissonMeasure s)-g 0| ≤ B/Real.sqrt r*(s:ℝ) := by
    have hconst : (∫ _ : ℕ, g 0 ∂poissonMeasure s)=g 0 := by simp
    rw [← hconst,← integral_sub hgi (integrable_const (g 0))]
    calc
      _ ≤ ∫ k, |g k-g 0| ∂poissonMeasure s := abs_integral_le_integral_abs
      _ ≤ ∫ k : ℕ, (B/Real.sqrt r)*(k:ℝ) ∂poissonMeasure s := by
        apply integral_mono (hgi.sub (integrable_const (g 0))).abs ((poisson_integrable_count s).const_mul _)
        intro k
        change |g k-g 0|≤(B/Real.sqrt r)*(k:ℝ)
        simpa only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k)] using hl k 0
      _ = _ := by rw [integral_const_mul,poisson_mean]
  have hi (t : ℝ≥0) : Integrable f (poissonMeasure t) :=
    (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hconv : (∫ k, g k ∂poissonMeasure s)=∫ n, f n ∂poissonMeasure (r+s) := by
    rw [add_comm r s,← poissonMeasure_conv_poissonMeasure s r]
    rw [integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r))]
    simp only [g,Nat.add_comm]
  dsimp only [g] at hc
  simp only [Nat.add_zero] at hc
  change |(∫ k, g k ∂poissonMeasure s)-(∫ n, f n ∂poissonMeasure r)|≤_ at hc
  rw [hconv] at hc
  simpa only [div_mul_eq_mul_div] using hc
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RegularNodeEstimates
attribute [-instance] _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

lemma BoundedDistance.prod {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (μ.prod τ) (ν.prod τ) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (κ.prod τ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod _ (hi μ),integral_prod _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_right'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (x,y)))

lemma BoundedDistance.prod_left {μ ν : Measure X} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (h : BoundedDistance μ ν d)
    (τ : Measure Y) [IsProbabilityMeasure τ] :
    BoundedDistance (τ.prod μ) (τ.prod ν) d := by
  intro f hm B hf
  have hi (κ : Measure X) [IsProbabilityMeasure κ] : Integrable f (τ.prod κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_prod_symm _ (hi μ),integral_prod_symm _ (hi ν)]
  exact h _ hm.stronglyMeasurable.integral_prod_left'.measurable B
    (fun x => abs_integral_le_bound (fun y => hf (y,x)))

lemma poisson_boundedDistance (r s : ℝ≥0) (hr : 0 < r) :
    BoundedDistance (ProbabilityTheory.poissonMeasure (r+s))
      (ProbabilityTheory.poissonMeasure r) ((s:ℝ)/Real.sqrt r) := by
  intro f _ B hf
  simpa only [mul_div_assoc] using poisson_bounded_rate_add r s hr hf

lemma BoundedDistance.familyLaw {I : Type} [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {Z : I → Type} [∀ i, MeasurableSpace (Z i)]
    {μ ν : Measure I} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (h : BoundedDistance μ ν d)
    (κ : (i : I) → Measure (Z i)) [∀ i, IsProbabilityMeasure (κ i)] :
    BoundedDistance (familyLaw μ κ) (familyLaw ν κ) d := by
  intro f hm B hf
  have hi (ρ : Measure I) [IsProbabilityMeasure ρ] : Integrable f (DilutedSpinGlass.familyLaw ρ κ) :=
    (bounded_memLp hm hf 1).integrable le_rfl
  rw [integral_familyLaw μ κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi μ),
    integral_familyLaw ν κ (fun i x => f ⟨i,x⟩)
      (fun i => hm.comp (measurable_sigmaMk i)) (hi ν)]
  exact h _ (measurable_of_countable _) B
    (fun i => abs_integral_le_bound (fun x => hf ⟨i,x⟩))

lemma fullRoot_boundedDistance {M : ℕ} {I : Type} [MeasurableSpace I]
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s t : ℝ≥0) (hr : 0 < r) :
    BoundedDistance (fullRootLaw ξ μ ν (r+s) t) (fullRootLaw ξ μ ν r t)
      ((s:ℝ)/Real.sqrt r) := by
  exact (((poisson_boundedDistance r s hr).familyLaw
    (fun k => rootLaw k (fun _ => μ))).prod (compoundRootLaw ν t)).prod_left (rootLaw M ξ)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootOverlapVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

lemma mixedVariance_eq_centered (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    mixedVariance μ Ω P F = ∫ z, (P z).expect
      (fun w => (F z w-(∫ z, (P z).expect (F z) ∂μ))^2) ∂μ := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  have he (z : Z) : (P z).expect (fun w => (F z w-c)^2)=
      (P z).expect (fun w => (F z w)^2) - 2*c*(P z).expect (F z)+c^2 := by
    calc
      _ = (P z).expect (fun w => (F z w)^2-(2*c)*F z w+c^2) :=
        (P z).expect_congr (fun w => by ring)
      _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]
  change _=∫ z, (P z).expect (fun w => (F z w-c)^2) ∂μ
  simp_rw [he]
  have hm : Integrable (fun z => 2*c*(P z).expect (F z)) μ := hF.const_mul (2*c)
  have hd : Integrable (fun z => (P z).expect (fun w => (F z w)^2)-2*c*(P z).expect (F z)) μ := hFsq.sub hm
  rw [integral_add hd (integrable_const _),
    integral_sub hFsq hm,integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  unfold mixedVariance
  dsimp only [c]
  ring

lemma mixedVariance_nonneg (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ) :
    0 ≤ mixedVariance μ Ω P F := by
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  exact integral_nonneg (fun z => (P z).expect_nonneg (fun _ => sq_nonneg _))

lemma mixedVariance_le_one (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (hF : ∀ z w, |F z w|≤1) : mixedVariance μ Ω P F≤1 := by
  have he : ∀ z, (P z).expect (fun w => (F z w)^2)≤1 := by
    intro z
    exact ((P z).expect_mono (fun w => (sq_le_one_iff_abs_le_one _).mpr (hF z w))).trans_eq
      ((P z).expect_const 1)
  have h := integral_mono hFsq (integrable_const (1:ℝ)) he
  simp only [integral_const,probReal_univ,one_smul] at h
  unfold mixedVariance
  linarith [sq_nonneg (∫ z, (P z).expect (F z) ∂μ)]

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixedDeviation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

lemma mixedDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ) :
    0 ≤ mixedDeviation μ Ω P F := integral_nonneg (fun z => (P z).expect_nonneg (fun _ => abs_nonneg _))

lemma expect_centered_sq (Ω : Type) [Fintype Ω] (P : FiniteLaw Ω) (F : Ω → ℝ) (c : ℝ) :
    P.expect (fun w => (F w-c)^2)=P.expect (fun w => (F w)^2)-2*c*P.expect F+c^2 := by
  calc
    _ = P.expect (fun w => (F w)^2-(2*c)*F w+c^2) := P.expect_congr (fun w => by ring)
    _ = _ := by simp only [expect_add,expect_sub,expect_mul_left,expect_const]

lemma mixedDeviation_le_variance (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (P : (z : Z) → FiniteLaw (Ω z)) (F : (z : Z) → Ω z → ℝ)
    (hF : Integrable (fun z => (P z).expect (F z)) μ)
    (hFsq : Integrable (fun z => (P z).expect (fun w => (F z w)^2)) μ)
    (habs : Integrable (fun z => (P z).expect (fun w => |F z w-(∫ y, (P y).expect (F y) ∂μ)|)) μ)
    {t : ℝ} (ht : 0<t) :
    mixedDeviation μ Ω P F ≤ mixedVariance μ Ω P F/(2*t)+t/2 := by
  let c := ∫ y, (P y).expect (F y) ∂μ
  have hi : Integrable (fun z => (P z).expect (fun w => (F z w-c)^2)) μ := by
    simp_rw [expect_centered_sq]
    exact (hFsq.sub (hF.const_mul (2*c))).add (integrable_const (c^2))
  rw [mixedVariance_eq_centered μ Ω P F hF hFsq]
  unfold mixedDeviation
  calc
    _ ≤ ∫ z, (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2 ∂μ := by
      apply integral_mono habs ((hi.div_const (2*t)).add (integrable_const (t/2)))
      intro z
      change (P z).expect (fun w => |F z w-c|) ≤ (P z).expect (fun w => (F z w-c)^2)/(2*t)+t/2
      rw [← expect_div,← expect_const (P z) (t/2),← expect_add]
      apply expect_mono
      intro w
      have hs := sq_nonneg (|F z w-c|-t)
      have ha := sq_abs (F z w-c)
      apply (mul_le_mul_iff_left₀ (by positivity : 0<2*t)).mp
      calc
        |F z w-c| * (2*t) ≤ (F z w-c)^2+t^2 := by nlinarith
        _ = ((F z w-c)^2/(2*t)+t/2)*(2*t) := by field_simp
    _ = _ := by rw [integral_add (hi.div_const (2*t)) (integrable_const (t/2)),integral_div,integral_const]; simp only [probReal_univ,one_smul]; rfl

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootOverlapBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma root_overlapMoment_eq [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] (j : ℕ) (z : FullRootState Y X I M) :
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j) =
    rootTreeMean S T Q m base old (fun x => (spatialProduct (fun _ : S.Leaf => V) x)^j) z := by
  unfold rootTreeMean packRoot
  apply FiniteLaw.expect_congr
  intro w
  rw [treeOverlap_eq_spatialProduct]
  rfl

include hb hV in
lemma integrable_rootOverlapMoment (j : ℕ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect (fun w => (treeOverlap S (rootVector V z) w)^j)) μ := by
  simp_rw [root_overlapMoment_eq]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1)
  intro x
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (spatialProduct_bound _ (fun _ => hV) x)

include hb hV in
lemma root_overlapVariance_nonneg :
    0 ≤ overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) := by
  apply FiniteLaw.mixedVariance_nonneg
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2

include hb hV in
lemma root_overlapVariance_le_one :
    overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)≤1 := by
  apply FiniteLaw.mixedVariance_le_one
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · intro z w
    rw [treeOverlap_eq_spatialProduct]
    exact spatialProduct_bound _ (fun _ y i => hV _ i) _

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z]

lemma mixedDeviation_distance {μ ν : Measure Z} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {d : ℝ} (hd : BoundedDistance μ ν d)
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    (F : (z : Z) → Ω z → ℝ) (hF : ∀ z w, |F z w|≤1)
    (hm : Measurable (fun z => (P z).expect (F z)))
    (ha : ∀ c : ℝ, Measurable (fun z => (P z).expect (fun w => |F z w-c|))) :
    |mixedDeviation μ Ω P F-mixedDeviation ν Ω P F|≤3*d := by
  let c := ∫ z, (P z).expect (F z) ∂μ
  let e := ∫ z, (P z).expect (F z) ∂ν
  let G (a : ℝ) (z : Z) := (P z).expect (fun w => |F z w-a|)
  have hc : |c|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have he : |e|≤1 := abs_integral_le_bound (fun z => (P z).abs_expect_le (hF z))
  have hce : |c-e|≤d := by simpa only [one_mul] using hd _ hm 1 (fun z => (P z).abs_expect_le (hF z))
  have hG (a : ℝ) (z : Z) : |G a z|≤1+|a| := by
    apply (P z).abs_expect_le
    intro w
    rw [abs_abs]
    exact (abs_sub (F z w) a).trans (by linarith [hF z w])
  have hi (a : ℝ) (κ : Measure Z) [IsProbabilityMeasure κ] : Integrable (G a) κ :=
    (bounded_memLp (ha a) (hG a) 1).integrable le_rfl
  have hGc (z : Z) : |G c z|≤2 := (hG c z).trans (by linarith)
  have hdist : |(∫ z, G c z ∂μ)-(∫ z, G c z ∂ν)|≤2*d := hd _ (ha c) 2 hGc
  have hchange : |(∫ z, G c z ∂ν)-(∫ z, G e z ∂ν)|≤|c-e| := by
    rw [← integral_sub (hi c ν) (hi e ν)]
    apply abs_integral_le_bound
    intro z
    change |(P z).expect (fun w => |F z w-c|)-(P z).expect (fun w => |F z w-e|)|≤_
    rw [← expect_sub]
    apply (P z).abs_expect_le
    intro w
    calc
      _ ≤ |(F z w-c)-(F z w-e)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |c-e| := by rw [show (F z w-c)-(F z w-e)=e-c by ring,abs_sub_comm]
  change |(∫ z, G c z ∂μ)-(∫ z, G e z ∂ν)|≤_
  have ht := (abs_sub_le (∫ z, G c z ∂μ) (∫ z, G c z ∂ν) (∫ z, G e z ∂ν)).trans
    (add_le_add hdist (hchange.trans hce))
  linarith

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_HierarchyBasic
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.ReducedTopology.hierarchyBasicDecidableEq
lemma mem_nodes (k : ℕ+) (hk : 2≤(k:ℕ)) (s : Finset ReducedTopology)
    (C : Fin k → ReducedTopology) (hC : ∀ j, C j∈s) : .node k hk C∈nodes k hk s := by
  exact Finset.mem_image.mpr ⟨fun j => ⟨C j,hC j⟩,Finset.mem_univ _,rfl⟩

lemma node_arity_le_leaf_card (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology) :
    (k:ℕ)≤Fintype.card (ReducedTopology.node k hk C).Leaf := by
  change _≤Fintype.card ((j : Fin k) × (C j).Leaf)
  rw [Fintype.card_sigma]
  have := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin k) _ => Nat.succ_le_iff.mpr (leaf_card_pos (C j)))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.succ_eq_add_one,zero_add,mul_one] using this

lemma mem_boundedTopologies (n : ℕ) (S : ReducedTopology)
    (h : Fintype.card S.Leaf≤n) : S∈boundedTopologies n := by
  induction n generalizing S with
  | zero => have := leaf_card_pos S; omega
  | succ n ih =>
    cases S with
    | leaf => exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    | node k hk C =>
      apply Finset.mem_union_right
      have hk' := (node_arity_le_leaf_card k hk C).trans h
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨k,by omega⟩,Finset.mem_univ _,?_⟩
      simp only [dite_true,hk]
      apply mem_nodes
      intro j
      apply ih
      have := child_leaf_card_lt k hk C j
      omega

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_QTreeLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

noncomputable local instance qTreeLawDecidableEq_r13125a_1 (type : Type) :
    DecidableEq type := Classical.decEq type
theorem qExpect_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1) (c : ℝ)
    (k : ℕ) (S : PrescribedTree n) : qExpect m (fun _ => c) k S = c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [qExpect, ih]
    rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, sum_gamma, hroot, hend]
    have hn : (leaves S:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (leaves_pos S))
    simp [hn]

theorem qExpect_mono {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) {F G : PrescribedTree n → ℝ}
    (hFG : ∀ S, F S ≤ G S) (k : ℕ) (S : PrescribedTree n) :
    qExpect m F k S ≤ qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S
  | succ k ih =>
    exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ih (grow S v))
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)))

lemma qExpect_nonneg {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ)
    (hF : ∀ S, 0≤F S) (k : ℕ) (S : PrescribedTree n) : 0≤qExpect m F k S := by
  induction k generalizing S with
  | zero => exact hF S
  | succ k ih => exact Finset.sum_nonneg (fun v _ => mul_nonneg
      (div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)) (ih _))

lemma qExpect_mul_const {n : ℕ} (m : Fin (n+1) → ℝ)
    (F : PrescribedTree n → ℝ) (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T*c) k S=qExpect m F k S*c := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,Finset.sum_mul,mul_assoc]

/-- Only the genuine reachable terminal leaf number is required. -/
lemma qExpect_mono_leaves {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n)
    (hFG : ∀ T, T.leaves=S.leaves+k → F T≤G T) :
    qExpect m F k S≤qExpect m G k S := by
  induction k generalizing S with
  | zero => exact hFG S (by omega)
  | succ k ih =>
    apply Finset.sum_le_sum
    intro v _
    apply mul_le_mul_of_nonneg_left
    · apply ih
      intro T hT
      apply hFG
      rw [leaves_grow] at hT
      omega
    · exact div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg _)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLogExpansion
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators

noncomputable local instance finiteLogExpansionDecidableEq_r13125a_1 (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
/-- Suppression of unary vertices loses neither the leveled tree nor labels. -/
theorem exists_realize {r : ℕ} (T : PrescribedTree r) (d : ℕ) :
    ∃ (S : ReducedTopology) (q : S.Vertex → ℕ),
      Admissible S q d (d+r) ∧ realize r d S q=T := by
  induction T generalizing d with
  | leaf => exact ⟨.leaf,Empty.elim,trivial,rfl⟩
  | @node r k C ih =>
    classical
    by_cases hk : (k:ℕ)=1
    · have hk' : k=1 := Subtype.ext hk
      subst k
      obtain ⟨S,q,hq,he⟩ := ih 0 (d+1)
      refine ⟨S,q,?_,?_⟩
      · exact admissible_mono_lower S q (lo := d+1) (Nat.le_succ d) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq)
      · rw [realize_unary_of_later]
        · rw [he]
          unfold PrescribedTree.unary
          congr 1
          funext i
          have hi : i=0 := Fin.ext (by have h := i.isLt; change i.val<1 at h; simp only [Fin.val_zero]; omega)
          rw [hi]
        · intro v
          have := admissible_lower S q hq v
          omega
    · have hk2 : 2≤(k:ℕ) := by have := k.pos; omega
      choose S q hq he using fun i => ih i (d+1)
      let Q : (ReducedTopology.node k hk2 S).Vertex → ℕ :=
        fun v => match v with | none => d | some ⟨i,w⟩ => q i w
      refine ⟨.node k hk2 S,Q,?_,?_⟩
      · refine ⟨le_rfl,by change d<d+(r+1); omega,?_⟩
        intro i
        simpa only [Q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq i
      · simp only [realize,Q,lt_self_iff_false,ite_false]
        congr 1
        funext i
        exact he i

/-- For bounded leaf number there are finitely many possible reduced shapes. -/
theorem exists_bounded_realize {r : ℕ} (T : PrescribedTree r) (K : ℕ)
    (hK : T.leaves≤K) :
    ∃ (S : ReducedTopology), S∈boundedTopologies K ∧
      ∃ q : S.Vertex → Fin r,
        Admissible S (fun v => q v) 0 r ∧ realize r 0 S (fun v => q v)=T := by
  obtain ⟨S,q,ha,he⟩ := exists_realize T 0
  have hc : Fintype.card S.Leaf≤K := by
    rw [← realize_leaves r 0 S q ha,he]
    exact hK
  refine ⟨S,mem_boundedTopologies K S hc,fun v => ⟨q v,?_⟩,by simpa using ha,he⟩
  simpa using admissible_upper S q ha v

end DilutedSpinGlass.ReducedTopology

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SubsetTree
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

lemma leaves_le {n : ℕ} {S T : PrescribedTree n} (f : SplitMap S T) : S.leaves ≤ T.leaves := by
  simpa only [card_leaf] using Fintype.card_le_of_injective f.leaf f.injective

end SplitMap

/-- Every nonempty set of leaf positions has its literal induced leveled tree.
Singleton unary stretches are kept; a SplitMap retains the exact pair splits. -/
theorem exists_subset_tree {n : ℕ} (T : PrescribedTree n) (A : Finset T.Leaf) (hA : A.Nonempty) :
    ∃ (U : PrescribedTree n) (f : SplitMap U T), ∀ b, (∃ a, f.leaf a=b) ↔ b∈A := by
  classical
  induction T with
  | leaf =>
    refine ⟨.leaf,⟨id,fun _ _ => rfl⟩,?_⟩
    intro b
    have hb : b∈A := by obtain ⟨a,ha⟩ := hA; cases a; cases b; exact ha
    exact iff_of_true ⟨b,rfl⟩ hb
  | @node n k C ih =>
    let B (i : Fin k) : Finset (C i).Leaf := Finset.univ.filter (fun b => (⟨i,b⟩ : (PrescribedTree.node k C).Leaf)∈A)
    let I := {i : Fin k // (B i).Nonempty}
    have hn : Nonempty I := by
      obtain ⟨⟨i,b⟩,hb⟩ := hA
      refine ⟨⟨i,⟨b,?_⟩⟩⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb
    let : Nonempty I := hn
    let l : ℕ+ := ⟨Fintype.card I,Fintype.card_pos⟩
    let e : Fin l ≃ I := (Fintype.equivFin I).symm
    choose U f hf using fun i : I => ih i.val (B i.val) i.property
    let g : SplitMap (.node l (fun j => U (e j))) (.node k C) :=
      SplitMap.ofChildren (fun j => (e j).val)
        (fun i j h => e.injective (Subtype.ext h)) (fun j => f (e j))
    refine ⟨.node l (fun j => U (e j)),g,?_⟩
    rintro ⟨i,b⟩
    constructor
    · rintro ⟨⟨j,a⟩,ha⟩
      have hh : (⟨(e j).val,(f (e j)).leaf a⟩ : (PrescribedTree.node k C).Leaf)∈A := by
        exact (Finset.mem_filter.mp ((hf (e j) _).mp ⟨a,rfl⟩)).2
      exact ha ▸ hh
    · intro hb
      have hbi : b∈B i := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      let t : I := ⟨i,⟨b,hbi⟩⟩
      obtain ⟨a,ha⟩ := (hf t b).mpr hbi
      have hh : ∃ a' : (U (e (e.symm t))).Leaf,
          (⟨(e (e.symm t)).val,(f (e (e.symm t))).leaf a'⟩ : (PrescribedTree.node k C).Leaf)=⟨i,b⟩ := by
        rw [Equiv.apply_symm_apply]
        exact ⟨a,congrArg (fun z : (C i).Leaf => (⟨i,z⟩ : (PrescribedTree.node k C).Leaf)) ha⟩
      obtain ⟨a',ha'⟩ := hh
      exact ⟨⟨e.symm t,a'⟩,ha'⟩

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_QSubtreePotential
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n N : ℕ} {Ω : Type} [Fintype Ω]

lemma SplitMap.prod_range {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A) (g : T.Leaf → ℝ) :
    (∏ a : U.Leaf, g (f.leaf a))=∏ b∈A, g b := by
  classical
  apply Finset.prod_bij (fun a _ => f.leaf a)
  · intro a _; exact (hA _).mp ⟨a,rfl⟩
  · intro a _ b _ he; exact f.injective he
  · intro b hb
    obtain ⟨a,ha⟩ := (hA b).mpr hb
    exact ⟨a,Finset.mem_univ _,ha⟩
  · intro a _; rfl

lemma SplitMap.expect_subsetOverlap {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : KernelTower Ω n) (V : FinitePath Ω n → Fin N → ℝ) (g : ℝ → ℝ) :
    (T.sampleLaw K).expect (fun w => g (subsetOverlap T A V w))=
      (U.sampleLaw K).expect (fun w => g (treeOverlap U V w)) := by
  have he := f.expect_paths K (fun x => g ((∑ i, ∏ a : U.Leaf, V (x a) i)/(N:ℝ)))
  simp_rw [subsetOverlap,treeOverlap,leafProduct_eq_prod]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply FiniteLaw.expect_congr
  intro w
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact (f.prod_range A hA (fun b => V (T.pathAt b w) i)).symm

omit [Fintype Ω] in
lemma subsetOverlap_bound (T : PrescribedTree n) (A : Finset T.Leaf)
    (V : FinitePath Ω n → Fin N → ℝ) (hV : ∀ x i, |V x i|≤1) (w : Sample Ω T) :
    |subsetOverlap T A V w|≤1 := by
  have hh := FiniteLaw.abs_dot_le_one (fun i => ∏ a∈A, V (T.pathAt a w) i) (fun _ => (1:ℝ))
    (fun index => by rw [Finset.abs_prod]; exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => hV _ index))
    (fun _ => by norm_num)
  simpa only [FiniteLaw.dot,subsetOverlap,mul_one] using hh

end DilutedSpinGlass.PrescribedTree

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage
open scoped BigOperators

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialDecidableEq
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubtreePotentialPropDecidable
lemma subtreePotential_nonneg {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T) (T) :
    0≤ subtreePotential K F T := by
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> first | exact hF _ | rfl

lemma le_subtreePotential {L K : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ T, 0≤F T)
    {U T : PrescribedTree L} (f : SplitMap U T) (hU : U.leaves≤K) : F U≤ subtreePotential K F T := by
  obtain ⟨S,hS,q,hq,he⟩ := ReducedTopology.exists_bounded_realize U K hU
  subst U
  unfold subtreePotential
  have hn (R : ReducedTopology) (v : R.Vertex → Fin L) :
      0≤(if R.Admissible (fun w => v w) 0 L then
        if Nonempty (SplitMap (R.realize L 0 (fun w => v w)) T) then F (R.realize L 0 (fun w => v w)) else 0 else 0) := by
    split_ifs <;> first | exact hF _ | rfl
  apply le_trans (b := ∑ q : S.Vertex → Fin L, if S.Admissible (fun v => q v) 0 L then
    if Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) then F (S.realize L 0 (fun v => q v)) else 0 else 0)
  · have hh := Finset.single_le_sum (fun (v : S.Vertex → Fin L) (_ : v∈Finset.univ) => hn S v) (Finset.mem_univ q)
    simpa only [ite_eq_left hq,ite_eq_left (show Nonempty (SplitMap (S.realize L 0 (fun v => q v)) T) from ⟨f⟩)] using hh
  · exact Finset.single_le_sum (fun (R : ReducedTopology) (_ : R∈boundedTopologies K) =>
      Finset.sum_nonneg (s := Finset.univ) (fun (v : R.Vertex → Fin L) _ => hn R v)) hS

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalSubtreeConcentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance physicalSubtreeConcentrationDecidableEq_r13125a_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma physicalTreeVariance_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0≤physicalTreeVariance M C H N L u T := by
  unfold physicalTreeVariance
  exact root_overlapVariance_nonneg _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

lemma physicalTreeVariance_le_one (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    physicalTreeVariance M C H N L u T≤1 := by
  unfold physicalTreeVariance
  exact root_overlapVariance_le_one _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootOverlapDeviation
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

lemma SplitMap.subsetDeviation_eq (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    {U T : PrescribedTree n} (f : SplitMap U T)
    (A : Finset T.Leaf) (hA : ∀ b, (∃ a, f.leaf a=b) ↔ b∈A)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    subsetDeviation μ Ω T A K V=overlapDeviation μ Ω U K V := by
  unfold subsetDeviation overlapDeviation FiniteLaw.mixedDeviation
  have hm (z : Z) := f.expect_subsetOverlap A hA (K z) (V z) id
  simp only [id_eq] at hm
  simp_rw [hm]
  apply integral_congr_ae
  exact ae_of_all μ (fun z => f.expect_subsetOverlap A hA (K z) (V z)
    (fun x => |x-(∫ y, (U.sampleLaw (K y)).expect (treeOverlap U (V y)) ∂μ)|))

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PrescribedTree
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (S : PrescribedTree L)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

include hb hV in
lemma integrable_rootOverlapCenteredAbs (c : ℝ) : Integrable (fun z : FullRootState Y X I M =>
    (S.sampleLaw (rootTower T Q m base old z)).expect
      (fun w => |treeOverlap S (rootVector V z) w-c|)) μ := by
  have he (z : FullRootState Y X I M) :
      (S.sampleLaw (rootTower T Q m base old z)).expect
        (fun w => |treeOverlap S (rootVector V z) w-c|)=
      rootTreeMean S T Q m base old (fun x => |spatialProduct (fun _ : S.Leaf => V) x-c|) z := by
    unfold rootTreeMean packRoot
    apply FiniteLaw.expect_congr
    intro w
    rw [treeOverlap_eq_spatialProduct]
    rfl
  simp_rw [he]
  apply integrable_rootTreeMean T Q m base old hb _ _ μ (B := 1+|c|)
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (add_le_add (spatialProduct_bound _ (fun _ => hV) x) le_rfl)

include hb hV in
lemma root_overlapDeviation_le_variance {t : ℝ} (ht : 0<t) :
    overlapDeviation μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V) ≤
      overlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S (rootTower T Q m base old) (rootVector V)/(2*t)+t/2 := by
  apply FiniteLaw.mixedDeviation_le_variance
  · simpa using integrable_rootOverlapMoment S T Q m base old V hb μ hV 1
  · exact integrable_rootOverlapMoment S T Q m base old V hb μ hV 2
  · exact integrable_rootOverlapCenteredAbs S T Q m base old V hb μ hV _
  · exact ht

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_QSubsetDeviation
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory ReducedTopology Filter
open scoped BigOperators Topology
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}

attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubsetDeviationDecidableEq
attribute [local instance] OAI.DilutedSpinGlass.PrescribedTree.qSubsetDeviationDecidable
lemma shapeDeviation_nonneg (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree n) (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ) :
    0 ≤ shapeDeviation μ Ω S K V := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs
  · exact FiniteLaw.mixedDeviation_nonneg _ _ _ _
  · rfl

lemma shapeDeviation_le_subtree (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2)
    (S : PrescribedTree n) (b : ℕ) (hS : S.leaves=b) :
    shapeDeviation μ Ω S K V ≤ (2:ℝ)^b*(subtreePotential b F S/(2*t)+t/2) := by
  have hle (A : Finset S.Leaf) :
      (if A.Nonempty then subsetDeviation μ Ω S A K V else 0)≤ subtreePotential b F S/(2*t)+t/2 := by
    by_cases ha : A.Nonempty
    · rw [ite_eq_left ha]
      obtain ⟨U,f,hf⟩ := exists_subset_tree S A ha
      rw [f.subsetDeviation_eq μ Ω A hf K V]
      apply (hdev U).trans
      exact add_le_add (div_le_div_of_nonneg_right
        (le_subtreePotential F hF f (f.leaves_le.trans_eq hS)) (by positivity)) le_rfl
    · rw [ite_eq_right ha]
      have := subtreePotential_nonneg F hF S (K := b)
      positivity
  unfold shapeDeviation
  apply (Finset.sum_le_sum (fun A _ => hle A)).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,card_leaf,hS,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma qExpect_add {n : ℕ} (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T+G T) k S=qExpect m F k S+qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_add,Finset.sum_add_distrib]

lemma qExpect_div_const {n : ℕ} (m : Fin (n+1) → ℝ) (F : PrescribedTree n → ℝ)
    (c : ℝ) (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T/c) k S=qExpect m F k S/c := by
  simpa only [div_eq_mul_inv] using qExpect_mul_const m F c⁻¹ k S

lemma subtreePotential_le_card {L b : ℕ} (F : PrescribedTree L → ℝ) (hF : ∀ S, F S≤1)
    (S : PrescribedTree L) : subtreePotential b F S≤
      ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ) := by
  unfold subtreePotential
  apply Finset.sum_le_sum
  intro R _
  calc
    _ ≤ ∑ _q : R.Vertex → Fin L, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro q _
      split_ifs <;> first | exact hF _ | norm_num
    _ = _ := by simp

lemma qExpect_subtree_bounded {L : ℕ} [NeZero L] (b k : ℕ)
    (F : ℕ → PrescribedTree L → ℝ) (hF : ∀ n S, F n S≤1) :
    IsBoundedUnder (·≤·) atTop (fun n => qExpect (grid L 0 L) (subtreePotential b (F n)) k (single L)) := by
  apply isBoundedUnder_of_eventually_le (a := ∑ R∈boundedTopologies b, (Fintype.card (R.Vertex → Fin L):ℝ))
  apply Eventually.of_forall
  intro n
  have hh := qExpect_mono (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => subtreePotential_le_card (F n) (hF n) S (b := b)) k (single L)
  simpa only [qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] using hh

lemma qExpect_shapeDeviation_le {L : ℕ} [NeZero L]
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ)
    (F : PrescribedTree L → ℝ) (hF : ∀ S, 0≤F S) {t : ℝ} (ht : 0<t)
    (hdev : ∀ S, overlapDeviation μ Ω S K V≤F S/(2*t)+t/2) (k : ℕ) :
    qExpect (grid L 0 L) (fun S => shapeDeviation μ Ω S K V) k (single L) ≤
      (2:ℝ)^(k+1)*(qExpect (grid L 0 L) (subtreePotential (k+1) F) k (single L)/(2*t)+t/2) := by
  have hh := qExpect_mono_leaves (grid L 0 L) (grid_strictMono (NeZero.pos L)).monotone grid_nonneg
    (fun S => shapeDeviation μ Ω S K V)
    (fun S => (subtreePotential (k+1) F S/(2*t)+t/2)*(2:ℝ)^(k+1)) k (single L)
    (fun S hS => by
      rw [leaves_single] at hS
      have he : S.leaves=k+1 := by omega
      simpa only [mul_comm] using shapeDeviation_le_subtree μ Ω K V F hF ht hdev S (k+1) he)
  rw [qExpect_mul_const,qExpect_add,qExpect_div_const,
    qExpect_const _ (show grid L 0 L 0=0 by simp [grid]) (grid_last (NeZero.pos L))] at hh
  simpa only [mul_comm] using hh

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalShapeError
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

noncomputable local instance physicalShapeErrorDecidableEq_r13125a_1 (type : Type) :
    DecidableEq type := Classical.decEq type
lemma physicalTreeDeviation_le_variance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) {t : ℝ} (ht : 0<t) :
    physicalTreeDeviation M C H N L u T ≤ physicalTreeVariance M C H N L u T/(2*t)+t/2 := by
  unfold physicalTreeDeviation physicalTreeVariance
  exact root_overlapDeviation_le_variance _ _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i) ht

lemma physicalShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (T : PrescribedTree (L+1)) :
    0 ≤ physicalShapeDeviation M C H N L u T := shapeDeviation_nonneg _ _ _ _ _

lemma physicalShapeDeviation_qExpect_le (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {t : ℝ} (ht : 0<t) (k : ℕ) :
    qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1)) ≤
      (2:ℝ)^(k+1)*(qExpect (grid (L+1) 0 (L+1))
        (subtreePotential (k+1) (physicalTreeVariance M C H N L u)) k (single (L+1))/(2*t)+t/2) := by
  apply qExpect_shapeDeviation_le _ _ _ _ _ (physicalTreeVariance_nonneg M C H N L u) ht
  exact fun T => physicalTreeDeviation_le_variance M C H N L u T ht

/-- The complete finite-shape MAD error for the actual selected reservoir tends
 to zero. This is the error required by the empirical pattern comparison. -/
theorem physicalShapeError_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  apply doubleLimit_young _ (fun L n => qExpect (grid (L+1) 0 (L+1))
    (subtreePotential (k+1) (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
    k (single (L+1))) ((2:ℝ)^(k+1)) (by positivity)
  · intro L n
    exact qExpect_nonneg _ (grid_strictMono (by omega)).monotone grid_nonneg
      _ (physicalShapeDeviation_nonneg _ _ _ _ _ _) _ _
  · intro L
    exact qExpect_subtree_bounded (k+1) k _ (fun _ _ => physicalTreeVariance_le_one _ _ _ _ _ _ _)
  · intro t ht L n
    exact physicalShapeDeviation_qExpect_le _ _ _ _ _ _ ht k
  · exact physicalSubtree_limsup_tendsto M C H Ns us hcontrol (k+1) k

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped Topology BigOperators
namespace FiniteLaw
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (Q : (z : Z) → FiniteLaw (Ω z))
    (f : (z : Z) → Ω z → ℝ)
lemma mixedDeviation_le_two (hf : ∀ z x, |f z x|≤1) : mixedDeviation μ Ω Q f≤2 := by
  have he : |∫ z, (Q z).expect (f z) ∂μ|≤1 :=
    abs_integral_le_bound (fun z => (Q z).abs_expect_le (hf z))
  apply (le_abs_self _).trans
  apply abs_integral_le_bound
  intro z
  apply (Q z).abs_expect_le
  intro x
  rw [abs_abs]
  exact (abs_sub _ _).trans (by linarith [hf z x])
end FiniteLaw
namespace PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {n N : ℕ}
lemma shapeDeviation_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (S : PrescribedTree n)
    (K : (z : Z) → KernelTower (Ω z) n)
    (V : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (hV : ∀ z y i, |V z y i|≤1) : shapeDeviation μ Ω S K V≤(2:ℝ)^S.leaves*2 := by
  classical
  unfold shapeDeviation
  calc
    _ ≤ ∑ _A : Finset S.Leaf, (2:ℝ) := by
      apply Finset.sum_le_sum
      intro A _
      split_ifs
      · exact FiniteLaw.mixedDeviation_le_two μ _ _ _
          (fun z w => subsetOverlap_bound S A (V z) (hV z) w)
      · norm_num
    _ = _ := by simp [card_leaf]

lemma qExpect_shape_bound {n : ℕ} (m : Fin (n+1) → ℝ)
    (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (F : PrescribedTree n → ℝ) (hF : ∀ S, F S≤(2:ℝ)^S.leaves*2)
    (k : ℕ) : qExpect m F k (single n) ≤ (2:ℝ)^(k+1)*2 := by
  have hh := qExpect_mono_leaves m hm hpos F (fun _ => (2:ℝ)^(k+1)*2) k (single n)
    (fun S hS => by simpa only [hS,leaves_single,Nat.add_comm 1 k] using hF S)
  simpa only [qExpect_const m hroot hend] using hh
end PrescribedTree

lemma limsup_le_of_vanishing_error (f g e : ℕ → ℝ)
    (hf : ∀ n, 0≤f n) (hg : IsBoundedUnder (·≤·) atTop g)
    (he : Tendsto e atTop (𝓝 0)) (h : ∀ n, f n≤g n+e n) :
    limsup f atTop≤limsup g atTop := by
  have hle (t : ℝ) (ht : 0<t) : limsup f atTop≤limsup g atTop+2*t := by
    have hgf : ∀ᶠ n in atTop, g n<limsup g atTop+t :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ht) hg
    have hef : ∀ᶠ n in atTop, e n<t := he.eventually (Iio_mem_nhds ht)
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall hf).frequently))
    filter_upwards [hgf,hef] with n hgn hen
    linarith [h n]
  have hc : ContinuousAt (fun t : ℝ => limsup g atTop+2*t) 0 := by fun_prop
  have hh := ge_of_tendsto (hc.continuousWithinAt.tendsto (s := Set.Ioi 0))
    (eventually_nhdsWithin_of_forall (fun t ht => hle t ht))
  simpa using hh
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_QIntegration
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] {n : ℕ}

lemma qExpect_sub (m : Fin (n+1) → ℝ) (F G : PrescribedTree n → ℝ)
    (k : ℕ) (S : PrescribedTree n) :
    qExpect m (fun T => F T-G T) k S=qExpect m F k S-qExpect m G k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [qExpect,ih,mul_sub,Finset.sum_sub_distrib]

lemma abs_qExpect_le_qExpect_abs (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F : PrescribedTree n → ℝ) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S| ≤ qExpect m (fun T => |F T|) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    unfold qExpect
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro v _
    have hcoef := div_nonneg (neg_nonneg.mpr (gamma_nonpos S m hm hpos v)) (Nat.cast_nonneg S.leaves)
    rw [abs_mul,abs_of_nonneg hcoef]
    exact mul_le_mul_of_nonneg_left (ih (grow S v)) hcoef

lemma qExpect_difference_bound (m : Fin (n+1) → ℝ) (hm : Monotone m)
    (hpos : ∀ j, 0 ≤ m j) (F G E : PrescribedTree n → ℝ)
    (h : ∀ S, |F S-G S|≤E S) (k : ℕ) (S : PrescribedTree n) :
    |qExpect m F k S-qExpect m G k S|≤qExpect m E k S := by
  rw [← qExpect_sub]
  exact (abs_qExpect_le_qExpect_abs m hm hpos _ k S).trans (qExpect_mono m hm hpos h k S)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory
open scoped NNReal Topology

lemma reservoirRate_nonzero (α : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    0 < reservoirRate α q N := by
  unfold reservoirRate
  positivity

lemma reservoirRate_le (α : ℝ≥0) (q N : ℕ) : reservoirRate α q N ≤ α*N := by
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by simp))

lemma reservoirRate_lower (α : ℝ≥0) (q N : ℕ) :
    (α:ℝ)*((N:ℝ)-q) ≤ reservoirRate α q N := by
  have hden : (0:ℝ) < N+1 := by positivity
  have hx0 : (0:ℝ) ≤ N/(N+1) := by positivity
  have hx1 : (N:ℝ)/(N+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hb := one_add_mul_sub_le_pow (R := ℝ) (a := (N:ℝ)/(N+1)) (by linarith : -1 ≤ (N:ℝ)/(N+1)) q
  have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ α*N by positivity)
  have he : (N:ℝ)/(N+1)-1 = -1/(N+1) := by field_simp; ring
  rw [he] at hh
  have hqq : (N:ℝ)*q/(N+1) ≤ q := by
    rw [div_le_iff₀ hden]
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  change (α:ℝ)*((N:ℝ)-q) ≤ (α:ℝ)*N*((N:ℝ)/(N+1))^q
  calc
    _ ≤ (α:ℝ)*(N-N*q/(N+1)) := mul_le_mul_of_nonneg_left (by linarith) α.coe_nonneg
    _ = (α:ℝ)*N*(1+q*(-1/(N+1))) := by ring
    _ ≤ _ := hh

lemma reservoirRate_deficit_le (α : ℝ≥0) (q N : ℕ) :
    ((α*N-reservoirRate α q N:ℝ≥0):ℝ) ≤ (α:ℝ)*q := by
  rw [NNReal.coe_sub (reservoirRate_le α q N)]
  push_cast
  linarith [reservoirRate_lower α q N]

lemma reservoirRate_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (fun N => (reservoirRate α q N:ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (fun N => reservoirRate_lower α q N)
  have hn : Tendsto (fun N : ℕ => (N:ℝ)-(q:ℝ)) atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (-(q:ℝ)) tendsto_natCast_atTop_atTop
  exact hn.const_mul_atTop hα

lemma reservoirDistance_nonneg (α : ℝ≥0) (q N : ℕ) : 0 ≤ reservoirDistance α q N := by
  unfold reservoirDistance
  positivity

lemma reservoirDistance_tendsto (α : ℝ≥0) (hα : 0 < α) (q : ℕ) :
    Tendsto (reservoirDistance α q) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (reservoirRate_tendsto α hα q))).const_mul ((α:ℝ)*q)
  simp only [mul_zero] at hh
  apply squeeze_zero (reservoirDistance_nonneg α q) _ hh
  intro N
  exact mul_le_mul_of_nonneg_right (reservoirRate_deficit_le α q N) (by positivity)

lemma fullRoot_reservoirDistance {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] {M : ℕ}
    (ξ : Fin M → Measure Y) [∀ i, IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (α s : ℝ≥0) (hα : 0 < α) (q N : ℕ) (hN : 0 < N) :
    BoundedDistance (fullRootLaw ξ μ ν (α*N) s)
      (fullRootLaw ξ μ ν (reservoirRate α q N) s) (reservoirDistance α q N) := by
  have he : reservoirRate α q N+(α*N-reservoirRate α q N)=α*N :=
    add_tsub_cancel_of_le (reservoirRate_le α q N)
  simpa only [he,reservoirDistance] using fullRoot_boundedDistance ξ μ ν
    (reservoirRate α q N) (α*N-reservoirRate α q N) s (reservoirRate_nonzero α hα q N hN)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootDeviationDistance
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable {μ ν : Measure (FullRootState Y X I M)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d : ℝ} (hd : BoundedDistance μ ν d)
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hV : ∀ y i, |V y i| ≤ 1)

include hd hb hV in
lemma root_subsetDeviation_distance (B : Finset S.Leaf) :
    |subsetDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V) -
     subsetDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S B
      (rootTower T Q m base old) (rootVector V)| ≤ 3*d := by
  apply FiniteLaw.mixedDeviation_distance hd
  · intro z w
    exact subsetOverlap_bound S B _ (fun y i => hV _ i) w
  · exact measurable_rootTreeMean S T Q m base old
      (fun x => (∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)) hb
  · intro c
    exact measurable_rootTreeMean S T Q m base old
      (fun x => |(∑ i, ∏ a∈B, V (x a) i)/(N:ℝ)-c|) hb

include hd hb hV in
lemma root_shapeDeviation_distance (hd0 : 0 ≤ d) :
    |shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V) -
     shapeDeviation ν (rootAlphabet (Ω := Ω) (A := A)) S
      (rootTower T Q m base old) (rootVector V)| ≤ (2:ℝ)^S.leaves*(3*d) := by
  classical
  unfold shapeDeviation
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _B : Finset S.Leaf, 3*d := by
      apply Finset.sum_le_sum
      intro B _
      by_cases hB : B.Nonempty
      · simp only [ite_eq_left hB]
        exact root_subsetDeviation_distance hd S T Q m base old V hb hV B
      · simp only [ite_eq_right hB,sub_self,abs_zero]
        positivity
    _ = _ := by simp [card_leaf]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteTowerPi
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

lemma reservoirShapeDeviation_nonneg (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    0 ≤ reservoirShapeDeviation M C H N L u S := shapeDeviation_nonneg _ _ _ _ _

lemma reservoirShapeDeviation_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    |physicalShapeDeviation M C H N L u S-reservoirShapeDeviation M C H N L u S|≤
      (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N) := by
  apply root_shapeDeviation_distance
    (fullRoot_reservoirDistance _ _ _ _ _ hα (p-1) N hN)
    S _ _ _ _ _ _ (measurable_physicalBase M C H N)
    (fun y i => readVector_bound _ y i) (reservoirDistance_nonneg _ _ _)

lemma reservoirShape_qExpect_distance (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (N L : ℕ) (hN : 0<N) (u : Spec L×ℕ → ℝ) (k : ℕ) :
    |qExpect (grid (L+1) 0 (L+1)) (physicalShapeDeviation M C H N L u) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1)) (reservoirShapeDeviation M C H N L u) k (single (L+1))|≤
      (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N) := by
  have hh := qExpect_difference_bound (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg _ _ _
    (reservoirShapeDeviation_distance M hα C H N L hN u) k (single (L+1))
  apply hh.trans
  have h := qExpect_mono_leaves (grid (L+1) 0 (L+1))
    (grid_strictMono (by omega)).monotone grid_nonneg
    (fun S => (2:ℝ)^S.leaves*(3*reservoirDistance M.alpha (p-1) N))
    (fun _ => (2:ℝ)^(k+1)*(3*reservoirDistance M.alpha (p-1) N)) k (single (L+1))
    (fun S hS => by rw [hS,leaves_single,Nat.add_comm 1 k])
  have hz : grid (L+1) 0 (L+1) 0=0 := by simp [grid]
  simpa only [qExpect_const _ hz (grid_last (by omega : 0<L+1))] using h

lemma reservoirShape_qExpect_difference_tendsto (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (L : ℕ) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (us : ℕ → Spec L×ℕ → ℝ)
    (k : ℕ) :
    Tendsto (fun n => qExpect (grid (L+1) 0 (L+1))
      (physicalShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))-
      qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns n+1) L (us n)) k (single (L+1))) atTop (𝓝 0) := by
  have hd := (reservoirDistance_tendsto M.alpha hα (p-1)).comp
    (tendsto_add_atTop_nat 1 |>.comp hNs)
  have hh := (hd.const_mul 3).const_mul ((2:ℝ)^(k+1))
  simp only [mul_zero,Function.comp_apply] at hh
  exact squeeze_zero_norm (fun n : ℕ => by simpa only [Real.norm_eq_abs] using
      (reservoirShape_qExpect_distance M hα C H (Ns n+1) L (by omega) (us n) k)) hh

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ReservoirShapeLimit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p : ℕ}
lemma reservoirShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    reservoirShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold reservoirShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)
lemma physicalShapeDeviation_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : PrescribedTree (L+1)) :
    physicalShapeDeviation M C H N L u S ≤ (2:ℝ)^S.leaves*2 := by
  unfold physicalShapeDeviation
  exact shapeDeviation_bound _ _ _ _ _ (fun z y i => readVector_bound _ _ _)

lemma reservoirShapeError_tendsto_sat_oai (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  let f := fun L n => qExpect (grid (L+1) 0 (L+1))
    (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  let g := fun L n => qExpect (grid (L+1) 0 (L+1))
    (physicalShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))
  have hf (L n : ℕ) : 0≤f L n := qExpect_nonneg _
    (grid_strictMono (by omega)).monotone grid_nonneg _
    (reservoirShapeDeviation_nonneg _ _ _ _ _ _) _ _
  have hfb (L : ℕ) : IsBoundedUnder (·≤·) atTop (f L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact reservoirShapeDeviation_bound _ _ _ _ _ _ _
  have hgb (L : ℕ) : IsBoundedUnder (·≤·) atTop (g L) := by
    refine isBoundedUnder_of_eventually_le (a := (2:ℝ)^(k+1)*2) (Eventually.of_forall (fun n => ?_))
    apply qExpect_shape_bound _ (grid_strictMono (by omega)).monotone grid_nonneg
      (by simp [grid]) (grid_last (by omega))
    intro S
    exact physicalShapeDeviation_bound _ _ _ _ _ _ _
  apply squeeze_zero (fun L => le_limsup_of_frequently_le ((Eventually.of_forall (hf L)).frequently) (hfb L)) _
    (physicalShapeError_tendsto M C H Ns us hcontrol k)
  intro L
  exact limsup_le_of_vanishing_error (f L) (g L) (fun n => -(g L n-f L n)) (hf L) (hgb L)
    (by simpa only [neg_zero] using
      (reservoirShape_qExpect_difference_tendsto M hα C H L (Ns L) (hNs L) (us L) k).neg)
    (fun n => by linarith)
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat_oai := @OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat_oai
