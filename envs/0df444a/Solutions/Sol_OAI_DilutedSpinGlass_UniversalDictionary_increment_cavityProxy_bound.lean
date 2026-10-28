-- Prove2me | solution 1 for OAI.DilutedSpinGlass.UniversalDictionary.increment_cavityProxy_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:04:33.163992+00:00
-- url     : https://prove2.me/submissions/2e2461ec-c6c2-46b2-9dff-5ce9220bf5fa

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_clippedPhysicalMean_reservoir_bound

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

variable {n : ℕ}

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact insertion identity for a single finite backward step. -/
theorem logMean_insertion {m : ℝ} (f a : Ω → ℝ) :
    P.logMean m (fun x => f x + a x) - P.logMean m f =
      (P.tilt m f).logMean m a := by
  have hmom : (P.tilt m f).expMoment m a =
      P.expMoment m (fun x => f x + a x) / P.expMoment m f := by
    rw [expMoment, tilt_expect]
    congr 1
    exact P.expect_congr (fun x => by rw [mul_add, Real.exp_add])
  rw [logMean, logMean, logMean, hmom,
    Real.log_div (ne_of_gt (P.expMoment_pos _ _)) (ne_of_gt (P.expMoment_pos _ _)),
    sub_div]

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
-- module Solutions.OAIQ041_DS.DilutedSpin_KernelTower
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

namespace KernelTower

variable {Ω : Type} [Fintype Ω]


theorem insertion (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (f a : FinitePath Ω n → ℝ) :
    backwardLog n T m (fun x => f x + a x) - backwardLog n T m f =
      backwardLog n (tilt n T m f) m a := by
  induction n with
  | zero => simp only [backwardLog]; ring
  | succ n ih =>
    let F := fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y))
    let A := fun x => backwardLog n
      (tilt n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))
      (fun j => m j.succ) (fun y => a (x,y))
    have hc : (fun x => backwardLog n (T.2 x) (fun j => m j.succ)
        (fun y => f (x,y) + a (x,y))) = (fun x => F x + A x) := by
      funext x
      have hi := ih (T.2 x) (fun j => m j.succ) (fun y => f (x,y)) (fun y => a (x,y))
      change _ - F x = A x at hi
      linarith
    change T.1.logMean (m 0) _ - T.1.logMean (m 0) F =
      (T.1.tilt (m 0) F).logMean (m 0) A
    rw [hc]
    exact T.1.logMean_insertion F A



theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

end KernelTower
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
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonMoments
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

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
-- module Solutions.OAIQ041_DS.DilutedSpin_ProductTowers
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
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

/-- Conditional power means commute with literal relabeling of every hidden
mark variable. This is needed for the physical Palm exchangeability. -/
theorem backwardLog_transport (e : Ω ≃ Λ) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n (transport e n T) m f =
      backwardLog n T m (f ∘ pathEquiv e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, transport]
    have he : (fun a : Λ => backwardLog n (transport e n (T.2 (e.symm a)))
        (fun j => m j.succ) (fun y => f (a,y))) =
      (fun a : Λ => backwardLog n (T.2 (e.symm a))
        (fun j => m j.succ) ((fun y => f (a,y)) ∘ pathEquiv e n)) :=
      funext (fun a => ih (T.2 (e.symm a)) (fun j => m j.succ) (fun y => f (a,y)))
    rw [he, FiniteLaw.logMean_transport]
    congr 1
    funext a
    simp only [Function.comp_def, Equiv.symm_apply_apply, pathEquiv_cons]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

theorem eq_of_weights {P Q : FiniteLaw Ω} (h : ∀ x, P.weight x = Q.weight x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

/-- A mark block not present in a log weight integrates out, before or after
any one power-mean tilt. -/
theorem logMean_bind_fst (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω → ℝ) :
    (P.bind (fun _ => Q)).logMean m (fun z => f z.1) = P.logMean m f := by
  simp [logMean, expMoment]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n)
    (m : Fin n → ℝ) (f : FinitePath Ω n → ℝ) :
    backwardLog n (prod n T U) m (fun y => f (pathFst n y)) = backwardLog n T m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog, prod, pathFst]
    have hh : (fun z : Ω × Λ => backwardLog n
        (prod n (T.2 z.1) (U.2 z.2)) (fun j => m j.succ)
        (fun y => f (z.1, pathFst n y))) =
        (fun z : Ω × Λ => backwardLog n (T.2 z.1) (fun j => m j.succ)
          (fun y => f (z.1,y))) := by
      funext z
      exact ih (T.2 z.1) (U.2 z.2) (fun j => m j.succ) (fun y => f (z.1,y))
    rw [hh]
    exact FiniteLaw.logMean_bind_fst T.1 U.1 (m 0)
      (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun y => f (x,y)))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

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

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_integrable :
    Integrable (fun z : Sigma X => (z.1 : ℝ)) (familyLaw (poissonMeasure r) ν) := by
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (poisson_integrable_count r)
  intro n _
  simp

theorem familyPoisson_count_mean :
    (∫ z : Sigma X, (z.1 : ℝ) ∂familyLaw (poissonMeasure r) ν) = (r : ℝ) := by
  rw [integral_familyLaw (poissonMeasure r) ν (fun n _ => (n : ℝ)) (fun _ => measurable_const)
    (familyPoisson_count_integrable ν r)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,poisson_mean]

theorem familyPoisson_memLp_linear {f : (n : ℕ) → X n → ℝ}
    (hf : ∀ n, Measurable (f n)) {A B : ℝ} (hb : ∀ n x, |f n x| ≤ A+B*n) :
    MemLp (fun z : Sigma X => f z.1 z.2) 2 (familyLaw (poissonMeasure r) ν) := by
  apply (memLp_two_iff_integrable_sq (measurable_sigmaUncurry hf).aestronglyMeasurable).mpr
  apply familyLaw_integrable_bound (poissonMeasure r) ν (fun n x => (f n x)^2) (fun n => (hf n).pow_const 2)
    (B := fun n => 2*A^2+2*B^2*(n : ℝ)^2)
  · apply poisson_integrable_quadratic r (A := 2*A^2) (B := 2*B^2)
    intro n
    rw [abs_of_nonneg (by positivity)]
  · intro n x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hsq : (f n x)^2 ≤ (A+B*n)^2 := by
      exact sq_le_sq' (abs_le.mp (hb n x)).1 (abs_le.mp (hb n x)).2
    nlinarith [sq_nonneg (A-B*n)]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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
open scoped NNReal ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (ν : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℝ≥0)

theorem familyPoisson_count_memLp :
    MemLp (fun z : Sigma X => (z.1 : ℝ)) 2 (familyLaw (poissonMeasure r) ν) := by
  apply familyPoisson_memLp_linear ν r (fun _ => measurable_const) (A := 0) (B := 1)
  intro n x
  simp

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_HeterogeneousMarks
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
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- Adding a type uses its own prior, independently of all old marks. -/
theorem tower_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (split roots i) L (tower (Fin.cons i roots) L T Q) =
      KernelTower.prod L (tower roots L T Q) (markPrior L (Q i)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 *
          (∏ j : Fin (k+1), (Q ((Fin.cons i roots : Fin (k+1) → I) j) 0).weight
            ((Fin.cons z.2 z.1.2 : Row (A := A) (Fin.cons i roots)) j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      rw [Fin.prod_univ_succ]
      change T.1.weight z.1.1 *
        ((Q i 0).weight z.2 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    physical roots L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      physical (Fin.cons i roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) =
      (y.1.1, physical (Fin.cons i roots) L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_succ {k : ℕ} (roots : Fin k → I) (i : I) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    mark q L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      mark q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, mark q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) = (y.1.2 q.succ, mark q.succ L y.2)
    rw [ih]
    rfl

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_zero {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y) = mark 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y.2)) =
      (y.1.2 0, mark 0 L y.2)
    rw [ih]
    rfl

variable {k L : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem insertedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    insertedLog base roots factor i (KernelTower.pathEquiv (split roots i) L y) =
      logWeight base (Fin.cons i roots) factor y := by
  simp only [insertedLog, logWeight, physical_split, mark_split_succ,
    mark_split_zero, Fin.sum_univ_succ]
  change base (physical (Fin.cons i roots) L y) +
      (∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y))) +
      Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) =
    base (physical (Fin.cons i roots) L y) +
      (Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) +
      ∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y)))
  ring

/-- Uniform add/delete control does not depend on the mark dimension or type. -/
theorem root_cons_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hfactor : ∀ x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Fin.cons i roots) factor - root T Q m base roots factor| ≤ C := by
  have h := KernelTower.backwardLog_transport (split roots i) L
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
  have heq : insertedLog base roots factor i ∘ KernelTower.pathEquiv (split roots i) L =
      logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  unfold root
  rw [← h, ← KernelTower.backwardLog_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
    (logWeight base roots factor)]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [insertedLog, add_sub_cancel_left] using hfactor
    (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)

/-- Typewise log-factor errors sum on the actual root list. -/
theorem root_factor_stability (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y) - Real.log (factor' i x y)| ≤ C i) :
    |root T Q m base roots factor - root T Q m base roots factor'| ≤ ∑ q, C (roots q) := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [logWeight, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ => hC _ _ _))

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
variable {k L : ℕ}

/-- The complete independent row can be integrated as a single finite mark.
Its dimension depends on the realized labels, never on a deterministic cutoff. -/
theorem tower_eq_prod (roots : Fin k → I) (L : ℕ) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower roots L T Q = KernelTower.prod L T
      (markPrior L (fun d => FiniteLaw.pi (fun j => Q (roots j) d))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_eq_fst (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L y = KernelTower.pathFst L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L y.2) = (y.1.1, KernelTower.pathFst L y.2)
    rw [ih]

/-- All unused finite priors integrate out, exactly, even if their dimension
varies over the full countable type list. -/
theorem root_one (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I) :
    root T Q m base roots (fun _ _ _ => 1) = KernelTower.backwardLog L T m base := by
  unfold root
  have heq : logWeight (A := A) base roots (fun _ _ _ => 1) =
      base ∘ KernelTower.pathFst L := by
    funext y
    simp only [logWeight, Real.log_one, Finset.sum_const_zero, add_zero,
      physical_eq_fst, Function.comp_apply]
  rw [heq, tower_eq_prod]
  exact KernelTower.backwardLog_prod_fst L T _ m base

/-- The pathwise perturbation cost is additive over all realized labels. -/
theorem root_base_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor - KernelTower.backwardLog L T m base| ≤
      ∑ q, C (roots q) := by
  rw [← root_one T Q m base roots]
  exact root_factor_stability T Q m hm base roots factor (fun _ _ _ => 1) C
    (fun i x y => by simpa only [Real.log_one, sub_zero] using hC i x y)

/-- No lower bound on a type's intensity occurs in this global domination. -/
theorem abs_root_le (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ |KernelTower.backwardLog L T m base| + C*k := by
  have h := root_base_bound T Q m hm base roots factor (fun _ => C) hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have ht := abs_add_le (root T Q m base roots factor - KernelTower.backwardLog L T m base)
    (KernelTower.backwardLog L T m base)
  rw [sub_add_cancel] at ht
  linarith

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkInsertion
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
open Set



namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L : ℕ}

/-- Physical disorder changes only the base energy, even with all countably
many type laws available to the finite realized auxiliary row. -/
theorem root_base_stability (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base base' : FinitePath Ω L → ℝ) {k : ℕ} (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hb : ∀ x, |base x-base' x| ≤ C) :
    |root T Q m base roots factor-root T Q m base' roots factor| ≤ C := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [logWeight, add_sub_add_right_eq_sub] using hb (physical roots L y)

end DilutedSpinGlass.HeterogeneousMarks



end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

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
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

end FiniteLaw

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniformIndexCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω I X : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace X] {L : ℕ}

theorem root_uniform_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j) (base : FinitePath Ω L → ℝ)
    {n : ℕ} (roots : Fin n → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ B+C*n := by
  have hh := KernelTower.backwardLog_stability L T m hm
    (f := base) (g := fun _ => 0) (by simpa only [sub_zero] using hb)
  rw [KernelTower.backwardLog_const L T m (fun j => ne_of_gt (hm j)) 0, sub_zero] at hh
  exact (abs_root_le T Q m hm base roots factor hf).trans (add_le_add hh le_rfl)

theorem measurable_root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (factor : X → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (hf : ∀ i y z, Measurable (fun x => factor x i y z)) :
    Measurable (fun x => root T Q m (base x) roots (factor x)) := by
  apply KernelTower.measurable_backwardLog
  intro y
  exact (hb _).add (Finset.measurable_sum _ (fun j _ => (hf _ _ _).log))

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Coordinatewise pushforwards tensorize even for tests that do not factor. -/
theorem Projects.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {P : (i : ι) → FiniteLaw (α i)} {Q : (i : ι) → FiniteLaw (β i)}
    {π : (i : ι) → α i → β i} (h : ∀ i, Projects (P i) (Q i) (π i)) :
    Projects (FiniteLaw.pi P) (FiniteLaw.pi Q) (fun x i => π i (x i)) := by
  intro f
  have hh := expect_pi_weighted_map P Q π (fun _ _ => 1) (fun _ _ => 1)
    (fun i g => by simpa only [one_mul] using h i g) f
  simpa only [Finset.prod_const_one,mul_one] using hh

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

theorem oldIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform oldIndex := by
  intro f
  unfold indexLaw
  rw [FiniteLaw.expect_bind,FiniteLaw.uniform_expect,Fin.sum_univ_succ]
  simp only [oldIndex, Fin.cases_zero, Fin.cases_succ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  change ((FiniteLaw.uniform : FiniteLaw (Fin N)).expect f+
    ∑ i, (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun _ => f i))/(N+1) = _
  simp only [FiniteLaw.expect_const,FiniteLaw.uniform_expect,Fintype.card_fin]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (N:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem newIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform newIndex := by
  intro f
  simp only [indexLaw,FiniteLaw.expect_bind,newIndex,FiniteLaw.expect_const]

/-- The exact probability of changing a site is 1/(N+1). -/
theorem newIndex_probability (N : ℕ) [NeZero N] :
    (indexLaw N).expect (fun z => if z.1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
  calc
    _ = (FiniteLaw.uniform : FiniteLaw (Fin (N+1))).expect
        (fun j => if j = 0 then (1:ℝ) else 0) :=
      newIndex_projects N (fun j => if j = 0 then (1:ℝ) else 0)
    _ = _ := by rw [FiniteLaw.uniform_expect]; simp

lemma same_index_off_new {N : ℕ} (z : Fin (N+1) × Fin N) (hz : z.1 ≠ 0) :
    (oldIndex z).succ = newIndex z := by
  rcases z with ⟨j,i⟩
  induction j using Fin.cases with
  | zero => exact (hz rfl).elim
  | succ j => rfl

theorem expected_new_count (N p : ℕ) [NeZero N] :
    (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
      (fun z => ∑ j, if (z j).1 = 0 then (1:ℝ) else 0) = (p:ℝ)/(N+1) := by
  rw [FiniteLaw.expect_fintype_sum]
  have hm (j : Fin p) :
      (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
        (fun z => if (z j).1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
    exact (FiniteLaw.expect_pi_marginal (fun _ : Fin p => indexLaw N) j
      (fun z => if z.1 = 0 then (1:ℝ) else 0)).trans (newIndex_probability N)
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SizeSpinRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I J : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

lemma tower_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower (A := fun j => A (f j)) roots L T (fun j => Q (f j)) =
      tower (f ∘ roots) L T Q := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma physical_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    physical roots L y = physical (f ∘ roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.1,z)) (ih y.2)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
lemma mark_pullback (f : J → I) {k : ℕ} (roots : Fin k → J) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := fun j => A (f j)) roots) L) :
    mark (A := fun j => A (f j)) q L y = mark (A := A) (roots := f ∘ roots) q L y := by
  induction L with
  | zero => rfl
  | succ L ih => exact congrArg (fun z => (y.1.2 q,z)) (ih y.2)

/-- Mere relabeling preserves every realized heterogeneous prior and factor.
This is used to identify per-occurrence and dictionary-label presentations. -/
theorem root_pullback (f : J → I) {k L : ℕ} (roots : Fin k → J)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T (fun j => Q (f j)) m base roots (fun j => factor (f j)) =
      root T Q m base (f ∘ roots) factor := by
  unfold root
  rw [tower_pullback]
  congr 1
  funext y
  simp only [logWeight,physical_pullback,mark_pullback,Function.comp_apply]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ActualPrefix
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
variable {Ω : Type*} [Fintype Ω]

theorem abs_expect_le_expect_abs (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.expect f| ≤ P.expect (fun x => |f x|) := by
  unfold expect
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul,abs_of_nonneg (P.nonneg x)])

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PatternComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open scoped Topology BigOperators

namespace DilutedSpinGlass

theorem extractionProbe_pos (j : ℕ) : 0 < extractionProbe j := by
  unfold extractionProbe
  positivity

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSuperposition
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

lemma extractionProbe_le_quarter (j : ℕ) : extractionProbe j ≤ 1/4 := by
  unfold extractionProbe
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

lemma extractionProbe_abs_le_quarter (j : ℕ) : |extractionProbe j| ≤ 1/4 := by
  rw [abs_of_pos (extractionProbe_pos j)]
  exact extractionProbe_le_quarter j

lemma probeLow_pos (j : ℕ) : 0 < probeLow j := pow_pos (extractionProbe_pos j) _
lemma probeLow_lt_high (j : ℕ) : probeLow j < probeHigh j := by
  have := probeLow_pos j
  unfold probeHigh
  linarith
lemma probeHigh_lt_quarter (j : ℕ) : probeHigh j < 1/4 := by
  have hp : probeLow j ≤ (1/4:ℝ)^4 := by
    apply (pow_le_pow_left₀ (extractionProbe_pos j).le (extractionProbe_le_quarter j) (j+4)).trans
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold probeHigh
  nlinarith

lemma probe_interval_quarter (j : ℕ) :
    Icc (probeLow j) (probeHigh j) ⊆ Icc (-(1:ℝ)/4) (1/4) := by
  intro u hu
  have := probeLow_pos j
  have := probeHigh_lt_quarter j
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma charFunDual_nnreal_smul (r : ℝ≥0) (μ : Measure E) (L : StrongDual ℝ E) :
    charFunDual ((r:ℝ≥0∞) • μ) L = (r:ℂ)*charFunDual μ L := by
  simp only [charFunDual_apply,integral_smul_measure,ENNReal.coe_toReal,Complex.real_smul]

omit [SecondCountableTopology E] in
lemma charFunDual_add_measure (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual ℝ E) : charFunDual (μ+ν) L = charFunDual μ L+charFunDual ν L := by
  have h (ξ : Measure E) [IsFiniteMeasure ξ] :
      Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) ξ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  exact integral_add_measure (h μ) (h ν)

/-- Superposition of marked Poisson sums follows solely from equality of
 the finite intensity measures. No independence of coordinates of a mark is needed. -/
lemma compoundPoisson_superposition [CompleteSpace E] (s t : ℝ≥0)
    (μ ν τ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (h : ((s+t:ℝ≥0):ℝ≥0∞) • μ = (s:ℝ≥0∞) • ν+(t:ℝ≥0∞) • τ) :
    compoundPoisson (s+t) μ = compoundPoisson s ν ∗ compoundPoisson t τ := by
  apply Measure.ext_of_charFunDual
  funext L
  let : IsFiniteMeasure ((s:ℝ≥0∞) • ν) := inferInstanceAs (IsFiniteMeasure (s • ν))
  let : IsFiniteMeasure ((t:ℝ≥0∞) • τ) := inferInstanceAs (IsFiniteMeasure (t • τ))
  have hh := congrArg (fun ξ : Measure E => charFunDual ξ L) h
  simp only [charFunDual_add_measure,charFunDual_nnreal_smul] at hh
  rw [charFunDual_conv,charFunDual_compoundPoisson,charFunDual_compoundPoisson,
    charFunDual_compoundPoisson,← Complex.exp_add]
  congr 1
  push_cast at hh ⊢
  linear_combination hh

lemma compoundPoisson_add [CompleteSpace E] (s t : ℝ≥0)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    compoundPoisson (s+t) μ = compoundPoisson s μ ∗ compoundPoisson t μ := by
  apply compoundPoisson_superposition
  simp only [ENNReal.coe_add,add_smul]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSpinMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {Z : Type} [MeasurableSpace Z]

/-- Measurability for the literal root before quenched averaging. Only the
interaction table values are read; auxiliary factorization witnesses are not. -/
theorem measurable_spinMean {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hθ : ∀ j σ, Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i, Measurable (fun z => h z i)) :
    Measurable (fun z => spinMean Q m (theta z) (h z) ψ) := by
  unfold spinMean
  apply FiniteLaw.measurable_expect
  intro indices
  apply FiniteLaw.measurable_expect
  intro sites
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact measurable_const

lemma finite_logWeight_bound {N p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin)
    {C H : ℝ} (hθ : ∀ j x, |(theta j).1 x| ≤ C) (hh : ∀ i, |h i| ≤ H) :
    |logWeight theta h indices σ| ≤ H*N+C*k := by
  have hs (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]
  unfold logWeight
  apply (abs_add_le _ _).trans
  have h1 := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hθ j (fun q => σ (indices j q))))
  have h2 : |∑ i, h i*spin (σ i)| ≤ ∑ _i : Fin N, H :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simpa only [abs_mul,hs,mul_one] using hh i))
  simpa [mul_comm,add_comm] using add_le_add h1 h2

theorem spinMean_bound {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ i, |h i| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ| ≤ H*N+C*k+D*l := by
  apply FiniteLaw.abs_expect_le
  intro indices
  apply FiniteLaw.abs_expect_le
  intro sites
  exact root_uniform_bound _ Q m hm _ id _
    (fun x => finite_logWeight_bound theta h indices (KernelTower.terminalState r x) hθ hh)
    (fun i x a => hψ i _ a)

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_le_const (μ : Measure Z) [IsProbabilityMeasure μ] {f : Z → ℝ} {B : ℝ}
    (h : ∀ z, |f z| ≤ B) : |∫ z, f z ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (ae_of_all μ (fun z => by simpa only [Real.norm_eq_abs] using h z)))

omit [Countable I] [MeasurableSingletonClass I] in
theorem countedMean_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ H*N+C*k+D*l := by
  apply abs_integral_le_const
  intro a
  apply abs_integral_le_const
  intro x
  apply abs_integral_le_const
  intro h
  exact spinMean_bound _ m hm _ _ _ (fun j σ => hθ _ σ) (fun i => hh _) (fun j σ a => hψ _ σ a)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
theorem abs_expect_sub_le {f g : Ω → ℝ} {C : ℝ} (h : ∀ x, |f x-g x| ≤ C) :
    |P.expect f-P.expect g| ≤ C := by
  rw [← expect_sub]
  exact P.abs_expect_le h
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open HeterogeneousMarks
open scoped BigOperators

/-- Deleting one realized factor integrates out only its own independent marks.
The surviving factors keep their alphabets and level priors exactly. -/
theorem spinRoot_mark_step {N p k l r : ℕ} {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin (l+1) → Fin N)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinRoot Q m theta h indices sites ψ-
      spinRoot (fun j => Q j.succ) m theta h indices (fun j => sites j.succ) (fun j => ψ j.succ)| ≤ D := by
  have hid : Fin.cons 0 (fun j : Fin l => j.succ) = (id : Fin (l+1) → Fin (l+1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hp := root_pullback (Fin.succ : Fin l → Fin (l+1)) id
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m
    (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
  unfold spinRoot
  rw [hp]
  exact (by
    simpa only [hid,Function.comp_id] using
      root_cons_bound
        (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m hm
        (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
        (fun j : Fin l => j.succ) 0
        (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
        (fun x a => hψ _ a))

theorem spinMean_mark_step {N p k l r : ℕ} [NeZero N] {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinMean Q m theta h ψ-
      spinMean (fun j => Q j.succ) m theta h (fun j => ψ j.succ)| ≤ D := by
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  rw [FiniteLaw.expect_pi_cons]
  rw [← (FiniteLaw.uniform : FiniteLaw (Fin N)).expect_const
    ((FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect _)]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  exact spinRoot_mark_step Q m hm theta h indices (Fin.cons i sites) ψ hψ

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSizeCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_sub_le_const {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {f g : Z → ℝ} {B : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ z, |f z-g z| ≤ B) :
    |(∫ z, f z ∂μ)-(∫ z, g z ∂μ)| ≤ B := by
  rw [← integral_sub hf hg]
  exact abs_integral_le_const μ h

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PoissonRateCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
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

/-- Common Poisson points give the exact first-moment rate coupling estimate.
This is a consequence of convolution, not a coupling hypothesis. -/
theorem poisson_average_rate_add (r s : ℝ≥0) {f : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hstep : ∀ n, |f (n+1)-f n| ≤ C) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤ C*(s:ℝ) := by
  have hl := nat_lipschitz_of_step hC hstep
  have hb (n : ℕ) : |f n| ≤ |f 0|+C*n := by
    have hh := hl n 0
    simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)] at hh
    calc
      |f n| = |(f n-f 0)+f 0| := by congr 1; ring
      _ ≤ |f n-f 0|+|f 0| := abs_add_le _ _
      _ ≤ |f 0|+C*n := by linarith
  have hi (q : ℝ≥0) : Integrable f (poissonMeasure q) := poisson_integrable_linear q hb
  have hin (n : ℕ) : Integrable (fun k => f (n+k)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := |f 0|+C*n) (B := C)
    intro k
    convert hb (n+k) using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hd (n : ℕ) : |(∫ k, f (n+k) ∂poissonMeasure s)-f n| ≤ C*(s:ℝ) := by
    have h := integral_mono ((hin n).sub (integrable_const (f n))).abs
      ((poisson_integrable_count s).const_mul C) (fun k => by
        change |f (n+k)-f n| ≤ C*(k:ℝ)
        have hh := hl (n+k) n
        simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k)] using hh)
    simp only [Pi.sub_apply] at h
    rw [integral_const_mul,poisson_mean] at h
    have ha := abs_integral_le_integral_abs.trans h
    rw [integral_sub (hin n) (integrable_const (f n))] at ha
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ha
  have hj : Integrable (fun n => ∫ k, f (n+k) ∂poissonMeasure s) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := |f 0|+C*s) (B := C)
    intro n
    have hh := abs_sub_le_iff.mp (hd n)
    have hf := abs_le.mp (hb n)
    rw [abs_le]
    constructor <;> linarith
  have hconv : Integrable f (poissonMeasure r ∗ poissonMeasure s) := by
    rw [poissonMeasure_conv_poissonMeasure]
    exact hi (r+s)
  rw [← poissonMeasure_conv_poissonMeasure,integral_conv hconv,← integral_sub hj (hi r)]
  exact abs_integral_le_bound hd

end DilutedSpinGlass
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

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)

/-- Quadratic envelopes allow both the pressure and its square to be passed
through the two independent compound laws, without any count cut-off. -/
theorem fullRoot_integrable_quadratic
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : ∀ k n, Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n y, |F h k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (packRoot F) (fullRootLaw ξ μ ν r s) := by
  have hk := (((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)).comp_snd (rootLaw M ξ)
  have hn := (((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)).comp_snd (rootLaw M ξ)
  have he : Integrable (fun z : FullRootState Y X I M => B+C*(z.2.1.1:ℝ)^2+D*(z.2.2.1:ℝ)^2)
      (fullRootLaw ξ μ ν r s) := (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' (measurable_packRoot hF).aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,packRoot] using hb z.1 z.2.1.1 z.2.1.2 z.2.2.1 z.2.2.2))


theorem twoCompound_integrable_quadratic
    {F : (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hF : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2))
    {B C D : ℝ} (hb : ∀ k x n y, |F k x n y| ≤ B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) => F z.1.1 z.1.2 z.2.1 z.2.2)
      ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) := by
  have hk := ((familyPoisson_count_memLp (fun k => rootLaw k (fun _ => μ)) r).integrable_sq).comp_fst
    (compoundRootLaw ν s)
  have hn := ((familyPoisson_count_memLp (fun n => rootLaw n (fun _ => ν)) s).integrable_sq).comp_snd
    (compoundRootLaw μ r)
  have he : Integrable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      B+C*(z.1.1:ℝ)^2+D*(z.2.1:ℝ)^2) ((compoundRootLaw μ r).prod (compoundRootLaw ν s)) :=
    (integrable_const B).add (hk.const_mul C) |>.add (hn.const_mul D)
  exact he.mono' hF.aestronglyMeasurable (ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using hb z.1.1 z.1.2 z.2.1 z.2.2))

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinRootData
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

theorem abs_spin (s : Spin) : |spin s| = 1 := by
  cases s <;> norm_num [spin]

end DilutedSpinGlass.PhysicalRoot
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountedSteps
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma fieldMean_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |fieldMean (N := N) ξ theta field Q m ψ| ≤ H*N+C*k+D*l :=
  abs_integral_le_const _ (fun root => spinMean_bound Q m hm theta _ ψ hθ
    (fun index => hh (rootArray N root index)) hψ)

lemma measurable_fieldMean {Z : Type} [MeasurableSpace Z] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Z → Fin k → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ j σ, Measurable (fun z => (theta z j).1 σ)) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ) :
    Measurable (fun z => fieldMean (N := N) ξ (theta z) field Q m ψ) := by
  exact (measurable_spinMean Q m (fun z : Z × RootPath Y N => theta z.1)
    (fun z i => field (rootArray N z.2 i)) ψ
    (fun j σ => (hθm j σ).comp measurable_fst)
    (fun i => hhm.comp ((measurable_rootArray N i).comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_spinMean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    Integrable (fun h : RootPath Y N => spinMean Q m theta
      (fun i => field (rootArray N h i)) ψ) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound (measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hhm.comp (measurable_rootArray N i))).aestronglyMeasurable
    (H*N+C*k+D*l)
  filter_upwards [] with h
  simpa only [Real.norm_eq_abs,Function.comp_def] using
    spinMean_bound Q m hm theta (fun i => field (rootArray N h i)) ψ hθ (fun i => hh _) hψ

/-- Count insertion draws the original countable dictionary type; its entire
finite mark alphabet and all level priors are kept. -/
theorem countedMean_mark_step (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k (l+1)-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ D := by
  let F := fun (l : ℕ) (a : RootPath I l) (x : RootPath X k) =>
    fieldMean (N := N) ξ (fun j => theta (rootArray k x j)) field
      (fun j => Q (rootArray l a j)) m (fun j => ψ (rootArray l a j))
  have hFm (l : ℕ) (a : RootPath I l) : Measurable (F l a) :=
    measurable_fieldMean ξ _ field (fun j σ => (hθm σ).comp (measurable_rootArray k j)) hhm _ m _
  have hFb (l : ℕ) (a : RootPath I l) (x : RootPath X k) : |F l a x| ≤ H*N+C*k+D*l :=
    fieldMean_bound ξ _ field _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b)
  have hFi (l : ℕ) (a : RootPath I l) : Integrable (F l a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm l a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb l a x))
  have hOi (l : ℕ) : Integrable (fun a => ∫ x, F l a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb l a)))
  have hg := (hOi l).comp_snd ν
  have he : (∫ a : I × RootPath I l, (∫ x, F l a.2 x ∂rootLaw k (fun _ => μ))
      ∂ν.prod (rootLaw l (fun _ => ν))) =
      ∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν) := by
    rw [integral_prod _ hg]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ a, ∫ x, F (l+1) a x ∂rootLaw k (fun _ => μ) ∂ν.prod (rootLaw l (fun _ => ν)))-
    (∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν))| ≤ D
  rw [← he]
  apply abs_integral_sub_le_const (ν.prod (rootLaw l (fun _ => ν))) (hOi (l+1)) hg
  intro a
  apply abs_integral_sub_le_const _ (hFi (l+1) a) (hFi l a.2)
  intro x
  apply abs_integral_sub_le_const _
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
  intro h
  exact spinMean_mark_step _ m hm _ _ _ (hψ a.1)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma poisson_abs_mean_le (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A+B*n) : |∫ n, f n ∂poissonMeasure r| ≤ A+B*r := by
  have hi := poisson_integrable_linear r h
  have hg : Integrable (fun n : ℕ => A+B*n) (poissonMeasure r) :=
    (integrable_const A).add ((poisson_integrable_count r).const_mul B)
  calc
    _ ≤ ∫ n, |f n| ∂poissonMeasure r := abs_integral_le_integral_abs
    _ ≤ ∫ n : ℕ, A+B*n ∂poissonMeasure r := integral_mono hi.abs hg h
    _ = _ := by rw [integral_add (integrable_const A) ((poisson_integrable_count r).const_mul B),
        integral_const_mul,poisson_mean]; simp

lemma twoPoisson_inner_integrable (r s : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D : ℝ}
    (h : ∀ k l, |f k l| ≤ A+B*k+D*l) :
    Integrable (fun k => ∫ l, f k l ∂poissonMeasure s) (poissonMeasure r) := by
  apply poisson_integrable_linear r (A := A+D*s) (B := B)
  intro k
  have ht := poisson_abs_mean_le s (h k)
  linarith

lemma twoPoissonMean_rate_add_right (r s t : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D C : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hC : 0 ≤ C)
    (hs : ∀ k l, |f k (l+1)-f k l| ≤ C) :
    |twoPoissonMean r (s+t) f-twoPoissonMean r s f| ≤ C*t := by
  apply SizeCoupling.abs_integral_sub_le_const _ (twoPoisson_inner_integrable r (s+t) hf)
    (twoPoisson_inner_integrable r s hf)
  intro k
  exact poisson_average_rate_add s t hC (hs k)

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PerturbedSizeCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass
open scoped NNReal

lemma scoreScale_mono : Monotone scoreScale := by
  intro M N hMN
  exact Real.rpow_le_rpow (Nat.cast_nonneg M) (by exact_mod_cast hMN) (by norm_num)

end DilutedSpinGlass

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

lemma rootArrayEquiv_apply (n : ℕ) (x : RootPath X n) : rootArrayEquiv (X := X) n x = rootArray n x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.insertNth 0 x.1 (rootArrayEquiv (X := X) n x.2) =
      Fin.cons (α := fun _ : Fin (n+1) => X) x.1 (rootArray n x.2)
    rw [Fin.insertNth_zero', ih]


/-- Exact law identification for arbitrary measurable disorder alphabets,
including the continuous physical interaction tables and external fields. -/
theorem measurePreserving_rootArray (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (rootArrayEquiv (X := X) n) (rootLaw n (fun _ => μ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    refine ⟨(rootArrayEquiv 0).measurable, ?_⟩
    rw [rootLaw,Measure.map_dirac' (rootArrayEquiv 0).measurable,Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.comp
      ((MeasurePreserving.id μ).prod ih)

theorem integral_rootArray_eq_pi (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) :
    (∫ x, f (rootArray n x) ∂rootLaw n (fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ n).integral_comp' f

end DilutedSpinGlass
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
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootAE
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

lemma measurePreserving_rootArray_coordinate {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun z : RootPath X n => rootArray n z i) (rootLaw n μ) (μ i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact measurePreserving_fst
    | succ i =>
      exact (ih (fun j => μ j.succ) i).comp (measurePreserving_snd)

lemma rootLaw_ae_all {X : Type} [MeasurableSpace X] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (P : Fin n → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ i, P i x) :
    ∀ᵐ z ∂rootLaw n μ, ∀ i, P i (rootArray n z i) := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_rootArray_coordinate n μ i).quasiMeasurePreserving.ae (hP i)

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) μ ξ ν theta field Q m ψ k l =
      countedMean (N := N) μ ξ ν theta' field' Q m ψ k l := by
  unfold countedMean
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all k (fun _ => μ) (fun _ x => theta x = theta' x) (fun _ => hθ)] with x hx
  apply integral_congr_ae
  filter_upwards [rootLaw_ae_all N (fun _ => ξ) (fun _ y => field y = field' y) (fun _ => hh)] with y hy
  congr 1
  · funext i; exact hx i
  · funext i; exact hy i

end SizeCoupling
end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullSelectedRegularity
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.bondLaw_probability _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal

lemma clipReal_bound {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clipReal C x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma clipReal_eq {C x : ℝ} (hx : |x| ≤ C) : clipReal C x = x := by
  simp only [clipReal,min_eq_right (abs_le.mp hx).2,max_eq_right (abs_le.mp hx).1]

lemma clipSample_bound {p : ℕ} {C : ℝ} (hC : 0 ≤ C) (z : InteractionSample p) (σ) :
    |(clipSample C z).1 σ| ≤ C := clipReal_bound hC _

lemma clipSample_eq {p : ℕ} {C : ℝ} {z : InteractionSample p}
    (hz : ∀ σ, |z.1 σ| ≤ C) : clipSample C z = z := by
  apply Prod.ext
  · funext σ; exact clipReal_eq (hz σ)
  · rfl

namespace SizeCoupling
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

omit [Countable I] [MeasurableSingletonClass I] in
lemma perturbedMean_congr (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta theta' : X → InteractionSample p) (field field' : Y → ℝ)
    (hθ : theta =ᵐ[μ] theta') (hh : field =ᵐ[ξ] field')
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (u v : ℝ≥0) :
    perturbedMean (N := N) μ ξ ν theta field Q m ψ u v =
      perturbedMean (N := N) μ ξ ν theta' field' Q m ψ u v := by
  unfold perturbedMean twoPoissonMean
  simp_rw [countedMean_congr μ ξ ν theta theta' field field' hθ hh Q m ψ]

end SizeCoupling
end DilutedSpinGlass
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
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Set


lemma boundParameter_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    boundParameter a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ExternalRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

lemma abs_log_affine_le {d e t u : ℝ} (hD : |d| ≤ 1) (hE : |e| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) : |Real.log (1+t*d+u*e)| ≤ 1 := by
  have htd : |t*d| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg t,abs_nonneg d]
  have hue : |u*e| ≤ 1/4 := by rw [abs_mul]; nlinarith [abs_nonneg u,abs_nonneg e]
  have hlo : 1/2 ≤ 1+t*d+u*e := by linarith [(abs_le.mp htd).1,(abs_le.mp hue).1]
  have hhi : 1+t*d+u*e ≤ 3/2 := by linarith [(abs_le.mp htd).2,(abs_le.mp hue).2]
  have hpos : 0 < 1+t*d+u*e := by linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hinv : (1+t*d+u*e)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    linarith
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [∀ q, Fintype (A q)] in
lemma spinFactor_log_bound
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (u : K×ℕ → ℝ) (i : K×ℕ) (σ : Spin) (y : FinitePath (A i.1) (L+1)) :
    |Real.log (spinFactor D E u i σ y)| ≤ 1 := by
  apply abs_log_affine_le (hD _ _ _) (hE _ _ _) (extractionProbe_abs_le_quarter _)
  have hu := probe_interval_quarter i.2 (boundParameter_mem (probeLow_lt_high i.2).le (u i))
  exact abs_le.mpr ⟨by linarith [hu.1],hu.2⟩

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UniversalDictionary
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators


lemma table_bound {L r : ℕ} (g : Table L r) (y : Fin L → Fin r → Bool) :
    |(g.1 y : ℝ)| ≤ 1 := by exact_mod_cast g.2 y
lemma direction_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |direction q σ y| ≤ 1 := by
  rw [direction,abs_mul]
  have hs : |spin σ| = 1 := by cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _
lemma anchor_bound {L : ℕ} (q : Spec L) (σ : Spin) (y) :
    |anchor q σ y| ≤ 1 := by
  rw [anchor,abs_mul]
  have hs : |(if q.2.2.2 then spin σ else 1 : ℝ)| = 1 := by
    split <;> cases σ <;> norm_num [spin]
  rw [hs,mul_one]
  exact table_bound _ _

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

lemma gridExponents_lower (L : ℕ) (j : Fin (L+1)) :
    ((L+1:ℕ):ℝ)⁻¹ ≤ gridExponents L j := by
  change _ ≤ (((j:ℕ)+1:ℕ):ℝ)/((L+1:ℕ):ℝ)
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.le_add_left 1 j.val)

lemma gridExponents_last (L : ℕ) : gridExponents L (Fin.last L) = 1 := by
  simp only [gridExponents,Fin.val_last]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos L)))

end DilutedSpinGlass.UniversalDictionary
end

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRegularSelection
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

noncomputable local instance fullRegularSelectionDecidableEq_rc0eab8_1 (β : Type) :
    DecidableEq β := Classical.decEq β
lemma gridExponents_pos (L : ℕ) (j : Fin (L+1)) :
    0 < gridExponents L j :=
  (inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos L))).trans_le (gridExponents_lower L j)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MixedPatterns
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
lemma measurable_rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (rootInsertion T Q m base old V a F) := by
  apply measurable_from_prod_countable_left
  intro v
  apply measurable_packRoot_into (F := fun h k x n y =>
    backwardLog (L+1) (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old)) m
      (fun w => F (fun i => V (physical (rootArray n y) (L+1) w) (v i))))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  simp_rw [← insertion]
  apply Measurable.sub
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact ((hb k _).add measurable_const).add measurable_const
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact (hb k _).add measurable_const

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open Filter _root_.MeasureTheory
open scoped NNReal Topology

lemma reservoirRate_le (α : ℝ≥0) (q N : ℕ) : reservoirRate α q N ≤ α*N := by
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr (by simp))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IntegralError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integrate_error {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g E : X → ℝ} (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hE : Integrable E μ) (h : ∀ᵐ x ∂μ,|f x-g x|≤E x) :
    Integrable f μ ∧ |(∫ x,f x ∂μ)-(∫ x,g x ∂μ)|≤∫ x,E x ∂μ := by
  have hd : Integrable (fun x => f x-g x) μ := hE.mono' (hf.sub hg.aestronglyMeasurable) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by simpa only [Pi.add_def,sub_add_cancel] using hd.add hg
  refine ⟨hfi,?_⟩
  rw [← integral_sub hfi hg]
  calc
    _ ≤ ∫ x,|f x-g x| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x-g x)
    _ ≤ _ := integral_mono_ae hd.abs hE h

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SameInsertionAverage
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma sameInsertionAverage_bound (hm : ∀ i, 0 < m i) (a : ℕ)
    (F : (Fin a → Spin) → ℝ) {C : ℝ} (hF : ∀ s, |F s|≤C) (z : FullRootState Y X I M) :
    |sameInsertionAverage T Q m base old V a F z|≤C := by
  apply FiniteLaw.abs_expect_le
  intro i
  exact backwardLog_bound (L+1) _ m hm (fun y => hF _)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators Topology
variable {p : ℕ}

lemma reservoirInsertion_bound (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (a : ℕ) (F : (Fin a → Spin) → ℝ) {D : ℝ} (hF : ∀ s, |F s|≤D) :
    |reservoirInsertion M C H N L u a F|≤D := by
  apply abs_integral_le_bound
  intro z
  exact sameInsertionAverage_bound _ _ _ _ _ _ (gridExponents_pos L) a F hF z


end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma map_familyLaw_sum {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] (μ : Measure I) (ν : ∀ i, Measure (X i))
    (f : (i : I) → X i → Y) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) =
      Measure.sum (fun i => μ {i} • Measure.map (f i) (ν i)) := by
  rw [familyLaw,Measure.comp_eq_sum_of_countable]
  rw [Measure.map_sum (measurable_sigmaUncurry hf).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul]
  change μ {i} • Measure.map (fun z : Sigma X => f z.1 z.2)
    (Measure.map (Sigma.mk i) (ν i)) = _
  rw [Measure.map_map (measurable_sigmaUncurry hf) (measurable_sigmaMk i)]
  rfl

variable {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma map_iid_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (n : ℕ) :
    Measure.map (fun x : RootPath X n => ∑ i, V (rootArray n x i)) (rootLaw n (fun _ => μ)) =
      Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => Measure.map V μ)) := by
  have hp := (measurePreserving_rootArray μ n).map_eq
  rw [← Measure.pi_map_pi (fun _ : Fin n => hV.aemeasurable)]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hp,Measure.map_map (by fun_prop) (rootArrayEquiv n).measurable]
  congr 1
  funext x
  simp only [Function.comp_apply,rootArrayEquiv_apply]

omit [NormedSpace ℝ E] in
/-- The physical recursive Poisson container has exactly the compound-sum
energy law, including its independent random count. -/
lemma map_compoundRoot_energy (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) :
    Measure.map (fun z : Sigma (RootPath X) => ∑ i, V (rootArray z.1 z.2 i)) (compoundRootLaw μ r) =
      compoundPoisson r (Measure.map V μ) := by
  rw [compoundRootLaw,map_familyLaw_sum _ _ (fun n x => ∑ i,V (rootArray n x i)) (fun n => by
    simpa only [rootArrayEquiv_apply] using
      (show Measurable (fun x : RootPath X n => ∑ i,V (rootArrayEquiv (X := X) n x i)) by fun_prop))]
  simp only [poissonMeasure_singleton,map_iid_energy μ V hV,compoundPoisson]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] in
lemma iid_energy_integrable (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    Integrable id (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) := by
  rw [integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  change Integrable (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))
  exact integrable_finsetSum _ (fun i _ => integrable_eval (μ := fun _ : Fin n => μ) (i := i) hi)

omit [NormedSpace ℝ E] in
lemma iid_energy_norm_le (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) (n : ℕ) :
    (∫ x, ‖x‖ ∂Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) ≤
      n*(∫ x, ‖x‖ ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  calc
    _ ≤ ∫ x : Fin n → E, ∑ i, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono (integrable_finsetSum _ (fun i _ => integrable_eval hi)).norm
        (integrable_finsetSum _ (fun i _ => integrable_comp_eval hi.norm))
        (fun x => norm_sum_le _ _)
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ => integrable_comp_eval hi.norm)]
      have he (i : Fin n) : (∫ x : Fin n → E, ‖x i‖ ∂Measure.pi (fun _ : Fin n => μ)) = ∫ x,‖x‖ ∂μ :=
        integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) (by fun_prop)
      simp only [he,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

omit [NormedSpace ℝ E] in
lemma compoundPoisson_integrable_id (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) : Integrable id (compoundPoisson r μ) := by
  unfold compoundPoisson
  apply integrable_sum_measure
  · intro n
    exact (iid_energy_integrable μ hi n).smul_measure ENNReal.ofReal_ne_top
  · have hs := ((hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right
      (∫ x, ‖x‖ ∂μ)).summable
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) _ hs
    intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)

omit [NormedSpace ℝ E] in
lemma compoundPoisson_norm_le (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable id μ) :
    (∫ x, ‖x‖ ∂compoundPoisson r μ) ≤ r*(∫ x, ‖x‖ ∂μ) := by
  have hc : Integrable (fun x : E => ‖x‖) (compoundPoisson r μ) :=
    (compoundPoisson_integrable_id r μ hi).norm
  rw [compoundPoisson,integral_sum_measure hc]
  have hs := (hasSum_integral_poissonMeasure (poisson_integrable_count r)).mul_right (∫ x,‖x‖ ∂μ)
  rw [poisson_mean] at hs
  rw [← hs.tsum_eq]
  apply Summable.tsum_le_tsum
  · intro n
    rw [integral_smul_measure,ENNReal.toReal_ofReal (by positivity)]
    change (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*_ ≤
      ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial)*(n:ℝ))*(∫ x,‖x‖ ∂μ)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (iid_energy_norm_le μ hi n) (by positivity)
  · exact (hasSum_integral_measure hc).summable
  · exact hs.summable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [NormedSpace ℝ E] [SecondCountableTopology E] in
lemma integrable_lipschitz_of_id (μ : Measure E) [IsFiniteMeasure μ]
    (hi : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) : Integrable f μ := by
  apply ((hi.norm.const_mul (C:ℝ)).add (integrable_const |f 0|)).mono' hf.continuous.measurable.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hh := hf.norm_sub_le x 0
  simp only [Real.norm_eq_abs,sub_zero] at hh
  calc
    |f x| = |(f x-f 0)+f 0| := by rw [sub_add_cancel]
    _ ≤ |f x-f 0|+|f 0| := abs_add_le _ _
    _ ≤ (C:ℝ)*‖x‖+|f 0| := by linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_id_conv (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) : Integrable id (μ∗ν) := by
  rw [Measure.conv,integrable_map_measure aestronglyMeasurable_id (by fun_prop)]
  exact (hμ.comp_fst ν).add (hν.comp_snd μ)

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma lipschitz_conv_add_bound (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x, f x ∂(μ∗ν))-(∫ x, f x ∂μ)| ≤ C*(∫ y,‖y‖ ∂ν) := by
  have hfi := integrable_lipschitz_of_id μ hμ hf
  have hfc := integrable_lipschitz_of_id (μ∗ν) (integrable_id_conv μ ν hμ hν) hf
  have hfp : Integrable (fun z : E×E => f (z.1+z.2)) (μ.prod ν) := by
    exact (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable (by fun_prop)).mp hfc
  rw [integral_conv hfc,← integral_sub hfp.integral_prod_left hfi]
  calc
    _ ≤ ∫ x, |(∫ y, f (x+y) ∂ν)-f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _x, (C:ℝ)*(∫ y,‖y‖ ∂ν) ∂μ := by
      apply integral_mono (hfp.integral_prod_left.sub hfi).abs (integrable_const _)
      intro x
      have hx : Integrable (fun y => f (x+y)) ν := by
        apply integrable_lipschitz_of_id ν hν
        simpa only [mul_one,Function.comp_def] using hf.comp (isometry_add_left x).lipschitz
      change |(∫ y, f (x+y) ∂ν)-f x|≤_
      have hc : (∫ _y : E, f x ∂ν)=f x := by simp
      rw [← hc,← integral_sub hx (integrable_const _)]
      calc
        _ ≤ ∫ y, |f (x+y)-f x| ∂ν := abs_integral_le_integral_abs
        _ ≤ ∫ y, (C:ℝ)*‖y‖ ∂ν := by
          apply integral_mono (hx.sub (integrable_const _)).abs (hν.norm.const_mul _)
          intro y
          simpa only [add_sub_cancel_left,Real.norm_eq_abs,Pi.sub_apply,id_eq] using hf.norm_sub_le (x+y) x
        _ = _ := integral_const_mul _ _
    _ = _ := by simp

lemma compoundPoisson_rate_add_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson (r+s) μ)-(∫ x, f x ∂compoundPoisson r μ)| ≤
      C*s*(∫ y,‖y‖ ∂μ) := by
  rw [compoundPoisson_add]
  exact (lipschitz_conv_add_bound _ _ (compoundPoisson_integrable_id r μ hμ)
    (compoundPoisson_integrable_id s μ hμ) hf).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (compoundPoisson_norm_le s μ hμ) C.coe_nonneg)

lemma compoundPoisson_rate_bound (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    |(∫ x, f x ∂compoundPoisson r μ)-(∫ x, f x ∂compoundPoisson s μ)| ≤
      C*|(r:ℝ)-s| *(∫ y,‖y‖ ∂μ) := by
  rcases le_total s r with h|h
  · have hh := compoundPoisson_rate_add_bound s (r-s) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh
  · have hh := compoundPoisson_rate_add_bound r (s-r) μ hμ hf
    rw [add_tsub_cancel_of_le h,NNReal.coe_sub h] at hh
    rw [abs_sub_comm (∫ x, f x ∂compoundPoisson r μ),abs_sub_comm (r:ℝ),
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h))]
    exact hh

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal ENNReal BigOperators
variable {Ω I S : Type} [Fintype Ω] [Fintype S]
    {A : I → Type} [∀ i,Fintype (A i)] {L k : ℕ}

lemma root_energy_insertion (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base F : FinitePath Ω L → ℝ)
    (roots : Fin k → I) (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    root T Q m (base+F) roots factor-root T Q m base roots factor =
      backwardLog L (tilt L (tower roots L T Q) m (logWeight base roots factor)) m
        (fun y => F (physical roots L y)) := by
  unfold root
  rw [← insertion]
  congr 2
  funext y
  simp only [logWeight,Pi.add_apply]
  ring

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RandomInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] {M : ℕ}

lemma integral_fullRootLaw_reordered
    (ξ : Fin M → Measure Y) [∀ i,IsProbabilityMeasure (ξ i)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (r s : ℝ≥0)
    {F : RootPath Y M → (k : ℕ) → RootPath X k → (n : ℕ) → RootPath I n → ℝ}
    (hf : ∀ k n,Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2))
    {B C D : ℝ} (hb : ∀ h k x n a,|F h k x n a|≤B+C*(k:ℝ)^2+D*(n:ℝ)^2) :
    (∫ z,packRoot F z ∂fullRootLaw ξ μ ν r s) =
      ∫ h,∫ a : Sigma (RootPath I),∫ x : Sigma (RootPath X),F h x.1 x.2 a.1 a.2
        ∂compoundRootLaw μ r ∂compoundRootLaw ν s ∂rootLaw M ξ := by
  rw [fullRootLaw,integral_prod _ (fullRoot_integrable_quadratic ξ μ ν r s hf hb)]
  apply integral_congr_ae
  filter_upwards [] with h
  have hmf : Measurable (fun z : Sigma (RootPath X) × Sigma (RootPath I) =>
      F h z.1.1 z.1.2 z.2.1 z.2.2) :=
    (measurable_packRoot hf).comp (measurable_const.prodMk measurable_id)
  exact integral_prod_symm _ (twoCompound_integrable_quadratic μ ν r s hmf (hb h))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundPhysicalMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal ENNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_lipschitz (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) :
    LipschitzWith 1 (energyRoot Q m field factor h a) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  apply root_base_stability _ Q m hm
  intro y
  simp only [add_sub_add_right_eq_sub]
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FinitePoissonSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

lemma integral_root_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) × (Fin n → Y) → ℝ)
    (hF : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ν)))) :
    (∫ z : RootPath (X×Y) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod ν)) =
      ∫ x : Fin n → X,∫ y : Fin n → Y,F (x,y)
        ∂Measure.pi (fun _ : Fin n => ν) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_rootArray_eq_pi (μ.prod ν) n (fun z : Fin n → X×Y => F ((fun i => (z i).1),(fun i => (z i).2)))]
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun _ => μ) (fun _ => ν)).integral_comp' F
  exact he.trans (integral_prod F hF)

lemma integral_root_prod_finite {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (hF : Measurable F)
    {B : ℝ} (hb : ∀ z,|F z|≤B) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (PMF.uniformOfFintype J).toMeasure)) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  have hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype J).toMeasure))) :=
    Integrable.of_bound hF.aestronglyMeasurable B (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb z))
  rw [integral_root_prod μ (PMF.uniformOfFintype J).toMeasure n F hi]
  apply integral_congr_ae
  filter_upwards [] with x
  change (∫ j,F (x,j) ∂Measure.pi (fun _ : Fin n => finiteUniform J)) = _
  rw [finiteUniform_pi,integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

lemma expMoment_bind_one (P : FiniteLaw Ω) (Q : FiniteLaw A) (F : Ω×A → ℝ) :
    (P.bind (fun _ => Q)).expMoment 1 F =
      Q.expect (fun a => P.expMoment 1 (fun s => F (s,a))) := by
  unfold expMoment
  rw [expect_bind]
  simp only [one_mul,expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma logMean_bind_one_congr (P : FiniteLaw Ω) (R : FiniteLaw Λ) (Q : FiniteLaw A)
    (F : Ω×A → ℝ) (G : Λ×A → ℝ)
    (h : ∀ a, P.expMoment 1 (fun s => F (s,a)) = R.expMoment 1 (fun s => G (s,a))) :
    (P.bind (fun _ => Q)).logMean 1 F = (R.bind (fun _ => Q)).logMean 1 G := by
  simp only [logMean,div_one,expMoment_bind_one]
  rw [show (fun a => P.expMoment 1 (fun s => F (s,a))) =
    (fun a => R.expMoment 1 (fun s => G (s,a))) from funext h]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ A : Type} [Fintype Ω] [Fintype Λ] [Fintype A]

/-- Equality of the genuine final-spin marginal propagates through every
auxiliary conditional power mean. The only required endpoint is m_L=1. -/
lemma terminal_marginal_congr (L : ℕ) (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (U : KernelTower A (L+1)) (m : Fin (L+1) → ℝ) (hm : m (Fin.last L)=1)
    (F : Ω → FinitePath A (L+1) → ℝ) (G : Λ → FinitePath A (L+1) → ℝ)
    (h : ∀ y, P.expMoment 1 (fun s => F s y) = R.expMoment 1 (fun s => G s y)) :
    backwardLog (L+1) (prod (L+1) (terminalTower a P L) U) m
      (fun y => F (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) =
    backwardLog (L+1) (prod (L+1) (terminalTower b R L) U) m
      (fun y => G (terminalState L (pathFst (L+1) y)) (pathSnd (L+1) y)) := by
  induction L with
  | zero =>
    change (P.bind (fun _ => U.1)).logMean (m 0) (fun z => F z.1 (z.2,())) =
      (R.bind (fun _ => U.1)).logMean (m 0) (fun z => G z.1 (z.2,()))
    change m 0=1 at hm
    rw [hm]
    exact FiniteLaw.logMean_bind_one_congr P R U.1 _ _ (fun u => h (u,()))
  | succ L ih =>
    change ( (FiniteLaw.point a).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower a P L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => F (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y))) =
      ((FiniteLaw.point b).bind (fun _ => U.1)).logMean (m 0)
      (fun z => backwardLog (L+1) (prod (L+1) (terminalTower b R L) (U.2 z.2))
        (fun i => m i.succ)
        (fun y => G (terminalState L (pathFst (L+1) y)) (z.2,pathSnd (L+1) y)))
    unfold FiniteLaw.logMean FiniteLaw.expMoment
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    simp only [FiniteLaw.expect_point]
    congr 1
    congr 1
    apply congrArg (FiniteLaw.expect U.1)
    funext u
    congr 1
    congr 1
    exact ih (U.2 u) (fun i => m i.succ) hm (fun s y => F s (u,y)) (fun s y => G s (u,y))
      (fun y => h (u,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_SpinMarginal
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma uniform_cons_expect (N : ℕ) (F : (Fin (N+1) → Spin) → ℝ) :
    (uniform : FiniteLaw (Fin (N+1) → Spin)).expect F =
      (uniform : FiniteLaw (Fin N → Spin)).expect (fun σ =>
        (uniform : FiniteLaw Spin).expect (fun ε => F (Fin.cons ε σ))) := by
  rw [uniform_expect,uniform_expect]
  simp_rw [uniform_expect]
  rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp F]
  simp only [Fintype.sum_prod_type,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,← Finset.sum_div,Fin.consEquiv,Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  push_cast
  rw [pow_succ]
  ring

lemma exp_logMean_one (P : FiniteLaw Spin) (F : Spin → ℝ) :
    Real.exp (P.logMean 1 F) = P.expect (fun ε => Real.exp (F ε)) := by
  rw [logMean,div_one,Real.exp_log (expMoment_pos P 1 F)]
  simp only [expMoment,one_mul]

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {Ω Λ I : Type} [Fintype Ω] [Fintype Λ] {A : I → Type} [∀ i,Fintype (A i)]
    {k L N : ℕ}

omit [Fintype Ω] [∀ index, Fintype (A index)] in
lemma mark_eq_pathMap (roots : Fin k → I) (j : Fin k) (n : ℕ)
    (y : FinitePath (Ω × Row (A := A) roots) n) :
    mark j n y = pathMap (fun a : Row (A := A) roots => a j) n (pathSnd n y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (y.1.2 j,mark j n y.2) = (y.1.2 j,pathMap _ n (pathSnd n y.2))
    rw [ih]

lemma terminalRoot_eq_backward (a : Ω) (P : FiniteLaw Ω)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (E : Ω → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot a P Q m E roots ψ =
      backwardLog (L+1) (prod (L+1) (terminalTower a P L)
        (markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d)))) m
        (fun y => E (terminalState L (pathFst (L+1) y))+
          ∑ j,Real.log (ψ (roots j) (terminalState L (pathFst (L+1) y))
            (pathMap (fun a : Row (A := A) roots => a j) (L+1) (pathSnd (L+1) y)))) := by
  simp only [terminalRoot,root,tower_eq_prod]
  congr 1
  funext y
  simp only [HeterogeneousMarks.logWeight,physical_eq_fst,mark_eq_pathMap]

lemma terminalRoot_marginal (a : Ω) (b : Λ) (P : FiniteLaw Ω) (R : FiniteLaw Λ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : Ω → ℝ) (G : Λ → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Ω → FinitePath (A i) (L+1) → ℝ)
    (φ : (i : I) → Λ → FinitePath (A i) (L+1) → ℝ)
    (h : ∀ y : FinitePath (Row (A := A) roots) (L+1),
      P.expMoment 1 (fun s => E s+∑ j, Real.log (ψ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))) =
      R.expMoment 1 (fun s => G s+∑ j, Real.log (φ (roots j) s
        (pathMap (fun a : Row (A := A) roots => a j) (L+1) y)))) :
    terminalRoot a P Q m E roots ψ = terminalRoot b R Q m G roots φ := by
  rw [terminalRoot_eq_backward,terminalRoot_eq_backward]
  let U : KernelTower (Row (A := A) roots) (L+1) :=
    markPrior (L+1) (fun d => FiniteLaw.pi (fun j => Q (roots j) d))
  let F : Ω → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    E s+∑ j, Real.log (ψ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  let G' : Λ → FinitePath (Row (A := A) roots) (L+1) → ℝ := fun s y =>
    G s+∑ j, Real.log (φ (roots j) s (pathMap (fun a : Row (A := A) roots => a j) (L+1) y))
  exact terminal_marginal_congr L a b P R U m hm F G' h

/-- Exact new-spin marginalization at the final exponent1. -/
lemma terminalRoot_spin_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ) (G : (Fin (N+1) → Spin) → ℝ)
    (roots : Fin k → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+G σ) roots (fun i σ a => ψ i (fun j => σ j.succ) a) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))) roots ψ := by
  apply terminalRoot_marginal _ _ _ _ Q m hm
  intro a
  unfold FiniteLaw.expMoment
  simp only [one_mul]
  rw [FiniteLaw.uniform_cons_expect]
  apply FiniteLaw.expect_congr
  intro σ
  simp only [Fin.cons_succ]
  let c := ∑ j,Real.log (ψ (roots j) σ (pathMap (fun a : Row (A := A) roots => a j) (L+1) a))
  change (FiniteLaw.uniform : FiniteLaw Spin).expect (fun ε => Real.exp (E σ+G (Fin.cons ε σ)+c)) =
    Real.exp (E σ+(FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun ε => G (Fin.cons ε σ))+c)
  simp_rw [Real.exp_add]
  rw [FiniteLaw.expect_mul_right,FiniteLaw.expect_mul_left,FiniteLaw.exp_logMean_one]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkSiteCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower SizeCoupling
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k L : ℕ} [NeZero N]

omit [NeZero N] in
/-- Move only perturbation sites off the added spin, leaving energy and all
auxiliary mark labels and count laws unchanged. -/
lemma terminalRoot_mark_sites
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D)
    (z : Fin k → Fin (N+1) × Fin N) :
    |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a) -
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)| ≤
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
  have h := root_factor_stability (terminalTower (fun _ : Fin (N+1) => false)
    FiniteLaw.uniform L) (fun j : Fin k => Q (roots j)) m hm
    (fun y => E (terminalState L y)) id
    (fun j y a => ψ (roots j) (terminalState L y (newIndex (z j))) a)
    (fun j y a => ψ (roots j) (terminalState L y (oldIndex (z j)).succ) a)
    (fun j => if (z j).1=0 then 2*D else 0) (by
      intro j y a
      by_cases hj : (z j).1=0
      · simp only [hj,↓reduceIte]
        have h1 := hψ (roots j) (terminalState L y (newIndex (z j))) a
        have h2 := hψ (roots j) (terminalState L y (oldIndex (z j)).succ) a
        exact (abs_sub _ _).trans (by linarith)
      · simp only [hj,↓reduceIte,same_index_off_new (z j) hj,sub_self,abs_zero,le_refl])
  have he : (∑ j : Fin k,if (z j).1=0 then 2*D else 0) =
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero]
  exact h.trans_eq he

lemma terminalRoot_mark_site_expect
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D) :
    |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)) -
      (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a))| ≤
      2*D*k/(N+1) := by
  let R := FiniteLaw.pi (fun _ : Fin k => indexLaw N)
  have hn := FiniteLaw.Projects.pi (fun _ : Fin k => newIndex_projects N)
  have ho := FiniteLaw.Projects.pi (fun _ : Fin k => oldIndex_projects N)
  rw [← hn (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)),
    ← ho (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a)),
    ← FiniteLaw.expect_sub]
  calc
    _ ≤ R.expect (fun z => |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a)-
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)|) :=
      FiniteLaw.abs_expect_le_expect_abs R _
    _ ≤ R.expect (fun z => 2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0)) :=
      R.expect_mono (terminalRoot_mark_sites Q m hm E roots ψ hψ)
    _ = _ := by rw [FiniteLaw.expect_mul_left,expected_new_count]; ring

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

lemma measurable_indexedPotential (theta : X → InteractionSample p)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (indexedPotential (N := N) theta) := by
  apply Measurable.of_eval
  intro σ
  apply measurable_from_prod_countable_left
  intro j
  simpa only [indexedPotential] using hθ (fun q => σ (j q))

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CountBridgeTools
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory
open scoped BigOperators
variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]
lemma integral_expect (P : FiniteLaw Ω) (μ : Measure X) (f : X → Ω → ℝ)
    (hf : ∀ i,Integrable (fun x => f x i) μ) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) := by
  unfold expect
  rw [integral_finsetSum _ (fun i _ => (hf i).const_mul _)]
  simp only [integral_const_mul]
lemma integral_expect_bounded (P : FiniteLaw Ω) (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Ω → ℝ) (hf : ∀ i,Measurable (fun x => f x i)) {B : ℝ}
    (hb : ∀ x i,|f x i|≤B) :
    (∫ x,P.expect (f x) ∂μ)=P.expect (fun i => ∫ x,f x i ∂μ) :=
  integral_expect P μ f (fun i => Integrable.of_bound (hf i).aestronglyMeasurable B
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x i)))
end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionAlgebra
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory

lemma cavitySiteEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) :
    |cavitySiteEnergy θ h s| ≤ |h|+∑ j,‖(θ j).1‖ := by
  change |Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)| ≤ _
  have hh (ε : Spin) : |h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)| ≤ |h|+∑ j,‖(θ j).1‖ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul,abs_spin,mul_one]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (appendSpin (fun l => s (j,l)) ε)))
  -- This is the logarithm of the uniform two-spin exponential moment.
  have hb := (FiniteLaw.uniform : FiniteLaw Spin).logMean_stability (show (0:ℝ)<1 by norm_num)
    (g := fun _ => 0) (fun ε => by simpa only [sub_zero] using hh ε)
  simp only [FiniteLaw.logMean_const _ (one_ne_zero), sub_zero] at hb
  simpa only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
    FiniteLaw.uniform,Fintype.card_bool,← Finset.mul_sum,inv_mul_eq_div,Nat.cast_ofNat,← Finset.sum_div] using hb

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PerturbedEnergyMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ} [NeZero N]

lemma integrable_indexedPotential
    (μ : Measure X) [IsProbabilityMeasure μ] (theta : X → InteractionSample p)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ))
    {C : ℝ} (hC : 0≤C) (hθ : ∀ x σ,|(theta x).1 σ|≤C) :
    Integrable id (Measure.map (indexedPotential (N := N) theta) (μ.prod (finiteUniform (Fin p → Fin N)))) := by
  apply (integrable_map_measure measurable_id.aestronglyMeasurable (measurable_indexedPotential theta hθm).aemeasurable).mpr
  apply (integrable_const C).mono' (measurable_indexedPotential theta hθm).aestronglyMeasurable
  exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs, indexedPotential, id_eq] using hθ z.1 (fun l => σ (z.2 l))))

end DilutedSpinGlass.SizeCoupling

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedEnergyRoot
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory Filter
open scoped BigOperators Topology

namespace UniversalDictionary
open ConcreteReservoir

lemma reservoirInsertionOn_bound {ι : Type} [Fintype ι] {p : ℕ}
    (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ)
    {D : ℝ} (hF : ∀ s,|F s|≤D) : |reservoirInsertionOn M C H N L u F|≤D :=
  reservoirInsertion_bound M C H N L u (Fintype.card ι) _ (fun _ => hF _)

end UniversalDictionary
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace Y] [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma energyRoot_bound (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a E|≤‖E‖+H*N+D*a.1 := by
  apply root_uniform_bound _ Q m hm _ _ factor _ hf
  intro y
  apply (abs_add_le _ _).trans
  apply add_le_add
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul,abs_spin,mul_one]; exact hh _)
      _ = H*N := by simp [mul_comm]

lemma measurable_energyRoot (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ) (field : Y → ℝ) (hh : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ) :
    Measurable (fun z : ((RootPath Y N) × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2) := by
  apply measurable_prodSigma (f := fun (z : (RootPath Y N) × ((Fin N → Spin) → ℝ)) n a => energyRoot Q m field factor z.1 ⟨n,a⟩ z.2)
  intro k
  apply measurable_from_prod_countable_left
  intro a
  apply measurable_root _ Q m _ (rootArray k a) (fun _ => factor) _ (fun _ _ _ => measurable_const)
  intro y
  exact ((measurable_pi_apply _).comp measurable_snd).add
    (Finset.measurable_sum _ (fun i _ => (hh.comp ((measurable_rootArray N i).comp measurable_fst)).mul_const _))

omit [MeasurableSpace Y] in
lemma integrable_energyRoot_marks (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    Integrable (fun a => energyRoot Q m field factor h a E) (compoundRootLaw ν s) := by
  have hc : Integrable (fun a : Sigma (RootPath I) => (a.1:ℝ)) (compoundRootLaw ν s) :=
    familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s
  have hmeas : Measurable (fun a : Sigma (RootPath I) => energyRoot Q m field factor h a E) :=
    measurable_sigmaUncurry (f := fun n a => energyRoot Q m field factor h ⟨n,a⟩ E) (fun n => measurable_of_countable _)
  apply ((integrable_const (‖E‖+H*N)).add (hc.const_mul D)).mono' hmeas.aestronglyMeasurable
  exact ae_of_all _ (fun a => by simpa only [Real.norm_eq_abs,Pi.add_apply] using energyRoot_bound Q m hm field factor hh hf h a E)

omit [MeasurableSpace Y] in
lemma energyRoot_marks_bound (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (h : RootPath Y N) (E : (Fin N → Spin) → ℝ) :
    |∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s|≤‖E‖+H*N+D*s := by
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E).abs
    ((integrable_const (‖E‖+H*N)).add ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D))
    (fun a => energyRoot_bound Q m hm field factor hh hf h a E)).trans_eq
  simp only [Pi.add_apply]
  change (∫ a : Sigma (RootPath I), (‖E‖+H*N)+D*a.1 ∂familyLaw (poissonMeasure s) (fun n => rootLaw n (fun _ => ν))) = _
  rw [integral_add (integrable_const _) ((familyPoisson_count_integrable (fun n => rootLaw n (fun _ => ν)) s).const_mul D),
    integral_const_mul,familyPoisson_count_mean]
  simp

lemma averagedEnergyRoot_lipschitz (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (hhm : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D) :
    LipschitzWith 1 (averagedEnergyRoot ξ ν s Q m field factor) := by
  have hmi E : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hhm factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hi E : Integrable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) (rootLaw N (fun _ => ξ)) :=
    bounded_memLp (hmi E) (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E) 1 |>.integrable le_rfl
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,averagedEnergyRoot]
  rw [← integral_sub (hi E) (hi F)]
  apply abs_integral_le_bound
  intro h
  rw [← integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h F)]
  apply abs_integral_le_bound
  intro a
  simpa only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul E F

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory KernelTower PhysicalRoot ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i,Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma rootInsertion_eq_difference (T : KernelTower Ω (L+1))
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin) (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M) (i : Fin a → Site N) :
    rootInsertion T Q m base old V a F (z,i) =
      root T Q m (fun y => base z.1 z.2.1.1 z.2.1.2 y+F (fun j => V y (i j)))
        (rootArray z.2.2.1 z.2.2.2) old -
      root T Q m (base z.1 z.2.1.1 z.2.1.2) (rootArray z.2.2.1 z.2.2.2) old := by
  exact (root_energy_insertion T Q m (base z.1 z.2.1.1 z.2.1.2)
    (fun y => F (fun j => V y (i j))) _ old).symm

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityTrialIdentity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k p l L : ℕ}

lemma terminalRoot_cavity_marginal
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (roots : Fin l → I) (ψ : (i : I) → (Fin N → Spin) → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform Q m
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) roots
      (fun i σ z => ψ i (fun v => σ v.succ) z) =
    terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform Q m
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) roots ψ := by
  have he : (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
      (fun σ => E (fun i => σ i.succ)+(h*spin (σ 0)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))) := by
    funext σ; ring
  rw [he,terminalRoot_spin_marginal Q m hm]
  congr 1
  funext σ
  congr 1
  simp only [Fin.cons_succ,Fin.cons_zero]
  simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.uniform_expect,
    Fintype.card_bool,Nat.cast_ofNat,cavitySiteEnergy]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_InsertionPoissonAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_bound (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : |∫ k,f k ∂poissonMeasure ρ|≤B+D*ρ := by
  have hg : Integrable (fun k : ℕ => B+D*k) (poissonMeasure ρ) :=
    (integrable_const _).add ((poisson_integrable_count ρ).const_mul D)
  have hh := norm_integral_le_of_norm_le (f := f) hg (ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs] using h k))
  simpa only [Real.norm_eq_abs,integral_add (integrable_const _) ((poisson_integrable_count ρ).const_mul D),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,poisson_mean] using hh

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_MarkMeanProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N J k L : ℕ}

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (a : RootPath (I×Fin J) k) :
    |locatedTerminalRoot Q m ψ site E a|≤‖E‖+D*k := by
  unfold locatedTerminalRoot terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m hm _ (rootArray k a) _ (B := ‖E‖) (C := D)
      (hf := fun i _ b => hf i.1 _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_pullback
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ) (a : RootPath (I×Fin J) k) :
    locatedTerminalRoot Q m ψ site E a =
      terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
        (fun j : Fin k => Q (rootArray k a j).1) m E id
        (fun j σ b => ψ (rootArray k a j).1 (σ (site (rootArray k a j).2)) b) := by
  unfold locatedTerminalRoot terminalRoot
  exact (root_pullback (fun j : Fin k => rootArray k a j) id
    (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m _ _).symm

lemma integral_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
      ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))=
      ∫ a : Fin k → I,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b))
        ∂Measure.pi (fun _ : Fin k => ν) := by
  simp_rw [locatedTerminalRoot_pullback]
  have he : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin J)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [he]
  apply integral_root_prod_finite ν k
    (fun z : (Fin k → I) × (Fin k → Fin J) => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
      (fun j : Fin k => Q (z.1 j)) m E id (fun j σ b => ψ (z.1 j) (σ (site (z.2 j))) b))
    (measurable_of_countable _) (B := ‖E‖+D*k)
  intro z
  unfold terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun j : Fin k => Q (z.1 j)) m hm _ id _ (B := ‖E‖) (C := D)
      (hf := fun j y b => hf (z.1 j) _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

lemma terminalMean_count_integral [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    terminalMean ν s Q m ψ site E =
      ∫ k,∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))) ∂poissonMeasure s := by
  apply integral_familyLaw (poissonMeasure s) (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

/-- The original Poisson marked system may move mark sites off the added
spin at cost exactly twice the mark amplitude times its expected new-site count. -/
lemma terminalMean_mark_projection [NeZero N]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin (N+1) → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ (id : Fin (N+1) → Fin (N+1)) E-
      terminalMean ν s Q m ψ (Fin.succ : Fin N → Fin (N+1)) E|≤2*D*s/(N+1) := by
  have hx (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) (k : ℕ) :
      Integrable (fun a : Fin k → I =>
        (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b)))
        (Measure.pi (fun _ : Fin k => ν)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (‖E‖+D*k)
    apply ae_of_all
    intro a
    simp only [Real.norm_eq_abs]
    apply FiniteLaw.abs_expect_le
    intro sites
    unfold terminalRoot
    apply root_uniform_bound (terminalTower (fun _ : Fin (N+1) => false) FiniteLaw.uniform L)
      (fun j : Fin k => Q (a j)) m hm _ id _ (B := ‖E‖) (C := D)
        (hf := fun j y b => hf (a j) _ b)
    intro y
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  have hi (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) :
      Integrable (fun k => ∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J)))) (poissonMeasure s) := by
    apply poisson_average_integrable s _
    intro k
    exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
  rw [terminalMean_count_integral ν s Q m hm ψ id E hf,
    terminalMean_count_integral ν s Q m hm ψ Fin.succ E hf,← integral_sub (hi (N+1) id) (hi N Fin.succ)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,2*D*k/(N+1) ∂poissonMeasure s := by
      apply integral_mono ((hi (N+1) id).sub (hi N Fin.succ)).abs
        ((((poisson_integrable_count s).const_mul (2*D)).div_const (N+1)))
      intro k
      simp only [Pi.sub_apply]
      rw [integral_locatedTerminalRoot ν Q m hm ψ id E hf,
        integral_locatedTerminalRoot ν Q m hm ψ Fin.succ E hf,← integral_sub (hx (N+1) id k) (hx N Fin.succ k)]
      exact abs_integral_le_bound (fun a => terminalRoot_mark_site_expect Q m hm E a ψ hf)
    _ = _ := by rw [integral_div,integral_const_mul,poisson_mean]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanCavity
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

omit [Countable I] [MeasurableSingletonClass I] in
lemma terminalMean_cavity_marginal [NeZero N]
    (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : m (Fin.last L)=1) (E : (Fin N → Spin) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (θ : Fin k → InteractionSample p) (h : ℝ) (j : Fin k × Fin (p-1) → Fin N) :
    terminalMean ν s Q m ψ Fin.succ
      (fun σ => E (fun i => σ i.succ)+h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) =
    terminalMean ν s Q m ψ id
      (fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a))) := by
  unfold terminalMean
  apply integral_congr_ae
  filter_upwards [] with a
  exact terminalRoot_cavity_marginal (fun i : I×Fin N => Q i.1) m hm E
    (rootArray a.1 a.2) (fun i σ b => ψ i.1 (σ i.2) b) θ h j

omit [Countable I] [MeasurableSingletonClass I] in
lemma averagedEnergyRoot_eq_terminalMean [NeZero N]
    (ξ : Measure Y) (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1)
      m field (locatedFactor ψ) E =
      ∫ h,terminalMean ν s Q m ψ id
        (fun σ => E σ+∑ i,field (rootArray N h i)*spin (σ i)) ∂rootLaw N (fun _ => ξ) := rfl

lemma integrable_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun a : Sigma (RootPath (I×Fin J)) => locatedTerminalRoot Q m ψ site E a.2)
      (compoundRootLaw (ν.prod (finiteUniform (Fin J))) s) := by
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

lemma terminalMean_bound [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ site E|≤‖E‖+D*s := by
  rw [terminalMean_count_integral ν s Q m hm ψ site E hf]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,‖E‖+D*k ∂poissonMeasure s := by
      apply integral_mono
      · exact (poisson_average_integrable s _
          (fun k => abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a))).abs
      · exact (integrable_const _).add ((poisson_integrable_count s).const_mul D)
      · intro k
        exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
    _ = _ := by
      rw [integral_add (integrable_const _) ((poisson_integrable_count s).const_mul D),
        integral_const_mul,poisson_mean]
      simp

lemma terminalMean_lipschitz [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    LipschitzWith 1 (terminalMean ν s Q m ψ site) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,terminalMean]
  rw [← integral_sub (integrable_locatedTerminalRoot ν s Q m hm ψ site E hf)
    (integrable_locatedTerminalRoot ν s Q m hm ψ site F hf)]
  apply abs_integral_le_bound
  intro a
  apply root_base_stability _ (fun i : I×Fin J => Q i.1) m hm
  intro y
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (E-F) (terminalState L y)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_TerminalMeanField
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N J k p L : ℕ}

lemma measurable_fieldEnergy (field : Y → ℝ) (hh : Measurable field) :
    Measurable (fieldEnergy (N := N) field) := by
  apply Measurable.of_eval
  intro σ
  exact Finset.measurable_sum _ (fun i _ => (hh.comp (measurable_rootArray N i)).mul_const _)

omit [MeasurableSpace Y] in
lemma fieldEnergy_bound (field : Y → ℝ) {H : ℝ} (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) (σ : Fin N → Spin) : |fieldEnergy field h σ|≤H*N := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin N,H := Finset.sum_le_sum (fun _ _ => by
      rw [abs_mul,abs_spin,mul_one]; exact hh _)
    _ = _ := by simp [mul_comm]

omit [MeasurableSpace Y] in
lemma fieldEnergy_norm (field : Y → ℝ) {H : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (h : RootPath Y N) : ‖fieldEnergy field h‖≤H*N := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hH (Nat.cast_nonneg N))).mpr
  intro σ
  simpa only [Real.norm_eq_abs] using fieldEnergy_bound field hh h σ

omit [MeasurableSpace Y] in
lemma fieldEnergy_cons (field : Y → ℝ) (h : Y×RootPath Y N) (σ : Fin (N+1) → Spin) :
    fieldEnergy field h σ=field h.1*spin (σ 0)+fieldEnergy field h.2 (fun i => σ i.succ) := by
  simp [fieldEnergy,Fin.sum_univ_succ,rootArray]

lemma terminalMean_field_integrable [NeZero J]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    Integrable (fun h => terminalMean ν s Q m ψ site (E+fieldEnergy field h)) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound
    ((terminalMean_lipschitz ν s Q m hm ψ site hf).continuous.measurable.comp
      (measurable_const.add (measurable_fieldEnergy field hhm))).aestronglyMeasurable
    (‖E‖+H*N+D*s)
  filter_upwards [] with h
  change |terminalMean ν s Q m ψ site (E+fieldEnergy field h)|≤_
  calc
    _ ≤ ‖E+fieldEnergy field h‖+D*s := terminalMean_bound ν s Q m hm ψ site _ hf
    _ ≤ (‖E‖+‖fieldEnergy field h‖)+D*s := by have := norm_add_le E (fieldEnergy field h); linarith
    _ ≤ _ := by have := fieldEnergy_norm field hH hh h; linarith

lemma averagedEnergyRoot_mark_projection [NeZero N]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin (N+1) → Spin) → ℝ)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s (fun i : I×Fin (N+1) => Q i.1)
      m field (locatedFactor ψ) E-
      (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤
        2*D*s/(N+1) := by
  let : IsProbabilityMeasure (rootLaw (N+1) (fun _ => ξ)) := rootLawProbability _ _
  rw [averagedEnergyRoot_eq_terminalMean]
  change |(∫ h,terminalMean ν s Q m ψ id (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))-
    (∫ h,terminalMean ν s Q m ψ Fin.succ (E+fieldEnergy field h) ∂rootLaw (N+1) (fun _ => ξ))|≤_
  rw [← integral_sub (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm id E hH hh hf)
    (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ E hH hh hf)]
  exact abs_integral_le_bound (fun _ => terminalMean_mark_projection ν s Q m hm ψ _ hf)

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalNewSpin
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I Y : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    [MeasurableSpace Y] {A : I → Type} [∀ i,Fintype (A i)] {N k p L : ℕ} [NeZero N]

lemma newSpin_field_marginal
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ h,terminalMean ν s Q m ψ Fin.succ
      ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
          ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field h)
        ∂rootLaw (N+1) (fun _ => ξ)) =
      ∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ := by
  rw [show rootLaw (N+1) (fun _ => ξ)=ξ.prod (rootLaw N (fun _ => ξ)) from rfl]
  rw [integral_prod _ (terminalMean_field_integrable ξ ν s Q m hm ψ field hhm Fin.succ _ hH hh hf)]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [averagedEnergyRoot_eq_terminalMean]
  apply integral_congr_ae
  filter_upwards [] with h'
  have he : ((fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
      ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0)))+fieldEnergy field (h,h')) =
      (fun σ => (E+fieldEnergy field h') (fun i => σ i.succ)+field h*spin (σ 0)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) := by
    funext σ
    simp only [Pi.add_apply,fieldEnergy_cons]
    ring
  rw [he,terminalMean_cavity_marginal ν s Q m hend]
  congr 1
  funext σ
  change (E σ+fieldEnergy field h' σ)+_=(E σ+_)+fieldEnergy field h' σ
  ring

/-- Removing marks on the new site and then summing out that spin gives the
actual cavity-site root, with precisely the O(s/N) projection error. -/
lemma averagedEnergyRoot_newSpin
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (field : Y → ℝ) (hhm : Measurable field) (E : (Fin N → Spin) → ℝ)
    (θ : Fin k → InteractionSample p) (j : Fin k × Fin (p-1) → Fin N)
    {H D : ℝ} (hH : 0≤H) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
      (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
      (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ)+
        ∑ a,(θ a).1 (appendSpin (fun b => σ (j (a,b)).succ) (σ 0))) -
      (∫ h,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)
        (fun σ => E σ+cavitySiteEnergy θ (field h) (fun a => σ (j a))) ∂ξ)|≤2*D*s/(N+1) := by
  rw [← newSpin_field_marginal ξ ν s Q m hm hend ψ field hhm E θ j hH hh hf]
  exact averagedEnergyRoot_mark_projection ξ ν s Q m hm ψ field hhm _ hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_AveragedRootBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {Y I : Type} [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma averagedEnergyRoot_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (field : Y → ℝ) (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |averagedEnergyRoot ξ ν s Q m field factor E|≤‖E‖+H*N+D*s := by
  have := rootLawProbability N (fun _ => ξ)
  exact abs_integral_le_bound (fun h => energyRoot_marks_bound ν s Q m hm field factor hh hf h E)

lemma cavitySiteEnergy_norm_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (j : Fin k×Fin (p-1) → Fin N) (E : (Fin N → Spin) → ℝ)
    {C H : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ a,‖(θ a).1‖≤C) (hh : |h|≤H) :
    ‖(fun σ => E σ+cavitySiteEnergy θ h (fun a => σ (j a)))‖≤‖E‖+H+C*k := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro σ
  rw [Real.norm_eq_abs]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ ‖E‖+(|h|+∑ a,‖(θ a).1‖) := add_le_add (norm_le_pi_norm E σ) (cavitySiteEnergy_bound θ h _)
    _ ≤ ‖E‖+(H+∑ _a : Fin k,C) := add_le_add_right (add_le_add hh (Finset.sum_le_sum (fun a _ => hθ a))) _
    _ = _ := by simp [mul_comm,add_assoc]

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySeparable
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N k p : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_cavityArrayEnergy (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (E : (Fin N → Spin) → ℝ) (j : Fin k → Fin (p-1) → Fin N) :
    Measurable (cavityArrayEnergy theta field E j) := by
  apply Measurable.of_eval
  intro σ
  unfold cavityArrayEnergy cavitySiteEnergy
  apply measurable_const.add
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp ((measurable_pi_apply a).comp measurable_fst))

lemma measurable_cavityArrayValue (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (E : (Fin N → Spin) → ℝ) :
    Measurable (cavityArrayValue (k := k) ξ theta field F E) := by
  apply FiniteLaw.measurable_expect
  intro j
  exact (hF.measurable.comp (measurable_cavityArrayEnergy theta field hθ hh E j)).stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
lemma cavityArrayValue_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hθ : ∀ x,‖(theta x).1‖ ≤ C) (hh : ∀ y,|field y| ≤ H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ v,|F v| ≤ ‖v‖+B)
    (E : (Fin N → Spin) → ℝ) (z : Fin k → X) :
    |cavityArrayValue ξ theta field F E z| ≤ ‖E‖+H+C*k+B := by
  apply FiniteLaw.abs_expect_le
  intro j
  apply abs_integral_le_bound
  intro h
  apply (hF _).trans
  apply add_le_add _ le_rfl
  exact PhysicalRoot.cavitySiteEnergy_norm_bound (fun a => theta (z a)) (field h)
    (fun a => j a.1 a.2) E hH hC (fun _ => hθ _) (hh h)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundSample
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]

lemma measurable_compound_sample (V : X → E) (hV : Measurable V) :
    Measurable (fun z : Sigma (RootPath X) => ∑ i,V (rootArray z.1 z.2 i)) := by
  apply measurable_sigmaUncurry (f := fun n z => ∑ i,V (rootArray n z i))
  intro n
  apply Finset.measurable_sum
  intro i _
  exact hV.comp (measurable_rootArray n i)

lemma compound_sample_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    Integrable (fun z : Sigma (RootPath X) => F (∑ i,V (rootArray z.1 z.2 i)))
      (compoundRootLaw μ r) := by
  have : IsProbabilityMeasure (Measure.map V μ) :=
    (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr inferInstance
  have hiV : Integrable id (Measure.map V μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hV.aemeasurable).mpr hVi
  have hi := integrable_lipschitz_of_id (compoundPoisson r (Measure.map V μ))
    (compoundPoisson_integrable_id r _ hiV) hF
  rw [← map_compoundRoot_energy μ V hV r] at hi
  exact (integrable_map_measure hF.continuous.aestronglyMeasurable
    (measurable_compound_sample V hV).aemeasurable).mp hi

lemma integral_compound_sample (μ : Measure X) [IsProbabilityMeasure μ]
    (V : X → E) (hV : Measurable V) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) (hVi : Integrable V μ) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V μ))=
      ∫ k,∫ z : RootPath X k,F (∑ i,V (rootArray k z i)) ∂rootLaw k (fun _ => μ) ∂poissonMeasure r := by
  rw [← map_compoundRoot_energy μ V hV r,
    integral_map (measurable_compound_sample V hV).aemeasurable hF.continuous.aestronglyMeasurable]
  exact integral_familyLaw (poissonMeasure r) (fun k => rootLaw k (fun _ => μ))
    (fun k z => F (∑ i,V (rootArray k z i)))
    (fun k => by
      apply hF.continuous.measurable.comp
      apply Finset.measurable_sum
      intro i _
      exact hV.comp (measurable_rootArray k i))
    (compound_sample_integrable μ V hV r hF hVi)

lemma integral_compound_finite_sample {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (V : X×J → E) (hV : Measurable V)
    {C : ℝ} (hVb : ∀ x,‖V x‖≤C) (r : ℝ≥0) {c : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith c F) :
    (∫ E,F E ∂compoundPoisson r (Measure.map V (μ.prod (finiteUniform J))))=
      ∫ k,∫ z : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → J)).expect
        (fun j => F (∑ i,V (z i,j i))) ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r := by
  rw [integral_compound_sample (μ.prod (finiteUniform J)) V hV r hF
    (Integrable.of_bound hV.aestronglyMeasurable C (ae_of_all _ hVb))]
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_root_prod_finite μ k (fun z => F (∑ i,V (z.1 i,z.2 i)))
  · apply hF.continuous.measurable.comp
    exact Finset.measurable_sum _ (fun i _ => hV.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)))
  · intro z
    have hn : ‖∑ i : Fin k,V (z.1 i,z.2 i)‖ ≤ C*k := by
      calc
        _ ≤ ∑ i : Fin k,‖V (z.1 i,z.2 i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin k,C := Finset.sum_le_sum (fun _ _ => hVb _)
        _ = _ := by simp [mul_comm]
    have hh := hF.dist_le_mul (∑ i,V (z.1 i,z.2 i)) 0
    simp only [dist_eq_norm,sub_zero,Real.norm_eq_abs] at hh
    calc
      _ = |F (∑ i,V (z.1 i,z.2 i))-F 0+F 0| := by rw [sub_add_cancel]
      _ ≤ |F (∑ i,V (z.1 i,z.2 i))-F 0|+|F 0| := abs_add_le _ _
      _ ≤ (c:ℝ)*(C*k)+|F 0| := add_le_add (hh.trans
        (mul_le_mul_of_nonneg_left hn c.coe_nonneg)) le_rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_EnergyInsertionMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma integrable_energyRoot_field_mean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    Integrable (fun h => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s)
      (rootLaw N (fun _ => ξ)) := by
  have hmi : Measurable (fun h : RootPath Y N => ∫ a,energyRoot Q m field factor h a E ∂compoundRootLaw ν s) := by
    exact ((measurable_energyRoot Q m field hfield factor).comp
      ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  exact Integrable.of_bound hmi.aestronglyMeasurable (‖E‖+H*N+D*s)
    (ae_of_all _ (fun h => by simpa only [Real.norm_eq_abs] using energyRoot_marks_bound ν s Q m hm field factor hh hf h E))

lemma averagedEnergyRoot_increment (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (E J : (Fin N → Spin) → ℝ) :
    averagedEnergyRoot ξ ν s Q m field factor (E+J)-averagedEnergyRoot ξ ν s Q m field factor E=
      ∫ h,∫ a,energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E
        ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
  unfold averagedEnergyRoot
  rw [← integral_sub (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf (E+J))
    (integrable_energyRoot_field_mean ξ ν s Q m hm field hfield factor hh hf E)]
  apply integral_congr_ae
  filter_upwards [] with h
  exact (integral_sub (integrable_energyRoot_marks ν s Q m hm field factor hh hf h (E+J))
    (integrable_energyRoot_marks ν s Q m hm field factor hh hf h E)).symm

omit [MeasurableSpace Y] [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma energyRoot_increment_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (a : Sigma (RootPath I)) (E J : (Fin N → Spin) → ℝ) :
    |energyRoot Q m field factor h a (E+J)-energyRoot Q m field factor h a E|≤‖J‖ := by
  simpa only [dist_eq_norm,Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul] using
    (energyRoot_lipschitz Q m hm field factor h a).dist_le_mul (E+J) E

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_OneNewLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
variable {X : Type} [MeasurableSpace X] {q N : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_newPotential (theta : X → InteractionSample (q+1))
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (newPotential (N := N) theta) := by
  apply measurable_from_prod_countable_left
  intro i
  exact Measurable.of_eval (fun σ => by
    change Measurable (fun c => (theta c).1 (appendSpin (fun b => σ (i b).succ) (σ 0)))
    exact hθ _)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

lemma measurable_reorder_increment {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Add γ] [MeasurableAdd₂ γ]
    (F : (α × γ) × β → ℝ) (hF : Measurable F) (J : γ) :
    Measurable (fun z : (α × β) × γ => F ((z.1.1,z.2+J),z.1.2)-F ((z.1.1,z.2),z.1.2)) := by
  exact (hF.comp ((measurable_fst.fst.prodMk (measurable_snd.add_const J)).prodMk measurable_fst.snd)).sub
    (hF.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))

lemma measurable_energyRoot_increment
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (J : (Fin N → Spin) → ℝ) :
    Measurable (fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
      energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2) :=
  measurable_reorder_increment
    (fun z : (RootPath Y N × ((Fin N → Spin) → ℝ)) × Sigma (RootPath I) =>
      energyRoot Q m field factor z.1.1 z.2 z.1.2)
    (measurable_energyRoot Q m field hfield factor) J

lemma fullRoot_energy_increment
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (J : (Fin N → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      energyRoot Q m field factor z.1 z.2.2 ((∑ i,V (rootArray z.2.1.1 z.2.1.2 i))+J)-
        energyRoot Q m field factor z.1 z.2.2 (∑ i,V (rootArray z.2.1.1 z.2.1.2 i))
       ∂fullRootLaw (fun _ => ξ) μ ν r s) =
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+J)-
        averagedEnergyRoot ξ ν s Q m field factor E ∂compoundPoisson r (Measure.map V μ) := by
  let κ := compoundPoisson r (Measure.map V μ)
  let : IsProbabilityMeasure (Measure.map V μ) := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  let G := fun z : (RootPath Y N × Sigma (RootPath I)) × ((Fin N → Spin) → ℝ) =>
    energyRoot Q m field factor z.1.1 z.1.2 (z.2+J)-energyRoot Q m field factor z.1.1 z.1.2 z.2
  have hmG : Measurable G := measurable_energyRoot_increment Q m field hfield factor J
  have hbG (z) : |G z|≤‖J‖ := energyRoot_increment_bound Q m hm field factor z.1.1 z.1.2 z.2 J
  have hiG : Integrable G (((rootLaw N (fun _ => ξ)).prod (compoundRootLaw ν s)).prod κ) :=
    Integrable.of_bound hmG.aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hbG z))
  let F := fun (h : RootPath Y N) (k : ℕ) (x : RootPath X k) (n : ℕ) (a : RootPath I n) =>
    G ((h,⟨n,a⟩),∑ i,V (rootArray k x i))
  have hFm k n : Measurable (fun z : (RootPath Y N × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply hmG.comp
    apply Measurable.prodMk
    · exact measurable_fst.fst.prodMk ((measurable_sigmaMk (i := n)).comp measurable_snd)
    · exact Finset.measurable_sum _ (fun i _ => hV.comp ((measurable_rootArray k i).comp measurable_fst.snd))
  have he : (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=
      ∫ h,∫ a,∫ E,G ((h,a),E) ∂κ ∂compoundRootLaw ν s ∂rootLaw N (fun _ => ξ) := by
    rw [integral_fullRootLaw_reordered (fun _ => ξ) μ ν r s hFm
      (B := ‖J‖) (C := 0) (D := 0) (fun h k x n a => by simpa only [zero_mul,add_zero] using hbG ((h,⟨n,a⟩),∑ i,V (rootArray k x i)))]
    apply integral_congr_ae
    filter_upwards [] with h
    apply integral_congr_ae
    filter_upwards [] with a
    dsimp only [F,κ]
    rw [← map_compoundRoot_energy μ V hV r]
    have hma : Measurable (fun E : (Fin N → Spin) → ℝ => G ((h,a),E)) :=
      hmG.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (measurable_compound_sample V hV).aemeasurable hma.aestronglyMeasurable]
  change (∫ z,packRoot F z ∂fullRootLaw (fun _ => ξ) μ ν r s)=_
  rw [he,← integral_prod _ hiG.integral_prod_left,integral_integral_swap hiG]
  apply integral_congr_ae
  filter_upwards [hiG.prod_left_ae] with E hE
  rw [integral_prod _ hE,← averagedEnergyRoot_increment ξ ν s Q m hm field hfield factor hh hf E J]

end DilutedSpinGlass.PhysicalRoot

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    {N p k : ℕ} [NeZero N]

lemma measurable_cavityArrayValue_joint (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) :
    Measurable (fun z : ((Fin N → Spin) → ℝ)×(Fin k → X) =>
      cavityArrayValue ξ theta field F z.1 z.2) := by
  apply FiniteLaw.measurable_expect
  intro j
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    F (cavityArrayEnergy theta field z.1.1 j (z.1.2,z.2)))
  apply Measurable.stronglyMeasurable
  apply hF.measurable.comp
  apply Measurable.of_eval
  intro σ
  change Measurable (fun z : (((Fin N → Spin) → ℝ)×(Fin k → X))×Y =>
    z.1.1 σ+cavitySiteEnergy (fun a => theta (z.1.2 a)) (field z.2) (fun a => σ (j a.1 a.2)))
  apply ((measurable_pi_apply σ).comp (measurable_fst.comp measurable_fst)).add
  unfold cavitySiteEnergy
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro ε _
  apply Measurable.exp
  apply ((hh.comp measurable_snd).mul_const _).add
  exact Finset.measurable_sum _ (fun a _ => (hθ _).comp
    ((measurable_pi_apply a).comp (measurable_snd.comp measurable_fst)))

lemma measurable_cavityPoissonValue (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [SFinite ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (r : ℝ≥0) :
    Measurable (cavityPoissonValue μ ξ theta field F r) := by
  unfold cavityPoissonValue
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun z : ((Fin N → Spin) → ℝ)×ℕ =>
    ∫ x : Fin z.2 → X,cavityArrayValue ξ theta field F z.1 x ∂Measure.pi (fun _ : Fin z.2 => μ))
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_left
  intro k
  exact (measurable_cavityArrayValue_joint (k := k) ξ theta field hθ hh hF).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable

lemma cavityPoissonValue_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    {H C B : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) (E : (Fin N → Spin) → ℝ) :
    |cavityPoissonValue μ ξ theta field F r E|≤‖E‖+H+C*r+B := by
  have hb (k : ℕ) : |∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)|≤‖E‖+H+C*k+B :=
    abs_integral_le_bound (fun z => cavityArrayValue_bound ξ theta field hH hC hθ hh hF E z)
  have h := poisson_average_bound r (fun k : ℕ => ∫ z : Fin k → X,
    cavityArrayValue ξ theta field F E z ∂Measure.pi (fun _ : Fin k => μ))
    (B := ‖E‖+H+B) (D := C) (fun k => (hb k).trans_eq (by ring))
  exact h.trans_eq (by ring)

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot HeterogeneousMarks
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_poisson_bridge
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {H C B δ : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} {G : ((Fin (N+1) → Spin) → ℝ) → ℝ}
    (hF : Continuous F) (hFb : ∀ v,|F v|≤‖v‖+B) (hG : LipschitzWith 1 G)
    (E : (Fin N → Spin) → ℝ) (r : ℝ≥0)
    (he : ∀ k (z : Fin k → X) (j : Fin k → Fin q → Fin N),
      |G (fun σ => E (fun i => σ i.succ)+∑ a,(theta (z a)).1
        (appendSpin (fun b => σ (j a b).succ) (σ 0)))-
        ∫ h,F (cavityArrayEnergy theta field E j (z,h)) ∂ξ|≤δ) :
    |(∫ v,G (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤δ := by
  have hGs : LipschitzWith 1 (fun v : (Fin (N+1) → Spin) → ℝ => G (fun σ => E (fun i => σ i.succ)+v σ)) := by
    simpa only [mul_one,Function.comp_def,Pi.add_def] using
      hG.comp (isometry_add_left (fun σ : Fin (N+1) → Spin => E (fun i => σ i.succ))).lipschitz
  have hVb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  rw [integral_compound_finite_sample μ (newPotential theta)
    (measurable_newPotential theta hθm) hVb r hGs]
  let f (k : ℕ) (z : Fin k → X) :=
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin q → Fin N)).expect
      (fun j => G (fun σ => E (fun i => σ i.succ)+∑ a,newPotential theta (z a,j a) σ))
  let g (k : ℕ) (z : Fin k → X) := cavityArrayValue ξ theta field F E z
  have hgm k : Measurable (g k) := measurable_cavityArrayValue ξ theta field hθm hhm hF E
  have hgb k z : |g k z|≤‖E‖+H+C*k+B := cavityArrayValue_bound ξ theta field hH hC hθ hh hFb E z
  have hgi k : Integrable (g k) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable _ (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k z))
  have hfm k : Measurable (f k) := by
    apply FiniteLaw.measurable_expect
    intro j
    apply hG.continuous.measurable.comp
    apply Measurable.of_eval
    intro σ
    change Measurable (fun z : Fin k → X => E (fun i => σ i.succ)+∑ a,(theta (z a)).1 (appendSpin (fun b => σ (j a b).succ) (σ 0)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ => (hθm _).comp (measurable_pi_apply a)))
  have he' k z : |f k z-g k z|≤δ := by
    apply FiniteLaw.abs_expect_sub_le
    intro j
    exact he k z j
  have hb k : |(∫ z,f k z ∂Measure.pi (fun _ : Fin k => μ))-
      ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)|≤δ := by
    have h := integrate_error (Measure.pi (fun _ : Fin k => μ))
      (hfm k).aestronglyMeasurable (hgi k) (integrable_const δ) (ae_of_all _ (he' k))
    simpa using h.2
  have hgI : Integrable (fun k => ∫ z,g k z ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := ‖E‖+H+B) (B := C)
    intro k
    calc
      _ ≤ ‖E‖+H+C*k+B := abs_integral_le_bound (hgb k)
      _ = _ := by ring
  have h := integrate_error (poissonMeasure r) (measurable_of_countable _).aestronglyMeasurable
    hgI (integrable_const δ) (ae_of_all _ hb)
  simpa only [Pi.add_apply,Finset.sum_apply,Real.norm_eq_abs,integral_const,
    Measure.real,measure_univ,ENNReal.toReal_one,one_smul,f,g] using h.2

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalCavityPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_newSpin_poisson
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D)
    (E : (Fin N → Spin) → ℝ) :
    |(∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
        (fun σ => E (fun i => σ i.succ)+v σ)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))))-
      (∫ k,∫ z : Fin k → X,cavityArrayValue ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) E z
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)|≤2*D*s/(N+1) := by
  apply cavity_poisson_bridge μ ξ theta field hθm hhm hH hC hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (fun v => by
      simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
        (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) v)
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)) E r
  intro k z j
  exact averagedEnergyRoot_newSpin ξ ν s Q m hm hend ψ field hhm E
    (fun a => theta (z a)) (fun a => j a.1 a.2) hH hh hf

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma integrable_cavityPoissonValue
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    (r : ℝ≥0) : Integrable (cavityPoissonValue μ ξ θ field F r) ρ := by
  have hb E : |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  exact (hρ.norm.add (integrable_const (H+C*r+B))).mono'
    (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
    (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hb E))

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_UpperRealEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N q : ℕ} [NeZero N]

lemma cavity_old_average_error
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    (θ : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (θ x).1 σ)) (hhm : Measurable field)
    {C H B δ : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ x,‖(θ x).1‖≤C) (hh : ∀ y,|field y|≤H)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : Continuous F) (hFb : ∀ E,|F E|≤‖E‖+B)
    {G : ((Fin (N+1) → Spin) → ℝ) → ℝ} (hG : Continuous G) (r : ℝ≥0)
    (he : ∀ E,|(∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))))-
      cavityPoissonValue μ ξ θ field F r E|≤δ) :
    |(∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r
        (Measure.map (newPotential (N := N) θ) (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ θ field F r E ∂ρ)|≤δ := by
  let : IsProbabilityMeasure (Measure.map (newPotential (N := N) θ)
      (μ.prod (finiteUniform (Fin q → Fin N)))) :=
    Measure.isProbabilityMeasure_map (measurable_newPotential θ hθm).aemeasurable
  have hgb (E : (Fin N → Spin) → ℝ) :
      |cavityPoissonValue μ ξ θ field F r E|≤‖E‖+(H+C*r+B) := by
    simpa only [add_assoc] using cavityPoissonValue_bound μ ξ θ field hH hC hθ hh hFb r E
  have hgi : Integrable (cavityPoissonValue μ ξ θ field F r) ρ :=
    (hρ.norm.add (integrable_const (H+C*r+B))).mono'
      (measurable_cavityPoissonValue μ ξ θ field hθm hhm hF r).aestronglyMeasurable
      (ae_of_all _ (fun E => by simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using hgb E))
  have hfm : AEStronglyMeasurable (fun E => ∫ v,G (liftOldEnergy E+v)
      ∂compoundPoisson r (Measure.map (newPotential (N := N) θ)
        (μ.prod (finiteUniform (Fin q → Fin N))))) ρ := by
    have hc : Continuous (fun z : ((Fin N → Spin) → ℝ)×((Fin (N+1) → Spin) → ℝ) =>
        G (liftOldEnergy z.1+z.2)) := hG.comp
      (((liftOldEnergy (N := N)).continuous.comp continuous_fst).add continuous_snd)
    exact hc.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have h := integrate_error ρ hfm hgi (integrable_const δ) (ae_of_all _ he)
  simpa only [integral_const,probReal_univ,one_smul] using h.2

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavitySiteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory ProbabilityTheory PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

lemma averagedEnergyRoot_old_new_compare
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,∫ v,averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
        (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ) (liftOldEnergy E+v)
        ∂compoundPoisson r (Measure.map (newPotential (N := N) theta)
          (μ.prod (finiteUniform (Fin q → Fin N)))) ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)|≤2*D*s/(N+1) := by
  apply cavity_old_average_error μ ξ ρ hρ theta field hθm hhm hC hH hθ hh
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin N))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous
    (B := H*N+D*s) _
    (averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s _ m hm field hhm
      (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)).continuous r
  · intro E
    simpa only [cavityPoissonValue,liftOldEnergy,ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk,AddHom.coe_mk,Pi.add_def] using
      averagedEnergyRoot_newSpin_poisson μ ξ ν r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf E
  · intro E
    simpa only [add_assoc] using averagedEnergyRoot_bound ξ (ν.prod (finiteUniform (Fin N))) s
      (fun i : I×Fin N => Q i.1) m hm field (locatedFactor ψ) hh (fun i y a => hf i.1 _ a) E

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalInsertionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower ConcreteReservoir
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N L : ℕ}

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I] in
lemma rootInsertion_energyRoot
    (V : X → (Fin N → Spin) → ℝ) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) (z : FullRootState Y X I N) (i : Fin a → Site N) :
    rootInsertion (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
      (fun h k x y => energy V field h k x (terminalState L y)) factor
      (fun y s => readSpin (terminalState L y) s) a F (z,i) =
    energyRoot Q m field factor z.1 z.2.2
      ((∑ j,V (rootArray z.2.1.1 z.2.1.2 j))+(fun σ => F (fun j => readSpin σ (i j))))-
      energyRoot Q m field factor z.1 z.2.2 (∑ j,V (rootArray z.2.1.1 z.2.1.2 j)) := by
  rw [rootInsertion_eq_difference]
  unfold energyRoot
  apply congrArg₂ (fun x y : ℝ => x-y)
  · congr 1
    funext y
    simp only [energy,Pi.add_apply,Finset.sum_apply]
    ring
  · simp only [energy,Finset.sum_apply]

lemma fullRoot_sameInsertion_energy
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (V : X → (Fin N → Spin) → ℝ) (hV : Measurable V)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (field : Y → ℝ) (hfield : Measurable field)
    (factor : (i : I) → FinitePath (Fin N → Spin) (L+1) → FinitePath (A i) (L+1) → ℝ)
    {H D : ℝ} (hh : ∀ y,|field y|≤H) (hf : ∀ i y a,|Real.log (factor i y a)|≤D)
    (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    (∫ z : FullRootState Y X I N,
      sameInsertionAverage (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L) Q m
        (fun h k x y => energy V field h k x (terminalState L y)) factor
        (fun y i => readSpin (terminalState L y) i) a F z
      ∂fullRootLaw (fun _ => ξ) μ ν r s) =
    (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)).expect (fun i =>
      ∫ E,averagedEnergyRoot ξ ν s Q m field factor (E+(fun σ => F (fun j => readSpin σ (i j))))-
        averagedEnergyRoot ξ ν s Q m field factor E
        ∂compoundPoisson r (Measure.map V μ)) := by
  unfold sameInsertionAverage
  rw [FiniteLaw.integral_expect_bounded (FiniteLaw.uniform : FiniteLaw (Fin a → Site N)) (fullRootLaw (fun _ => ξ) μ ν r s) (B := ‖F‖)]
  · apply FiniteLaw.expect_congr
    intro i
    simp only [rootInsertion_energyRoot]
    exact fullRoot_energy_increment ξ μ ν r s V hV Q m hm field hfield factor hh hf _
  · intro i
    exact (measurable_rootInsertion _ Q m _ factor _
      (fun k _ => measurable_energy V field (fun σ => (measurable_pi_apply σ).comp hV) hfield k _) a F).comp
        (measurable_id.prodMk measurable_const)
  · intro z i
    exact backwardLog_bound (L+1) _ m hm (fun _ => norm_le_pi_norm F _)

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirInsertionEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p : ℕ}

lemma reservoirInsertion_energy (M : Model p) (C H : ℝ) (hH : 0≤H) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) {D : ℝ}
    (hf : ∀ i y a,|Real.log (dictionaryFactor (observableAt direction N) (observableAt anchor N) u i y a)|≤D)
    (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Site N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u)
            (E+(fun σ => F (fun j => readSpin σ (i j))))-
          averagedEnergyRoot M.field.toMeasure (markLaw (weights L) N) (scoreRate N)
            (fun i : Labels L (Site N) => prior i.1.1) (gridExponents L) (clipReal H)
            (dictionaryFactor (observableAt direction N) (observableAt anchor N) u) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (boundedPotential C) (bondLaw M N))) := by
  unfold reservoirInsertion reservoirLaw physicalBase physicalSpin
  exact fullRoot_sameInsertion_energy M.field.toMeasure (bondLaw M N) (markLaw (weights L) N)
    (reservoirRate M.alpha (p-1) N) (scoreRate N) (boundedPotential C)
    (Measurable.of_eval (measurable_boundedPotential C)) _ (gridExponents L)
    (gridExponents_pos L) (clipReal H) (measurable_clipReal H) _
    (fun y => clipReal_bound hH y) hf b F

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirSiteTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirInsertion_energy_positive (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (b : ℕ) (F : (Fin b → Spin) → ℝ) :
    reservoirInsertion M C H N L u b F=
      (FiniteLaw.uniform : FiniteLaw (Fin b → Fin N)).expect (fun i =>
        ∫ E,averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u))
            (E+(fun σ => F (fun j => σ (i j))))-
          averagedEnergyRoot M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
            (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (clipReal H)
            (locatedFactor (spinFactor direction anchor u)) E
          ∂compoundPoisson (reservoirRate M.alpha (p-1) N)
            (Measure.map (fun z : InteractionSample p × (Fin p → Fin N) =>
              fun σ => clipReal C (z.1.1 (fun j => σ (z.2 j))))
              (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))) := by
  have he := reservoirInsertion_energy M C H hH N L u (D := 1)
    (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) b F
  rw [he]
  change variableSiteInsertion (N := N) M C H u b F (max N 1)=_
  have hmax : max N 1=N := max_eq_left (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  simp only [hmax]
  unfold variableSiteInsertion
  simp only [Fin.is_lt,↓reduceDIte,Fin.eta]
  rfl

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirInsertionOnEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirInsertionOn_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (F : (ι → Spin) → ℝ) :
    reservoirInsertionOn M C H N L u F=
      (FiniteLaw.uniform : FiniteLaw (ι → Fin N)).expect (fun i =>
        ∫ E,reservoirEnergyRoot M H N L u (E+(fun σ => F (fun j => σ (i j))))-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N) := by
  unfold reservoirInsertionOn
  rw [reservoirInsertion_energy_positive M C H hH]
  let e : (Fin (Fintype.card ι) → Fin N) ≃ (ι → Fin N) :=
    Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl (Fin N))
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityAllocatedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertion_integrable (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    Integrable (fun E => F (E+v)-F E) ρ := by
  apply Integrable.of_bound (hF.continuous.comp (continuous_id.add continuous_const) |>.sub hF.continuous).aestronglyMeasurable ‖v‖
  exact ae_of_all _ (fun E => by simpa using hF.norm_sub_le (E+v) E)

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_lipschitz (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (energyInsertionFunctional ρ F) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs,energyInsertionFunctional]
  rw [← integral_sub (energyInsertion_integrable ρ hF v) (energyInsertion_integrable ρ hF w)]
  apply abs_integral_le_bound
  intro E
  simpa only [sub_sub_sub_cancel_right,add_sub_add_left_eq_sub,NNReal.coe_one,one_mul,
    Real.norm_eq_abs] using hF.norm_sub_le (E+v) (E+w)

omit [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
lemma energyInsertionFunctional_bound (ρ : Measure E) [IsProbabilityMeasure ρ]
    {F : E → ℝ} (hF : LipschitzWith 1 F) (v : E) :
    |energyInsertionFunctional ρ F v|≤‖v‖ := by
  apply abs_integral_le_bound
  intro E
  simpa only [add_sub_cancel_left,NNReal.coe_one,one_mul,Real.norm_eq_abs] using hF.norm_sub_le (E+v) E

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integral_energyInsertionFunctional (ρ μ : Measure E) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure μ] (hμ : Integrable id μ) {F : E → ℝ} (hF : LipschitzWith 1 F) :
    (∫ v,energyInsertionFunctional ρ F v ∂μ)=∫ E,∫ v,F (E+v)-F E ∂μ ∂ρ := by
  unfold energyInsertionFunctional
  apply integral_integral_swap
  apply (hμ.norm.comp_fst ρ).mono'
    ((hF.continuous.comp (continuous_snd.add continuous_fst)).sub
      (hF.continuous.comp continuous_snd)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simpa only [Function.comp_def,id_eq,Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul]
      using hF.norm_sub_le (z.2+z.1) z.2)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityInsertionFunctional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArray_insertionFunctional (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hhm : Measurable field) {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) :
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
      ∫ y,energyInsertionFunctional ρ F
        (fun σ => cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))) ∂ξ)=
      ∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ := by
  let V := fun (j : Fin k → Fin (p-1) → Fin N) (y : Y) (σ : Fin N → Spin) =>
    cavitySiteEnergy (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
  have hVm j : Measurable (V j) := by
    apply Measurable.of_eval
    intro σ
    change Measurable (fun y => cavitySiteEnergy (fun a => theta (z a)) (field y)
      (fun a => σ (j a.1 a.2)))
    unfold cavitySiteEnergy
    apply Measurable.log
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro ε _
    apply Measurable.exp
    exact (hhm.mul_const _).add measurable_const
  have hVb j y : ‖V j y‖≤H+C*k := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro σ
    have hb := cavitySiteEnergy_bound (fun a => theta (z a)) (field y) (fun a => σ (j a.1 a.2))
    have hs : (∑ a : Fin k,‖(theta (z a)).1‖)≤C*k := by
      simpa [mul_comm] using Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin k))) => hz a)
    simpa only [Real.norm_eq_abs] using hb.trans (add_le_add (hh y) hs)
  have hi j : Integrable (fun w : Y×((Fin N → Spin) → ℝ) => F (w.2+V j w.1)-F w.2) (ξ.prod ρ) := by
    apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_snd.add ((hVm j).comp measurable_fst))).sub
      (hF.continuous.measurable.comp measurable_snd)).aestronglyMeasurable (H+C*k)
    exact ae_of_all _ (fun w => by
      simpa only [Real.norm_eq_abs,add_sub_cancel_left,NNReal.coe_one,one_mul,Pi.sub_apply,Pi.add_apply,Function.comp_apply] using
        (hF.norm_sub_le (w.2+V j w.1) w.2).trans (by simpa using hVb j w.1))
  have hj j : (∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=
      ∫ E,∫ y,F (E+V j y)-F E ∂ξ ∂ρ := integral_integral_swap (hi j)
  have hsub E j : (∫ y,F (E+V j y)-F E ∂ξ)=(∫ y,F (E+V j y) ∂ξ)-F E := by
    have he : Integrable (fun y => F (E+V j y)-F E) ξ := by
      apply Integrable.of_bound ((hF.continuous.measurable.comp (measurable_const.add (hVm j))).sub measurable_const).aestronglyMeasurable (H+C*k)
      exact ae_of_all _ (fun y => by simpa using (hF.norm_sub_le (E+V j y) E).trans (by simpa using hVb j y))
    have he' : Integrable (fun y => F (E+V j y)) ξ := by
      exact (he.add (integrable_const (F E))).congr (ae_of_all _ (fun y => by simp))
    rw [integral_sub he' (integrable_const _)]; simp
  change (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect
    (fun j => ∫ y,energyInsertionFunctional ρ F (V j y) ∂ξ)=_
  simp_rw [hj]
  rw [← FiniteLaw.integral_expect _ ρ _ (fun j => (hi j).integral_prod_right)]
  apply integral_congr_ae
  filter_upwards [] with E
  simp only [hsub,FiniteLaw.expect_sub,FiniteLaw.expect_const,cavityArrayValue]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CompoundRateAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] [CompleteSpace V]

omit [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E] in
lemma integral_add_lipschitz [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {F : E → ℝ} (hF : LipschitzWith 1 F) :
    LipschitzWith 1 (fun x => ∫ y,F (x+y) ∂μ) := by
  have hi x : Integrable (fun y => F (x+y)) μ :=
    integrable_lipschitz_of_id μ hμ (by simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left x).lipschitz)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [NNReal.coe_one,one_mul,dist_eq_norm,Real.norm_eq_abs]
  rw [← integral_sub (hi x) (hi z)]
  apply abs_integral_le_bound
  intro y
  simpa only [Real.norm_eq_abs,add_sub_add_right_eq_sub,NNReal.coe_one,one_mul] using hF.norm_sub_le (x+y) (z+y)

omit [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V] in
lemma integrated_compound_rate_bound [NormedSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (ρ : Measure V) [IsProbabilityMeasure ρ] (hρ : Integrable id ρ)
    {e : V → E} (he : LipschitzWith 1 e) {F : E → ℝ} (hF : LipschitzWith 1 F)
    (r s : ℝ≥0) :
    |(∫ x,∫ y,F (e x+y) ∂compoundPoisson r μ ∂ρ)-
      (∫ x,∫ y,F (e x+y) ∂compoundPoisson s μ ∂ρ)|≤
        |(r:ℝ)-s| * (∫ y,‖y‖ ∂μ) := by
  have hl t : LipschitzWith 1 (fun x => ∫ y,F (e x+y) ∂compoundPoisson t μ) := by
    simpa only [one_mul,Function.comp_def] using
      (integral_add_lipschitz (compoundPoisson t μ) (compoundPoisson_integrable_id t μ hμ) hF).comp he
  rw [← integral_sub (integrable_lipschitz_of_id ρ hρ (hl r)) (integrable_lipschitz_of_id ρ hρ (hl s))]
  apply abs_integral_le_bound
  intro x
  have hx : LipschitzWith 1 (fun y => F (e x+y)) := by
    simpa only [mul_one, Function.comp_def] using hF.comp (isometry_add_left (e x)).lipschitz
  simpa only [NNReal.coe_one,one_mul] using compoundPoisson_rate_bound r s μ hμ hx

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalCavityRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p k : ℕ} [NeZero N]

omit [MeasurableSpace X] in
lemma cavityArrayValue_shift [MeasurableSpace X] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hh : ∀ y,|field y|≤H)
    (z : Fin k → X) (hz : ∀ a,‖(theta (z a)).1‖≤C) (E : (Fin N → Spin) → ℝ) :
    cavityArrayValue ξ theta field (fun v => F (E+v)-F E) 0 z=
      cavityArrayValue ξ theta field F E z-F E := by
  have h := cavityArray_insertionFunctional (Measure.dirac E) ξ theta field hhm hF hH hC hh z hz
  have he v : energyInsertionFunctional (Measure.dirac E) F v=F (E+v)-F E := by
    unfold energyInsertionFunctional
    rw [integral_dirac]
  simp only [integral_dirac,he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold cavityArrayValue cavityArrayEnergy
  congr 1
  ext j
  congr 1
  ext y
  congr 2
  ext σ
  simp

lemma cavityArrayValue_gap_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (z : Fin k → X) (E : (Fin N → Spin) → ℝ) :
    |cavityArrayValue ξ theta field F E z-F E|≤H+C*k := by
  rw [← cavityArrayValue_shift ξ theta field hhm hF hH hC hh z (fun a => hθ _) E]
  have hb : ∀ v,|F (E+v)-F E|≤‖v‖+0 := fun v => by
    simpa using hF.norm_sub_le (E+v) E
  simpa using cavityArrayValue_bound ξ theta field hH hC hθ hh hb 0 z

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot SizeCoupling
open scoped NNReal BigOperators
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N q L : ℕ} [NeZero N]

omit [NeZero N] in
lemma liftOldEnergy_lipschitz [NeZero N] : LipschitzWith 1 (liftOldEnergy (N := N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro E F
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro σ
  exact norm_le_pi_norm (E-F) (fun i => σ i.succ)

lemma averagedEnergyRoot_cavity_rate_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν] (ρ : Measure ((Fin N → Spin) → ℝ))
    [IsProbabilityMeasure ρ] (hρ : Integrable id ρ) (r t s : ℝ≥0)
    (theta : X → InteractionSample (q+1)) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last L)=1)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {H C D : ℝ} (hH : 0≤H) (hC : 0≤C)
    (hθ : ∀ x,‖(theta x).1‖≤C) (hh : ∀ y,|field y|≤H)
    (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |(∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)-
      (∫ E,cavityPoissonValue μ ξ theta field
        (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s
          (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)|≤
      C*|(r:ℝ)-t|+4*D*s/(N+1) := by
  let G := averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    (fun i : I×Fin (N+1) => Q i.1) m field (locatedFactor ψ)
  let μn := Measure.map (newPotential (N := N) theta)
    (μ.prod (finiteUniform (Fin q → Fin N)))
  have hnM := measurable_newPotential (N := N) theta hθm
  have : IsProbabilityMeasure μn := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hnb (z : X×(Fin q → Fin N)) : ‖newPotential theta z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => (norm_le_pi_norm (theta z.1).1 _).trans (hθ z.1))
  have hin : Integrable id μn := by
    apply (integrable_map_measure aestronglyMeasurable_id hnM.aemeasurable).mpr
    exact Integrable.of_bound hnM.aestronglyMeasurable C (ae_of_all _ hnb)
  have hni : (∫ v,‖v‖ ∂μn)≤C := by
    rw [show (∫ v,‖v‖ ∂μn)=∫ z,‖newPotential theta z‖ ∂(μ.prod (finiteUniform (Fin q → Fin N))) from
      integral_map hnM.aemeasurable continuous_norm.aestronglyMeasurable]
    exact (le_abs_self _).trans (abs_integral_le_bound (fun z => by simpa only [abs_of_nonneg (norm_nonneg _)] using hnb z))
  have hGl : LipschitzWith 1 G := averagedEnergyRoot_lipschitz ξ (ν.prod (finiteUniform (Fin (N+1)))) s
    _ m hm field hhm (locatedFactor ψ) hh (fun i y a => hf i.1 _ a)
  have hrate := (integrated_compound_rate_bound μn hin ρ hρ liftOldEnergy_lipschitz hGl r t).trans
    (mul_le_mul_of_nonneg_left hni (abs_nonneg ((r:ℝ)-t)))
  have hr := averagedEnergyRoot_old_new_compare μ ξ ν ρ hρ r s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  have ht := averagedEnergyRoot_old_new_compare μ ξ ν ρ hρ t s theta field hθm hhm Q m hm hend ψ hH hC hθ hh hf
  dsimp only [G,μn] at hrate
  have h1 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson r μn ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
  have h2 := abs_sub_le (∫ E,cavityPoissonValue μ ξ theta field
    (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) r E ∂ρ)
    (∫ E,∫ v,G (liftOldEnergy E+v) ∂compoundPoisson t μn ∂ρ)
    (∫ E,cavityPoissonValue μ ξ theta field
      (averagedEnergyRoot ξ (ν.prod (finiteUniform (Fin N))) s (fun i : I×Fin N => Q i.1) m field (locatedFactor ψ)) t E ∂ρ)
  dsimp only [G,μn] at h1 h2
  rw [abs_sub_comm] at hr
  exact (h2.trans (add_le_add (h1.trans (add_le_add hr hrate)) ht)).trans_eq (by ring)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_CavityGapFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {N p : ℕ} [NeZero N]

lemma cavityPoisson_gap_fubini
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ρ : Measure ((Fin N → Spin) → ℝ)) [IsProbabilityMeasure ρ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    {F : ((Fin N → Spin) → ℝ) → ℝ} (hF : LipschitzWith 1 F)
    {H C : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : ∀ x,‖(theta x).1‖≤C)
    (hh : ∀ y,|field y|≤H) (r : ℝ≥0) :
    (∫ k,∫ z : Fin k → X,∫ E,cavityArrayValue ξ theta field F E z-F E ∂ρ
        ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=
      ∫ E,cavityPoissonValue μ ξ theta field F r E-F E ∂ρ := by
  let g := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) (z : Fin k → X) =>
    cavityArrayValue ξ theta field F E z-F E
  have hgm k : Measurable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2) :=
    (measurable_cavityArrayValue_joint ξ theta field hθm hhm hF.continuous).sub
      (hF.continuous.measurable.comp measurable_fst)
  have hgb k E z : |g k E z|≤H+C*k :=
    cavityArrayValue_gap_bound ξ theta field hhm hF hH hC hθ hh z E
  have hgi k : Integrable (fun w : ((Fin N → Spin) → ℝ)×(Fin k → X) => g k w.1 w.2)
      (ρ.prod (Measure.pi (fun _ : Fin k => μ))) :=
    Integrable.of_bound (hgm k).aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hgb k w.1 w.2))
  have hs k : (∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ))=
      ∫ E,∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ) ∂ρ :=
    (integral_integral_swap (hgi k)).symm
  let f := fun (k : ℕ) (E : (Fin N → Spin) → ℝ) =>
    ∫ z : Fin k → X,g k E z ∂Measure.pi (fun _ : Fin k => μ)
  have hfm : Measurable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1) := by
    apply measurable_from_prod_countable_left
    intro k
    exact (hgm k).stronglyMeasurable.integral_prod_right' (ν := Measure.pi (fun _ : Fin k => μ)) |>.measurable
  have hfb k E : |f k E|≤H+C*k := abs_integral_le_bound (fun z => hgb k E z)
  have hfi : Integrable (fun w : ((Fin N → Spin) → ℝ)×ℕ => f w.2 w.1)
      (ρ.prod (poissonMeasure r)) := by
    apply (((integrable_const H).add ((poisson_integrable_count r).const_mul C)).comp_snd ρ).mono'
      hfm.aestronglyMeasurable
    exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Pi.add_apply,Function.comp_apply] using hfb w.2 w.1)
  change (∫ k,∫ z : Fin k → X,∫ E,g k E z ∂ρ ∂Measure.pi (fun _ : Fin k => μ) ∂poissonMeasure r)=_
  simp_rw [hs]
  rw [show (∫ k,∫ E,f k E ∂ρ ∂poissonMeasure r)=∫ E,∫ k,f k E ∂poissonMeasure r ∂ρ from
    (integral_integral_swap hfi).symm]
  apply integral_congr_ae
  filter_upwards [] with E
  have hge k : Integrable (g k E) (Measure.pi (fun _ : Fin k => μ)) :=
    Integrable.of_bound (((hgm k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (H+C*k) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hgb k E z))
  have ha k : Integrable (cavityArrayValue ξ theta field F E : (Fin k → X) → ℝ)
      (Measure.pi (fun _ : Fin k => μ)) := by
    exact ((hge k).add (integrable_const (F E))).congr (ae_of_all _ (fun z => by simp [g]))
  have he k : f k E=(∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ))-F E := by
    dsimp only [f,g]
    rw [integral_sub (ha k) (integrable_const _)]; simp
  have hfie : Integrable (fun k => f k E) (poissonMeasure r) := poisson_average_integrable r _ (fun k => hfb k E)
  have hca : Integrable (fun k => ∫ z : Fin k → X,cavityArrayValue ξ theta field F E z
      ∂Measure.pi (fun _ : Fin k => μ)) (poissonMeasure r) := by
    exact (hfie.add (integrable_const (F E))).congr (ae_of_all _ (fun k => by simp [he k]))
  simp_rw [he]
  rw [integral_sub hca (integrable_const _)]; simp [cavityPoissonValue]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirEnergyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma reservoirEnergyRoot_lipschitz (M : Model p) {H : ℝ} (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) : LipschitzWith 1 (reservoirEnergyRoot M H N L u) :=
  averagedEnergyRoot_lipschitz M.field.toMeasure ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
    _ (gridExponents L) (gridExponents_pos L) (clipReal H) (measurable_clipReal H)
    (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
    (fun i _ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a)

lemma reservoirEnergyLaw_eq (M : Model p) (C : ℝ) :
    reservoirEnergyLaw M C N=compoundPoisson (reservoirRate M.alpha (p-1) N)
      (Measure.map (indexedPotential (N := N) (clipSample C))
        (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) := rfl

instance reservoirEnergyLaw_probability (M : Model p) (C : ℝ) :
    IsProbabilityMeasure (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

lemma reservoirEnergyLaw_integrable (M : Model p) {C : ℝ} (hC : 0≤C) :
    Integrable id (reservoirEnergyLaw M C N) := by
  rw [reservoirEnergyLaw_eq]
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  have : IsProbabilityMeasure (Measure.map (indexedPotential (N := N) (clipSample C))
      (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply compoundPoisson_integrable_id
  exact integrable_indexedPotential M.disorder.toMeasure (clipSample C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)) hC
    (fun _ _ => clipReal_bound hC _)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirBondEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L k : ℕ} [NeZero N]

lemma reservoirInsertionOn_site_energy (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (h : ℝ) :
    reservoirInsertionOn M C H N L u (cavitySiteEnergy θ h)=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (p-1) → Fin N)).expect (fun j =>
        energyInsertionFunctional (reservoirEnergyLaw M C N) (reservoirEnergyRoot M H N L u)
          (fun σ => cavitySiteEnergy θ h (fun a => σ (j a.1 a.2)))) := by
  rw [reservoirInsertionOn_energy M C H hH]
  let e := Equiv.curry (Fin k) (Fin (p-1)) (Fin N)
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma integral_reservoirInsertionOn_site (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) (hθ : ∀ a,‖(θ a).1‖≤C) :
    (∫ y,reservoirInsertionOn M C H N L u (cavitySiteEnergy θ (clipReal H y)) ∂M.field.toMeasure)=
      ∫ E,cavityArrayValue M.field.toMeasure id (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
        reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N := by
  let F := reservoirEnergyRoot M H N L u
  let ρ := reservoirEnergyLaw M C N
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  simp_rw [reservoirInsertionOn_site_energy M C H hH]
  rw [FiniteLaw.integral_expect]
  · exact cavityArray_insertionFunctional ρ M.field.toMeasure id (clipReal H) (measurable_clipReal H)
      hF hH hC (fun y => clipReal_bound hH y) θ hθ
  · intro j
    apply Integrable.of_bound
      ((energyInsertionFunctional_lipschitz ρ hF).continuous.measurable.comp ?_).aestronglyMeasurable (H+C*k)
    · exact ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs]
        apply (energyInsertionFunctional_bound ρ hF _).trans
        have hb := cavitySiteEnergy_norm_bound θ (clipReal H y) (fun a => j a.1 a.2) 0 hH hC hθ (clipReal_bound hH y)
        simpa only [Pi.zero_apply,zero_add,norm_zero] using hb)
    · apply Measurable.of_eval
      intro σ
      change Measurable (fun y => cavitySiteEnergy θ (clipReal H y) (fun a => σ (j a.1 a.2)))
      unfold cavitySiteEnergy
      apply Measurable.log
      apply Measurable.div_const
      apply Finset.measurable_sum
      intro ε _
      apply Measurable.exp
      exact ((measurable_clipReal H).mul_const _).add measurable_const

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L k : ℕ} [NeZero N]

lemma reservoirInsertionOn_bond_energy (M : Model p) (C H : ℝ) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (θ : Fin k → InteractionSample p) :
    reservoirInsertionOn M C H N L u (cavityBondEnergy θ)=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
        energyInsertionFunctional (reservoirEnergyLaw M C N) (reservoirEnergyRoot M H N L u)
          (∑ i,indexedPotential id (θ i,j i))) := by
  rw [reservoirInsertionOn_energy M C H hH]
  let e := Equiv.curry (Fin k) (Fin p) (Fin N)
  rw [FiniteLaw.uniform_expect,FiniteLaw.uniform_expect,Fintype.card_congr e]
  congr 1
  apply Fintype.sum_equiv e
  intro j
  have he : (fun σ => cavityBondEnergy θ (fun a => σ (j a)))=
      (∑ i,indexedPotential id (θ i,e j i)) := by
    ext σ
    simp [cavityBondEnergy,indexedPotential,e]
  unfold energyInsertionFunctional
  rw [he]

lemma insertionPoisson_bond_energy (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) :
    insertionPoisson M C H N L u
      (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
      (fun _ θ => cavityBondEnergy (fun j => clipSample C (θ j))) r=
      ∫ E,∫ v,reservoirEnergyRoot M H N L u (E+v)-reservoirEnergyRoot M H N L u E
        ∂compoundPoisson r (Measure.map (indexedPotential (N := N) (clipSample C))
          (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))))
        ∂reservoirEnergyLaw M C N := by
  let μ := Measure.map (indexedPotential (N := N) (clipSample C))
    (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hμ : Integrable id μ := integrable_indexedPotential M.disorder.toMeasure (clipSample C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)) hC
    (fun z σ => clipReal_bound hC _)
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  rw [← integral_energyInsertionFunctional (reservoirEnergyLaw M C N)
    (compoundPoisson r μ) (compoundPoisson_integrable_id r μ hμ) hF]
  rw [integral_compound_finite_sample M.disorder.toMeasure (indexedPotential (N := N) (clipSample C)) hm
    (C := C) (fun z => (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by
      simpa only [Real.norm_eq_abs,indexedPotential,clipSample] using clipReal_bound hC (z.1.1 (fun i => σ (z.2 i))))) r
    (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF)]
  unfold insertionPoisson
  apply integral_congr_ae
  filter_upwards [] with k
  apply integral_congr_ae
  filter_upwards [] with θ
  exact reservoirInsertionOn_bond_energy M C H hH u (fun j => clipSample C (θ j))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ReservoirSitePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ} [NeZero N]

lemma insertionPoisson_site_energy (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r : ℝ≥0) :
    insertionPoisson M C H N L u
      (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
      (fun _ z => cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2)) r=
      ∫ E,cavityPoissonValue M.disorder.toMeasure M.field.toMeasure (clipSample C) (clipReal H)
        (reservoirEnergyRoot M H N L u) r E-reservoirEnergyRoot M H N L u E
        ∂reservoirEnergyLaw M C N := by
  have hclip (z : InteractionSample p) : ‖(clipSample C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs,clipSample] using clipReal_bound hC (z.1 σ))
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have ha (k : ℕ) :
      (∫ z : (Fin k → InteractionSample p)×ℝ,
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))
        ∂(Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)=
      ∫ θ : Fin k → InteractionSample p,∫ E,
        cavityArrayValue M.field.toMeasure (clipSample C) (clipReal H) (reservoirEnergyRoot M H N L u) E θ-
          reservoirEnergyRoot M H N L u E ∂reservoirEnergyLaw M C N
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
    have hm : Measurable (fun z : (Fin k → InteractionSample p)×ℝ =>
        reservoirInsertionOn M C H N L u (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))) := by
      simp_rw [reservoirInsertionOn_site_energy M C H hH]
      apply FiniteLaw.measurable_expect
      intro j
      apply (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF).continuous.measurable.comp
      convert measurable_cavityArrayEnergy (N := N) (p := p) (k := k) (clipSample C) (clipReal H)
          (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
          (measurable_clipReal H) (0 : (Fin N → Spin) → ℝ) j using 1
      all_goals try with_reducible_and_instances rfl
      ext z σ
      simp [cavityArrayEnergy]
    have hb (z : (Fin k → InteractionSample p)×ℝ) : |reservoirInsertionOn M C H N L u
        (cavitySiteEnergy (fun j => clipSample C (z.1 j)) (clipReal H z.2))|≤H+C*k := by
      apply reservoirInsertionOn_bound
      intro σ
      apply (cavitySiteEnergy_bound _ _ σ).trans
      have hs : (∑ j : Fin k,‖(clipSample C (z.1 j)).1‖)≤C*k := by
        simpa [mul_comm] using Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin k))) => hclip (z.1 j))
      exact add_le_add (clipReal_bound hH _) hs
    rw [integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable (H+C*k)
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb z)))]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact integral_reservoirInsertionOn_site M hC hH u (fun j => clipSample C (θ j)) (fun _ => hclip _)
  unfold insertionPoisson
  simp_rw [ha]
  exact cavityPoisson_gap_fubini M.disorder.toMeasure M.field.toMeasure (reservoirEnergyLaw M C N)
    (clipSample C) (clipReal H)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
    (measurable_clipReal H) hF hH hC hclip (fun y => clipReal_bound hH y) r

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedCavityProxy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {p N L : ℕ}

lemma clippedCavityProxy_eq (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H) :
    clippedCavityProxy M C H N L u=cavityProxy M C H N L u := by
  have heθ : ∀ k,∀ᵐ θ ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure),
      (fun j => clipSample C (θ j))=θ := by
    intro k
    have hh := Filter.eventually_all.mpr (fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => M.disorder.toMeasure) (i := j)).eventually hθ)
    filter_upwards [hh] with θ hθ
    exact funext (fun j => clipSample_eq (hθ j))
  have hes r : clippedSiteInsertion M C H N L u r=
      insertionPoisson M C H N L u
        (fun k => (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod M.field.toMeasure)
        (fun _ z => cavitySiteEnergy z.1 z.2) r := by
    unfold clippedSiteInsertion insertionPoisson
    apply integral_congr_ae
    filter_upwards [] with k
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (heθ k),
      Measure.quasiMeasurePreserving_snd.ae hh] with z hz hh
    rw [hz,clipReal_eq hh]
  have heb r : clippedBondInsertion M C H N L u r=
      insertionPoisson M C H N L u (fun k => Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
        (fun _ θ => cavityBondEnergy θ) r := by
    unfold clippedBondInsertion insertionPoisson
    apply integral_congr_ae
    filter_upwards [] with k
    apply integral_congr_ae
    filter_upwards [heθ k] with θ hθ
    rw [hθ]
  simp only [clippedCavityProxy,cavityProxy,hes,heb]

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ClippedProxyRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma clippedSiteInsertion_rate_bound (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedSiteInsertion M C H N L u r-clippedSiteInsertion M C H N L u t|≤
      C*|(r:ℝ)-t|+4*(scoreRate N:ℝ)/(N+1) := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  have hθ z : ‖(clipSample (p := q+1) C z).1‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs] using clipSample_bound hC z σ)
  have hρ := reservoirEnergyLaw_integrable (N := N) M hC
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  have hFi := integrable_lipschitz_of_id (reservoirEnergyLaw M C N) hρ hF
  have hFb (E : (Fin N → Spin) → ℝ) : |reservoirEnergyRoot M H N L u E|≤‖E‖+(H*N+1*scoreRate N) := by
    simpa only [reservoirEnergyRoot,add_assoc] using averagedEnergyRoot_bound M.field.toMeasure
      ((weights L).prod (finiteUniform (Fin N))) (scoreRate N)
      (fun i : (Spec L×ℕ)×Fin N => prior i.1.1) (gridExponents L) (gridExponents_pos L)
      (clipReal H) (locatedFactor (spinFactor direction anchor u)) (fun y => clipReal_bound hH y)
      (fun i y a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i.1 _ a) E
  have hCi a := integrable_cavityPoissonValue M.disorder.toMeasure M.field.toMeasure
    (reservoirEnergyLaw M C N) hρ (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    hC hH hθ (fun y => clipReal_bound hH y) hF.continuous hFb a
  have hh := averagedEnergyRoot_cavity_rate_bound M.disorder.toMeasure M.field.toMeasure (weights L)
    (reservoirEnergyLaw M C N) hρ r t (scoreRate N) (clipSample C) (clipReal H) hθm (measurable_clipReal H)
    (fun i : Spec L×ℕ => prior i.1) (gridExponents L) (gridExponents_pos L) (gridExponents_last L)
    (spinFactor direction anchor u) hH hC hθ (fun y => clipReal_bound hH y)
    (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)
  unfold clippedSiteInsertion
  rw [insertionPoisson_site_energy M hC hH,insertionPoisson_site_energy M hC hH,
    integral_sub (hCi r) hFi,integral_sub (hCi t) hFi,sub_sub_sub_cancel_right]
  simpa only [mul_one,reservoirEnergyRoot] using hh

lemma clippedBondInsertion_rate_bound {p : ℕ} (M : Model p) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) (r t : ℝ≥0) :
    |clippedBondInsertion M C H N L u r-clippedBondInsertion M C H N L u t|≤C*|(r:ℝ)-t| := by
  let μ := Measure.map (indexedPotential (N := N) (clipSample (p := p) C))
    (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N)))
  have hm := measurable_indexedPotential (N := N) (clipSample (p := p) C)
    (fun σ => (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst))
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hb (z : InteractionSample p×(Fin p → Fin N)) : ‖indexedPotential (clipSample C) z‖≤C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun σ => by simpa only [Real.norm_eq_abs,indexedPotential,clipSample] using clipReal_bound hC (z.1.1 (fun i => σ (z.2 i))))
  have hi : Integrable id μ :=
    (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).mpr
      (Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb))
  have hnorm : (∫ v,‖v‖ ∂μ)≤C := by
    rw [show (∫ v,‖v‖ ∂μ)=∫ z,‖indexedPotential (clipSample C) z‖
        ∂(M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))) from
      integral_map hm.aemeasurable continuous_norm.aestronglyMeasurable]
    exact (le_abs_self _).trans (abs_integral_le_bound (fun z => by simpa only [abs_of_nonneg (norm_nonneg _)] using hb z))
  have hF := reservoirEnergyRoot_lipschitz (N := N) M hH u
  unfold clippedBondInsertion
  rw [insertionPoisson_bond_energy M hC hH,insertionPoisson_bond_energy M hC hH,
    ← integral_energyInsertionFunctional (reservoirEnergyLaw M C N) (compoundPoisson r μ) (compoundPoisson_integrable_id r μ hi) hF,
    ← integral_energyInsertionFunctional (reservoirEnergyLaw M C N) (compoundPoisson t μ) (compoundPoisson_integrable_id t μ hi) hF]
  exact (compoundPoisson_rate_bound r t μ hi (energyInsertionFunctional_lipschitz (reservoirEnergyLaw M C N) hF)).trans
    (by simpa only [NNReal.coe_one,one_mul,mul_one,mul_comm] using mul_le_mul_of_nonneg_left hnorm (abs_nonneg ((r:ℝ)-t)))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_PhysicalScoreRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirEnergyLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i,Fintype (A i)] {p L N : ℕ} [NeZero N]

lemma perturbedMean_score_rate (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hD : 0≤D) (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (u v w : ℝ≥0) (hvw : v≤w) :
    |perturbedMean (N := N) μ ξ ν theta field Q m ψ u w-
      perturbedMean (N := N) μ ξ ν theta field Q m ψ u v|≤D*((w:ℝ)-v) := by
  have h := twoPoissonMean_rate_add_right u v (w-v)
    (countedMean_bound (N := N) μ ξ ν theta field Q m hm ψ hθ hh hψ) hD
    (countedMean_mark_step μ ξ ν theta field hθm hhm Q m hm ψ hθ hh hψ)
  rw [add_tsub_cancel_of_le hvw,NNReal.coe_sub hvw] at h
  simpa only [perturbedMean,add_sub_add_left_eq_sub] using h

end DilutedSpinGlass.SizeCoupling

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_ProxyRateIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators
variable {N L q : ℕ} [NeZero N]

lemma energyCavityIncrement_proxy_bound (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (u : Spec L×ℕ → ℝ) :
    |energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
        (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
        (spinFactor direction anchor u)-clippedCavityProxy M C H N L u|≤
      C*|(oneNewRate M.alpha q N:ℝ)-(M.alpha*(q+1):ℝ≥0)|+4*(scoreRate N:ℝ)/(N+1)+
      C*|((M.alpha*N-reservoirRate M.alpha q N:ℝ≥0):ℝ)-(M.alpha*q:ℝ≥0)| := by
  have hs := clippedSiteInsertion_rate_bound (N := N) M hC hH u
    (oneNewRate M.alpha q N) (M.alpha*(q+1))
  have hb := clippedBondInsertion_rate_bound (N := N) M hC hH u
    (M.alpha*N-reservoirRate M.alpha q N) (M.alpha*q)
  have he : energyCavityIncrement (N := N) M.disorder.toMeasure M.field.toMeasure (weights L) M.alpha (scoreRate N)
        (clipSample C) (clipReal H) (fun i : Spec L×ℕ => prior i.1) (gridExponents L)
        (spinFactor direction anchor u)=Real.log 2+
      clippedSiteInsertion M C H N L u (oneNewRate M.alpha q N)-
      clippedBondInsertion M C H N L u (M.alpha*N-reservoirRate M.alpha q N) := by
    unfold clippedSiteInsertion clippedBondInsertion
    rw [insertionPoisson_site_energy M hC hH,insertionPoisson_bond_energy M hC hH]
    simp only [energyCavityIncrement,reservoirEnergyRoot,reservoirEnergyLaw,Nat.add_sub_cancel]
    rfl
  rw [he]
  unfold clippedCavityProxy
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  have hx := (abs_sub
    (clippedSiteInsertion M C H N L u (oneNewRate M.alpha q N)-clippedSiteInsertion M C H N L u (M.alpha*(q+1)))
    (clippedBondInsertion M C H N L u (M.alpha*N-reservoirRate M.alpha q N)-clippedBondInsertion M C H N L u (M.alpha*q))).trans (add_le_add hs hb)
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_GridIncrementSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

lemma scoreRate_real (N : ℕ) : (scoreRate N : ℝ)=scoreScale N := rfl

lemma clippedPhysicalMean_score_bound {q L : ℕ} (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (N : ℕ) (u : Spec L×ℕ → ℝ) :
    |clippedPhysicalMean M C H (N+1) (scoreRate (N+1)) u-
      clippedPhysicalMean M C H (N+1) (scoreRate N) u| ≤ scoreScale (N+1)-scoreScale N := by
  have hθm σ : Measurable (fun z : InteractionSample (q+1) => (clipSample C z).1 σ) :=
    (measurable_clipReal C).comp ((measurable_pi_apply σ).comp measurable_fst)
  simpa [clippedPhysicalMean,mul_one,one_mul,scoreRate_real,Nat.cast_add,Nat.cast_one,NNReal.coe_mk,Subtype.coe_mk] using
    perturbedMean_score_rate (N := N+1) M.disorder.toMeasure M.field.toMeasure (weights L)
      (clipSample C) (clipReal H) hθm (measurable_clipReal H) (fun i : Spec L×ℕ => prior i.1)
      (gridExponents L) (gridExponents_pos L) (spinFactor direction anchor u) (by norm_num : (0:ℝ)≤1)
      (clipSample_bound hC) (fun y => clipReal_bound hH y)
      (fun i σ a => spinFactor_log_bound direction anchor direction_bound anchor_bound u i σ a)
      (M.alpha*(N+1)) (scoreRate N) (scoreRate (N+1)) (scoreScale_mono (Nat.le_succ N))

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

section
-- module Solutions.OAIQ041_DS.DilutedSpin_IncrementCavityProxy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir KernelTower SizeCoupling
open scoped NNReal BigOperators

lemma increment_cavityProxy_bound_oai {q L : ℕ} (M : Model (q+1)) {C H : ℝ} (hC : 0≤C) (hH : 0≤H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ|≤C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h|≤H)
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)),IdentDistrib (fun z : InteractionSample (q+1) => z.1)
      (fun z : InteractionSample (q+1) => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (N : ℕ) (u : Spec L×ℕ → ℝ) :
    |increment (weights L) prior (gridExponents L) direction anchor M N u-
      cavityProxy M C H (N+1) L u| ≤ cavityIncrementError M.alpha q C (N+1) := by
  have heθ : id =ᵐ[M.disorder.toMeasure] clipSample C := hθ.mono (fun z hz => (clipSample_eq hz).symm)
  have heh : id =ᵐ[M.field.toMeasure] clipReal H := hh.mono (fun y hy => (clipReal_eq hy).symm)
  have h1 := clippedPhysicalMean_score_bound M hC hH (N+1) u
  have h2 := clippedPhysicalMean_reservoir_bound (N := N+1) M hC hH hsym u
  have h3 := energyCavityIncrement_proxy_bound (N := N+1) M hC hH u
  rw [← clippedCavityProxy_eq M C H (N+1) L u hθ hh]
  unfold increment
  rw [perturbedMean_congr _ _ (weights L) id (clipSample C) id (clipReal H) heθ heh,
    perturbedMean_congr _ _ (weights L) id (clipSample C) id (clipReal H) heθ heh]
  have halg (a b c d e A B D : ℝ) (h1 : |a-b|≤A) (h2 : |(b-c)-d|≤B) (h3 : |d-e|≤D) :
      |(a-c)-e|≤A+B+D := by
    have h := (abs_add_le ((a-b)+((b-c)-d)) (d-e)).trans
      (add_le_add ((abs_add_le (a-b) ((b-c)-d)).trans (add_le_add h1 h2)) h3)
    convert h using 1; congr 1; ring
  change |clippedReservoirIncrement M C H (N+1) u-clippedCavityProxy M C H (N+1) L u| ≤ _ at h3
  rw [NNReal.coe_sub (reservoirRate_le M.alpha q (N+1))] at h3
  have hf := halg _ _ _ _ _ _ _ _ h1 h2 h3
  simp only [clippedPhysicalMean,Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_one] at hf
  apply hf.trans_eq
  simp only [cavityIncrementError,
    NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,scoreRate_real,Nat.cast_add,Nat.cast_one]
  ring

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end

theorem solution : type_of% @OAI.DilutedSpinGlass.UniversalDictionary.increment_cavityProxy_bound_oai := @OAI.DilutedSpinGlass.UniversalDictionary.increment_cavityProxy_bound_oai
