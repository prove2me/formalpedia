-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T06:27:50.988244+00:00
-- url     : https://prove2.me/submissions/a22a969c-1c61-449e-baee-459cbe3b364c

import Mathlib

namespace Prove2SwarmSubmission

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory ENNReal


/- Native source part: MomentInduction.lean -/
open scoped BigOperators MeasureTheory

namespace BacklogCuratorGreedy.Core

open MeasureTheory

theorem Icc_one_succ (k : ℕ) :
    Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem sum_Icc_one_succ {β : Type*} [AddCommMonoid β]
    (f : ℕ → β) (k : ℕ) :
    (∑ i ∈ Finset.Icc 1 (k + 1), f i) =
      (∑ i ∈ Finset.Icc 1 k, f i) + f (k + 1) := by
  have hnot : k + 1 ∉ Finset.Icc 1 k := by
    simp only [Finset.mem_Icc]
    omega
  rw [Icc_one_succ, Finset.sum_insert hnot]
  exact add_comm _ _

/-- Only adaptedness on the finite interval is used. -/
theorem prefix_stronglyMeasurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (n : ℕ)
    (hadapted : ∀ i ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ i] (D i))
    (k : ℕ) (hk : k ≤ n) :
    StronglyMeasurable[ℱ k] (fun ω => ∑ i ∈ Finset.Icc 1 k, D i ω) := by
  have hmeas : Measurable[ℱ k] (fun ω => ∑ i ∈ Finset.Icc 1 k, D i ω) := by
    refine Finset.measurable_sum (Finset.Icc 1 k) ?_
    intro i hi
    have hbounds := Finset.mem_Icc.mp hi
    have hin : i ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨hbounds.1, hbounds.2.trans hk⟩
    exact ((hadapted i hin).mono (ℱ.mono hbounds.2)).measurable
  exact hmeas.stronglyMeasurable

/-- The one-step moment recurrence. Prefix integrability is an explicit
internal input; it is not added to the public theorem's assumptions. -/
theorem integral_exp_prefix_succ_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (σk : ℕ → ℝ) (n : ℕ)
    (hadapted : ∀ i ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ i] (D i))
    (hint : ∀ i ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * D i ω)) P)
    (hsubG : ∀ i ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      condExp (m₀ := mΩ) (ℱ (i - 1)) P (fun ω => Real.exp (τ * D i ω))
        ≤ᵐ[P] fun _ => Real.exp (σk i ^ 2 * τ ^ 2 / 2))
    (hprefix : ∀ j, j ≤ n → ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * ∑ i ∈ Finset.Icc 1 j, D i ω)) P)
    (τ : ℝ) (k : ℕ) (hk : k < n) :
    (∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω) ∂P) ≤
      Real.exp (σk (k + 1) ^ 2 * τ ^ 2 / 2) *
        ∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 k, D i ω) ∂P := by
  let A : Ω → ℝ := fun ω => Real.exp (τ * ∑ i ∈ Finset.Icc 1 k, D i ω)
  let B : Ω → ℝ := fun ω => Real.exp (τ * D (k + 1) ω)
  let C : ℝ := Real.exp (σk (k + 1) ^ 2 * τ ^ 2 / 2)
  have hk' : k ≤ n := Nat.le_of_lt hk
  have hkn : k + 1 ≤ n := by omega
  have hin : k + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, hkn⟩
  have hA : StronglyMeasurable[ℱ k] A := by
    have hpre := prefix_stronglyMeasurable ℱ D n hadapted k hk'
    exact (hpre.measurable.const_mul τ).exp.stronglyMeasurable
  have hexp :
      (fun ω => Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω)) = A * B := by
    funext ω
    change Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω) =
      Real.exp (τ * ∑ i ∈ Finset.Icc 1 k, D i ω) * Real.exp (τ * D (k + 1) ω)
    rw [sum_Icc_one_succ (fun i => D i ω) k, mul_add, Real.exp_add]
  have hprod : Integrable (A * B) P := by
    rw [← hexp]
    exact hprefix (k + 1) hkn τ
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := ℱ k) (mΩ := mΩ) (μ := P) hA hprod (hint (k + 1) hin τ)
  have hsub : condExp (m₀ := mΩ) (ℱ k) P B ≤ᵐ[P] fun _ => C := by
    simpa only [Nat.add_sub_cancel] using hsubG (k + 1) hin τ
  have hbound :
      condExp (m₀ := mΩ) (ℱ k) P
          (fun ω => Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω))
        ≤ᵐ[P] fun ω => C * A ω := by
    rw [hexp]
    filter_upwards [hpull, hsub] with ω hp hs
    calc
      condExp (m₀ := mΩ) (ℱ k) P (A * B) ω =
          A ω * condExp (m₀ := mΩ) (ℱ k) P B ω := hp
      _ ≤ A ω * C := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = C * A ω := mul_comm _ _
  calc
    (∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω) ∂P) =
        ∫ ω, condExp (m₀ := mΩ) (ℱ k) P
          (fun ω' => Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω')) ω ∂P :=
      (integral_condExp (m₀ := mΩ) (m := ℱ k) (μ := P) (ℱ.le k)).symm
    _ ≤ ∫ ω, C * A ω ∂P :=
      integral_mono_ae integrable_condExp ((hprefix k hk' τ).const_mul C) hbound
    _ = C * ∫ ω, A ω ∂P := by rw [integral_const_mul]

/-- Finite-filtration MGF induction for every real parameter. There is no
independence or regularity assumption on the underlying measurable space. -/
theorem integral_exp_prefix_le_of_integrable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (σk : ℕ → ℝ) (n : ℕ)
    (hadapted : ∀ i ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ i] (D i))
    (hint : ∀ i ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * D i ω)) P)
    (hsubG : ∀ i ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      condExp (m₀ := mΩ) (ℱ (i - 1)) P (fun ω => Real.exp (τ * D i ω))
        ≤ᵐ[P] fun _ => Real.exp (σk i ^ 2 * τ ^ 2 / 2))
    (hprefix : ∀ j, j ≤ n → ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * ∑ i ∈ Finset.Icc 1 j, D i ω)) P)
    (τ : ℝ) :
    (∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 n, D i ω) ∂P) ≤
      Real.exp ((∑ i ∈ Finset.Icc 1 n, σk i ^ 2) * τ ^ 2 / 2) := by
  have haux : ∀ k, k ≤ n →
      (∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 k, D i ω) ∂P) ≤
        Real.exp ((∑ i ∈ Finset.Icc 1 k, σk i ^ 2) * τ ^ 2 / 2) := by
    intro k
    induction k with
    | zero =>
        intro _hk
        simp
    | succ k ih =>
        intro hk
        have hk' : k ≤ n := by omega
        calc
          (∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 (k + 1), D i ω) ∂P) ≤
              Real.exp (σk (k + 1) ^ 2 * τ ^ 2 / 2) *
                ∫ ω, Real.exp (τ * ∑ i ∈ Finset.Icc 1 k, D i ω) ∂P :=
            integral_exp_prefix_succ_le P ℱ D σk n hadapted hint hsubG hprefix τ k
              (by omega)
          _ ≤ Real.exp (σk (k + 1) ^ 2 * τ ^ 2 / 2) *
              Real.exp ((∑ i ∈ Finset.Icc 1 k, σk i ^ 2) * τ ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left (ih hk') (Real.exp_pos _).le
          _ = Real.exp ((∑ i ∈ Finset.Icc 1 (k + 1), σk i ^ 2) * τ ^ 2 / 2) := by
            rw [← Real.exp_add, sum_Icc_one_succ (fun i => σk i ^ 2) k]
            congr 1
            ring
  exact haux n le_rfl

end BacklogCuratorGreedy.Core


/- Native source part: Integrability.lean -/
open scoped BigOperators MeasureTheory

namespace BacklogCuratorGreedy

open MeasureTheory

/-- Squaring an exponential doubles the parameter. -/
theorem exp_mul_sq (τ x : ℝ) :
    (Real.exp (τ * x)) ^ 2 = Real.exp ((2 * τ) * x) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- An integrable doubled exponential supplies the L2 input for Cauchy-Schwarz. -/
theorem exp_memLp_two {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) (X : Ω → ℝ) (τ : ℝ)
    (hX : AEStronglyMeasurable (fun ω => Real.exp (τ * X ω)) P)
    (hdouble : Integrable (fun ω => Real.exp ((2 * τ) * X ω)) P) :
    MemLp (fun ω => Real.exp (τ * X ω)) 2 P := by
  apply (memLp_two_iff_integrable_sq hX).mpr
  simpa only [exp_mul_sq] using hdouble

/-- Every finite adapted prefix has all exponential moments. The induction
uses doubled parameters before multiplying the two L2 functions. -/
theorem integrable_exp_prefix {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (n : ℕ)
    (hadapted : ∀ i ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ i] (D i))
    (hint : ∀ i ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * D i ω)) P) :
    ∀ k, k ≤ n → ∀ τ : ℝ,
      Integrable (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 k, D i ω))) P := by
  intro k
  induction k with
  | zero =>
      intro _hk τ
      simp
  | succ k ih =>
      intro hk τ
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hnext : k + 1 ∈ Finset.Icc 1 n :=
        Finset.mem_Icc.mpr ⟨by omega, hk⟩
      have hpre : StronglyMeasurable[ℱ k]
          (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 k, D i ω))) :=
        (((Core.prefix_stronglyMeasurable ℱ D n hadapted k hk').measurable.const_mul τ).exp).stronglyMeasurable
      have hinc : StronglyMeasurable[ℱ (k + 1)]
          (fun ω => Real.exp (τ * D (k + 1) ω)) :=
        (((hadapted (k + 1) hnext).measurable.const_mul τ).exp).stronglyMeasurable
      have hpre2 : MemLp
          (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 k, D i ω))) 2 P :=
        exp_memLp_two P (fun ω => ∑ i ∈ Finset.Icc 1 k, D i ω) τ
          ((hpre.mono (ℱ.le k)).aestronglyMeasurable) (ih hk' (2 * τ))
      have hinc2 : MemLp (fun ω => Real.exp (τ * D (k + 1) ω)) 2 P :=
        exp_memLp_two P (D (k + 1)) τ
          ((hinc.mono (ℱ.le (k + 1))).aestronglyMeasurable)
          (hint (k + 1) hnext (2 * τ))
      have hprod : Integrable
          (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 k, D i ω)) *
            Real.exp (τ * D (k + 1) ω)) P :=
        hpre2.integrable_mul hinc2
      have hsplit :
          (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 (k + 1), D i ω))) =
            (fun ω => Real.exp (τ * (∑ i ∈ Finset.Icc 1 k, D i ω)) *
              Real.exp (τ * D (k + 1) ω)) := by
        funext ω
        rw [Core.sum_Icc_one_succ (fun i => D i ω) k, mul_add, Real.exp_add]
      rw [hsplit]
      exact hprod

end BacklogCuratorGreedy


/- Native source part: Tails.lean -/
/-!
Independent native tail argument for greedy-lemma8.
SOURCE ONLY: this file has not been compiled or independently checked.
Pinned primary API: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
Probability/Moments/Basic.lean (signed Chernoff bounds),
MeasureTheory/Measure/Real.lean (real-valued union bound), and
MeasureTheory/Measure/Typeclasses/Probability.lean (probability at most one).
No measurability or StandardBorel premise is imposed on the sample space.
-/

namespace BacklogCuratorGreedy.Tail

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The exponent at the positive optimizing parameter `t / V`. -/
theorem upper_optimizer (V t : ℝ) (hV : V ≠ 0) :
    -(t / V) * t + V * (t / V) ^ 2 / 2 = -(t ^ 2 / (2 * V)) := by
  field_simp [hV]
  ring

/-- The exponent at the negative optimizing parameter `-(t / V)`. -/
theorem lower_optimizer (V t : ℝ) (hV : V ≠ 0) :
    -(-(t / V)) * (-t) + V * (-(t / V)) ^ 2 / 2 =
      -(t ^ 2 / (2 * V)) := by
  calc
    -(-(t / V)) * (-t) + V * (-(t / V)) ^ 2 / 2 =
        -(t / V) * t + V * (t / V) ^ 2 / 2 := by ring
    _ = -(t ^ 2 / (2 * V)) := upper_optimizer V t hV

omit mΩ in
/-- Exact inclusive absolute-tail event, expressed as two signed events. -/
theorem absolute_event_union (S : Ω → ℝ) (t : ℝ) :
    {ω | t ≤ |S ω|} = {ω | t ≤ S ω} ∪ {ω | S ω ≤ -t} := by
  ext ω
  change (t ≤ |S ω|) ↔ (t ≤ S ω ∨ S ω ≤ -t)
  constructor
  · intro h
    by_cases hS : 0 ≤ S ω
    · left
      simpa only [abs_of_nonneg hS] using h
    · right
      have hSneg : S ω < 0 := lt_of_not_ge hS
      have hneg : t ≤ -S ω := by
        simpa only [abs_of_neg hSneg] using h
      linarith
  · rintro (h | h)
    · exact h.trans (le_abs_self (S ω))
    · have hneg : t ≤ -S ω := by linarith
      exact hneg.trans (neg_le_abs (S ω))

/-- Subadditivity needs no event-measurability assumption. -/
theorem absolute_tail_union_bound (P : Measure[mΩ] Ω) (S : Ω → ℝ) (t : ℝ) :
    (P {ω | t ≤ |S ω|}).toReal ≤
      (P {ω | t ≤ S ω}).toReal + (P {ω | S ω ≤ -t}).toReal := by
  change P.real {ω | t ≤ |S ω|} ≤
    P.real {ω | t ≤ S ω} + P.real {ω | S ω ≤ -t}
  rw [absolute_event_union S t]
  exact measureReal_union_le _ _

/-- Upper tail from unconditional exponential moments; `τ = t / V`. -/
theorem upper_tail_of_mgf (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (V t : ℝ) (hV : 0 < V) (ht : 0 ≤ t)
    (hint : ∀ τ : ℝ, Integrable[mΩ] (fun ω => Real.exp (τ * S ω)) P)
    (hmgf : ∀ τ : ℝ, (∫ ω, Real.exp (τ * S ω) ∂P) ≤
      Real.exp (V * τ ^ 2 / 2)) :
    (P {ω | t ≤ S ω}).toReal ≤ Real.exp (-(t ^ 2 / (2 * V))) := by
  have hτ : 0 ≤ t / V := div_nonneg ht hV.le
  calc
    (P {ω | t ≤ S ω}).toReal ≤
        Real.exp (-(t / V) * t) * (∫ ω, Real.exp ((t / V) * S ω) ∂P) :=
      measure_ge_le_exp_mul_mgf (μ := P) (X := S) t hτ (hint (t / V))
    _ ≤ Real.exp (-(t / V) * t) * Real.exp (V * (t / V) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hmgf (t / V)) (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2 / (2 * V))) := by
      rw [← Real.exp_add, upper_optimizer V t hV.ne']

/-- Lower tail from unconditional exponential moments; `τ = -(t / V)`. -/
theorem lower_tail_of_mgf (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (V t : ℝ) (hV : 0 < V) (ht : 0 ≤ t)
    (hint : ∀ τ : ℝ, Integrable[mΩ] (fun ω => Real.exp (τ * S ω)) P)
    (hmgf : ∀ τ : ℝ, (∫ ω, Real.exp (τ * S ω) ∂P) ≤
      Real.exp (V * τ ^ 2 / 2)) :
    (P {ω | S ω ≤ -t}).toReal ≤ Real.exp (-(t ^ 2 / (2 * V))) := by
  have hτ : -(t / V) ≤ 0 := neg_nonpos.mpr (div_nonneg ht hV.le)
  calc
    (P {ω | S ω ≤ -t}).toReal ≤
        Real.exp (-(-(t / V)) * (-t)) *
          (∫ ω, Real.exp ((-(t / V)) * S ω) ∂P) :=
      measure_le_le_exp_mul_mgf (μ := P) (X := S) (-t) hτ (hint (-(t / V)))
    _ ≤ Real.exp (-(-(t / V)) * (-t)) *
          Real.exp (V * (-(t / V)) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hmgf (-(t / V))) (Real.exp_pos _).le
    _ = Real.exp (-(t ^ 2 / (2 * V))) := by
      rw [← Real.exp_add, lower_optimizer V t hV.ne']

/-- Positive-variance two-sided bound, with both inclusive signed tails. -/
theorem absolute_tail_of_mgf_pos (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (V t : ℝ) (hV : 0 < V) (ht : 0 ≤ t)
    (hint : ∀ τ : ℝ, Integrable[mΩ] (fun ω => Real.exp (τ * S ω)) P)
    (hmgf : ∀ τ : ℝ, (∫ ω, Real.exp (τ * S ω) ∂P) ≤
      Real.exp (V * τ ^ 2 / 2)) :
    (P {ω | t ≤ |S ω|}).toReal ≤ 2 * Real.exp (-(t ^ 2 / (2 * V))) := by
  calc
    (P {ω | t ≤ |S ω|}).toReal ≤
        (P {ω | t ≤ S ω}).toReal + (P {ω | S ω ≤ -t}).toReal :=
      absolute_tail_union_bound P S t
    _ ≤ Real.exp (-(t ^ 2 / (2 * V))) + Real.exp (-(t ^ 2 / (2 * V))) :=
      add_le_add (upper_tail_of_mgf P S V t hV ht hint hmgf)
        (lower_tail_of_mgf P S V t hV ht hint hmgf)
    _ = 2 * Real.exp (-(t ^ 2 / (2 * V))) := by ring

/-- The exact Lean division-by-zero interpretation only asks for probability ≤ 2. -/
theorem absolute_tail_zero_variance (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (t : ℝ) :
    (P {ω | t ≤ |S ω|}).toReal ≤ 2 * Real.exp (-(t ^ 2 / (2 * (0 : ℝ)))) := by
  calc
    (P {ω | t ≤ |S ω|}).toReal ≤ 1 := measureReal_le_one
    _ ≤ 2 * Real.exp (-(t ^ 2 / (2 * (0 : ℝ)))) := by norm_num

/-- Generic exact two-sided sub-Gaussian tail, including the zero-variance case. -/
theorem absolute_tail_of_mgf (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (V t : ℝ) (hV : 0 ≤ V) (ht : 0 < t)
    (hint : ∀ τ : ℝ, Integrable[mΩ] (fun ω => Real.exp (τ * S ω)) P)
    (hmgf : ∀ τ : ℝ, (∫ ω, Real.exp (τ * S ω) ∂P) ≤
      Real.exp (V * τ ^ 2 / 2)) :
    (P {ω | t ≤ |S ω|}).toReal ≤ 2 * Real.exp (-(t ^ 2 / (2 * V))) := by
  by_cases hVzero : V = 0
  · subst V
    exact absolute_tail_zero_variance P S t
  · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hVzero)
    exact absolute_tail_of_mgf_pos P S V t hVpos ht.le hint hmgf

end BacklogCuratorGreedy.Tail


/- Native source part: Assembly.lean -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_8 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (σk : ℕ → ℝ) (n : ℕ)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ k] (D k))
    (hint : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ, Integrable (fun ω => Real.exp (τ * D k ω)) P)
    (hsubG : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      condExp (ℱ (k - 1)) P (fun ω => Real.exp (τ * D k ω))
        ≤ᵐ[P] fun _ => Real.exp (σk k ^ 2 * τ ^ 2 / 2))
    (t : ℝ) (ht : 0 < t) :
    (P {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|}).toReal
      ≤ 2 * Real.exp (-(t ^ 2 / (2 * ∑ k ∈ Finset.Icc 1 n, σk k ^ 2))) := by
  by_cases hn : n = 0
  · subst n
    simp [not_le.mpr ht]
  let V : ℝ := ∑ k ∈ Finset.Icc 1 n, σk k ^ 2
  change (P {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|}).toReal ≤
    2 * Real.exp (-(t ^ 2 / (2 * V)))
  by_cases hVzero : V = 0
  · rw [hVzero]
    exact BacklogCuratorGreedy.Tail.absolute_tail_zero_variance P
      (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) t
  have hVnonneg : 0 ≤ V :=
    Finset.sum_nonneg (fun k _hk => sq_nonneg (σk k))
  have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hVzero)
  have hprefix := BacklogCuratorGreedy.integrable_exp_prefix P ℱ D n hadapted hint
  have hmgf : ∀ τ : ℝ,
      (∫ ω, Real.exp (τ * (∑ k ∈ Finset.Icc 1 n, D k ω)) ∂P) ≤
        Real.exp (V * τ ^ 2 / 2) := by
    intro τ
    exact BacklogCuratorGreedy.Core.integral_exp_prefix_le_of_integrable
      P ℱ D σk n hadapted hint hsubG hprefix τ
  exact BacklogCuratorGreedy.Tail.absolute_tail_of_mgf_pos P
    (fun ω => ∑ k ∈ Finset.Icc 1 n, D k ω) V t hVpos ht.le
    (hprefix n le_rfl) hmgf

end MostlyExplorationFree.GreedyBandit

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (σk : ℕ → ℝ) (n : ℕ)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ k] (D k))
    (hint : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ, Integrable (fun ω => Real.exp (τ * D k ω)) P)
    (hsubG : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      condExp (ℱ (k - 1)) P (fun ω => Real.exp (τ * D k ω))
        ≤ᵐ[P] fun _ => Real.exp (σk k ^ 2 * τ ^ 2 / 2))
    (t : ℝ) (ht : 0 < t) :
    (P {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|}).toReal
      ≤ 2 * Real.exp (-(t ^ 2 / (2 * ∑ k ∈ Finset.Icc 1 n, σk k ^ 2))) := by
  exact Prove2SwarmSubmission.MostlyExplorationFree.GreedyBandit.lemma_8 P ℱ D σk n hadapted hint hsubG t ht
