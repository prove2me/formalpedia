-- Prove2me | solution 1 for OAI.Balanced.robustDeletion_of_profileCounting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:25:19.557921+00:00
-- url     : https://prove2.me/submissions/c754b2c4-00a2-4a96-b682-a6c26ce2539f

import Mathlib
import Definitions.Def_OAIQ63Br004

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] {k : ℕ}

 theorem deletionEventProbability_mono (Q : PMF (DeletionSet F k))
    {E G : DeletionSet F k → Prop} (hEG : ∀ D, E D → G D) :
    deletionEventProbability Q E ≤ deletionEventProbability Q G := by
  classical
  unfold deletionEventProbability
  apply Finset.sum_le_sum
  intro D _
  by_cases he : E D
  · simp [he, hEG D he]
  · simp only [he, ite_false]
    split_ifs <;> positivity

theorem deletionEventProbability_le_uniform {K : ℝ} (Q : PMF (DeletionSet F k))
    (hdom : DeletionDominated k K Q) (E : DeletionSet F k → Prop) :
    deletionEventProbability Q E ≤
      Real.exp (K * (Fintype.card F : ℝ)) *
        (deletionEventCard E : ℝ) / (Fintype.card (DeletionSet F k) : ℝ) := by
  classical
  calc
    deletionEventProbability Q E ≤
        ∑ D : DeletionSet F k, if E D then
          Real.exp (K * (Fintype.card F : ℝ)) * uniformDeletionMass (F := F) k
        else 0 := by
      unfold deletionEventProbability
      apply Finset.sum_le_sum
      intro D _
      split_ifs with h
      · exact hdom D
      · rfl
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, uniformDeletionMass]
      unfold deletionEventCard
      ring

theorem deletionEventProbability_or_le (Q : PMF (DeletionSet F k))
    (E G : DeletionSet F k → Prop) :
    deletionEventProbability Q (fun D => E D ∨ G D) ≤
      deletionEventProbability Q E + deletionEventProbability Q G := by
  classical
  unfold deletionEventProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro D _
  by_cases he : E D <;> by_cases hg : G D <;> simp [he, hg]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_ExponentialDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace BalancedRyser

theorem tendsto_exp_linear_mul_exp_neg_mul_log
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℕ => Real.exp (C * q) *
      Real.exp (-c * q * Real.log q)) atTop (𝓝 0) := by
  have hn : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun q : ℕ => c * Real.log q + (-C)) atTop atTop :=
    ((Real.tendsto_log_atTop.comp hn).const_mul_atTop hc).atTop_add
      tendsto_const_nhds
  have hp := hn.atTop_mul_atTop₀ hl
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [← Real.exp_add]
  congr 1
  simp only [Function.comp_apply]
  ring

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem uniformDeletionVanishing_of_superexponential_count
    (k : ℕ) (K : ℝ)
    (E : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    {b : ℝ} (hb : 0 < b)
    (hcount : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        (deletionEventCard (E F) : ℝ) / (Fintype.card (DeletionSet F k) : ℝ) ≤
          Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F))) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  have ht := BalancedRyser.tendsto_exp_linear_mul_exp_neg_mul_log K hb
  have hsmall : ∀ᶠ q : ℕ in atTop,
      Real.exp (K * q) * Real.exp (-b * q * Real.log q) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hsmall
  obtain ⟨N₀, hN₀⟩ := hcount
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk Q hdom
  have hn₀ : N₀ ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hn₁ : N₁ ≤ Fintype.card F := (le_max_right _ _).trans hN
  calc
    deletionEventProbability Q (E F) ≤
        Real.exp (K * (Fintype.card F : ℝ)) * (deletionEventCard (E F) : ℝ) /
          (Fintype.card (DeletionSet F k) : ℝ) :=
      deletionEventProbability_le_uniform Q hdom (E F)
    _ = Real.exp (K * (Fintype.card F : ℝ)) *
        ((deletionEventCard (E F) : ℝ) / (Fintype.card (DeletionSet F k) : ℝ)) := by
      ring
    _ ≤ Real.exp (K * (Fintype.card F : ℝ)) *
        Real.exp (-b * (Fintype.card F : ℝ) * Real.log (Fintype.card F)) :=
      mul_le_mul_of_nonneg_left (hN₀ F hn₀ hk) (Real.exp_nonneg _)
    _ < ε := hN₁ (Fintype.card F) hn₁

theorem uniformDeletionVanishing_mono
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hEG : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ D, E F D → G F D)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  obtain ⟨N, hN⟩ := hG ε hε
  refine ⟨N, ?_⟩
  intro F _ _ _ hn hk Q hdom
  exact (deletionEventProbability_mono Q (hEG F)).trans_lt (hN F hn hk Q hdom)

theorem uniformDeletionVanishing_eventually_mono
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hEG : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → ∀ D, E F D → G F D)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K E := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hEG
  obtain ⟨N₁, hN₁⟩ := hG ε hε
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hn hk Q hdom
  exact (deletionEventProbability_mono Q
    (hN₀ F ((le_max_left _ _).trans hn))).trans_lt
      (hN₁ F ((le_max_right _ _).trans hn) hk Q hdom)

theorem uniformDeletionVanishing_or
    (k : ℕ) (K : ℝ)
    (E G : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hE : UniformDeletionVanishing k K E)
    (hG : UniformDeletionVanishing k K G) :
    UniformDeletionVanishing k K (fun F _ _ _ D => E F D ∨ G F D) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := hE (ε / 2) hhalf
  obtain ⟨N₁, hN₁⟩ := hG (ε / 2) hhalf
  refine ⟨max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk Q hdom
  have hn₀ : N₀ ≤ Fintype.card F := (le_max_left _ _).trans hN
  have hn₁ : N₁ ≤ Fintype.card F := (le_max_right _ _).trans hN
  have he := hN₀ F hn₀ hk Q hdom
  have hg := hN₁ F hn₁ hk Q hdom
  have hu := deletionEventProbability_or_le Q (E F) (G F)
  linarith

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfilePoissonLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped NNReal

namespace Balanced
open scoped _root_.Balanced

theorem profile_recurrence_factorial {p : ℕ → ℝ} {k : ℝ}
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = k * p n) (n : ℕ) :
    p n = p 0 * k ^ n / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      p (n + 1) = k * p n / (n + 1 : ℝ) := by
        apply (eq_div_iff hn).2
        nlinarith [hrec n]
      _ = p 0 * k ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        rw [ih, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp

theorem profile_recurrence_poisson {p : ℕ → ℝ} {k : ℝ}
    (hsum : HasSum p 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = k * p n) (n : ℕ) :
    p n = Real.exp (-k) * k ^ n / (n.factorial : ℝ) := by
  have hseries : HasSum p (p 0 * Real.exp k) := by
    have hexp : HasSum (fun i : ℕ => k ^ i / (i.factorial : ℝ)) (Real.exp k) := by
      simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp k
    have hp : p = fun i => p 0 * (k ^ i / (i.factorial : ℝ)) := by
      funext i
      rw [profile_recurrence_factorial hrec i]
      ring
    convert! hexp.mul_left (p 0) using 1
    all_goals try with_reducible_and_instances rfl
  have hzero : p 0 = Real.exp (-k) := by
    have hnorm : p 0 * Real.exp k = 1 := hseries.unique hsum
    calc
      p 0 = 1 / Real.exp k := (eq_div_iff (Real.exp_ne_zero k)).2 hnorm
      _ = Real.exp (-k) := by simp [Real.exp_neg]
  rw [profile_recurrence_factorial hrec n, hzero]

theorem profile_recurrence_eq_poissonMeasure {p : ℕ → ℝ} (k : ℝ≥0)
    (hsum : HasSum p 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = (k : ℝ) * p n) :
    ∀ n : ℕ, p n = (ProbabilityTheory.poissonMeasure k).real {n} := by
  intro n
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  exact profile_recurrence_poisson hsum hrec n

theorem profile_recurrence_factorization {p : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * p (i + 1) j = k * p i j)
    (i j : ℕ) : p i j = k ^ i / (i.factorial : ℝ) * p 0 j := by
  rw [profile_recurrence_factorial (p := fun n => p n j) (fun n => hrec n j) i]
  ring

end Balanced

end

section

namespace Balanced
open scoped _root_.Balanced
namespace ProfileVisibility

open MeasureTheory

theorem ae_eq_const_of_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ a)
    (hint : (∫ x, f x ∂ν) = ν.real Set.univ * a) :
    f =ᵐ[ν] fun _ => a := by
  apply (integral_eq_iff_of_ae_le hf (integrable_const a) hupper).mp
  simpa [integral_const] using hint

theorem ae_eq_const_of_probability_integral {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ a)
    (hint : (∫ x, f x ∂ν) = a) :
    f =ᵐ[ν] fun _ => a := by
  apply ae_eq_const_of_integral_eq hf hupper
  simpa using hint

theorem recurrence_of_invisible {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν]
    (P : ℕ → ℕ → ℝ) (X : Ω → ℕ → ℕ → ℝ) {k : ℝ}
    (hmass : ν.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, X x (i + 1) j ∂ν) =
      (i + 1 : ℝ) * P (i + 1) j)
    (hinvisible : ∀ i j : ℕ,
      (fun x => X x (i + 1) j) =ᵐ[ν] fun _ => P i j) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j := by
  intro i j
  calc
    (i + 1 : ℝ) * P (i + 1) j = ∫ x, X x (i + 1) j ∂ν := (hinc i j).symm
    _ = ∫ _x, P i j ∂ν := integral_congr_ae (hinvisible i j)
    _ = k * P i j := by simp [integral_const, hmass]

theorem null_of_vanishes {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : Ω → ℝ} {a : ℝ} {I : Set Ω}
    (ha : a ≠ 0) (hf : f =ᵐ[ν] fun _ => a)
    (hI : ∀ x ∈ I, f x = 0) : ν I = 0 := by
  have hnot : ∀ᵐ x ∂ν, x ∉ I := by
    filter_upwards [hf] with x hx hxI
    apply ha
    exact hx.symm.trans (hI x hxI)
  simpa using (ae_iff.mp hnot)

theorem full_mass_of_vanishes {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : Ω → ℝ} {a : ℝ} {I : Set Ω}
    (ha : a ≠ 0) (hf : f =ᵐ[ν] fun _ => a)
    (hI : ∀ x ∈ I, f x = 0) : ν Iᶜ = ν Set.univ := by
  apply measure_congr
  filter_upwards [hf] with x hx
  apply propext
  apply iff_true_intro
  intro hxI
  apply ha
  exact hx.symm.trans (hI x hxI)

theorem saturated_coordinate_visible {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} {μ : ℝ}
    {invisible : Set Ω} (hμ : 0 < μ)
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ μ)
    (hint : (∫ x, f x ∂ν) = μ)
    (hvanish : ∀ x ∈ invisible, f x = 0) :
    ν invisible = 0 ∧ ν invisibleᶜ = 1 := by
  have heq := ae_eq_const_of_probability_integral hf hupper hint
  refine ⟨null_of_vanishes (ne_of_gt hμ) heq hvanish, ?_⟩
  rw [full_mass_of_vanishes (ne_of_gt hμ) heq hvanish, measure_univ]

end ProfileVisibility
end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open MeasureTheory
open scoped NNReal

theorem deletionVisible_positive_of_not_poisson
    (k : ℕ) (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hmass : ν.real Set.univ = (k : ℝ))
    (hnormalized : HasSum (fun i : ℕ => P (i, 0)) 1)
    (hincidence : ∀ i : ℕ,
      (∫ x : Profile, x (i + 1, 0) ∂ν) = (i + 1 : ℝ) * P (i + 1, 0))
    (hnot : (fun i : ℕ => P (i, 0)) ≠ deletionPoissonMass k) :
    0 < ν.real (deletionVisible P) := by
  by_contra hpositive
  have hzero : ν.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpositive) measureReal_nonneg
  have hinvisible : ∀ᵐ x : Profile ∂ν, deletionInvisible P x := by
    apply ae_iff.mpr
    exact (measureReal_eq_zero_iff).mp hzero
  have hrec : ∀ i : ℕ, (i + 1 : ℝ) * P (i + 1, 0) = (k : ℝ) * P (i, 0) := by
    intro i
    calc
      (i + 1 : ℝ) * P (i + 1, 0) = ∫ x : Profile, x (i + 1, 0) ∂ν :=
        (hincidence i).symm
      _ = ∫ _x : Profile, P (i, 0) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hinvisible] with x hx
        simpa [deletionInvisible] using hx (i + 1) 0
      _ = (k : ℝ) * P (i, 0) := by
        rw [integral_const, hmass]
        rfl
  apply hnot
  funext i
  unfold deletionPoissonMass
  simpa only [NNReal.coe_natCast] using
    profile_recurrence_eq_poissonMeasure (p := fun n => P (n, 0)) (k : ℝ≥0)
      hnormalized hrec i

theorem deletionVisible_positive_of_tv
    (k : ℕ) (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hmass : ν.real Set.univ = (k : ℝ))
    (hnormalized : HasSum (fun i : ℕ => P (i, 0)) 1)
    (hincidence : ∀ i : ℕ,
      (∫ x : Profile, x (i + 1, 0) ∂ν) = (i + 1 : ℝ) * P (i + 1, 0))
    (htv : 0 < (1 / 2 : ℝ) * ∑' i : ℕ, |P (i, 0) - deletionPoissonMass k i|) :
    0 < ν.real (deletionVisible P) := by
  apply deletionVisible_positive_of_not_poisson k P ν hmass hnormalized hincidence
  intro heq
  have hpoint (i : ℕ) : P (i, 0) = deletionPoissonMass k i := congrFun heq i
  simp only [hpoint, sub_self, abs_zero, tsum_zero, mul_zero] at htv
  exact (lt_irrefl 0) htv

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_RobustDeletionAssembly
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem uniformDeletionVanishing_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K : ℝ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A) :
    UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C : Finset (Line F), A F D.val C) := by
  classical
  obtain ⟨b, hb, N, hN⟩ := hcounting k hk A hvalid hgap hvisible
  apply uniformDeletionVanishing_of_superexponential_count k K _ hb
  refine ⟨N, ?_⟩
  intro F _ _ _ hn hkq
  have h := hN F hn hkq
  unfold uniformProfileWitnessProbability at h
  unfold deletionEventCard
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 3
  apply Finset.filter_congr_decidable

theorem multiplicityFailureClass_valid (k : ℕ) (τ : ℝ) :
    ProfileClassValid k (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C h
  rcases h with ⟨hD, rfl, hτ⟩
  exact ⟨hD, by simp, by simp⟩

theorem multiplicityFailureClass_sizeGap (k : ℕ) (τ : ℝ) :
    ProfileClassSizeGap 1 (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C h
  exact Or.inl (by rw [h.2.1]; simp)

theorem multiplicityFailureClass_witness_iff
    (k : ℕ) (τ : ℝ) (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D : DeletionSet F k) :
    (∃ C : Finset (Line F), multiplicityFailureClass k τ F D.val C) ↔
      τ ≤ deletionMultiplicityTV k D.val := by
  constructor
  · rintro ⟨C, hD, hC, hτ⟩
    exact hτ
  · intro hτ
    exact ⟨∅, D.property, rfl, hτ⟩

theorem multiplicityVanishing_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K τ : ℝ)
    (hvisible : ProfileVisibleExcess (multiplicityFailureClass.{u} k τ)) :
    UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) := by
  have hclass := uniformDeletionVanishing_of_profileCounting hcounting k hk K
    (multiplicityFailureClass k τ) (multiplicityFailureClass_valid k τ)
    ⟨1, by norm_num, multiplicityFailureClass_sizeGap k τ⟩ hvisible
  apply uniformDeletionVanishing_mono k K _ _ _ hclass
  intro F _ _ _ D hD
  exact (multiplicityFailureClass_witness_iff k τ F D).2 hD

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SlowThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Balanced.SlowThreshold

theorem exists_monotone_slow_sequence (R : ℕ → ℕ → Prop)
    (hR : ∀ k, ∀ᶠ n in atTop, R n k) :
    ∃ t : ℕ → ℕ, Monotone t ∧ Tendsto t atTop atTop ∧
      ∀ᶠ n in atTop, ∀ k ≤ t n, R n k := by
  classical
  choose N hN using fun k => eventually_atTop.mp (hR k)
  let t : ℕ → ℕ := fun n => Nat.findGreatest (fun k => ∀ j ≤ k, N j ≤ n) n
  refine ⟨t, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Nat.findGreatest_mono (fun k hk j hj => (hk j hj).trans hmn) hmn
  · refine tendsto_atTop.2 ?_
    intro k
    have hfinite : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1), N j ≤ n :=
      (eventually_all_finset _).2 fun j _ => eventually_ge_atTop (N j)
    filter_upwards [hfinite, eventually_ge_atTop k] with n hn hkn
    exact Nat.le_findGreatest hkn (fun j hj => hn j (Finset.mem_range.mpr (by omega)))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hspec : ∀ j ≤ t n, N j ≤ n :=
      Nat.findGreatest_spec (P := fun k => ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
        (by intro j hj; have : j = 0 := Nat.eq_zero_of_le_zero hj; simpa [this] using hn)
    intro k hk
    exact hN k n (hspec k hk)

end Balanced.SlowThreshold

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_UniformDeletionTolerance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_uniform_deletion_tolerance (k : ℕ) (K : ℝ)
    (E : ℝ → ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      DeletionSet F k → Prop)
    (hE : ∀ δ : ℝ, 0 < δ → UniformDeletionVanishing k K (E δ)) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing k K
        (fun F _ _ _ D => E (ε (Fintype.card F)) F D) := by
  let R : ℕ → ℕ → Prop := fun n t =>
    ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      n ≤ Fintype.card F → k ≤ Fintype.card F →
      ∀ Q : PMF (DeletionSet F k), DeletionDominated k K Q →
        deletionEventProbability Q (E (1 / ((t : ℝ) + 1)) F) <
          1 / ((t : ℝ) + 1)
  have hR : ∀ t, ∀ᶠ n in atTop, R n t := by
    intro t
    have ht : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := hE _ ht _ ht
    filter_upwards [eventually_ge_atTop N] with n hn
    intro F _ _ _ hcard hk Q hQ
    exact hN F (hn.trans hcard) hk Q hQ
  obtain ⟨t, htmono, ht, hbound⟩ := SlowThreshold.exists_monotone_slow_sequence R hR
  let ε : ℕ → ℝ := fun q => 1 / ((t q : ℝ) + 1)
  have hpos : ∀ q, 0 < ε q := by intro q; dsimp [ε]; positivity
  have hanti : Antitone ε := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (htmono hmn) 1
  have hlim : Tendsto ε atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).comp ht
  refine ⟨ε, hpos, hanti, hlim, ?_⟩
  intro η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hbound.and (hlim.eventually_lt_const hη))
  refine ⟨N, ?_⟩
  intro F _ _ _ hcard hk Q hQ
  have hb := (hN (Fintype.card F) hcard).1 (t (Fintype.card F)) le_rfl
  exact (hb F le_rfl hk Q hQ).trans (hN (Fintype.card F) hcard).2

theorem exists_uniform_poisson_tolerance (k : ℕ) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val)) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D => ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val) :=
  exists_uniform_deletion_tolerance k K
    (fun τ _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) hTV

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineProfileIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FiniteProfile

open scoped BigOperators

theorem histogram_hasSum {α β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → β) :
    HasSum (fun b ↦ ((U.filter fun p ↦ f p = b).card : ℝ)) (U.card : ℝ) := by
  classical
  have h := hasSum_sum (s := U)
    (fun p _ ↦ hasSum_ite_eq' (f p) (1 : ℝ))
  simpa only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    using h

theorem weighted_histogram_hasSum {α β : Type*} [DecidableEq β]
    (U : Finset α) (f : α → β) (w : β → ℝ) :
    HasSum (fun b ↦ w b * ((U.filter fun p ↦ f p = b).card : ℝ))
      (∑ p ∈ U, w (f p)) := by
  classical
  have h := hasSum_sum (s := U)
    (fun p _ ↦ hasSum_ite_eq' (f p) (w (f p)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext b
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  simp only [Nat.cast_one, mul_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpb : f p = b <;> simp [hpb]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem incidence_count (D : Finset (Line F)) (U : Finset (Point F)) :
    (∑ l ∈ D, (U.filter fun p ↦ OnLine p l).card) =
      ∑ p ∈ U, deletionMultiplicity D p := by
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, deletionMultiplicity]
    using Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (fun l p ↦ OnLine p l) (s := D) (t := U)

theorem deletion_coordinate_incidence (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ D, ((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card) =
    i * (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card := by
  classical
  let U : Finset (Point F) := Finset.univ.filter fun p ↦
    deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j
  have heq (l : Line F) : (linePoints l).filter (fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j) =
      U.filter (fun p ↦ OnLine p l) := by
    ext p
    simp only [linePoints, U, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [heq]
  rw [incidence_count]
  calc
    (∑ p ∈ U, deletionMultiplicity D p) = ∑ _p ∈ U, i := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1
    _ = i * U.card := by simp [Nat.mul_comm]

theorem deletion_coordinate_incidence_real (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ D, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) =
    (i : ℝ) * (((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2) := by
  rw [← Finset.sum_div]
  have hc := deletion_coordinate_incidence D C i j
  have hcR : (∑ l ∈ D, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ)) =
    (i : ℝ) * ((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) := by
    exact_mod_cast hc
  rw [hcR]
  ring

theorem cover_coordinate_incidence_real (D C : Finset (Line F)) (i j : ℕ) :
    (∑ l ∈ C, (((linePoints l).filter fun p ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ)) / (Fintype.card F : ℝ) =
    (j : ℝ) * (((Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = i ∧ deletionMultiplicity C p = j).card : ℝ) /
        (Fintype.card F : ℝ) ^ 2) := by
  simpa only [and_comm] using deletion_coordinate_incidence_real C D j i

theorem empirical_multiplicity_hasSum (D : Finset (Line F)) :
    HasSum (empiricalMultiplicityMass D) 1 := by
  have h := (histogram_hasSum (Finset.univ : Finset (Point F))
    (deletionMultiplicity D)).div_const ((Fintype.card F : ℝ) ^ 2)
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Finset.univ : Finset (Point F)).card = (Fintype.card F) ^ 2 := by
    simp [Point, pow_two]
  rw [hcard, Nat.cast_pow, div_self (pow_ne_zero 2 hq)] at h
  exact h

theorem sum_multiplicity (D : Finset (Line F)) :
    (∑ p : Point F, deletionMultiplicity D p) = D.card * Fintype.card F := by
  rw [← incidence_count D Finset.univ]
  change (∑ l ∈ D, (linePoints l).card) = _
  simp [linePoints_card]

omit [Field F] in

theorem deletionSet_card {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    D.card = k * (Fintype.card F + 1) := by
  have h := Finset.sum_card_fiberwise_eq_card_filter D
    (Finset.univ : Finset (Direction F)) Prod.fst
  have heach (d : Direction F) : (D.filter fun l ↦ l.1 = d).card = k := hD d
  simpa [heach, Fintype.card_option, Nat.mul_comm] using h.symm

end Balanced.FiniteProfile

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_FiniteProfileIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem integral_empirical_profile {Line Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (D : Finset Line) (X : Line → Ω)
    (f : Ω → ℝ) (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, f ω ∂((ENNReal.ofReal q⁻¹) • ∑ l ∈ D, Measure.dirac (X l))) =
      q⁻¹ * ∑ l ∈ D, f (X l) := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hq)]
  rw [integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProfileEmpiricalIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
open scoped BigOperators ENNReal NNReal

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem lineProfile_mem_Icc (D C : Finset (Line F)) (l : Line F) (ij : ℕ × ℕ) :
    lineProfile D C l ij ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [lineProfile]
  refine ⟨by positivity, ?_⟩
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  apply (div_le_one hq).mpr
  have h := Finset.card_filter_le (linePoints l) (fun p ↦
    lineMultiplicity D p = ij.1 ∧ lineMultiplicity C p = ij.2)
  rw [linePoints_card] at h
  exact_mod_cast h

theorem coe_empiricalProfileMeasure (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile) =
      ENNReal.ofReal ((Fintype.card F : ℝ)⁻¹) •
        ∑ l ∈ E, Measure.dirac (lineProfile D C l) := by
  let weight : ℝ≥0 := ⟨(Fintype.card F : ℝ)⁻¹, by positivity⟩
  change weight •
    ((∑ l ∈ E, profileDirac (lineProfile D C l) : FiniteMeasure Profile) :
      Measure Profile) = _
  rw [FiniteMeasure.toMeasure_sum]
  rw [← Measure.coe_nnreal_smul, ENNReal.coe_nnreal_eq]
  rfl

theorem empiricalProfileMeasure_integral (D C E : Finset (Line F))
    (f : Profile → ℝ) :
    (∫ x, f x ∂(empiricalProfileMeasure D C E : Measure Profile)) =
      (Fintype.card F : ℝ)⁻¹ * ∑ l ∈ E, f (lineProfile D C l) := by
  rw [coe_empiricalProfileMeasure]
  exact integral_empirical_profile E (lineProfile D C) f _ (by positivity)

theorem empiricalProfileMeasure_mass (D C E : Finset (Line F)) :
    (empiricalProfileMeasure D C E : Measure Profile).real Set.univ =
      (E.card : ℝ) / (Fintype.card F : ℝ) := by
  have h := empiricalProfileMeasure_integral D C E (fun _ ↦ 1)
  simpa [div_eq_mul_inv, mul_comm] using h

theorem empiricalProfileMeasure_deletion_incidence (D C : Finset (Line F))
    (i j : ℕ) :
    (∫ x, x (i, j) ∂(empiricalProfileMeasure D C D : Measure Profile)) =
      (i : ℝ) * planeProfile D C (i, j) := by
  rw [empiricalProfileMeasure_integral, mul_comm, ← div_eq_mul_inv]
  exact deletion_coordinate_incidence_real D C i j

theorem empiricalProfileMeasure_cover_incidence (D C : Finset (Line F))
    (i j : ℕ) :
    (∫ x, x (i, j) ∂(empiricalProfileMeasure D C C : Measure Profile)) =
      (j : ℝ) * planeProfile D C (i, j) := by
  rw [empiricalProfileMeasure_integral, mul_comm, ← div_eq_mul_inv]
  exact cover_coordinate_incidence_real D C i j

theorem ae_empiricalProfileMeasure_of_forall (D C E : Finset (Line F))
    (Q : Profile → Prop) (hQ : ∀ l ∈ E, Q (lineProfile D C l)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C E : Measure Profile), Q x := by
  rw [coe_empiricalProfileMeasure]
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro l hl
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hQ l hl

theorem empiricalProfileMeasure_unit_coordinates (D C E : Finset (Line F)) :
    ∀ᵐ x ∂(empiricalProfileMeasure D C E : Measure Profile),
      ∀ ij, x ij ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_empiricalProfileMeasure_of_forall
  intro l _ ij
  exact lineProfile_mem_Icc D C l ij

theorem empiricalProfileMeasure_deletion_mass (D C : Finset (Line F))
    {k : ℕ} (hD : IsDeletionSet k D) :
    (empiricalProfileMeasure D C D : Measure Profile).real Set.univ =
      (k : ℝ) + (k : ℝ) * (Fintype.card F : ℝ)⁻¹ := by
  rw [empiricalProfileMeasure_mass, deletionSet_card hD]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp

theorem empiricalProfileMeasure_deletion_mass_tendsto
    {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
    [∀ n, DecidableEq (K n)]
    (D C : ∀ n, Finset (Line (K n))) {k : ℕ}
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n ↦ Fintype.card (K n)) atTop atTop) :
    Tendsto (fun n ↦ (empiricalProfileMeasure (D n) (C n) (D n) :
      Measure Profile).real Set.univ) atTop (𝓝 (k : ℝ)) := by
  have hqR : Tendsto (fun n ↦ (Fintype.card (K n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hinv : Tendsto (fun n ↦ (Fintype.card (K n) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hqR
  have ht := (tendsto_const_nhds (x := (k : ℝ))).add
    ((tendsto_const_nhds (x := (k : ℝ))).mul hinv)
  simpa only [empiricalProfileMeasure_deletion_mass (D _) (C _) (hD _),
    mul_zero, add_zero] using ht

end Balanced.FiniteProfile

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileWeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Balanced
open scoped _root_.Balanced

theorem profile_incidence_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    {pn : ℕ → ℝ} {p w : ℝ} (hp : Tendsto pn atTop (𝓝 p))
    (hinc : ∀ n, (∫ ω, f ω ∂(νn n : Measure Ω)) = w * pn n) :
    (∫ ω, f ω ∂(ν : Measure Ω)) = w * p := by
  have hleft := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) f
  have hright : Tendsto (fun n => ∫ ω, f ω ∂(νn n : Measure Ω)) atTop
      (𝓝 (w * p)) := by
    simpa only [hinc] using (tendsto_const_nhds.mul hp :
      Tendsto (fun n => w * pn n) atTop (𝓝 (w * p)))
  exact tendsto_nhds_unique hleft hright

theorem profile_zero_integral_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    (hzero : ∀ n, (∫ ω, f ω ∂(νn n : Measure Ω)) = 0) :
    (∫ ω, f ω ∂(ν : Measure Ω)) = 0 := by
  have h := profile_incidence_weak_limit hν f
    (pn := fun _ => 0) (p := 0) (w := 1) tendsto_const_nhds
    (fun n => by simpa using hzero n)
  simpa using h

theorem profile_zero_coordinate_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω}
    (hν : Tendsto νn atTop (𝓝 ν)) (f : Ω →ᵇ ℝ)
    (hnonneg : ∀ ω, 0 ≤ f ω)
    (hzero : ∀ n, ∀ᵐ ω ∂(νn n : Measure Ω), f ω = 0) :
    ∀ᵐ ω ∂(ν : Measure Ω), f ω = 0 := by
  apply (integral_eq_zero_iff_of_nonneg hnonneg (f.integrable (ν : Measure Ω))).mp
  apply profile_zero_integral_weak_limit hν f
  intro n
  rw [integral_congr_ae (hzero n)]
  simp

theorem profile_mass_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    {νn : ℕ → FiniteMeasure Ω} {ν : FiniteMeasure Ω} {m : ℝ}
    (hν : Tendsto νn atTop (𝓝 ν))
    (hm : Tendsto (fun n => (νn n : Measure Ω).real Set.univ) atTop (𝓝 m)) :
    (ν : Measure Ω).real Set.univ = m := by
  have h := profile_incidence_weak_limit hν
    (BoundedContinuousFunction.const Ω (1 : ℝ)) (w := 1) hm
    (fun n => by simp)
  simpa using h

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Balanced
open scoped _root_.Balanced

theorem clippedProfileCoordinate_nonneg (ij : ℕ × ℕ) (x : Profile) :
    0 ≤ clippedProfileCoordinate ij x := le_max_left _ _

theorem clippedProfileCoordinate_eq {ij : ℕ × ℕ} {x : Profile}
    (hzero : 0 ≤ x ij) (hone : x ij ≤ 1) :
    clippedProfileCoordinate ij x = x ij := by
  simp only [clippedProfileCoordinate_apply, min_eq_right hone, max_eq_right hzero]

theorem boundedProfile_coordinate_bounds {M : ℝ} {x : Profile}
    (hx : IsBoundedProfile M x) (ij : ℕ × ℕ) : 0 ≤ x ij ∧ x ij ≤ 1 := by
  refine ⟨hx.1 ij, ?_⟩
  have h := hx.2.1.summable.le_tsum ij (fun j _ => hx.1 j)
  simpa only [hx.2.1.tsum_eq] using h

theorem clippedProfileCoordinate_eq_of_bounded {M : ℝ} {x : Profile}
    (hx : IsBoundedProfile M x) (ij : ℕ × ℕ) :
    clippedProfileCoordinate ij x = x ij :=
  clippedProfileCoordinate_eq (boundedProfile_coordinate_bounds hx ij).1
    (boundedProfile_coordinate_bounds hx ij).2

lemma profileCoordinateDeviation_nonneg (ij : ℕ × ℕ) (x : Profile) :
    0 ≤ profileCoordinateDeviation ij x := le_min (by norm_num) (abs_nonneg _)

lemma profileCoordinateDeviation_zero_iff (ij : ℕ × ℕ) (x : Profile) :
    profileCoordinateDeviation ij x = 0 ↔ x ij = clippedProfileCoordinate ij x := by
  change min 1 |x ij - clippedProfileCoordinate ij x| = 0 ↔ _
  constructor
  · intro hz
    by_contra hne
    have hp : 0 < min 1 |x ij - clippedProfileCoordinate ij x| :=
      lt_min (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hne))
    linarith
  · intro h
    rw [sub_eq_zero.mpr h, abs_zero]
    norm_num

theorem profile_coordinate_bounds_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (ij : ℕ × ℕ) (hν : Tendsto νn atTop (𝓝 ν))
    (hb : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1) :
    ∀ᵐ x ∂(ν : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1 := by
  have hz : ∀ᵐ x ∂(ν : Measure Profile), profileCoordinateDeviation ij x = 0 := by
    apply profile_zero_coordinate_weak_limit hν (profileCoordinateDeviation ij)
      (profileCoordinateDeviation_nonneg ij)
    intro n
    filter_upwards [hb n] with x hx
    apply (profileCoordinateDeviation_zero_iff ij x).mpr
    exact (clippedProfileCoordinate_eq hx.1 hx.2).symm
  filter_upwards [hz] with x hx
  rw [(profileCoordinateDeviation_zero_iff ij x).mp hx]
  exact ⟨clippedProfileCoordinate_nonneg ij x,
    max_le (by norm_num) (min_le_left _ _)⟩

theorem ambient_profile_incidence_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    {Pn : ℕ → Profile} {P : Profile} {w : ℝ} (ij : ℕ × ℕ)
    (hν : Tendsto νn atTop (𝓝 ν)) (hP : Tendsto Pn atTop (𝓝 P))
    (hb : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1)
    (hinc : ∀ n, (∫ x, x ij ∂(νn n : Measure Profile)) = w * Pn n ij) :
    (∫ x, x ij ∂(ν : Measure Profile)) = w * P ij := by
  have heq (n : ℕ) : (∫ x, clippedProfileCoordinate ij x ∂(νn n : Measure Profile)) =
      ∫ x, x ij ∂(νn n : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [hb n] with x hx
    exact clippedProfileCoordinate_eq hx.1 hx.2
  have hlim : (∫ x, clippedProfileCoordinate ij x ∂(ν : Measure Profile)) =
      ∫ x, x ij ∂(ν : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [profile_coordinate_bounds_weak_limit ij hν hb] with x hx
    exact clippedProfileCoordinate_eq hx.1 hx.2
  rw [← hlim]
  apply profile_incidence_weak_limit hν (clippedProfileCoordinate ij)
    ((continuous_apply ij).tendsto P |>.comp hP)
  intro n
  rw [heq, hinc]
  rfl

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem hasSum_profile_integrals {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : ι → Ω → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (x i) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ x i ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun i => x i ω) 1) :
    HasSum (fun i => ∫ ω, x i ω ∂μ) (μ.real Set.univ) := by
  have hint : Integrable (fun ω => ∑' i, x i ω) μ := by
    apply (integrable_const (1 : ℝ)).congr
    filter_upwards [hnorm] with ω hω
    exact hω.tsum_eq.symm
  have h := hasSum_integral_of_dominated_convergence x hmeas
    (fun i => (hnonneg i).mono (fun ω hω => by simp [Real.norm_eq_abs, abs_of_nonneg hω]))
    (hnorm.mono (fun ω hω => hω.summable)) hint hnorm
  simpa using h

theorem hasSum_profile_weighted_mass {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : ι → Ω → ℝ) (P w : ι → ℝ)
    (hmeas : ∀ i, AEStronglyMeasurable (x i) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ x i ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun i => x i ω) 1)
    (hinc : ∀ i, ∫ ω, x i ω ∂μ = w i * P i) :
    HasSum (fun i => w i * P i) (μ.real Set.univ) := by
  apply (hasSum_profile_integrals μ x hmeas hnonneg hnorm).congr_fun
  intro i
  exact (hinc i).symm

theorem deletion_profile_second_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : (ℕ × ℕ) → Ω → ℝ)
    (P : ℕ × ℕ → ℝ) (c : ℝ)
    (hmeas : ∀ ij, AEStronglyMeasurable (x ij) μ)
    (hnonneg : ∀ ij, ∀ᵐ ω ∂μ, 0 ≤ x ij ω)
    (hnorm : ∀ᵐ ω ∂μ, HasSum (fun ij => x ij ω) 1)
    (hinc : ∀ ij, ∫ ω, x ij ω ∂μ = (ij.2 : ℝ) * P ij)
    (hmass : μ.real Set.univ = c) :
    HasSum (fun ij => (ij.2 : ℝ) * P ij) c := by
  rw [← hmass]
  exact hasSum_profile_weighted_mass μ x P (fun ij => (ij.2 : ℝ))
    hmeas hnonneg hnorm hinc

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ProfileLimitIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

variable {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
  [∀ n, DecidableEq (F n)]
  {D C : ∀ n, Finset (Line (F n))}
  {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}

theorem ProfileSequenceLimit.deletion_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij := by
  apply ambient_profile_incidence_weak_limit ij hlim.2.2.1 hlim.2.1
  · intro n
    filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
      (D n) (C n) (D n)] with x hx
    exact hx ij
  · intro n
    exact FiniteProfile.empiricalProfileMeasure_deletion_incidence
      (D n) (C n) ij.1 ij.2

theorem ProfileSequenceLimit.cover_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij := by
  apply ambient_profile_incidence_weak_limit ij hlim.2.2.2 hlim.2.1
  · intro n
    filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
      (D n) (C n) (C n)] with x hx
    exact hx ij
  · intro n
    exact FiniteProfile.empiricalProfileMeasure_cover_incidence
      (D n) (C n) ij.1 ij.2

theorem ProfileSequenceLimit.cover_mass
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νC : Measure Profile).real Set.univ = c := by
  apply profile_mass_weak_limit hlim.2.2.2
  simpa only [FiniteProfile.empiricalProfileMeasure_mass] using hlim.1

theorem ProfileSequenceLimit.deletion_mass {k : ℕ}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    (νD : Measure Profile).real Set.univ = (k : ℝ) := by
  exact profile_mass_weak_limit hlim.2.2.1
    (FiniteProfile.empiricalProfileMeasure_deletion_mass_tendsto D C hD hq)

end Balanced

namespace Balanced.FiniteProfile
open scoped _root_.Balanced

variable {K : ℕ → Type*} [∀ n, Field (K n)] [∀ n, Fintype (K n)]
  [∀ n, DecidableEq (K n)]
  {D C : ∀ n, Finset (Line (K n))}
  {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}

theorem profileSequenceLimit_deletion_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij :=
  hlim.deletion_incidence ij

theorem profileSequenceLimit_cover_incidence
    (hlim : ProfileSequenceLimit D C c P νD νC) (ij : ℕ × ℕ) :
    (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij :=
  hlim.cover_incidence ij

theorem profileSequenceLimit_deletion_mass {k : ℕ}
    (hD : ∀ n, IsDeletionSet k (D n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νD : Measure Profile).real Set.univ = k :=
  hlim.deletion_mass hD hq

theorem profileSequenceLimit_cover_mass
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νC : Measure Profile).real Set.univ = c := hlim.cover_mass

theorem profileSequenceLimit_mass_incidence (k : ℕ)
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (K n)) atTop atTop)
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (νD : Measure Profile).real Set.univ = k ∧
    (νC : Measure Profile).real Set.univ = c ∧
    (∀ ij, (∫ x, x ij ∂(νD : Measure Profile)) = (ij.1 : ℝ) * P ij) ∧
    (∀ ij, (∫ x, x ij ∂(νC : Measure Profile)) = (ij.2 : ℝ) * P ij) :=
  ⟨profileSequenceLimit_deletion_mass (fun n => (hpair n).1) hq hlim,
    profileSequenceLimit_cover_mass hlim,
    profileSequenceLimit_deletion_incidence hlim,
    profileSequenceLimit_cover_incidence hlim⟩

end Balanced.FiniteProfile

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Finset
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem tendsto_tsum_abs_sub_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => ∑' i, |p n i - q i|) l (𝓝 0) := by
  have hmin_summable (n : α) : Summable (fun i => min (p n i) (q i)) := by
    apply hq_sum.summable.of_nonneg_of_le
    · intro i
      exact le_min (hp_nonneg n i) (hq_nonneg i)
    · intro i
      exact min_le_right _ _
  have hmin : Tendsto (fun n => ∑' i, min (p n i) (q i)) l (𝓝 1) := by
    rw [← hq_sum.tsum_eq]
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      simpa using (hpoint i).min (tendsto_const_nhds (x := q i))
    · exact Filter.Eventually.of_forall fun n i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp_nonneg n i) (hq_nonneg i))]
        exact min_le_right _ _
  have hid (n : α) : (∑' i, |p n i - q i|) = 2 - 2 * ∑' i, min (p n i) (q i) := by
    calc
      (∑' i, |p n i - q i|) = ∑' i, (p n i + q i - 2 * min (p n i) (q i)) := by
        apply tsum_congr
        intro i
        rcases le_total (p n i) (q i) with h | h
        · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
          ring
        · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
          ring
      _ = 2 - 2 * ∑' i, min (p n i) (q i) := by
        rw [((hp_sum n).summable.add hq_sum.summable).tsum_sub
          ((hmin_summable n).mul_left 2),
          (hp_sum n).summable.tsum_add hq_sum.summable, tsum_mul_left,
          (hp_sum n).tsum_eq, hq_sum.tsum_eq]
        norm_num
  simp_rw [hid]
  have hlim := (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hmin)
  simpa using hlim

theorem profile_tail_le_of_moment
    {ι : Type*} (w : ι → ℕ) (p : ι → ℝ) (M : ℝ) (B : ℕ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (hws : Summable (fun i => (w i : ℝ) * p i))
    (hM : (∑' i, (w i : ℝ) * p i) ≤ M) :
    (∑' i : {i // B < w i}, p i) ≤ M / (B + 1 : ℝ) := by
  have hB : (0 : ℝ) < B + 1 := by positivity
  apply (le_div_iff₀ hB).2
  rw [← tsum_mul_right]
  calc
    (∑' i : {i // B < w i}, p i * (B + 1 : ℝ)) ≤
        ∑' i : {i // B < w i}, (w i : ℝ) * p i := by
      apply Summable.tsum_le_tsum
      · intro i
        have hi : (B + 1 : ℝ) ≤ (w i : ℝ) := by exact_mod_cast i.property
        nlinarith [hp i]
      · exact (hs.subtype _).mul_right _
      · exact hws.subtype _
    _ ≤ ∑' i, (w i : ℝ) * p i := by
      exact Summable.tsum_subtype_le _ _ (fun i => mul_nonneg (Nat.cast_nonneg _) (hp i)) hws
    _ ≤ M := hM

theorem hasSum_one_of_tendsto_of_tight
    {ι α : Type*} {l : Filter α} [l.NeBot]
    {p : α → ι → ℝ} {q : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hp_sum : ∀ n, HasSum (p n) 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ n, 1 - ε ≤ ∑ i ∈ s, p n i) :
    HasSum q 1 := by
  have hq_nonneg (i : ι) : 0 ≤ q i :=
    ge_of_tendsto (hpoint i) (Filter.Eventually.of_forall fun n => hp_nonneg n i)
  have hfinite (s : Finset ι) : ∑ i ∈ s, q i ≤ 1 := by
    apply le_of_tendsto (tendsto_finsetSum s fun i _ => hpoint i)
    exact Filter.Eventually.of_forall fun n => by
      simpa only [(hp_sum n).tsum_eq] using
        (hp_sum n).summable.sum_le_tsum s (fun i _ => hp_nonneg n i)
  have hq_summable : Summable q := summable_of_sum_le hq_nonneg hfinite
  have hq_le : (∑' i, q i) ≤ 1 := hq_summable.tsum_le_of_sum_le hfinite
  have hq_ge : 1 ≤ ∑' i, q i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨s, hs⟩ := htight ε hε
    have hlim : 1 - ε ≤ ∑ i ∈ s, q i :=
      ge_of_tendsto (tendsto_finsetSum s fun i _ => hpoint i)
        (Filter.Eventually.of_forall hs)
    have hsum := hq_summable.sum_le_tsum s (fun i _ => hq_nonneg i)
    linarith
  simpa only [le_antisymm hq_le hq_ge] using hq_summable.hasSum

theorem profile_tight_of_moment
    {ι α : Type*} (w : ι → ℕ)
    (hfinite : ∀ B, Set.Finite {i | w i ≤ B})
    {p : α → ι → ℝ} {M : ℝ}
    (hp : ∀ n i, 0 ≤ p n i) (hs : ∀ n, HasSum (p n) 1)
    (hws : ∀ n, Summable (fun i => (w i : ℝ) * p n i))
    (hM : ∀ n, (∑' i, (w i : ℝ) * p n i) ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ n, 1 - ε ≤ ∑ i ∈ s, p n i := by
  classical
  intro ε hε
  obtain ⟨B, hB⟩ := exists_nat_gt (M / ε)
  let s := (hfinite B).toFinset
  have hset : (↑s : Set ι)ᶜ = {i | B < w i} := by
    ext i
    simp [s, not_le]
  have hratio : M / (B + 1 : ℝ) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < B + 1)).2
    have haux := (div_lt_iff₀ hε).1 hB
    nlinarith
  refine ⟨s, fun n => ?_⟩
  have htail := profile_tail_le_of_moment w (p n) M B (hp n)
    (hs n).summable (hws n) (hM n)
  have hsum := (hs n).summable.sum_add_tsum_compl (s := s)
  rw [hset, (hs n).tsum_eq] at hsum
  change (∑ i ∈ s, p n i) + (∑' i : {i // B < w i}, p n i) = 1 at hsum
  linarith

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_MultiplicityLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology NNReal

universe u

theorem tsum_abs_sub_distance_le {ι : Type*} {p q r : ι → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r) :
    |(∑' i, |p i - r i|) - (∑' i, |q i - r i|)| ≤ ∑' i, |p i - q i| := by
  have hpr := (hp.sub hr).abs
  have hqr := (hq.sub hr).abs
  have hdiff := (hpr.sub hqr).abs
  calc
    |(∑' i, |p i - r i|) - (∑' i, |q i - r i|)| =
        |∑' i, (|p i - r i| - |q i - r i|)| := by
      rw [hpr.tsum_sub hqr]
    _ ≤ ∑' i, abs (abs (p i - r i) - abs (q i - r i)) := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => |p i - r i| - |q i - r i|)
          (by simpa only [Real.norm_eq_abs] using hdiff))
    _ ≤ ∑' i, |p i - q i| := by
      apply Summable.tsum_le_tsum _ hdiff (hp.sub hq).abs
      intro i
      calc
        abs (abs (p i - r i) - abs (q i - r i)) ≤ |(p i - r i) - (q i - r i)| :=
          abs_abs_sub_abs_le_abs_sub _ _
        _ = |p i - q i| := by congr 1; ring

theorem tendsto_totalVariation_to_fixed
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q r : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hr : Summable r)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i))) :
    Tendsto (fun n => (1 / 2 : ℝ) * ∑' i, |p n i - r i|) l
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |q i - r i|)) := by
  have hraw : Tendsto (fun n => ∑' i, |p n i - r i|) l
      (𝓝 (∑' i, |q i - r i|)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (tendsto_tsum_abs_sub_of_probability_mass hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
    intro n
    simpa only [Real.norm_eq_abs] using
      tsum_abs_sub_distance_le (hp_sum n).summable hq_sum.summable hr
  exact tendsto_const_nhds.mul hraw

theorem deletionPoissonMass_hasSum (k : ℕ) : HasSum (deletionPoissonMass k) 1 := by
  change HasSum (fun n => (ProbabilityTheory.poissonMeasure (k : ℝ≥0)).real {n}) 1
  simp only [ProbabilityTheory.poissonMeasure_real_singleton]
  exact ProbabilityTheory.hasSum_one_poissonMeasure (k : ℝ≥0)

theorem empiricalMultiplicityMass_nonneg
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (i : ℕ) : 0 ≤ empiricalMultiplicityMass D i := by
  unfold empiricalMultiplicityMass
  positivity

theorem deletionMultiplicityTV_tendsto
    (k : ℕ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D : ∀ n, Finset (Line (F n)))
    (p : ℕ → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : HasSum p 1)
    (hpoint : ∀ i, Tendsto (fun n => empiricalMultiplicityMass (D n) i) atTop (𝓝 (p i))) :
    Tendsto (fun n => deletionMultiplicityTV k (D n)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' i, |p i - deletionPoissonMass k i|)) := by
  exact tendsto_totalVariation_to_fixed
    (fun n i => empiricalMultiplicityMass_nonneg (D n) i) hp_nonneg
    (fun n => FiniteProfile.empirical_multiplicity_hasSum (D n)) hp_sum
    (deletionPoissonMass_hasSum k).summable hpoint

theorem planeProfile_empty_cover_zero
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (i : ℕ) :
    planeProfile D ∅ (i, 0) = empiricalMultiplicityMass D i := by
  simp [planeProfile, lineMultiplicity, empiricalMultiplicityMass, deletionMultiplicity]
  rfl

theorem multiplicityFailureClass_limit_density_zero
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : c = 0 := by
  have hC (n : ℕ) : C n = ∅ := (hclass n).2.1
  have hratio : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 c) := by
    simpa only [hC, Finset.card_empty, Nat.cast_zero, zero_div] using hlim.1
  exact tendsto_nhds_unique hratio tendsto_const_nhds

theorem multiplicityFailureClass_limit_coordinates
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) (i : ℕ) :
    Tendsto (fun n => empiricalMultiplicityMass (D n) i) atTop (𝓝 (P (i, 0))) := by
  have hC (n : ℕ) : C n = ∅ := (hclass n).2.1
  have hcoord := (tendsto_pi_nhds.1 hlim.2.1) (i, 0)
  simpa only [hC, planeProfile_empty_cover_zero] using hcoord

theorem empiricalMultiplicityMass_firstMoment_hasSum
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) :
    HasSum (fun i : ℕ => (i : ℝ) * empiricalMultiplicityMass D i)
      ((D.card : ℝ) / (Fintype.card F : ℝ)) := by
  have h := (FiniteProfile.weighted_histogram_hasSum
    (Finset.univ : Finset (Point F)) (deletionMultiplicity D) (fun i : ℕ => (i : ℝ))).div_const
      ((Fintype.card F : ℝ) ^ 2)
  have hs : (∑ p : Point F, (deletionMultiplicity D p : ℝ)) =
      (D.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast FiniteProfile.sum_multiplicity D
  rw [hs] at h
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  convert! h using 1
  · funext i
    unfold empiricalMultiplicityMass
    ring
  · field_simp

theorem empiricalMultiplicityMass_mean_le
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    {k : ℕ} {D : Finset (Line F)} (hD : IsDeletionSet k D) :
    (∑' i : ℕ, (i : ℝ) * empiricalMultiplicityMass D i) ≤ 2 * (k : ℝ) := by
  rw [(empiricalMultiplicityMass_firstMoment_hasSum D).tsum_eq]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hqpos : (0 : ℝ) < Fintype.card F := by linarith
  have hcard : (D.card : ℝ) = (k : ℝ) * (Fintype.card F + 1) := by
    exact_mod_cast FiniteProfile.deletionSet_card hD
  rw [hcard, div_le_iff₀ hqpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem multiplicityFailureClass_limit_probability
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ i : ℕ, 0 ≤ P (i, 0)) ∧ HasSum (fun i : ℕ => P (i, 0)) 1 := by
  have hpoint := multiplicityFailureClass_limit_coordinates k τ D C hclass hlim
  have hnonneg (n i : ℕ) : 0 ≤ empiricalMultiplicityMass (D n) i :=
    empiricalMultiplicityMass_nonneg (D n) i
  have hnorm (n : ℕ) : HasSum (empiricalMultiplicityMass (D n)) 1 :=
    FiniteProfile.empirical_multiplicity_hasSum (D n)
  have hmoment (n : ℕ) : Summable (fun i : ℕ => (i : ℝ) * empiricalMultiplicityMass (D n) i) :=
    (empiricalMultiplicityMass_firstMoment_hasSum (D n)).summable
  have hbound (n : ℕ) :
      (∑' i : ℕ, (i : ℝ) * empiricalMultiplicityMass (D n) i) ≤ 2 * (k : ℝ) :=
    empiricalMultiplicityMass_mean_le (hclass n).1
  have htight := profile_tight_of_moment (fun i : ℕ => i)
    (fun B => Set.finite_Iic B) hnonneg hnorm hmoment hbound
  exact ⟨fun i => ge_of_tendsto (hpoint i) (Eventually.of_forall fun n => hnonneg n i),
    hasSum_one_of_tendsto_of_tight hnonneg hnorm hpoint htight⟩

theorem multiplicityFailureClass_limit_tv
    (k : ℕ) (τ : ℝ) {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, multiplicityFailureClass k τ (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    τ ≤ (1 / 2 : ℝ) * ∑' i : ℕ, |P (i, 0) - deletionPoissonMass k i| := by
  obtain ⟨hp0, hpsum⟩ := multiplicityFailureClass_limit_probability k τ D C hclass hlim
  have hp := multiplicityFailureClass_limit_coordinates k τ D C hclass hlim
  exact ge_of_tendsto (deletionMultiplicityTV_tendsto k D (fun i => P (i, 0)) hp0 hpsum hp)
    (Eventually.of_forall fun n => (hclass n).2.2)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_PoissonProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace PoissonProfile

theorem row_rigidity (p : ℕ → ℝ) (μ c : ℝ)
    (hpos : 0 < μ) (hc : c ≤ 1) (hp : ∀ n, 0 ≤ p n) (hp0 : p 0 = 0)
    (hsum : HasSum p μ) (hmoment : HasSum (fun n : ℕ => (n : ℝ) * p n) (c * μ)) :
    c = 1 ∧ p 1 = μ ∧ ∀ n : ℕ, n ≠ 1 → p n = 0 := by
  have hdom : ∀ n : ℕ, p n ≤ (n : ℝ) * p n := by
    intro n
    cases n with
    | zero => simp [hp0]
    | succ n =>
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [hp (n + 1), Nat.cast_nonneg (α := ℝ) n]
  have hle : μ ≤ c * μ := hasSum_le hdom hsum hmoment
  have hc1 : c = 1 := by nlinarith
  have hdif : HasSum (fun n : ℕ => (n : ℝ) * p n - p n) 0 := by
    simpa [hc1] using hmoment.sub hsum
  have hzero : ∀ n : ℕ, n ≠ 1 → p n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · simpa [hn0] using hp0
    have hn2 : 2 ≤ n := by omega
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hterm := le_hasSum hdif n (fun j _ => sub_nonneg.mpr (hdom j))
    nlinarith [hp n]
  refine ⟨hc1, ?_, hzero⟩
  calc
    p 1 = ∑' n, p n := (tsum_eq_single 1 hzero).symm
    _ = μ := hsum.tsum_eq

end PoissonProfile
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileVisibilityConcrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped NNReal

namespace Balanced
open scoped _root_.Balanced
namespace ProfileVisibility

theorem recurrence_of_zero_deletionVisible (P : Profile)
    (νD : Measure Profile) [IsFiniteMeasure νD] {k : ℝ}
    (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hzero : νD (deletionVisible P) = 0) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1, j) = k * P (i, j) := by
  have hinvis : ∀ᵐ x ∂νD, deletionInvisible P x := ae_iff.mpr hzero
  apply recurrence_of_invisible (fun i j => P (i, j)) (fun x i j => x (i, j)) hmass hinc
  intro i j
  filter_upwards [hinvis] with x hx
  simpa using hx (i + 1) j

theorem coverVisible_mass_one (P : Profile)
    (νC : Measure Profile) [IsProbabilityMeasure νC] {μ : ℝ}
    (hμ : 0 < μ) (hcorner : P (0, 0) = 0)
    (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ)
    (hint : (∫ x, x (0, 1) ∂νC) = μ) :
    νC.real (coverVisible P) = 1 := by
  have hzero : ∀ x ∈ {x : Profile | coverInvisible P x}, x (0, 1) = 0 := by
    intro x hx
    simpa [hcorner] using hx 0 1
  have hfull := (saturated_coordinate_visible hμ hf hupper hint hzero).2
  change νC.real ({x : Profile | coverInvisible P x}ᶜ) = 1
  simp [measureReal_def, hfull]

theorem deletionVisible_pos_of_uncovered (P : Profile)
    (νD : Measure Profile) [IsFiniteMeasure νD] {k : ℝ}
    (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hcorner : P (0, 0) = 0) (huncovered : 0 < ∑' i : ℕ, P (i, 0)) :
    0 < νD.real (deletionVisible P) := by
  by_contra hpos
  have hreal : νD.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpos) measureReal_nonneg
  have hzero : νD (deletionVisible P) = 0 :=
    (measureReal_eq_zero_iff (by finiteness)).mp hreal
  have hrec := recurrence_of_zero_deletionVisible P νD hmass hinc hzero
  have hz : ∀ i : ℕ, P (i, 0) = 0 := by
    intro i
    rw [profile_recurrence_factorization (p := fun i j => P (i, j)) hrec i 0,
      hcorner, mul_zero]
  have hsum : (∑' i : ℕ, P (i, 0)) = 0 := by simp only [hz, tsum_zero]
  rw [hsum] at huncovered
  exact lt_irrefl 0 huncovered

theorem visible_excess_of_cover_saturation (P : Profile)
    (νD νC : Measure Profile) [IsFiniteMeasure νD] [IsProbabilityMeasure νC]
    {k μ : ℝ} (hmass : νD.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hcorner : P (0, 0) = 0) (huncovered : 0 < ∑' i : ℕ, P (i, 0))
    (hμ : 0 < μ) (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ)
    (hint : (∫ x, x (0, 1) ∂νC) = μ) :
    1 < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  rw [coverVisible_mass_one P νC hμ hcorner hf hupper hint]
  linarith [deletionVisible_pos_of_uncovered P νD hmass hinc hcorner huncovered]

theorem zero_row_sum_of_coverInvisible (P x : Profile)
    (hP : Summable (fun j : ℕ => P (0, j))) (hx : coverInvisible P x) :
    (∑' j : ℕ, x (0, j)) = ∑' j : ℕ, P (0, j) := by
  have hzero : x (0, 0) = 0 := by simpa using hx 0 0
  have hshift : (fun j : ℕ => x (0, j + 1)) = fun j : ℕ => P (0, j) := by
    funext j
    simpa using hx 0 (j + 1)
  have htail : Summable (fun j : ℕ => x (0, j + 1)) := by rw [hshift]; exact hP
  have hs : Summable (fun j : ℕ => x (0, j)) := (summable_nat_add_iff 1).mp htail
  rw [hs.tsum_eq_zero_add, hzero, zero_add, hshift]

theorem coverVisible_full_of_row_deviation (P : Profile)
    (νC : Measure Profile) {μ lam : ℝ} (hlam : 0 < lam)
    (hP : Summable (fun j : ℕ => P (0, j)))
    (hrow : (∑' j : ℕ, P (0, j)) = μ)
    (hdev : ∀ᵐ x ∂νC, lam ≤ |(∑' j : ℕ, x (0, j)) - μ|) :
    νC.real (coverVisible P) = νC.real Set.univ := by
  have hvisible : ∀ᵐ x ∂νC, x ∈ coverVisible P := by
    filter_upwards [hdev] with x hx
    intro hinvisible
    have heq := zero_row_sum_of_coverInvisible P x hP hinvisible
    rw [heq, hrow, sub_self, abs_zero] at hx
    exact (not_le_of_gt hlam) hx
  have hmeas : νC (coverVisible P) = νC Set.univ := by
    apply measure_congr
    filter_upwards [hvisible] with x hx
    exact propext (iff_true_intro hx)
  exact congrArg ENNReal.toReal hmeas

end ProfileVisibility
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_NearCoverVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Balanced.NearCoverVisibility

theorem visible_excess_of_row_moments
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC] {k μ c δ : ℝ}
    (hμ : 0 < μ) (hδ : 0 < δ) (hc : c ≤ 1)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x : Profile, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hincC : (∫ x : Profile, x (0, 1) ∂νC) = P (0, 1))
    (hcorner : P (0, 0) = 0) (hPnonneg : ∀ j, 0 ≤ P (0, j))
    (hrow : HasSum (fun j : ℕ => P (0, j)) μ)
    (hmoment : HasSum (fun j : ℕ => (j : ℝ) * P (0, j)) (c * μ))
    (huncovered : δ ≤ ∑' i : ℕ, P (i, 0))
    (hf : Integrable (fun x : Profile => x (0, 1)) νC)
    (hsupport : ∀ᵐ x ∂νC, (∀ j, 0 ≤ x (0, j)) ∧
      Summable (fun j : ℕ => x (0, j)) ∧ (∑' j : ℕ, x (0, j)) = μ) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  obtain ⟨hc1, hp01, _⟩ := PoissonProfile.row_rigidity
    (fun j => P (0, j)) μ c hμ hc hPnonneg hcorner hrow hmoment
  have hreal : νC.real Set.univ = 1 := hmassC.trans hc1
  have hprob : IsProbabilityMeasure νC := by
    apply isProbabilityMeasure_iff.mpr
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top νC Set.univ) ENNReal.one_ne_top).mp
    simpa only [measureReal_def, ENNReal.toReal_one] using hreal
  let : IsProbabilityMeasure νC := hprob
  have hupper : ∀ᵐ x ∂νC, x (0, 1) ≤ μ := by
    filter_upwards [hsupport] with x hx
    rw [← hx.2.2]
    exact le_hasSum hx.2.1.hasSum 1 (fun j _ => hx.1 j)
  rw [hc1]
  exact ProfileVisibility.visible_excess_of_cover_saturation P νD νC
    hmassD hincD hcorner (lt_of_lt_of_le hδ huncovered) hμ hf hupper
    (hincC.trans hp01)

theorem nearCoverClass_valid (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) :
    ProfileClassValid k (NearCoverClass k δ ε) := by
  intro F _ _ _ D C h
  exact h.1

theorem nearCoverClass_of_badCoreCover (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {D : Finset (Line F)} (hD : IsDeletionSet k D) (hbad : BadCoreCover δ D)
    (hTV : deletionMultiplicityTV k D ≤ ε (Fintype.card F))
    (hocc : ((exceptionalOccupancyLines k (ε (Fintype.card F)) D).card : ℝ) ≤
      ε (Fintype.card F) * (Fintype.card F : ℝ)) :
    ∃ C, NearCoverClass k δ ε F D C := by
  obtain ⟨C, hdisj, hcard, hcover, hmiss⟩ := hbad
  exact ⟨C, ⟨hD, hdisj.symm, hcard⟩, hcover, hmiss, hTV, hocc⟩

end Balanced.NearCoverVisibility

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_ProfileOccupancy2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Balanced.FiniteProfile

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_uncoveredBy_iff (D : Finset (Line F)) (p : Point F) :
    p ∈ uncoveredBy D ↔ deletionMultiplicity D p = 0 := by
  simp [uncoveredBy, deletionMultiplicity, Finset.filter_eq_empty_iff]

theorem planeProfile_zero_row_hasSum (D C : Finset (Line F)) :
    HasSum (fun j ↦ planeProfile D C (0, j))
      (((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2) := by
  have h := (histogram_hasSum (uncoveredBy D) (deletionMultiplicity C)).div_const
    ((Fintype.card F : ℝ) ^ 2)
  have heq (j : ℕ) : (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j) =
      (uncoveredBy D).filter (fun p ↦ deletionMultiplicity C p = j) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_uncoveredBy_iff]
  change HasSum (fun j ↦
    (((Finset.univ.filter fun p : Point F ↦ deletionMultiplicity D p = 0 ∧
      deletionMultiplicity C p = j).card : ℝ) / (Fintype.card F : ℝ) ^ 2)) _
  simpa only [heq] using h

theorem planeProfile_zero_column_hasSum (D C : Finset (Line F)) :
    HasSum (fun i ↦ planeProfile D C (i, 0))
      (((uncoveredBy C).card : ℝ) / (Fintype.card F : ℝ) ^ 2) := by
  have h := planeProfile_zero_row_hasSum C D
  simpa only [planeProfile, and_comm] using h

theorem lineProfile_zero_row_hasSum (D C : Finset (Line F)) (l : Line F) :
    HasSum (fun j ↦ lineProfile D C l (0, j))
      ((((linePoints l) ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) := by
  have h := (histogram_hasSum (linePoints l ∩ uncoveredBy D)
    (deletionMultiplicity C)).div_const (Fintype.card F : ℝ)
  have heq (j : ℕ) : ((linePoints l).filter fun p ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = j) =
      (linePoints l ∩ uncoveredBy D).filter (fun p ↦ deletionMultiplicity C p = j) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter, mem_uncoveredBy_iff]
    tauto
  change HasSum (fun j ↦
    ((((linePoints l).filter fun p ↦ deletionMultiplicity D p = 0 ∧
      deletionMultiplicity C p = j).card : ℝ) / (Fintype.card F : ℝ))) _
  simpa only [heq] using h

theorem planeProfile_zero_zero_of_cover (D C : Finset (Line F))
    (hcover : CoversPoints C (uncoveredBy D)) : planeProfile D C (0, 0) = 0 := by
  have hempty : (Finset.univ.filter fun p : Point F ↦
      deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hD, hC⟩
    have hpD := (mem_uncoveredBy_iff D p).mpr hD
    obtain ⟨l, hl, hpl⟩ := hcover p hpD
    have hpos : 0 < deletionMultiplicity C p :=
      Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hpl⟩⟩
    omega
  change (((Finset.univ.filter fun p : Point F ↦
    deletionMultiplicity D p = 0 ∧ deletionMultiplicity C p = 0).card : ℝ) /
      (Fintype.card F : ℝ) ^ 2) = 0
  rw [hempty]
  simp

theorem covered_points_card_le (C : Finset (Line F)) (U : Finset (Point F))
    (hcover : CoversPoints C U) : U.card ≤ C.card * Fintype.card F := by
  calc
    U.card = ∑ _p ∈ U, 1 := by simp
    _ ≤ ∑ p ∈ U, deletionMultiplicity C p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨l, hl, hpl⟩ := hcover p hp
      exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hpl⟩⟩
    _ = ∑ l ∈ C, (U.filter fun p ↦ OnLine p l).card := (incidence_count C U).symm
    _ ≤ ∑ _l ∈ C, Fintype.card F := by
      apply Finset.sum_le_sum
      intro l hl
      rw [← linePoints_card l]
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    _ = C.card * Fintype.card F := by simp

theorem core_cover_normalized_card_le (D C : Finset (Line F))
    (hcover : CoversPoints C (uncoveredBy D)) :
    ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 ≤
      (C.card : ℝ) / (Fintype.card F : ℝ) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hR : ((uncoveredBy D).card : ℝ) ≤ (C.card : ℝ) * (Fintype.card F : ℝ) := by
    exact_mod_cast covered_points_card_le C (uncoveredBy D) hcover
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  convert! hR using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end Balanced.FiniteProfile

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_NearCoverFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal

namespace Balanced.NearCoverVisibility

theorem sum_le_tolerance_card_add_bad {α : Type*} [DecidableEq α]
    (C E : Finset α) (f : α → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hone : ∀ l ∈ C, f l ≤ 1)
    (hsmall : ∀ l ∈ C, l ∉ E → f l ≤ ε) :
    ∑ l ∈ C, f l ≤ ε * (C.card : ℝ) + (E.card : ℝ) := by
  have hp : ∀ l ∈ C, f l ≤ ε + if l ∈ E then 1 else 0 := by
    intro l hl
    by_cases he : l ∈ E
    · simp only [he, ↓reduceIte]
      linarith [hone l hl]
    · simpa only [he, ↓reduceIte, add_zero] using hsmall l hl he
  calc
    ∑ l ∈ C, f l ≤ ∑ l ∈ C, (ε + if l ∈ E then 1 else 0) :=
      Finset.sum_le_sum hp
    _ = ε * (C.card : ℝ) + ((C.filter fun l => l ∈ E).card : ℝ) := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one]
      ring
    _ ≤ ε * (C.card : ℝ) + (E.card : ℝ) := by
      gcongr
      exact fun l hl => (Finset.mem_filter.mp hl).2

theorem occupancy_deviation_le_one (k : ℕ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (l : Line F) :
    |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))| ≤ 1 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have ho : ((linePoints l ∩ uncoveredBy D).card : ℝ) /
      (Fintype.card F : ℝ) ≤ 1 := by
    apply (div_le_one hq).mpr
    exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left) |>.trans_eq
      (linePoints_card l))
  have hz : (0 : ℝ) ≤ ((linePoints l ∩ uncoveredBy D).card : ℝ) /
      (Fintype.card F : ℝ) := by positivity
  have hmu : Real.exp (-(k : ℝ)) ≤ 1 := by
    calc
      Real.exp (-(k : ℝ)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) k))
      _ = 1 := Real.exp_zero
  rw [abs_le]
  constructor <;> linarith [Real.exp_pos (-(k : ℝ))]

theorem empirical_absolute_row_deviation_le (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) (hDC : Disjoint D C) (hcard : C.card ≤ Fintype.card F)
    (hbad : ((exceptionalOccupancyLines k ε D).card : ℝ) ≤
      ε * (Fintype.card F : ℝ)) :
    (∫ x : Profile, |(∑' j : ℕ, x (0, j)) - Real.exp (-(k : ℝ))|
      ∂(empiricalProfileMeasure D C C : Measure Profile)) ≤ 2 * ε := by
  classical
  rw [FiniteProfile.empiricalProfileMeasure_integral]
  simp_rw [(FiniteProfile.lineProfile_zero_row_hasSum D C _).tsum_eq]
  let f : Line F → ℝ := fun l =>
    |(((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) -
      Real.exp (-(k : ℝ))|
  have hsum := sum_le_tolerance_card_add_bad C (exceptionalOccupancyLines k ε D)
    f hε (fun l _ => occupancy_deviation_le_one k D l) (by
      intro l hlC hlE
      apply le_of_lt
      apply lt_of_not_ge
      intro he
      apply hlE
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, he⟩
      intro hlD
      exact Finset.disjoint_left.mp hDC hlD hlC)
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcardR : (C.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hcard
  have htotal : ε * (C.card : ℝ) + ((exceptionalOccupancyLines k ε D).card : ℝ) ≤
      2 * ε * (Fintype.card F : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hcardR hε]
  change (Fintype.card F : ℝ)⁻¹ * (∑ l ∈ C, f l) ≤ _
  calc
    _ ≤ (Fintype.card F : ℝ)⁻¹ * (2 * ε * (Fintype.card F : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum.trans htotal) (inv_nonneg.mpr hq.le)
    _ = 2 * ε := by field_simp

theorem nearCoverClass_integral_abs_tendsto
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hεnonneg : ∀ n, 0 ≤ ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => ∫ x : Profile,
      |(∑' j : ℕ, x (0, j)) - Real.exp (-(k : ℝ))|
      ∂(empiricalProfileMeasure (D n) (C n) (C n) : Measure Profile))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => empirical_absolute_row_deviation_le k (hεnonneg _) (D n) (C n)
      (hclass n).1.2.1 (hclass n).1.2.2 (hclass n).2.2.2.2)
  simpa using (hε.comp hq).const_mul 2

theorem empiricalMultiplicityMass_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) : empiricalMultiplicityMass D 0 =
      ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
  have heq : (Finset.univ.filter fun p : Point F => deletionMultiplicity D p = 0) =
      uncoveredBy D := by
    ext p
    simp [FiniteProfile.mem_uncoveredBy_iff]
  unfold empiricalMultiplicityMass
  rw [heq]

theorem core_density_error_le_twice_tv (k : ℕ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) :
    |((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 -
      Real.exp (-(k : ℝ))| ≤ 2 * deletionMultiplicityTV k D := by
  have hp : HasSum (deletionPoissonMass k) 1 := by
    unfold deletionPoissonMass
    simp only [ProbabilityTheory.poissonMeasure_real_singleton]
    exact ProbabilityTheory.hasSum_one_poissonMeasure (k : ℝ≥0)
  have hs := ((FiniteProfile.empirical_multiplicity_hasSum D).summable.sub hp.summable).abs
  have hzero : deletionPoissonMass k 0 = Real.exp (-(k : ℝ)) := by
    simp [deletionPoissonMass, ProbabilityTheory.poissonMeasure_real_singleton]
  have h := hs.le_tsum 0 (fun i _ => abs_nonneg (empiricalMultiplicityMass D i -
    deletionPoissonMass k i))
  rw [empiricalMultiplicityMass_zero, hzero] at h
  unfold deletionMultiplicityTV
  linarith

theorem nearCoverClass_sizeGap (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ q, ε q ≤ Real.exp (-(k : ℝ)) / 4) :
    ProfileClassSizeGap (Real.exp (-(k : ℝ)) / 2) (NearCoverClass k δ ε) := by
  intro F _ _ _ D C h
  right
  have herr := core_density_error_le_twice_tv k D
  have htv := h.2.2.2.1
  have hcap := FiniteProfile.core_cover_normalized_card_le D C h.2.1
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hdensity : Real.exp (-(k : ℝ)) / 2 ≤
      ((uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ) ^ 2 := by
    have hlower := (abs_le.mp herr).1
    linarith [hε (Fintype.card F)]
  exact (le_div_iff₀ hq).mp (hdensity.trans hcap)

theorem nearCoverClass_core_density_tendsto
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => ((uncoveredBy (D n)).card : ℝ) /
      (Fintype.card (F n) : ℝ) ^ 2) atTop (𝓝 (Real.exp (-(k : ℝ)))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => 2 * ε (Fintype.card (F n))) atTop (𝓝 0) from
      by simpa using (hε.comp hq).const_mul 2)
  rw [Real.norm_eq_abs]
  exact (core_density_error_le_twice_tv k (D n)).trans
    (mul_le_mul_of_nonneg_left (hclass n).2.2.2.1 (by norm_num))

theorem nearCoverClass_limit_corner_budget
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ)
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : P (0, 0) = 0 ∧ c ≤ 1 := by
  constructor
  · have hcoord := hlim.2.1.apply_nhds (0, 0)
    have hz (n : ℕ) : planeProfile (D n) (C n) (0, 0) = 0 :=
      FiniteProfile.planeProfile_zero_zero_of_cover (D n) (C n) (hclass n).2.1
    simp only [hz] at hcoord
    exact tendsto_nhds_unique hcoord tendsto_const_nhds
  · apply le_of_tendsto hlim.1
    apply Eventually.of_forall
    intro n
    apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := F n))).mpr
    exact_mod_cast (hclass n).1.2.2

end Balanced.NearCoverVisibility

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMomentCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ProfileMomentCompactness
open scoped BigOperators
open Filter Topology

lemma weight_ge_of_not_mem_box {n : ℕ} {i : Index} (hi : i ∉ box n) :
    (n : ℝ) + 1 ≤ weight i := by
  simp only [box, Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hi
  unfold weight
  rcases hi with hi | hi
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh
  · have hh : n + 1 ≤ i.1 + i.2 := by omega
    exact_mod_cast hh

theorem finite_tail_bound (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M)
    (n : ℕ) (s : Finset Index) :
    ∑ i ∈ s \ box n, p i ≤ M / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  apply (le_div_iff₀ hn).2
  calc
    (∑ i ∈ s \ box n, p i) * ((n : ℝ) + 1) =
        ∑ i ∈ s \ box n, ((n : ℝ) + 1) * p i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ s \ box n, weight i * p i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (weight_ge_of_not_mem_box (Finset.mem_sdiff.mp hi).2) (hp i)
    _ ≤ M := hM _

theorem box_mass_lower (p : Index → ℝ) (M : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (hM : ∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) (n : ℕ) :
    1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i := by
  have htotal : ∑' i, p i ≤ (∑ i ∈ box n, p i) + M / ((n : ℝ) + 1) := by
    apply Real.tsum_le_of_sum_le hp
    intro s
    have ht := finite_tail_bound p M hp hM n s
    have hi : ∑ i ∈ s ∩ box n, p i ≤ ∑ i ∈ box n, p i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by
        intro i hi hni
        exact hp i)
    have he : (∑ i ∈ s ∩ box n, p i) + (∑ i ∈ s \ box n, p i) = ∑ i ∈ s, p i := by
      exact Finset.sum_inter_add_sum_sdiff s (box n) p
    linarith
  rw [hs.tsum_eq] at htotal
  linarith

theorem hasSum_one_of_box_lower (p : Index → ℝ) (M : ℝ)
    (_hM : 0 ≤ M) (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1)
    (hb : ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i) :
    HasSum p 1 := by
  have hsum : Summable p := summable_of_sum_le hp hs
  have hle : ∑' i, p i ≤ 1 := Real.tsum_le_of_sum_le hp hs
  have hge : 1 ≤ ∑' i, p i := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have hnp : 0 < (n : ℝ) + 1 := by positivity
    have hsmall : M / ((n : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hnp).2
      have hh : M < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
      nlinarith
    have hpart : ∑ i ∈ box n, p i ≤ ∑' i, p i :=
      hsum.sum_le_tsum (box n) (by intro i hi; exact hp i)
    linarith [hb n]
  simpa [le_antisymm hle hge] using hsum.hasSum

lemma profiles_eq_closed_constraints (M : ℝ) (hM : 0 ≤ M) :
    profiles M = {p | (∀ i, 0 ≤ p i) ∧
      (∀ s : Finset Index, ∑ i ∈ s, p i ≤ 1) ∧
      (∀ s : Finset Index, ∑ i ∈ s, weight i * p i ≤ M) ∧
      ∀ n : ℕ, 1 - M / ((n : ℝ) + 1) ≤ ∑ i ∈ box n, p i} := by
  ext p
  constructor
  · rintro ⟨hp, hs, hm⟩
    refine ⟨hp, ?_, hm, box_mass_lower p M hp hs hm⟩
    intro s
    calc
      ∑ i ∈ s, p i ≤ ∑' i, p i :=
        hs.summable.sum_le_tsum s (by intro i hi; exact hp i)
      _ = 1 := hs.tsum_eq
  · rintro ⟨hp, hs, hm, hb⟩
    exact ⟨hp, hasSum_one_of_box_lower p M hM hp hs hb, hm⟩

theorem isClosed_profiles (M : ℝ) (hM : 0 ≤ M) : IsClosed (profiles M) := by
  rw [profiles_eq_closed_constraints M hM]
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_apply i) continuous_const).inter ?_
  refine (isClosed_iInter fun s => isClosed_le
    (continuous_finsetSum s fun i hi => continuous_const.mul (continuous_apply i))
    continuous_const).inter ?_
  exact isClosed_iInter fun n => isClosed_le continuous_const
    (continuous_finsetSum (box n) fun i hi => continuous_apply i)

theorem isCompact_profiles (M : ℝ) (hM : 0 ≤ M) : IsCompact (profiles M) := by
  apply (isCompact_univ_pi fun _ : Index =>
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).of_isClosed_subset
    (isClosed_profiles M hM)
  intro p hp i hi
  refine ⟨hp.1 i, ?_⟩
  have hh := hp.2.1.summable.sum_le_tsum ({i} : Finset Index)
    (show ∀ j, j ∉ ({i} : Finset Index) → 0 ≤ p j from fun j hj => hp.1 j)
  simpa [hp.2.1.tsum_eq] using hh

end Balanced.ProfileMomentCompactness

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileAmbientCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.ProfileAmbientCompactness
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal

theorem boundedProfiles_eq (M : ℝ) :
    {p : Profile | IsBoundedProfile M p} = ProfileMomentCompactness.profiles M := by
  ext p
  rw [ProfileMomentCompactness.mem_profiles_iff]
  simp only [Set.mem_ofPred_eq, IsBoundedProfile, ProfileMomentCompactness.weight,
    Nat.cast_add]

theorem isCompact_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsCompact {p : Profile | IsBoundedProfile M p} := by
  rw [boundedProfiles_eq]
  exact ProfileMomentCompactness.isCompact_profiles M hM

theorem isClosed_boundedProfiles (M : ℝ) (hM : 0 ≤ M) :
    IsClosed {p : Profile | IsBoundedProfile M p} :=
  (isCompact_boundedProfiles M hM).isClosed

theorem boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {p : ℕ → Profile} {P : Profile}
    (hp : ∀ n, IsBoundedProfile M (p n)) (ht : Tendsto p atTop (𝓝 P)) :
    IsBoundedProfile M P :=
  (isClosed_boundedProfiles M hM).mem_of_tendsto ht (Eventually.of_forall hp)

theorem compact_support_of_tendsto
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hμ : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν)) :
    ν Kᶜ = 0 := by
  have hm : ∀ᶠ n in atTop, (μ n).mass ≤ ν.mass + 1 := by
    exact (ht.mass.eventually (eventually_lt_nhds (lt_add_one ν.mass))).mono
      (fun _ h => h.le)
  have hc := isCompact_setOfPred_finiteMeasure_le_of_isCompact (ν.mass + 1) hK
  have hmem : ν ∈ {η : FiniteMeasure E | η.mass ≤ ν.mass + 1 ∧ η Kᶜ = 0} := by
    apply hc.isClosed.mem_of_tendsto ht
    filter_upwards [hm] with n hn
    exact ⟨hn, hμ n⟩
  exact hmem.2

theorem boundedProfile_support_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ν {p | IsBoundedProfile M p}ᶜ = 0 :=
  compact_support_of_tendsto (isCompact_boundedProfiles M hM) hμ ht

theorem ae_boundedProfile_of_tendsto {M : ℝ} (hM : 0 ≤ M)
    {μ : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (hμ : ∀ n, μ n {p | IsBoundedProfile M p}ᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    ∀ᵐ p ∂ν.toMeasure, IsBoundedProfile M p := by
  apply ae_iff.mpr
  exact (FiniteMeasure.null_iff_toMeasure_null ν _).mp
    (boundedProfile_support_of_tendsto hM hμ ht)

theorem map_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure E)
    (hμ : μ Kᶜ = 0) :
    (μ.comap (Subtype.val : K → E)).map Subtype.val = μ := by
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
  rw [map_comap_subtype_coe hK.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    ((FiniteMeasure.null_iff_toMeasure_null μ Kᶜ).mp hμ)

end Balanced.ProfileAmbientCompactness

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileEmpiricalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.ProfileEmpiricalSupport
open MeasureTheory Filter Topology
open scoped NNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem empiricalProfileMeasure_compl_eq_zero
    (D C E : Finset (Line F)) {K : Set Profile} (hK : MeasurableSet K)
    (hE : ∀ l ∈ E, lineProfile D C l ∈ K) :
    empiricalProfileMeasure D C E Kᶜ = 0 := by
  rw [FiniteMeasure.null_iff_toMeasure_null]
  change (((Fintype.card F : ℝ≥0)⁻¹ •
    ∑ line ∈ E, profileDirac (lineProfile D C line) : FiniteMeasure Profile) :
      Measure Profile) Kᶜ = 0
  rw [FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_sum,
    Measure.smul_apply, Measure.finsetSum_apply]
  change (Fintype.card F : ℝ≥0)⁻¹ •
    (∑ line ∈ E, Measure.dirac (lineProfile D C line) Kᶜ) = 0
  have hz : ∑ l ∈ E, Measure.dirac (lineProfile D C l) Kᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [Measure.dirac_apply' _ hK.compl]
    simp [hE l hl]
  rw [hz]
  simp

theorem empiricalProfileMeasure_bounded_support
    (D C E : Finset (Line F)) {M : ℝ} (hM : 0 ≤ M)
    (hE : ∀ l ∈ E, IsBoundedProfile M (lineProfile D C l)) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile M p}ᶜ = 0 :=
  empiricalProfileMeasure_compl_eq_zero D C E
    (ProfileAmbientCompactness.isClosed_boundedProfiles M hM).measurableSet hE

theorem admissible_empirical_bounded_support
    (k : ℕ) (D C E : Finset (Line F)) (hD : IsDeletionSet k D)
    (hC : C.card ≤ Fintype.card F) :
    empiricalProfileMeasure D C E {p | IsBoundedProfile (2 * (k : ℝ) + 4) p}ᶜ = 0 :=
  empiricalProfileMeasure_bounded_support D C E (by positivity)
    (fun l _ => lineProfile_isBounded k D C l hD hC)

theorem profileSequenceLimit_bounded
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) :
    IsBoundedProfile (2 * (k : ℝ) + 4) P ∧
    (∀ᵐ p ∂νD.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) ∧
    (∀ᵐ p ∂νC.toMeasure, IsBoundedProfile (2 * (k : ℝ) + 4) p) := by
  have hM : 0 ≤ 2 * (k : ℝ) + 4 := by positivity
  refine ⟨ProfileAmbientCompactness.boundedProfile_of_tendsto hM
    (fun n => planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2)
    ht.2.1, ?_, ?_⟩
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (D n)
        (hpair n).1 (hpair n).2.2) ht.2.2.1
  · exact ProfileAmbientCompactness.ae_boundedProfile_of_tendsto hM
      (fun n => admissible_empirical_bounded_support k (D n) (C n) (C n)
        (hpair n).1 (hpair n).2.2) ht.2.2.2

end Balanced.ProfileEmpiricalSupport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology Classical

namespace Balanced.ProfileContinuity

theorem summable_mul_of_abs_le_one
    {ι : Type*} {p w : ι → ℝ} (hp : Summable p)
    (hw : ∀ i, |w i| ≤ 1) : Summable (fun i => p i * w i) := by
  apply hp.abs.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem abs_tsum_mul_sub_le_tsum_abs
    {ι : Type*} {p q w : ι → ℝ} (hp : Summable p) (hq : Summable q)
    (hw : ∀ i, |w i| ≤ 1) :
    |(∑' i, p i * w i) - ∑' i, q i * w i| ≤ ∑' i, |p i - q i| := by
  have hsub := summable_mul_of_abs_le_one (hp.sub hq) hw
  have hsubNorm : Summable (fun i => ‖(p i - q i) * w i‖) := by
    simpa only [Real.norm_eq_abs] using hsub.abs
  rw [← (summable_mul_of_abs_le_one hp hw).tsum_sub
    (summable_mul_of_abs_le_one hq hw)]
  simp_rw [← sub_mul]
  calc
    |∑' i, (p i - q i) * w i| ≤ ∑' i, ‖(p i - q i) * w i‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsubNorm
    _ ≤ ∑' i, |p i - q i| := by
      apply Summable.tsum_le_tsum _ hsubNorm (hp.sub hq).abs
      intro i
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)).trans_eq (mul_one _)

theorem tendsto_tsum_mul_of_probability_mass
    {ι α : Type*} {l : Filter α} {p : α → ι → ℝ} {q : ι → ℝ}
    {w : α → ι → ℝ} {v : ι → ℝ}
    (hp_nonneg : ∀ n i, 0 ≤ p n i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∀ n, HasSum (p n) 1) (hq_sum : HasSum q 1)
    (hpoint : ∀ i, Tendsto (fun n => p n i) l (𝓝 (q i)))
    (hweight : ∀ i, Tendsto (fun n => w n i) l (𝓝 (v i)))
    (hbound : ∀ n i, |w n i| ≤ 1) :
    Tendsto (fun n => ∑' i, p n i * w n i) l (𝓝 (∑' i, q i * v i)) := by
  have hfixed : Tendsto (fun n => ∑' i, q i * w n i)
      l (𝓝 (∑' i, q i * v i)) := by
    apply tendsto_tsum_of_dominated_convergence hq_sum.summable
    · intro i
      exact (hweight i).const_mul (q i)
    · exact Eventually.of_forall fun n i => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq_nonneg i)]
        exact (mul_le_mul_of_nonneg_left (hbound n i) (hq_nonneg i)).trans_eq (mul_one _)
  have hdiff : Tendsto (fun n => (∑' i, p n i * w n i) - ∑' i, q i * w n i)
      l (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => ?_) (tendsto_tsum_abs_sub_of_probability_mass
        hp_nonneg hq_nonneg hp_sum hq_sum hpoint)
    simpa only [Real.norm_eq_abs] using
      abs_tsum_mul_sub_le_tsum_abs (hp_sum n).summable hq_sum.summable (hbound n)
  simpa only [sub_add_cancel, zero_add] using hdiff.add hfixed

theorem continuous_tsum_mul_of_probability_mass
    {ι X : Type*} [TopologicalSpace X] {p w : X → ι → ℝ}
    (hp_nonneg : ∀ x i, 0 ≤ p x i) (hp_sum : ∀ x, HasSum (p x) 1)
    (hp_cont : ∀ i, Continuous (fun x => p x i))
    (hw_cont : ∀ i, Continuous (fun x => w x i))
    (hw_bound : ∀ x i, |w x i| ≤ 1) :
    Continuous (fun x => ∑' i, p x i * w x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact tendsto_tsum_mul_of_probability_mass hp_nonneg (hp_nonneg x)
    hp_sum (hp_sum x) (fun i => (hp_cont i).continuousAt)
    (fun i => (hw_cont i).continuousAt) hw_bound

end Balanced.ProfileContinuity

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileMarginalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped Topology

namespace Balanced.ProfileContinuity

theorem row_sum_eq_selected_sum (p : Profile) (hp : Summable p) (i : ℕ) :
    (∑' j, p (i, j)) = ∑' ij, p ij * (if ij.1 = i then 1 else 0) := by
  classical
  have hs := summable_mul_of_abs_le_one hp
    (w := fun ij => if ij.1 = i then 1 else 0) (by intro ij; split_ifs <;> norm_num)
  rw [hs.tsum_prod]
  simp only [mul_ite, mul_one, mul_zero]
  conv_rhs =>
    arg 1
    ext k
    rw [show (∑' j, if k = i then p (k, j) else 0) =
      if k = i then ∑' j, p (k, j) else 0 by
        by_cases hk : k = i <;> simp [hk]]
  simp

theorem continuous_profile_row_sum {S : Set Profile}
    (hnonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hsum : ∀ p ∈ S, HasSum p 1) (i : ℕ) :
    Continuous (fun p : S => ∑' j, p.val (i, j)) := by
  classical
  have hc : Continuous (fun p : S =>
      ∑' ij, p.val ij * (if ij.1 = i then 1 else 0)) := by
    apply continuous_tsum_mul_of_probability_mass
    · exact fun p => hnonneg p.val p.property
    · exact fun p => hsum p.val p.property
    · intro ij
      exact (continuous_apply ij).comp continuous_subtype_val
    · intro ij
      exact continuous_const
    · intro p ij
      split_ifs <;> norm_num
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact row_sum_eq_selected_sum p.val (hsum p.val p.property).summable i

theorem continuous_boundedProfile_row_sum (M : ℝ) (i : ℕ) :
    Continuous (fun p : {p : Profile | IsBoundedProfile M p} =>
      ∑' j : ℕ, p.val (i, j)) :=
  continuous_profile_row_sum (fun _ hp => hp.1) (fun _ hp => hp.2.1) i

theorem continuous_profile_column_sum {S : Set Profile}
    (hnonneg : ∀ p ∈ S, ∀ ij, 0 ≤ p ij)
    (hsum : ∀ p ∈ S, HasSum p 1) (j : ℕ) :
    Continuous (fun p : S => ∑' i, p.val (i, j)) := by
  classical
  have hc : Continuous (fun p : S =>
      ∑' ij, p.val ij * (if ij.2 = j then 1 else 0)) := by
    apply continuous_tsum_mul_of_probability_mass
    · exact fun p => hnonneg p.val p.property
    · exact fun p => hsum p.val p.property
    · intro ij
      exact (continuous_apply ij).comp continuous_subtype_val
    · intro ij
      exact continuous_const
    · intro p ij
      split_ifs <;> norm_num
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  have hs := summable_mul_of_abs_le_one (hsum p.val p.property).summable
    (w := fun ij => if ij.2 = j then 1 else 0) (by intro ij; split_ifs <;> norm_num)
  rw [hs.tsum_prod]
  simp

theorem continuous_boundedProfile_column_sum (M : ℝ) (j : ℕ) :
    Continuous (fun p : {p : Profile | IsBoundedProfile M p} =>
      ∑' i : ℕ, p.val (i, j)) :=
  continuous_profile_column_sum (fun _ hp => hp.1) (fun _ hp => hp.2.1) j

theorem measurable_profile_row_sum (i : ℕ) :
    Measurable (fun p : Profile => ∑' j : ℕ, p (i, j)) :=
  Measurable.tsum (fun j => measurable_pi_apply (i, j))

end Balanced.ProfileContinuity

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_ProfileShrinkingExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Balanced.ProfileShrinkingExceptions
open Filter Topology TopologicalSpace MeasureTheory
open scoped NNReal BoundedContinuousFunction

theorem tendsto_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [NormalSpace E] {K : Set E} (hK : IsClosed K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hs : ∀ n, μ n Kᶜ = 0) (hsν : ν Kᶜ = 0)
    (ht : Tendsto μ atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).comap (Subtype.val : K → E)) atTop
      (𝓝 (ν.comap (Subtype.val : K → E))) := by
  have hi := FiniteMeasure.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
    (Subtype.val : K → E) (Topology.IsClosedEmbedding.subtypeVal hK)
  apply hi.tendsto_nhds_iff.mpr
  have he : (fun η : FiniteMeasure K => η.map (Subtype.val : K → E)) ∘
      (fun n => (μ n).comap (Subtype.val : K → E)) = μ := by
    funext n
    exact ProfileAmbientCompactness.map_comap_subtype hK (μ n) (hs n)
  rw [he, ProfileAmbientCompactness.map_comap_subtype hK ν hsν]
  exact ht

theorem integral_comap_subtype
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {K : Set E} (hK : IsClosed K) (μ : FiniteMeasure E) (hs : μ Kᶜ = 0)
    (f : E → ℝ) (hf : Measurable f) :
    (∫ x : K, f x ∂(μ.comap (Subtype.val : K → E)).toMeasure) =
      ∫ x, f x ∂μ.toMeasure := by
  have hm := congrArg FiniteMeasure.toMeasure
    (ProfileAmbientCompactness.map_comap_subtype hK μ hs)
  rw [FiniteMeasure.toMeasure_map] at hm
  rw [← hm, integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]

theorem ae_eq_const_of_integral_tendsto_zero_on_compact
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [PseudoMetrizableSpace E]
    {K : Set E} (hK : IsCompact K)
    {μ : ℕ → FiniteMeasure E} {ν : FiniteMeasure E}
    (hs : ∀ n, μ n Kᶜ = 0) (ht : Tendsto μ atTop (𝓝 ν))
    (f : E → ℝ) (hf : Measurable f)
    (hfc : Continuous (fun x : K => f x)) (a : ℝ)
    (hi : Tendsto (fun n => ∫ x, |f x - a| ∂(μ n).toMeasure) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν.toMeasure, f x = a := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ' : ℕ → FiniteMeasure K := fun n => (μ n).comap Subtype.val
  let ν' : FiniteMeasure K := ν.comap Subtype.val
  have hsν := ProfileAmbientCompactness.compact_support_of_tendsto hK hs ht
  have ht' : Tendsto μ' atTop (𝓝 ν') := tendsto_comap_subtype hK.isClosed hs hsν ht
  let g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => |f x - a|, (hfc.sub continuous_const).abs⟩
  have hi' : Tendsto (fun n => ∫ x, g x ∂(μ' n).toMeasure) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ x, g x ∂(μ' n).toMeasure) =
        ∫ x, |f x - a| ∂(μ n).toMeasure :=
      integral_comap_subtype hK.isClosed (μ n) (hs n) (fun x => |f x - a|)
        ((hf.sub measurable_const).abs)
    simpa only [he] using hi
  have hw := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp ht') g
  have hz : (∫ x, g x ∂ν'.toMeasure) = 0 := tendsto_nhds_unique hw hi'
  have hzero := (integral_eq_zero_iff_of_nonneg (fun (x : K) => abs_nonneg (f x - a))
    (g.integrable ν'.toMeasure)).mp hz
  have hsub : ∀ᵐ (x : K) ∂ν'.toMeasure, f x = a := by
    filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp (abs_eq_zero.mp hx)
  have hmap : ∀ᵐ x ∂(ν'.map (Subtype.val : K → E)).toMeasure, f x = a := by
    change ∀ᵐ x ∂Measure.map (Subtype.val : K → E) ν'.toMeasure, f x = a
    exact (MeasurableEmbedding.subtype_coe hK.isClosed.measurableSet).ae_map_iff.mpr hsub
  have hmapν : ν'.map (Subtype.val : K → E) = ν :=
    ProfileAmbientCompactness.map_comap_subtype hK.isClosed ν hsν
  rwa [hmapν] at hmap

theorem profileSequenceLimit_row_sum_eq_of_integral_tendsto_zero
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (ht : ProfileSequenceLimit D C c P νD νC) (a : ℝ)
    (hi : Tendsto (fun n => ∫ x, |(∑' j : ℕ, x (0,j)) - a|
      ∂(empiricalProfileMeasure (D n) (C n) (C n)).toMeasure) atTop (𝓝 0)) :
    ∀ᵐ x ∂νC.toMeasure, (∑' j : ℕ, x (0,j)) = a := by
  apply ae_eq_const_of_integral_tendsto_zero_on_compact
    (ProfileAmbientCompactness.isCompact_boundedProfiles (2 * (k : ℝ) + 4) (by positivity))
    (fun n => ProfileEmpiricalSupport.admissible_empirical_bounded_support
      k (D n) (C n) (C n) (hpair n).1 (hpair n).2.2) ht.2.2.2
    (fun x : Profile => ∑' j : ℕ, x (0,j))
    (ProfileContinuity.measurable_profile_row_sum 0)
    (ProfileContinuity.continuous_boundedProfile_row_sum (2 * (k : ℝ) + 4) 0) a hi

end Balanced.ProfileShrinkingExceptions

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_PoissonProfile2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace PoissonProfileSupport

theorem factorization {P : ℕ → ℝ} {k : ℝ}
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * P (n + 1) = k * P n) (n : ℕ) :
    P n = k ^ n / (Nat.factorial n : ℝ) * P 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
      apply (mul_left_cancel₀ hn)
      rw [hrec, ih, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        pow_succ]
      field_simp

theorem bivariate_factorization {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (i j : ℕ) :
    P i j = k ^ i / (Nat.factorial i : ℝ) * P 0 j :=
  factorization (P := fun n => P n j) (k := k) (fun n => hrec n j) i

theorem column_hasSum {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (j : ℕ) :
    HasSum (fun i => P i j) (Real.exp k * P 0 j) := by
  have he : HasSum (fun i : ℕ => k ^ i / (Nat.factorial i : ℝ)) (Real.exp k) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp k
  have hform : (fun i => P i j) =
      fun i => k ^ i / (Nat.factorial i : ℝ) * P 0 j :=
    funext (fun i => bivariate_factorization hrec i j)
  rw [hform]
  exact he.mul_right (P 0 j)

theorem weighted_sum_factorization {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ × ℕ => w p.2 * P p.1 p.2)) :
    (∑' p : ℕ × ℕ, w p.2 * P p.1 p.2) =
      Real.exp k * ∑' j : ℕ, w j * P 0 j := by
  calc
    (∑' p : ℕ × ℕ, w p.2 * P p.1 p.2) =
        ∑' i : ℕ, ∑' j : ℕ, w j * P i j := hs.tsum_prod
    _ = ∑' j : ℕ, ∑' i : ℕ, w j * P i j := hs.tsum_comm.symm
    _ = ∑' j : ℕ, w j * (Real.exp k * P 0 j) := by
      apply tsum_congr
      intro j
      rw [tsum_mul_left, (column_hasSum hrec j).tsum_eq]
    _ = ∑' j : ℕ, Real.exp k * (w j * P 0 j) := by
      apply tsum_congr
      intro j
      ring
    _ = Real.exp k * ∑' j : ℕ, w j * P 0 j := tsum_mul_left

theorem weighted_zero_row {P : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (w : ℕ → ℝ)
    (hs : Summable (fun p : ℕ × ℕ => w p.2 * P p.1 p.2)) :
    (∑' j : ℕ, w j * P 0 j) =
      Real.exp (-k) * ∑' p : ℕ × ℕ, w p.2 * P p.1 p.2 := by
  rw [weighted_sum_factorization hrec w hs, ← mul_assoc, ← Real.exp_add]
  simp

theorem first_moment_zero_row {P : ℕ → ℕ → ℝ} {k c : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j)
    (hmean : HasSum (fun p : ℕ × ℕ => (p.2 : ℝ) * P p.1 p.2) c) :
    (∑' j : ℕ, (j : ℝ) * P 0 j) = Real.exp (-k) * c := by
  rw [weighted_zero_row hrec (fun j => (j : ℝ)) hmean.summable, hmean.tsum_eq]

end PoissonProfileSupport
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_ProfileOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PoissonProfile

open MeasureTheory

theorem not_ae_above_mean_with_margin
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ (∀ᵐ x ∂ν, μ + ε ≤ f x) := by
  intro hhigh
  have h := integral_mono_ae (integrable_const (μ + ε)) hf hhigh
  simp only [integral_const, smul_eq_mul] at h
  rw [hmass, hmean] at h
  nlinarith [mul_pos hc hε]

theorem not_ae_below_mean_with_margin
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ (∀ᵐ x ∂ν, f x ≤ μ - ε) := by
  intro hlow
  have h := integral_mono_ae hf (integrable_const (μ - ε)) hlow
  simp only [integral_const, smul_eq_mul] at h
  rw [hmass, hmean] at h
  nlinarith [mul_pos hc hε]

theorem no_common_sign_deviation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ν : Measure Ω) [IsFiniteMeasure ν]
    {f : Ω → ℝ} {μ c ε : ℝ} (hf : Integrable f ν)
    (hmass : ν.real Set.univ = c) (hc : 0 < c) (hε : 0 < ε)
    (hmean : (∫ x, f x ∂ν) = μ * c) :
    ¬ ((∀ᵐ x ∂ν, μ + ε ≤ f x) ∨ (∀ᵐ x ∂ν, f x ≤ μ - ε)) := by
  rintro (hhigh | hlow)
  · exact not_ae_above_mean_with_margin ν hf hmass hc hε hmean hhigh
  · exact not_ae_below_mean_with_margin ν hf hmass hc hε hmean hlow

end Balanced.PoissonProfile

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OccupancyVisibility

open MeasureTheory

theorem deletionVisible_pos_of_common_sign
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC]
    {k c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hmean : HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c)
    (hf : Integrable (fun x : Profile => ∑' j : ℕ, x (0, j)) νC)
    (hincC : (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂νC) =
      ∑' j : ℕ, (j : ℝ) * P (0, j))
    (hdev : (∀ᵐ x : Profile ∂νC, Real.exp (-k) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
      (∀ᵐ x : Profile ∂νC, (∑' j : ℕ, x (0, j)) ≤ Real.exp (-k) - lam)) :
    0 < νD.real (deletionVisible P) := by
  by_contra hpos
  have hreal : νD.real (deletionVisible P) = 0 :=
    le_antisymm (le_of_not_gt hpos) measureReal_nonneg
  have hzero : νD (deletionVisible P) = 0 :=
    (measureReal_eq_zero_iff (by finiteness)).mp hreal
  have hrec := ProfileVisibility.recurrence_of_zero_deletionVisible P νD hmassD hincD hzero
  have hrow : (∑' j : ℕ, (j : ℝ) * P (0, j)) = Real.exp (-k) * c :=
    PoissonProfileSupport.first_moment_zero_row (P := fun i j => P (i, j))
      (k := k) (c := c) hrec hmean
  exact PoissonProfile.no_common_sign_deviation νC
    (f := fun x : Profile => ∑' j : ℕ, x (0, j))
    (μ := Real.exp (-k)) (c := c) (ε := lam) hf hmassC hc hlam
    (hincC.trans hrow) hdev

theorem visible_excess_of_common_sign
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC]
    {k c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hmean : HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c)
    (hP : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-k)))
    (hf : Integrable (fun x : Profile => ∑' j : ℕ, x (0, j)) νC)
    (hincC : (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂νC) =
      ∑' j : ℕ, (j : ℝ) * P (0, j))
    (hdev : (∀ᵐ x : Profile ∂νC, Real.exp (-k) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
      (∀ᵐ x : Profile ∂νC, (∑' j : ℕ, x (0, j)) ≤ Real.exp (-k) - lam)) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  have habs : ∀ᵐ x : Profile ∂νC,
      lam ≤ |(∑' j : ℕ, x (0, j)) - Real.exp (-k)| := by
    rcases hdev with hhigh | hlow
    · filter_upwards [hhigh] with x hx
      exact le_trans (by linarith) (le_abs_self _)
    · filter_upwards [hlow] with x hx
      exact le_trans (by linarith) (neg_le_abs _)
  rw [ProfileVisibility.coverVisible_full_of_row_deviation P νC hlam
    hP.summable hP.tsum_eq habs, hmassC]
  linarith [deletionVisible_pos_of_common_sign P νD νC hc hlam hmassD hmassC
    hincD hmean hf hincC hdev]

end Balanced.OccupancyVisibility

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyRowIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.OccupancyVisibility

open MeasureTheory

theorem row_summable_of_probability (p : Profile)
    (hp : HasSum p 1) (i : ℕ) : Summable (fun j : ℕ => p (i, j)) :=
  hp.summable.comp_injective (fun _ _ h => Prod.mk.inj h |>.2)

theorem row_mass_le_one (p : Profile) (hp : HasSum p 1)
    (hnonneg : ∀ ij, 0 ≤ p ij) (i : ℕ) : (∑' j : ℕ, p (i, j)) ≤ 1 := by
  simpa only [Function.comp_def, hp.tsum_eq] using
    tsum_comp_le_tsum_of_inj hp.summable hnonneg
      (i := fun j : ℕ => (i, j)) (fun _ _ h => Prod.mk.inj h |>.2)

theorem integrable_row_of_probability_support
    (ν : Measure Profile) [IsFiniteMeasure ν] (i : ℕ)
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1) :
    Integrable (fun x : Profile => ∑' j : ℕ, x (i, j)) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (Measurable.tsum (fun j => measurable_pi_apply (i, j))).aestronglyMeasurable
  filter_upwards [hsupport] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun j => hx.1 (i, j)))]
  exact row_mass_le_one x hx.2 hx.1 i

theorem row_integral_hasSum
    (ν : Measure Profile) [IsFiniteMeasure ν] (i : ℕ)
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1) :
    HasSum (fun j : ℕ => ∫ x : Profile, x (i, j) ∂ν)
      (∫ x : Profile, ∑' j : ℕ, x (i, j) ∂ν) := by
  apply hasSum_integral_of_dominated_convergence (fun j (x : Profile) => x (i, j))
  · intro j
    exact (measurable_pi_apply (i, j)).aestronglyMeasurable
  · intro j
    filter_upwards [hsupport] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 (i, j))]
  · filter_upwards [hsupport] with x hx
    exact row_summable_of_probability x hx.2 i
  · exact integrable_row_of_probability_support ν i hsupport
  · filter_upwards [hsupport] with x hx
    exact (row_summable_of_probability x hx.2 i).hasSum

theorem row_integral_eq_weighted_row
    (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1)
    (hinc : ∀ j : ℕ, (∫ x : Profile, x (0, j) ∂ν) = (j : ℝ) * P (0, j)) :
    (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂ν) = ∑' j : ℕ, (j : ℝ) * P (0, j) := by
  have h := row_integral_hasSum ν 0 hsupport
  simpa only [hinc] using h.tsum_eq.symm

theorem visible_excess_of_normalized_common_sign
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC]
    {k c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hincC : ∀ ij : ℕ × ℕ, (∫ x, x ij ∂νC) = (ij.2 : ℝ) * P ij)
    (hsupport : ∀ᵐ x : Profile ∂νC, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1)
    (hP : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-k)))
    (hdev : (∀ᵐ x : Profile ∂νC, Real.exp (-k) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
      (∀ᵐ x : Profile ∂νC, (∑' j : ℕ, x (0, j)) ≤ Real.exp (-k) - lam)) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  have hmean : HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c := by
    apply deletion_profile_second_mean νC (fun ij (x : Profile) => x ij) P c
    · intro ij
      exact (measurable_pi_apply ij).aestronglyMeasurable
    · intro ij
      exact hsupport.mono (fun x hx => hx.1 ij)
    · exact hsupport.mono (fun x hx => hx.2)
    · exact hincC
    · exact hmassC
  exact visible_excess_of_common_sign P νD νC hc hlam hmassD hmassC hincD
    hmean hP (integrable_row_of_probability_support νC 0 hsupport)
    (row_integral_eq_weighted_row P νC hsupport (fun j => hincC (0, j))) hdev

end Balanced.OccupancyVisibility

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_NearCoverLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

namespace FiniteProfile

theorem profileSequenceLimit_marginals
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (k : ℕ) (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ i : ℕ, Tendsto (fun n => ∑' j : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' j : ℕ, P (i, j)))) ∧
    (∀ j : ℕ, Tendsto (fun n => ∑' i : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' i : ℕ, P (i, j)))) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  have hP : IsBoundedProfile M P :=
    (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  let p : ℕ → {x : Profile | IsBoundedProfile M x} := fun n =>
    ⟨planeProfile (D n) (C n),
      planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2⟩
  have ht : Tendsto p atTop (𝓝 ⟨P, hP⟩) := by
    exact tendsto_subtype_rng.mpr hlim.2.1
  constructor
  · intro i
    exact (ProfileContinuity.continuous_boundedProfile_row_sum M i).tendsto
      ⟨P, hP⟩ |>.comp ht
  · intro j
    exact (ProfileContinuity.continuous_boundedProfile_column_sum M j).tendsto
      ⟨P, hP⟩ |>.comp ht

end FiniteProfile

namespace NearCoverVisibility

theorem nearCoverClass_limit_row_ae
    (k : ℕ) (δ : ℝ) (ε : ℕ → ℝ) (hεnonneg : ∀ q, 0 ≤ ε q)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type*} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, NearCoverClass k δ ε (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    ∀ᵐ x ∂(νC : Measure Profile), (∑' j : ℕ, x (0, j)) = Real.exp (-(k : ℝ)) := by
  exact ProfileShrinkingExceptions.profileSequenceLimit_row_sum_eq_of_integral_tendsto_zero
    k D C (fun n => (hclass n).1) hlim _
    (nearCoverClass_integral_abs_tendsto k δ ε hεnonneg hε D C hclass hq)

theorem nearCoverClass_visibleExcess
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (ε : ℕ → ℝ)
    (hεnonneg : ∀ q, 0 ≤ ε q) (hε : Tendsto ε atTop (𝓝 0)) :
    ProfileVisibleExcess (NearCoverClass k δ ε) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hpair : ∀ n, IsProfilePair k (D n) (C n) := fun n => (hclass n).1
  obtain ⟨hP, hDsupport, hCsupport⟩ :=
    ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim
  obtain ⟨hmassD, hmassC, hincD, hincC⟩ :=
    FiniteProfile.profileSequenceLimit_mass_incidence k hpair hq hlim
  obtain ⟨hcorner, hbudget⟩ := nearCoverClass_limit_corner_budget k δ ε D C hclass hlim
  obtain ⟨hrows, hcols⟩ := FiniteProfile.profileSequenceLimit_marginals k D C hpair hlim
  have hrowSum : (∑' j : ℕ, P (0, j)) = Real.exp (-(k : ℝ)) := by
    apply tendsto_nhds_unique (hrows 0)
    simpa only [(FiniteProfile.planeProfile_zero_row_hasSum _ _).tsum_eq] using
      nearCoverClass_core_density_tendsto k δ ε hε D C hclass hq
  have hrow : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-(k : ℝ))) := by
    rw [← hrowSum]
    exact (OccupancyVisibility.row_summable_of_probability P hP.2.1 0).hasSum
  have huncovered : δ ≤ ∑' i : ℕ, P (i, 0) := by
    apply ge_of_tendsto (hcols 0)
    apply Eventually.of_forall
    intro n
    rw [(FiniteProfile.planeProfile_zero_column_hasSum _ _).tsum_eq]
    apply (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := F n)))).mpr
    exact (hclass n).2.2.1
  have hnormC : ∀ᵐ x ∂(νC : Measure Profile), (∀ ij, 0 ≤ x ij) ∧ HasSum x 1 := by
    filter_upwards [hCsupport] with x hx
    exact ⟨hx.1, hx.2.1⟩
  have hrowAE := nearCoverClass_limit_row_ae k δ ε hεnonneg hε D C hclass hq hlim
  have hmoment : HasSum (fun j : ℕ => (j : ℝ) * P (0, j))
      (c * Real.exp (-(k : ℝ))) := by
    have h := OccupancyVisibility.row_integral_hasSum (νC : Measure Profile) 0 hnormC
    have hint : (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂(νC : Measure Profile)) =
        c * Real.exp (-(k : ℝ)) := by
      rw [integral_congr_ae hrowAE, integral_const, smul_eq_mul, hmassC]
    rw [hint] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext j
    exact (hincC (0, j)).symm
  have hf : Integrable (fun x : Profile => x (0, 1)) (νC : Measure Profile) := by
    apply ((clippedProfileCoordinate (0, 1)).integrable (νC : Measure Profile)).congr
    filter_upwards [hCsupport] with x hx
    exact clippedProfileCoordinate_eq_of_bounded hx (0, 1)
  apply visible_excess_of_row_moments P (νD : Measure Profile) (νC : Measure Profile)
    (Real.exp_pos _) hδ hbudget hmassD hmassC
    (fun i j => by simpa using hincD (i + 1, j)) (by simpa using hincC (0, 1))
    hcorner (fun j => hP.1 (0, j)) hrow hmoment huncovered hf
  filter_upwards [hnormC, hrowAE] with x hx hxr
  exact ⟨fun j => hx.1 (0, j),
    OccupancyVisibility.row_summable_of_probability x hx.2 0, hxr⟩

end NearCoverVisibility
end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RobustMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology

universe u

theorem multiplicityFailureClass_visibleExcess
    (k : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ProfileVisibleExcess (multiplicityFailureClass.{u} k τ) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hc := multiplicityFailureClass_limit_density_zero k τ D C hclass hlim
  have hmass : (νD : Measure Profile).real Set.univ = (k : ℝ) :=
    profile_mass_weak_limit hlim.2.2.1
      (FiniteProfile.empiricalProfileMeasure_deletion_mass_tendsto D C
        (fun n => (hclass n).1) hq)
  have hinc (i : ℕ) :
      (∫ x : Profile, x (i + 1, 0) ∂(νD : Measure Profile)) =
        (i + 1 : ℝ) * P (i + 1, 0) := by
    apply ambient_profile_incidence_weak_limit (i + 1, 0) hlim.2.2.1 hlim.2.1
    · intro n
      filter_upwards [FiniteProfile.empiricalProfileMeasure_unit_coordinates
        (D n) (C n) (D n)] with x hx
      exact hx (i + 1, 0)
    · intro n
      simpa only [Nat.cast_add, Nat.cast_one] using
        FiniteProfile.empiricalProfileMeasure_deletion_incidence (D n) (C n) (i + 1) 0
  have hnorm := (multiplicityFailureClass_limit_probability k τ D C hclass hlim).2
  have htv := multiplicityFailureClass_limit_tv k τ D C hclass hlim
  have hvisible := deletionVisible_positive_of_tv k P (νD : Measure Profile)
    hmass hnorm hinc (lt_of_lt_of_le hτ htv)
  rw [hc]
  exact lt_of_lt_of_le hvisible (le_add_of_nonneg_right measureReal_nonneg)

theorem robustMultiplicity_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K τ : ℝ) (hτ : 0 < τ) :
    UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val) := by
  exact multiplicityVanishing_of_profileCounting hcounting k hk K τ
    (multiplicityFailureClass_visibleExcess k τ hτ)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_RobustNearCover
attribute [-instance] _root_.OAI.Balanced.ProfileClassMargin.instDecidableEqCarrier _root_.OAI.Balanced.ProfileClassMargin.instFieldCarrier _root_.OAI.Balanced.ProfileClassMargin.instFintypeCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_uniform_poisson_occupancy_tolerance_le (k : ℕ) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val))
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)))
    (b : ℝ) (hb : 0 < b) :
    ∃ ε : ℕ → ℝ, (∀ q, 0 < ε q) ∧ (∀ q, ε q ≤ b) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      UniformDeletionVanishing.{u} k K
        (fun F _ _ _ D =>
          ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val ∨
          ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
            ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)) := by
  obtain ⟨ε, hpos, hanti, hlim, hbad⟩ := exists_uniform_deletion_tolerance k K
    (fun t F _ _ _ D =>
      min t b ≤ deletionMultiplicityTV k D.val ∨
      min t b * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k (min t b) D.val).card : ℝ)) (by
      intro t ht
      have hmin : 0 < min t b := lt_min ht hb
      exact uniformDeletionVanishing_or k K _ _
        (hTV _ hmin) (hOcc _ _ hmin hmin))
  refine ⟨fun q => min (ε q) b, (fun q => lt_min (hpos q) hb),
    (fun q => min_le_right _ _), ?_, ?_, hbad⟩
  · intro m n hmn
    exact min_le_min_right b (hanti hmn)
  · simpa only [min_eq_left hb.le] using hlim.min (tendsto_const_nhds (x := b))

theorem robust_nearCover_of_profileCounting
    (hcount : ProfileCountingResult.{u}) (k : ℕ) (hk : 1 ≤ k) (K : ℝ)
    (hTV : ∀ τ : ℝ, 0 < τ → UniformDeletionVanishing.{u} k K
      (fun _ _ _ _ D => τ ≤ deletionMultiplicityTV k D.val))
    (hOcc : ∀ lam η : ℝ, 0 < lam → 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)))
    (δ : ℝ) (hδ : 0 < δ) :
    UniformDeletionVanishing.{u} k K (fun _ _ _ _ D => BadCoreCover δ D.val) := by
  obtain ⟨ε, hεpos, hεcap, _, hεlim, hbad⟩ :=
    exists_uniform_poisson_occupancy_tolerance_le k K hTV hOcc
      (Real.exp (-(k : ℝ)) / 4) (by positivity)
  let A : ProfileClass.{u} := NearCoverVisibility.NearCoverClass k δ ε
  have hvalid : ProfileClassValid k A := NearCoverVisibility.nearCoverClass_valid k δ ε
  have hgap : ProfileClassSizeGap (Real.exp (-(k : ℝ)) / 2) A :=
    NearCoverVisibility.nearCoverClass_sizeGap k δ ε hεcap
  have hvis : ProfileVisibleExcess A :=
    NearCoverVisibility.nearCoverClass_visibleExcess k δ hδ ε
      (fun q => (hεpos q).le) hεlim
  have hrestricted : UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C, A F D.val C) :=
    uniformDeletionVanishing_of_profileCounting hcount k hk K A hvalid
      ⟨Real.exp (-(k : ℝ)) / 2, by positivity, hgap⟩ hvis
  apply uniformDeletionVanishing_mono k K _ _ _
    (uniformDeletionVanishing_or k K _ _ hrestricted hbad)
  intro F _ _ _ D hcover
  by_cases htv : ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val
  · exact Or.inr (Or.inl htv)
  by_cases hocc : ε (Fintype.card F) * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k (ε (Fintype.card F)) D.val).card : ℝ)
  · exact Or.inr (Or.inr hocc)
  apply Or.inl
  exact NearCoverVisibility.nearCoverClass_of_badCoreCover k δ ε D.property hcover
    (le_of_lt (lt_of_not_ge htv)) (le_of_lt (lt_of_not_ge hocc))

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyFailureClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology

universe u

theorem occupancyFailureClass_valid (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool) :
    ProfileClassValid k (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C h
  exact h.1

theorem occupancyFailureClass_sizeGap (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool) :
    ProfileClassSizeGap a (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C h
  exact Or.inr h.2.1

theorem occupancyFailureClass_limit_density_lower
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : a ≤ c := by
  apply ge_of_tendsto hlim.1
  apply Eventually.of_forall
  intro n
  exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F n))).2 (hclass n).2.1

theorem exists_common_sign_subset {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) (μ lam : ℝ) (m : ℕ)
    (hsize : 2 * m ≤ S.card) (hdev : ∀ x ∈ S, lam ≤ |f x - μ|) :
    ∃ high : Bool, ∃ C : Finset α, C ⊆ S ∧ C.card = m ∧
      ∀ x ∈ C, if high then μ + lam ≤ f x else f x ≤ μ - lam := by
  classical
  let A := S.filter (fun x => μ + lam ≤ f x)
  by_cases hA : m ≤ A.card
  · obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hA
    refine ⟨true, C, fun x hx => (Finset.mem_filter.mp (hC hx)).1, hcard, ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (hC hx)).2
  · let B := S.filter (fun x => ¬ (μ + lam ≤ f x))
    have hpart : A.card + B.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (fun x => μ + lam ≤ f x)
    have hB : m ≤ B.card := by omega
    obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hB
    refine ⟨false, C, fun x hx => (Finset.mem_filter.mp (hC hx)).1, hcard, ?_⟩
    intro x hx
    obtain ⟨hxS, hxA⟩ := Finset.mem_filter.mp (hC hx)
    have hd := hdev x hxS
    rcases le_abs.mp hd with hpos | hneg
    · exact False.elim (hxA (by linarith))
    · change f x ≤ μ - lam
      linarith

theorem occupancyFailureClass_witness_of_exceptional
    (k : ℕ) {η lam : ℝ} (_hη : 0 ≤ η) (hηone : η ≤ 1)
    (ε : ℕ → ℝ) (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D : DeletionSet F k)
    (hlarge : 4 ≤ η * (Fintype.card F : ℝ))
    (hbad : η * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k lam D.val).card : ℝ))
    (hTV : deletionMultiplicityTV k D.val ≤ ε (Fintype.card F)) :
    ∃ high : Bool, ∃ C : Finset (Line F),
      occupancyFailureClass k (η / 4) lam ε high F D.val C := by
  classical
  let q : ℝ := Fintype.card F
  let m : ℕ := ⌊η * q / 2⌋₊
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hmle : (m : ℝ) ≤ η * q / 2 := Nat.floor_le (by positivity)
  have hmlt : η * q / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2m : 2 * m ≤ (exceptionalOccupancyLines k lam D.val).card := by
    have hh : (2 : ℝ) * m ≤ ((exceptionalOccupancyLines k lam D.val).card : ℝ) := by
      change η * q ≤ _ at hbad
      linarith
    exact_mod_cast hh
  have hdev : ∀ l ∈ exceptionalOccupancyLines k lam D.val,
      lam ≤ |survivingLineOccupancy D.val l - Real.exp (-(k : ℝ))| := by
    intro l hl
    exact (Finset.mem_filter.mp hl).2.2
  obtain ⟨high, C, hC, hcard, hsign⟩ := exists_common_sign_subset
    (exceptionalOccupancyLines k lam D.val) (survivingLineOccupancy D.val)
    (Real.exp (-(k : ℝ))) lam m h2m hdev
  refine ⟨high, C, ⟨D.property, ?_, ?_⟩, ?_, hTV, hsign⟩
  · apply Finset.disjoint_left.mpr
    intro l hlD hlC
    exact (Finset.mem_filter.mp (hC hlC)).2.1 hlD
  · rw [hcard]
    have hh : (m : ℝ) ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hηone hq]
    change (m : ℝ) ≤ (Fintype.card F : ℝ) at hh
    exact_mod_cast hh
  · rw [hcard]
    change (η / 4) * q ≤ (m : ℝ)
    change 4 ≤ η * q at hlarge
    nlinarith

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_order_for_occupancy_gap (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → 4 ≤ η * (q : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / η)
  refine ⟨N, ?_⟩
  intro q hq
  have hN' : 4 < (N : ℝ) * η := (div_lt_iff₀ hη).mp hN
  have hq' : (N : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_RobustOccupancyAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem robustOccupancy_of_profileCounting_of_visible
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K lam η : ℝ)
    (hη : 0 < η) (hηone : η ≤ 1)
    (hvisible : ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ high : Bool,
      ProfileVisibleExcess (occupancyFailureClass.{u} k (η / 4) lam ε high)) :
    UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  obtain ⟨ε, _hpos, _hanti, hlim, hbadTV⟩ := exists_uniform_poisson_tolerance k K
    (fun τ hτ => robustMultiplicity_of_profileCounting hcounting k hk K τ hτ)
  have hclass (high : Bool) : UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => ∃ C : Finset (Line F),
        occupancyFailureClass k (η / 4) lam ε high F D.val C) :=
    uniformDeletionVanishing_of_profileCounting hcounting k hk K _
      (occupancyFailureClass_valid k (η / 4) lam ε high)
      ⟨η / 4, by positivity, occupancyFailureClass_sizeGap k (η / 4) lam ε high⟩
      (hvisible ε hlim high)
  have hsigns := uniformDeletionVanishing_or k K _ _ (hclass false) (hclass true)
  have hall := uniformDeletionVanishing_or k K _ _ hbadTV hsigns
  apply uniformDeletionVanishing_eventually_mono k K _ _ _ hall
  obtain ⟨N, hN⟩ := exists_order_for_occupancy_gap η hη
  refine ⟨N, ?_⟩
  intro F _ _ _ hn D hbad
  by_cases hTV : ε (Fintype.card F) ≤ deletionMultiplicityTV k D.val
  · exact Or.inl hTV
  · obtain ⟨high, C, hC⟩ := occupancyFailureClass_witness_of_exceptional
      k hη.le hηone ε F D (hN _ hn) hbad (le_of_not_ge hTV)
    cases high
    · exact Or.inr (Or.inl ⟨C, hC⟩)
    · exact Or.inr (Or.inr ⟨C, hC⟩)

theorem robustOccupancy_extend_fraction
    (k : ℕ) (K lam : ℝ)
    (hsmall : ∀ η : ℝ, 0 < η → η ≤ 1 → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ))) :
    ∀ η : ℝ, 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  intro η hη
  apply uniformDeletionVanishing_mono k K _ _ _
    (hsmall (min η 1) (lt_min hη (by norm_num)) (min_le_right _ _))
  intro F _ _ _ D hD
  exact (mul_le_mul_of_nonneg_right (min_le_left η 1)
    (Nat.cast_nonneg (Fintype.card F))).trans hD

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_OccupancyClassVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology NNReal

universe u

namespace OccupancyClassVisibility

theorem coordinate_error_le_two_tv
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (k : ℕ) (D : Finset (Line F)) (i : ℕ) :
    |empiricalMultiplicityMass D i - deletionPoissonMass k i| ≤
      2 * deletionMultiplicityTV k D := by
  have hs := ((FiniteProfile.empirical_multiplicity_hasSum D).summable.sub
    (deletionPoissonMass_hasSum k).summable).abs
  have h := hs.le_tsum i (fun j _ => abs_nonneg
    (empiricalMultiplicityMass D j - deletionPoissonMass k j))
  unfold deletionMultiplicityTV
  linarith

theorem plane_zero_row_eq_empirical_zero
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D C : Finset (Line F)) :
    (∑' j : ℕ, planeProfile D C (0, j)) = empiricalMultiplicityMass D 0 := by
  rw [(FiniteProfile.planeProfile_zero_row_hasSum D C).tsum_eq]
  unfold empiricalMultiplicityMass uncoveredBy
  congr 3
  ext p
  simp [deletionMultiplicity, Finset.filter_eq_empty_iff]

theorem plane_row_tendsto
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (k : ℕ)
    (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) (i : ℕ) :
    Tendsto (fun n => ∑' j : ℕ, planeProfile (D n) (C n) (i, j))
      atTop (𝓝 (∑' j : ℕ, P (i, j))) := by
  let M : ℝ := 2 * (k : ℝ) + 4
  let S := {p : Profile | IsBoundedProfile M p}
  let p : ℕ → S := fun n => ⟨planeProfile (D n) (C n),
    planeProfile_isBounded k (D n) (C n) (hpair n).1 (hpair n).2.2⟩
  let p₀ : S := ⟨P,
    (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1⟩
  have ht : Tendsto p atTop (𝓝 p₀) := tendsto_subtype_rng.mpr hlim.2.1
  exact (ProfileContinuity.continuous_boundedProfile_row_sum M i).tendsto p₀ |>.comp ht

theorem isCompact_row_constraint (M : ℝ) (hM : 0 ≤ M)
    (i : ℕ) (A : Set ℝ) (hA : IsClosed A) :
    IsCompact {p : Profile | IsBoundedProfile M p ∧ (∑' j : ℕ, p (i, j)) ∈ A} := by
  let S := {p : Profile | IsBoundedProfile M p}
  let : CompactSpace S := isCompact_iff_compactSpace.mp
    (ProfileAmbientCompactness.isCompact_boundedProfiles M hM)
  have hc : IsCompact {p : S | (∑' j : ℕ, p.val (i, j)) ∈ A} :=
    (hA.preimage (ProfileContinuity.continuous_boundedProfile_row_sum M i)).isCompact
  have hi := hc.image (continuous_subtype_val : Continuous (Subtype.val : S → Profile))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨hp, hrow⟩
    exact ⟨⟨p, hp⟩, hrow, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

theorem cover_row_closed_support
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (k : ℕ)
    (D C : ∀ n, Finset (Line (F n)))
    (hpair : ∀ n, IsProfilePair k (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC)
    (i : ℕ) (A : Set ℝ) (hA : IsClosed A)
    (hrow : ∀ n, ∀ l ∈ C n, (∑' j : ℕ, lineProfile (D n) (C n) l (i, j)) ∈ A) :
    ∀ᵐ p ∂(νC : Measure Profile), (∑' j : ℕ, p (i, j)) ∈ A := by
  have hK := isCompact_row_constraint (2 * (k : ℝ) + 4) (by positivity) i A hA
  have hzero := ProfileAmbientCompactness.compact_support_of_tendsto hK
    (μ := fun n => empiricalProfileMeasure (D n) (C n) (C n))
    (fun n => ProfileEmpiricalSupport.empiricalProfileMeasure_compl_eq_zero
      (D n) (C n) (C n) hK.measurableSet (fun l hl =>
        ⟨lineProfile_isBounded k (D n) (C n) l (hpair n).1 (hpair n).2.2,
          hrow n l hl⟩)) hlim.2.2.2
  have hae := ae_iff.mpr ((FiniteMeasure.null_iff_toMeasure_null νC _).mp hzero)
  exact hae.mono fun _ hp => hp.2

end OccupancyClassVisibility

theorem occupancyFailureClass_limit_zero_row
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    (hε : Tendsto ε atTop (𝓝 0))
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    HasSum (fun j : ℕ => P (0, j)) (Real.exp (-(k : ℝ))) := by
  have hpair := fun n => (hclass n).1
  have hP := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).1
  have hrow := OccupancyClassVisibility.plane_row_tendsto k D C hpair hlim 0
  have hzero : deletionPoissonMass k 0 = Real.exp (-(k : ℝ)) := by
    simp [deletionPoissonMass, ProbabilityTheory.poissonMeasure_real_singleton]
  have hmass : Tendsto (fun n => empiricalMultiplicityMass (D n) 0)
      atTop (𝓝 (Real.exp (-(k : ℝ)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (by simpa using (hε.comp hq).const_mul 2)
    intro n
    rw [Real.norm_eq_abs, ← hzero]
    exact (OccupancyClassVisibility.coordinate_error_le_two_tv k (D n) 0).trans
      (mul_le_mul_of_nonneg_left (hclass n).2.2.1 (by norm_num))
  have heq : (∑' j : ℕ, P (0, j)) = Real.exp (-(k : ℝ)) := by
    apply tendsto_nhds_unique hrow
    simpa only [OccupancyClassVisibility.plane_zero_row_eq_empirical_zero] using hmass
  exact heq ▸ (OccupancyVisibility.row_summable_of_probability P hP.2.1 0).hasSum

theorem occupancyFailureClass_limit_common_sign
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) :
    (∀ᵐ x : Profile ∂(νC : Measure Profile),
      Real.exp (-(k : ℝ)) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
    (∀ᵐ x : Profile ∂(νC : Measure Profile),
      (∑' j : ℕ, x (0, j)) ≤ Real.exp (-(k : ℝ)) - lam) := by
  cases high
  · right
    apply OccupancyClassVisibility.cover_row_closed_support k D C
      (fun n => (hclass n).1) hlim 0 (Set.Iic _) isClosed_Iic
    intro n l hl
    rw [(FiniteProfile.lineProfile_zero_row_hasSum (D n) (C n) l).tsum_eq]
    exact (hclass n).2.2.2 l hl
  · left
    apply OccupancyClassVisibility.cover_row_closed_support k D C
      (fun n => (hclass n).1) hlim 0 (Set.Ici _) isClosed_Ici
    intro n l hl
    rw [(FiniteProfile.lineProfile_zero_row_hasSum (D n) (C n) l).tsum_eq]
    exact (hclass n).2.2.2 l hl

theorem occupancyFailureClass_visibleExcess
    (k : ℕ) (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (high : Bool) :
    ProfileVisibleExcess (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C hclass hq c P νD νC hlim
  have hpair := fun n => (hclass n).1
  have hs := (ProfileEmpiricalSupport.profileSequenceLimit_bounded k D C hpair hlim).2.2
  apply OccupancyVisibility.visible_excess_of_normalized_common_sign
    P (νD : Measure Profile) (νC : Measure Profile)
    (ha.trans_le (occupancyFailureClass_limit_density_lower k a lam ε high D C hclass hlim))
    hlam (hlim.deletion_mass (fun n => (hpair n).1) hq) hlim.cover_mass
  · intro i j
    simpa only [Nat.cast_add, Nat.cast_one] using hlim.deletion_incidence (i + 1, j)
  · exact hlim.cover_incidence
  · exact hs.mono (fun x hx => ⟨hx.1, hx.2.1⟩)
  · exact occupancyFailureClass_limit_zero_row k a lam ε high hε D C hclass hq hlim
  · exact occupancyFailureClass_limit_common_sign k a lam ε high D C hclass hlim

theorem robustOccupancy_of_profileCounting
    (hcounting : ProfileCountingResult.{u})
    (k : ℕ) (hk : 1 ≤ k) (K lam : ℝ) (hlam : 0 < lam) :
    ∀ η : ℝ, 0 < η → UniformDeletionVanishing.{u} k K
      (fun F _ _ _ D => η * (Fintype.card F : ℝ) ≤
        ((exceptionalOccupancyLines k lam D.val).card : ℝ)) := by
  apply robustOccupancy_extend_fraction k K lam
  intro η hη hηone
  apply robustOccupancy_of_profileCounting_of_visible hcounting k hk K lam η hη hηone
  intro ε hε high
  exact occupancyFailureClass_visibleExcess k (η / 4) lam (by positivity) hlam ε hε high

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Profiles_RobustFromProfileCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem robustDeletion_of_profileCounting_oai
    (hcounting : ProfileCountingResult.{u}) : RobustDeletionResult.{u} := by
  intro k hk K _hK
  have hTV := fun τ hτ => robustMultiplicity_of_profileCounting hcounting k hk K τ hτ
  have hOcc := fun lam η hlam hη =>
    robustOccupancy_of_profileCounting hcounting k hk K lam hlam η hη
  exact ⟨hTV, hOcc,
    fun δ hδ => robust_nearCover_of_profileCounting hcounting k hk K hTV hOcc δ hδ⟩

end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.robustDeletion_of_profileCounting_oai.{u} := @OAI.Balanced.robustDeletion_of_profileCounting_oai.{u}
