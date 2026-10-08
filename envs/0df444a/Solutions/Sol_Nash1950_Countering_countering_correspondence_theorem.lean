-- Prove2me | solution 1 for Nash1950.Countering.countering_correspondence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T17:27:16.02745+00:00
-- url     : https://prove2.me/submissions/67902c77-7f3b-4a9e-bc01-a81c550b04b0

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter

open Nash1950.Countering

namespace NcWork

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ι → Type*) [∀ i, Fintype (S i)]

theorem profileProb_update (P : ∀ i, S i → ℝ) (j : ι) (τ : S j → ℝ) (s : ∀ i, S i) :
    AGT.profileProb (Function.update P j τ) s =
      τ (s j) * ∏ k ∈ Finset.univ.erase j, P k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem expectedPayoff_update_linear (u : ι → (∀ i, S i) → ℝ) :
    ∀ (P : ∀ i, S i → ℝ) (j i : ι) (τ τ' : S j → ℝ) (a b : ℝ),
      AGT.expectedPayoff u (Function.update P j (a • τ + b • τ')) i =
        a * AGT.expectedPayoff u (Function.update P j τ) i +
          b * AGT.expectedPayoff u (Function.update P j τ') i := by
  intro P j i τ τ' a b
  unfold AGT.expectedPayoff
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [profileProb_update, profileProb_update, profileProb_update]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem expectedPayoff_continuous (u : ι → (∀ i, S i) → ℝ) :
    ∀ i, Continuous (fun P : ∀ i, S i → ℝ => AGT.expectedPayoff u P i) := by
  intro i
  unfold AGT.expectedPayoff AGT.profileProb
  fun_prop

open Classical in
/-- The payoff of player `i` is linear in his own lottery, with coefficients `c P i t`. -/
noncomputable def coef (u : ι → (∀ i, S i) → ℝ) (P : ∀ i, S i → ℝ) (i : ι) (t : S i) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : ∀ j, S j => s i = t),
    (∏ k ∈ Finset.univ.erase i, P k (s k)) * u i s

theorem expectedPayoff_eq_sum (u : ι → (∀ i, S i) → ℝ) (P : ∀ i, S i → ℝ) (i : ι)
    (τ : S i → ℝ) :
    AGT.expectedPayoff u (Function.update P i τ) i = ∑ t, τ t * coef S u P i t := by
  classical
  unfold AGT.expectedPayoff coef
  simp_rw [profileProb_update]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : ∀ j, S j => s i) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.1 hs).2]
  ring

theorem counteringSet_nonempty_subset [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, AGT.IsMixedProfile P →
      (counteringSet u P).Nonempty ∧
        counteringSet u P ⊆ {Q | AGT.IsMixedProfile Q} := by
  classical
  intro P hP
  refine ⟨?_, fun Q hQ => hQ.1⟩
  have hbest : ∀ i, ∃ t : S i, ∀ t' : S i, coef S u P i t' ≤ coef S u P i t := fun i => by
    obtain ⟨t, -, ht⟩ := Finset.exists_max_image (Finset.univ : Finset (S i)) (coef S u P i)
      Finset.univ_nonempty
    exact ⟨t, fun t' => ht t' (Finset.mem_univ _)⟩
  choose t ht using hbest
  refine ⟨fun i => Pi.single (t i) 1, ?_, ?_⟩
  · intro i
    refine ⟨fun a => ?_, ?_⟩
    · by_cases h : a = t i
      · subst h; simp
      · simp [Pi.single_apply, h]
    · simp
  · intro i τ hτ
    rw [expectedPayoff_eq_sum, expectedPayoff_eq_sum]
    have h1 : ∑ x, (Pi.single (t i) (1 : ℝ) : S i → ℝ) x * coef S u P i x = coef S u P i (t i) := by
      simp [Pi.single_apply]
    rw [h1]
    calc ∑ x, τ x * coef S u P i x ≤ ∑ x, τ x * coef S u P i (t i) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ht i x) (hτ.1 x)
      _ = coef S u P i (t i) := by rw [← Finset.sum_mul, hτ.2, one_mul]

theorem counteringSet_convex (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, Convex ℝ (counteringSet u P) := by
  intro P Q hQ Q' hQ' a b ha hb hab
  obtain ⟨hQm, hQc⟩ := hQ
  obtain ⟨hQm', hQc'⟩ := hQ'
  refine ⟨fun i => ⟨fun x => ?_, ?_⟩, fun i τ hτ => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha ((hQm i).1 x)) (mul_nonneg hb ((hQm' i).1 x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      (hQm i).2, (hQm' i).2]
    linarith
  · have h := expectedPayoff_update_linear S u P i i (Q i) (Q' i) a b
    have e : (a • Q + b • Q') i = a • Q i + b • Q' i := rfl
    rw [e, h]
    have h1 := hQc i τ hτ
    have h2 := hQc' i τ hτ
    have h3 := mul_le_mul_of_nonneg_left h1 ha
    have h4 := mul_le_mul_of_nonneg_left h2 hb
    have h5 : AGT.expectedPayoff u (Function.update P i τ) i =
        a * AGT.expectedPayoff u (Function.update P i τ) i +
          b * AGT.expectedPayoff u (Function.update P i τ) i := by
      rw [← add_mul, hab, one_mul]
    linarith

theorem counters_of_tendsto (u : ι → (∀ i, S i) → ℝ) :
    ∀ (P Q : ℕ → ∀ i, S i → ℝ) (P₀ Q₀ : ∀ i, S i → ℝ),
      (∀ k, AGT.IsMixedProfile (P k)) →
      Tendsto P atTop (nhds P₀) → Tendsto Q atTop (nhds Q₀) →
      (∀ k, Counters u (P k) (Q k)) → Counters u P₀ Q₀ := by
  intro P Q P₀ Q₀ hP hP₀ hQ₀ hC
  refine ⟨fun i => ⟨fun a => ?_, ?_⟩, fun i τ hτ => ?_⟩
  · have hcoord : Tendsto (fun k => Q k i a) atTop (nhds (Q₀ i a)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hQ₀ i) a
    exact ge_of_tendsto hcoord (Eventually.of_forall fun k => ((hC k).1 i).1 a)
  · have hsum : Tendsto (fun k => ∑ a, Q k i a) atTop (nhds (∑ a, Q₀ i a)) := by
      refine tendsto_finsetSum _ fun a _ => ?_
      exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hQ₀ i) a
    have hone : ∀ k, ∑ a, Q k i a = 1 := fun k => ((hC k).1 i).2
    simp only [hone] at hsum
    exact tendsto_nhds_unique hsum tendsto_const_nhds
  · have hF : Tendsto (fun k => AGT.expectedPayoff u (Function.update (P k) i τ) i) atTop
        (nhds (AGT.expectedPayoff u (Function.update P₀ i τ) i)) := by
      have hc : Continuous (fun P : ∀ i, S i → ℝ =>
          AGT.expectedPayoff u (Function.update P i τ) i) :=
        (expectedPayoff_continuous S u i).comp (continuous_id.update i continuous_const)
      exact hc.continuousAt.tendsto.comp hP₀
    have hG : Tendsto (fun k => AGT.expectedPayoff u (Function.update (P k) i (Q k i)) i) atTop
        (nhds (AGT.expectedPayoff u (Function.update P₀ i (Q₀ i)) i)) := by
      have hc : Continuous (fun x : (∀ i, S i → ℝ) × (∀ i, S i → ℝ) =>
          AGT.expectedPayoff u (Function.update x.1 i (x.2 i)) i) :=
        (expectedPayoff_continuous S u i).comp
          (continuous_fst.update i ((continuous_apply i).comp continuous_snd))
      have hlim := (hc.tendsto (P₀, Q₀)).comp (hP₀.prodMk_nhds hQ₀)
      exact hlim
    exact le_of_tendsto_of_tendsto' hF hG fun k => (hC k).2 i τ hτ

theorem counters_self_iff_isMixedNash (u : ι → (∀ i, S i) → ℝ) :
    ∀ P : ∀ i, S i → ℝ, Counters u P P ↔ AGT.IsMixedNash u P := by
  intro P
  simp only [Counters, AGT.IsMixedNash, Function.update_eq_self]

theorem countering_correspondence_theorem [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    (∀ P : ∀ i, S i → ℝ, AGT.IsMixedProfile P →
      (counteringSet u P).Nonempty ∧
        counteringSet u P ⊆ {Q | AGT.IsMixedProfile Q} ∧
          Convex ℝ (counteringSet u P)) ∧
    (∀ (P Q : ℕ → ∀ i, S i → ℝ) (P₀ Q₀ : ∀ i, S i → ℝ),
      (∀ k, AGT.IsMixedProfile (P k)) →
      Tendsto P atTop (nhds P₀) → Tendsto Q atTop (nhds Q₀) →
      (∀ k, Counters u (P k) (Q k)) → Counters u P₀ Q₀) ∧
    (∀ P : ∀ i, S i → ℝ, Counters u P P ↔ AGT.IsMixedNash u P) :=
  ⟨fun P hP => ⟨(counteringSet_nonempty_subset S u P hP).1, (counteringSet_nonempty_subset S u P hP).2,
      counteringSet_convex S u P⟩, counters_of_tendsto S u, counters_self_iff_isMixedNash S u⟩

end NcWork

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    (∀ P : ∀ i, S i → ℝ, AGT.IsMixedProfile P →
      (counteringSet u P).Nonempty ∧
        counteringSet u P ⊆ {Q | AGT.IsMixedProfile Q} ∧
          Convex ℝ (counteringSet u P)) ∧
    (∀ (P Q : ℕ → ∀ i, S i → ℝ) (P₀ Q₀ : ∀ i, S i → ℝ),
      (∀ k, AGT.IsMixedProfile (P k)) →
      Tendsto P atTop (nhds P₀) → Tendsto Q atTop (nhds Q₀) →
      (∀ k, Counters u (P k) (Q k)) → Counters u P₀ Q₀) ∧
    (∀ P : ∀ i, S i → ℝ, Counters u P P ↔ AGT.IsMixedNash u P) :=
  NcWork.countering_correspondence_theorem S u

#print axioms solution
