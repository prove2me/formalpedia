-- Prove2me | solution 1 for HarmonicKServer.Competitive.harmonic_competitive
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-20T02:30:43.339222+00:00
-- url     : https://prove2.me/submissions/94ddfd66-96ec-44bc-8ee6-fbd80f0b0ca9

import Definitions.Def_HarmonicKServer_Competitive_Interaction

namespace HarmonicKServerProof

open scoped BigOperators ENNReal
open MeasureTheory HarmonicKServer.Competitive Classical

/-! ## Section 1: Basic Metric, Harmonic, and Trajectory Lemmas -/

section Basics

lemma moveCost_self {k : ℕ} {V : Type*} [MetricSpace V] (C : KServer.Config k V) :
    KServer.moveCost C C = 0 := by
  simp [KServer.moveCost]

lemma moveCost_nonneg {k : ℕ} {V : Type*} [MetricSpace V] (C C' : KServer.Config k V) :
    0 ≤ KServer.moveCost C C' :=
  Finset.sum_nonneg (fun _ _ => dist_nonneg)

lemma moveCost_comm {k : ℕ} {V : Type*} [MetricSpace V] (C C' : KServer.Config k V) :
    KServer.moveCost C C' = KServer.moveCost C' C := by
  unfold KServer.moveCost
  exact Finset.sum_congr rfl (fun i _ => dist_comm _ _)

lemma moveCost_triangle {k : ℕ} {V : Type*} [MetricSpace V]
    (C₁ C₂ C₃ : KServer.Config k V) :
    KServer.moveCost C₁ C₃ ≤ KServer.moveCost C₁ C₂ + KServer.moveCost C₂ C₃ := by
  unfold KServer.moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => dist_triangle _ _ _)

lemma moveCost_relocate {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (i : Fin k) (r : V) :
    KServer.moveCost X (relocate X i r) = dist (X i) r := by
  classical
  unfold KServer.moveCost relocate
  have hterm : ∀ j : Fin k,
      dist (X j) (Function.update X i r j) = if j = i then dist (X i) r else 0 := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  simp [hterm]

lemma moveCost_execute_le_travel {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (ms : Moves k V) :
    KServer.moveCost Y (execute Y ms) ≤ travel Y ms := by
  induction ms generalizing Y with
  | nil => simp [execute, travel, moveCost_self]
  | cons m ms' ih =>
    rcases m with ⟨i, r⟩
    simp only [execute, travel]
    have h1 := moveCost_triangle Y (relocate Y i r) (execute (relocate Y i r) ms')
    rw [moveCost_relocate] at h1
    linarith [ih (relocate Y i r)]

lemma travel_nonneg {k : ℕ} {V : Type*} [MetricSpace V]
    (Y : KServer.Config k V) (ms : Moves k V) :
    0 ≤ travel Y ms :=
  le_trans (moveCost_nonneg Y (execute Y ms)) (moveCost_execute_le_travel Y ms)

lemma harmonicCost_eq {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) (i : Fin k) :
    harmonicCost X r i = if Covers X r then 0 else dist (X i) r := by
  unfold harmonicCost harmonicNext
  by_cases h : Covers X r
  · simp [h, moveCost_self]
  · simp [h, moveCost_relocate]

lemma harmonicCost_nonneg {k : ℕ} {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) (i : Fin k) :
    0 ≤ harmonicCost X r i := by
  rw [harmonicCost_eq]
  split_ifs
  · exact le_rfl
  · exact dist_nonneg

lemma dist_pos_of_not_covers {k : ℕ} {V : Type*} [MetricSpace V]
    {X : KServer.Config k V} {r : V} (h : ¬ Covers X r) (i : Fin k) :
    0 < dist (X i) r :=
  dist_pos.mpr (fun heq => h ⟨i, heq⟩)

lemma normalizer_pos_of_not_covers {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    {X : KServer.Config k V} {r : V} (h : ¬ Covers X r) :
    0 < normalizer X r := by
  unfold normalizer
  exact Finset.sum_pos
    (fun j _ => div_pos one_pos (dist_pos_of_not_covers h j))
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩

lemma harmonicProbability_nonneg {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) (i : Fin k) :
    0 ≤ harmonicProbability X r i := by
  classical
  unfold harmonicProbability
  by_cases hcov : Covers X r
  · simp only [if_pos hcov]
    split_ifs <;> norm_num
  · simp only [if_neg hcov]
    exact div_nonneg zero_le_one
      (mul_nonneg (normalizer_pos_of_not_covers hk hcov).le dist_nonneg)

lemma sum_harmonicProbability {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X : KServer.Config k V) (r : V) :
    ∑ i : Fin k, harmonicProbability X r i = 1 := by
  classical
  unfold harmonicProbability
  by_cases hcov : Covers X r
  · simp only [if_pos hcov]
    have hiff : ∀ i : Fin k, (i.val = 0) ↔ i = ⟨0, hk⟩ := by
      intro i
      constructor
      · intro hi; exact Fin.ext hi
      · intro hi; subst hi; rfl
    simp [hiff]
  · simp only [if_neg hcov]
    have hZ : normalizer X r ≠ 0 := (normalizer_pos_of_not_covers hk hcov).ne'
    have hrew : ∀ i : Fin k,
        1 / (normalizer X r * dist (X i) r) = (normalizer X r)⁻¹ * (1 / dist (X i) r) := by
      intro i; ring
    simp_rw [hrew, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hZ

lemma runFrom_append {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (h : History k) (S : State k V) (l₁ l₂ : List (Fin k)) :
    runFrom A h S (l₁ ++ l₂) = runFrom A (h ++ l₁) (runFrom A h S l₁) l₂ := by
  induction l₁ generalizing h S with
  | nil => simp [runFrom]
  | cons i t ih =>
    simp only [List.cons_append, runFrom]
    rw [ih (h ++ [i]) (advance S (A h) i)]
    simp [List.append_assoc]

lemma stateAt_append {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (h l : List (Fin k)) :
    stateAt A X Y (h ++ l) = runFrom A h (stateAt A X Y h) l := by
  unfold stateAt
  rw [runFrom_append]
  simp

lemma runFrom_costs_nonneg {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (h : History k) (S : State k V) (l : List (Fin k))
    (hon : 0 ≤ S.onlineCost) (hadv : 0 ≤ S.adversaryCost) :
    0 ≤ (runFrom A h S l).onlineCost ∧ 0 ≤ (runFrom A h S l).adversaryCost := by
  induction l generalizing h S with
  | nil => exact ⟨hon, hadv⟩
  | cons i t ih =>
    simp only [runFrom]
    apply ih
    · exact add_nonneg hon (harmonicCost_nonneg _ _ _)
    · exact add_nonneg hadv (travel_nonneg _ _)

lemma stateAt_costs_nonneg {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) (X Y : KServer.Config k V) (h : History k) :
    0 ≤ (stateAt A X Y h).onlineCost ∧ 0 ≤ (stateAt A X Y h).adversaryCost :=
  runFrom_costs_nonneg A [] (initial X Y) h le_rfl le_rfl

noncomputable def realPathWeightFrom {k : ℕ} {V : Type*} [MetricSpace V]
    (A : Adversary k V) : History k → State k V → List (Fin k) → ℝ
  | _, _, [] => 1
  | h, S, i :: tail =>
      harmonicProbability S.online (A h).request i *
        realPathWeightFrom A (h ++ [i]) (advance S (A h) i) tail

lemma realPathWeightFrom_nonneg {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (A : Adversary k V) (h : History k) (S : State k V) (l : List (Fin k)) :
    0 ≤ realPathWeightFrom A h S l := by
  induction l generalizing h S with
  | nil => norm_num [realPathWeightFrom]
  | cons i t ih =>
    simp only [realPathWeightFrom]
    exact mul_nonneg (harmonicProbability_nonneg hk _ _ _) (ih _ _)

lemma ofReal_realPathWeightFrom {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (A : Adversary k V) (h : History k) (S : State k V) (l : List (Fin k)) :
    ENNReal.ofReal (realPathWeightFrom A h S l) = pathWeightFrom A h S l := by
  induction l generalizing h S with
  | nil => simp [realPathWeightFrom, pathWeightFrom]
  | cons i t ih =>
    simp only [realPathWeightFrom, pathWeightFrom]
    rw [ENNReal.ofReal_mul (harmonicProbability_nonneg hk _ _ _), ih]

lemma ofFn_cons_eq {N k : ℕ} (i : Fin k) (w : Fin N → Fin k) :
    List.ofFn (Fin.cons i w) = i :: List.ofFn w := by
  simp

lemma sum_realPathWeightFrom {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (A : Adversary k V) (N : ℕ) (h : History k) (S : State k V) :
    ∑ w : Fin N → Fin k, realPathWeightFrom A h S (List.ofFn w) = 1 := by
  induction N generalizing h S with
  | zero =>
    rw [Fintype.sum_unique]
    simp [realPathWeightFrom]
  | succ N ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => Fin k))]
    rw [Fintype.sum_prod_type]
    change ∑ i : Fin k, ∑ w : Fin N → Fin k,
      realPathWeightFrom A h S (List.ofFn (Fin.cons i w)) = 1
    simp_rw [ofFn_cons_eq, realPathWeightFrom, ← Finset.mul_sum, ih, mul_one]
    exact sum_harmonicProbability hk _ _

/-- General potential-function competitive criterion (Lemma 2.3 lifted to AdaptiveCompetitive). -/
lemma adaptiveCompetitive_of_potential {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X₀ Y₀ : KServer.Config k V) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Ψ : KServer.Config k V → KServer.Config k V → ℝ)
    (hΨ_nonneg : ∀ X Y, 0 ≤ Ψ X Y)
    (hΨ_adv : ∀ X Y Y', Ψ X Y' - Ψ X Y ≤ ρ * KServer.moveCost Y Y')
    (hΨ_online : ∀ X Y r, Covers Y r →
      ∑ i : Fin k, harmonicProbability X r i *
        (harmonicCost X r i + Ψ (harmonicNext X r i) Y - Ψ X Y) ≤ 0) :
    AdaptiveCompetitive X₀ Y₀ ρ := by
  have hround : ∀ (X Y : KServer.Config k V) (act : Action k V),
      Covers (execute Y act.moves) act.request →
      ∑ i : Fin k, harmonicProbability X act.request i *
        (harmonicCost X act.request i +
          Ψ (harmonicNext X act.request i) (execute Y act.moves)) ≤
        Ψ X Y + ρ * travel Y act.moves := by
    intro X Y act hcov
    set Y' := execute Y act.moves
    have hon := hΨ_online X Y' act.request hcov
    have hsum1 := sum_harmonicProbability hk X act.request
    have hexp :
        ∑ i : Fin k, harmonicProbability X act.request i *
          (harmonicCost X act.request i + Ψ (harmonicNext X act.request i) Y' - Ψ X Y') =
        (∑ i : Fin k, harmonicProbability X act.request i *
          (harmonicCost X act.request i + Ψ (harmonicNext X act.request i) Y')) - Ψ X Y' := by
      have : ∀ i : Fin k,
          harmonicProbability X act.request i *
            (harmonicCost X act.request i + Ψ (harmonicNext X act.request i) Y' - Ψ X Y') =
          harmonicProbability X act.request i *
            (harmonicCost X act.request i + Ψ (harmonicNext X act.request i) Y') -
          harmonicProbability X act.request i * Ψ X Y' := fun i => by ring
      simp_rw [this, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
    have hadv1 : Ψ X Y' - Ψ X Y ≤ ρ * KServer.moveCost Y Y' := hΨ_adv X Y Y'
    have hadv2 : ρ * KServer.moveCost Y Y' ≤ ρ * travel Y act.moves :=
      mul_le_mul_of_nonneg_left (moveCost_execute_le_travel Y act.moves) hρ
    linarith
  have htree : ∀ (A : Adversary k V), ValidAdversary A X₀ Y₀ →
      ∀ (N : ℕ) (h : History k),
      let S := stateAt A X₀ Y₀ h
      ∑ w : Fin N → Fin k,
        realPathWeightFrom A h S (List.ofFn w) *
          ((runFrom A h S (List.ofFn w)).onlineCost +
            Ψ (runFrom A h S (List.ofFn w)).online
              (runFrom A h S (List.ofFn w)).adversary) ≤
      S.onlineCost + Ψ S.online S.adversary +
        ρ * ∑ w : Fin N → Fin k,
          realPathWeightFrom A h S (List.ofFn w) *
            ((runFrom A h S (List.ofFn w)).adversaryCost - S.adversaryCost) := by
    intro A hvalid N
    induction N with
    | zero =>
      intro h
      dsimp only
      rw [Fintype.sum_unique, Fintype.sum_unique]
      simp [realPathWeightFrom, runFrom]
    | succ N ih =>
      intro h
      dsimp only
      set S := stateAt A X₀ Y₀ h
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => Fin k))]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => Fin k))]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      change (∑ i : Fin k, ∑ w : Fin N → Fin k,
          realPathWeightFrom A h S (List.ofFn (Fin.cons i w)) *
            ((runFrom A h S (List.ofFn (Fin.cons i w))).onlineCost +
              Ψ (runFrom A h S (List.ofFn (Fin.cons i w))).online
                (runFrom A h S (List.ofFn (Fin.cons i w))).adversary)) ≤
        S.onlineCost + Ψ S.online S.adversary +
          ρ * ∑ i : Fin k, ∑ w : Fin N → Fin k,
            realPathWeightFrom A h S (List.ofFn (Fin.cons i w)) *
              ((runFrom A h S (List.ofFn (Fin.cons i w))).adversaryCost - S.adversaryCost)
      simp_rw [ofFn_cons_eq, realPathWeightFrom, runFrom]
      have hstep : ∀ i : Fin k,
          harmonicProbability S.online (A h).request i *
            ∑ w : Fin N → Fin k,
              realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).onlineCost +
                  Ψ (runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).online
                    (runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversary) ≤
          harmonicProbability S.online (A h).request i *
            ((advance S (A h) i).onlineCost +
              Ψ (advance S (A h) i).online (advance S (A h) i).adversary +
              ρ * ∑ w : Fin N → Fin k,
                realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                  ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                    (advance S (A h) i).adversaryCost)) := by
        intro i
        have hp := harmonicProbability_nonneg hk S.online (A h).request i
        have hSi : stateAt A X₀ Y₀ (h ++ [i]) = advance S (A h) i := by
          rw [stateAt_append]; rfl
        have hih := ih (h ++ [i])
        dsimp only at hih
        rw [hSi] at hih
        exact mul_le_mul_of_nonneg_left hih hp
      have hsum_step :
          (∑ i : Fin k, ∑ w : Fin N → Fin k,
            harmonicProbability S.online (A h).request i *
              realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).onlineCost +
                Ψ (runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).online
                  (runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversary)) ≤
          ∑ i : Fin k, harmonicProbability S.online (A h).request i *
            ((advance S (A h) i).onlineCost +
              Ψ (advance S (A h) i).online (advance S (A h) i).adversary +
              ρ * ∑ w : Fin N → Fin k,
                realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                  ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                    (advance S (A h) i).adversaryCost)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine le_trans ?_ (hstep i)
        apply le_of_eq
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
      refine le_trans hsum_step ?_
      have hsum_w : ∀ i : Fin k,
          ∑ w : Fin N → Fin k,
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) = 1 :=
        fun i => sum_realPathWeightFrom hk A N (h ++ [i]) (advance S (A h) i)
      have hadv_split : ∀ i : Fin k,
          ∑ w : Fin N → Fin k,
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                (advance S (A h) i).adversaryCost) =
          (∑ w : Fin N → Fin k,
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                S.adversaryCost)) -
          travel S.adversary (A h).moves := by
        intro i
        have h1 : ∀ w : Fin N → Fin k,
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                (advance S (A h) i).adversaryCost) =
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                S.adversaryCost) -
            realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              travel S.adversary (A h).moves := by
          intro w
          simp only [advance]
          ring
        simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_w i, one_mul]
      simp_rw [hadv_split]
      have hsum_p := sum_harmonicProbability hk S.online (A h).request
      have hrw :
          (∑ i : Fin k, harmonicProbability S.online (A h).request i *
            ((advance S (A h) i).onlineCost +
              Ψ (advance S (A h) i).online (advance S (A h) i).adversary +
              ρ * ((∑ w : Fin N → Fin k,
                realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                  ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                    S.adversaryCost)) - travel S.adversary (A h).moves))) =
          S.onlineCost +
          (∑ i : Fin k, harmonicProbability S.online (A h).request i *
            (harmonicCost S.online (A h).request i +
              Ψ (harmonicNext S.online (A h).request i) (execute S.adversary (A h).moves))) -
          ρ * travel S.adversary (A h).moves +
          ρ * ∑ i : Fin k, ∑ w : Fin N → Fin k,
            harmonicProbability S.online (A h).request i *
              realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
              ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                S.adversaryCost) := by
        have hterm : ∀ i : Fin k,
            harmonicProbability S.online (A h).request i *
              ((advance S (A h) i).onlineCost +
                Ψ (advance S (A h) i).online (advance S (A h) i).adversary +
                ρ * ((∑ w : Fin N → Fin k,
                  realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                    ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                      S.adversaryCost)) - travel S.adversary (A h).moves)) =
            (harmonicProbability S.online (A h).request i * S.onlineCost +
              harmonicProbability S.online (A h).request i *
                (harmonicCost S.online (A h).request i +
                  Ψ (harmonicNext S.online (A h).request i) (execute S.adversary (A h).moves)) -
              harmonicProbability S.online (A h).request i * (ρ * travel S.adversary (A h).moves)) +
            ρ * (∑ w : Fin N → Fin k,
              harmonicProbability S.online (A h).request i *
                realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                  S.adversaryCost)) := by
          intro i
          have hmul_w :
              harmonicProbability S.online (A h).request i *
                (∑ w : Fin N → Fin k,
                  realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                    ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                      S.adversaryCost)) =
              ∑ w : Fin N → Fin k,
                harmonicProbability S.online (A h).request i *
                  realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                  ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                    S.adversaryCost) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun w _ => by ring)
          calc harmonicProbability S.online (A h).request i *
                ((advance S (A h) i).onlineCost +
                  Ψ (advance S (A h) i).online (advance S (A h) i).adversary +
                  ρ * ((∑ w : Fin N → Fin k,
                    realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                      ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                        S.adversaryCost)) - travel S.adversary (A h).moves))
            _ = (harmonicProbability S.online (A h).request i * S.onlineCost +
                  harmonicProbability S.online (A h).request i *
                    (harmonicCost S.online (A h).request i +
                      Ψ (harmonicNext S.online (A h).request i) (execute S.adversary (A h).moves)) -
                  harmonicProbability S.online (A h).request i * (ρ * travel S.adversary (A h).moves)) +
                ρ * (harmonicProbability S.online (A h).request i *
                  (∑ w : Fin N → Fin k,
                    realPathWeightFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w) *
                      ((runFrom A (h ++ [i]) (advance S (A h) i) (List.ofFn w)).adversaryCost -
                        S.adversaryCost))) := by
              simp only [advance]; ring
            _ = _ := by rw [hmul_w]
        rw [Finset.sum_congr rfl (fun i _ => hterm i),
          Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hsum_p, one_mul, one_mul]
      rw [hrw]
      have hr := hround S.online S.adversary (A h) (hvalid h)
      linarith
  have hdet : ∀ (A : Adversary k V), ValidAdversary A X₀ Y₀ → ∀ N : ℕ,
      onlineExpectation A X₀ Y₀ N ≤
        ENNReal.ofReal ρ * adversaryExpectation A X₀ Y₀ N + ENNReal.ofReal (Ψ X₀ Y₀) := by
    intro A hvalid N
    have h0 := htree A hvalid N []
    have hS0 : stateAt A X₀ Y₀ [] = initial X₀ Y₀ := rfl
    dsimp only at h0
    rw [hS0] at h0
    have hinit_on : (initial X₀ Y₀).onlineCost = 0 := rfl
    have hinit_adv : (initial X₀ Y₀).adversaryCost = 0 := rfl
    have hinit_X : (initial X₀ Y₀).online = X₀ := rfl
    have hinit_Y : (initial X₀ Y₀).adversary = Y₀ := rfl
    rw [hinit_on, hinit_adv, hinit_X, hinit_Y] at h0
    simp only [zero_add, sub_zero] at h0
    have hon_le :
        (∑ w : Fin N → Fin k,
          realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
            (stateAt A X₀ Y₀ (List.ofFn w)).onlineCost) ≤
        ρ * (∑ w : Fin N → Fin k,
          realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
            (stateAt A X₀ Y₀ (List.ofFn w)).adversaryCost) + Ψ X₀ Y₀ := by
      have hdrop :
          (∑ w : Fin N → Fin k,
            realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
              (stateAt A X₀ Y₀ (List.ofFn w)).onlineCost) ≤
          ∑ w : Fin N → Fin k,
            realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
              ((runFrom A [] (initial X₀ Y₀) (List.ofFn w)).onlineCost +
                Ψ (runFrom A [] (initial X₀ Y₀) (List.ofFn w)).online
                  (runFrom A [] (initial X₀ Y₀) (List.ofFn w)).adversary) := by
        refine Finset.sum_le_sum (fun w _ => ?_)
        have hw := realPathWeightFrom_nonneg hk A [] (initial X₀ Y₀) (List.ofFn w)
        have hψ := hΨ_nonneg (runFrom A [] (initial X₀ Y₀) (List.ofFn w)).online
          (runFrom A [] (initial X₀ Y₀) (List.ofFn w)).adversary
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hψ) hw
      change _ ≤ ρ * (∑ w : Fin N → Fin k,
        realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
          (runFrom A [] (initial X₀ Y₀) (List.ofFn w)).adversaryCost) + Ψ X₀ Y₀
      linarith
    have hon_eq :
        onlineExpectation A X₀ Y₀ N =
        ENNReal.ofReal (∑ w : Fin N → Fin k,
          realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
            (stateAt A X₀ Y₀ (List.ofFn w)).onlineCost) := by
      unfold onlineExpectation treeExpectation pathWeight
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [ENNReal.ofReal_mul (realPathWeightFrom_nonneg hk _ _ _ _),
          ofReal_realPathWeightFrom hk]
      · intro w _
        exact mul_nonneg (realPathWeightFrom_nonneg hk _ _ _ _)
          (stateAt_costs_nonneg A X₀ Y₀ _).1
    have hadv_nonneg :
        0 ≤ ∑ w : Fin N → Fin k,
          realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
            (stateAt A X₀ Y₀ (List.ofFn w)).adversaryCost :=
      Finset.sum_nonneg (fun w _ =>
        mul_nonneg (realPathWeightFrom_nonneg hk _ _ _ _)
          (stateAt_costs_nonneg A X₀ Y₀ _).2)
    have hadv_eq :
        adversaryExpectation A X₀ Y₀ N =
        ENNReal.ofReal (∑ w : Fin N → Fin k,
          realPathWeightFrom A [] (initial X₀ Y₀) (List.ofFn w) *
            (stateAt A X₀ Y₀ (List.ofFn w)).adversaryCost) := by
      unfold adversaryExpectation treeExpectation pathWeight
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [ENNReal.ofReal_mul (realPathWeightFrom_nonneg hk _ _ _ _),
          ofReal_realPathWeightFrom hk]
      · intro w _
        exact mul_nonneg (realPathWeightFrom_nonneg hk _ _ _ _)
          (stateAt_costs_nonneg A X₀ Y₀ _).2
    rw [hon_eq, hadv_eq, ← ENNReal.ofReal_mul hρ,
      ← ENNReal.ofReal_add (mul_nonneg hρ hadv_nonneg) (hΨ_nonneg X₀ Y₀)]
    exact ENNReal.ofReal_le_ofReal hon_le
  refine ⟨Ψ X₀ Y₀, hΨ_nonneg X₀ Y₀, ?_⟩
  intro Ω _ μ _ A hM N
  unfold mixedOnline mixedAdversary
  have hmono :
      (∫⁻ ω, onlineExpectation (A ω) X₀ Y₀ N ∂μ) ≤
      ∫⁻ ω, (ENNReal.ofReal ρ * adversaryExpectation (A ω) X₀ Y₀ N +
        ENNReal.ofReal (Ψ X₀ Y₀)) ∂μ :=
    lintegral_mono (fun ω => hdet (A ω) (hM.1 ω) N)
  have haem_adv : AEMeasurable (fun ω => adversaryExpectation (A ω) X₀ Y₀ N) μ := by
    unfold adversaryExpectation treeExpectation
    let g : (Fin N → Fin k) → Ω → ℝ≥0∞ := fun w ω =>
      pathWeight (A ω) X₀ Y₀ (List.ofFn w) *
        ENNReal.ofReal (stateAt (A ω) X₀ Y₀ (List.ofFn w)).adversaryCost
    have hsum := Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin N → Fin k)))
      (f := g)
      (fun w _ => (hM.2.1 (List.ofFn w)).mul (hM.2.2.2 (List.ofFn w)))
    have heq : (∑ w : Fin N → Fin k, g w) = (fun ω => ∑ w : Fin N → Fin k, g w ω) := by
      funext ω
      exact Finset.sum_apply ω (Finset.univ : Finset (Fin N → Fin k)) g
    rwa [heq] at hsum
  rw [lintegral_add_right' _ aemeasurable_const,
    lintegral_const_mul'' _ haem_adv, lintegral_const, measure_univ, mul_one] at hmono
  exact hmono

/-- The trivial k = 1 case. -/
lemma harmonic_competitive_one {k : ℕ} (hk1 : k = 1) {V : Type*} [MetricSpace V]
    (X₀ Y₀ : KServer.Config k V) :
    AdaptiveCompetitive X₀ Y₀ (2 * (k : ℝ)^4) := by
  subst hk1
  have hk : 1 ≤ 1 := le_rfl
  let i₀ : Fin 1 := ⟨0, hk⟩
  refine adaptiveCompetitive_of_potential hk X₀ Y₀ (by positivity)
    (fun X Y => dist (X i₀) (Y i₀))
    (fun X Y => dist_nonneg) ?_ ?_
  · intro X Y Y'
    have h1 : dist (X i₀) (Y' i₀) - dist (X i₀) (Y i₀) ≤ dist (Y i₀) (Y' i₀) := by
      have := dist_triangle (X i₀) (Y i₀) (Y' i₀)
      linarith
    have h2 : KServer.moveCost Y Y' = dist (Y i₀) (Y' i₀) := by
      unfold KServer.moveCost
      rw [Fintype.sum_unique]
      rfl
    rw [h2]
    have hd : 0 ≤ dist (Y i₀) (Y' i₀) := dist_nonneg
    norm_num
    linarith
  · intro X Y r hcov
    rcases hcov with ⟨s, hs⟩
    have hs0 : s = i₀ := Subsingleton.elim s i₀
    subst hs0
    rw [Fintype.sum_unique]
    change harmonicProbability X r i₀ *
      (harmonicCost X r i₀ + dist (harmonicNext X r i₀ i₀) (Y i₀) - dist (X i₀) (Y i₀)) ≤ 0
    have hprob1 : harmonicProbability X r i₀ = 1 := by
      have h := sum_harmonicProbability hk X r
      rw [Fintype.sum_unique] at h
      exact h
    rw [hprob1, one_mul]
    by_cases hX : Covers X r
    · have hcost : harmonicCost X r i₀ = 0 := by simp [harmonicCost_eq, hX]
      have hnext : harmonicNext X r i₀ = X := by simp [harmonicNext, hX]
      rw [hcost, hnext]
      linarith
    · have hcost : harmonicCost X r i₀ = dist (X i₀) r := by simp [harmonicCost_eq, hX]
      have hnext : harmonicNext X r i₀ i₀ = r := by simp [harmonicNext, hX, relocate]
      rw [hcost, hnext, hs, dist_self]
      linarith

end Basics

/-! ## Section 2: Extended Metric Space (`V × ℝ` Isometric Lift) -/

section ExtendedMetric

/-- Embed `V` isometrically into `V × ℝ` via `v ↦ (v, 0)` and separate `k` initial servers via `(Y₀ j, j + 1)`. -/
abbrev ExtSpace {k : ℕ} {V : Type*} (_Y₀ : KServer.Config k V) := V × ℝ

namespace ExtSpace

def inl {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V) (v : V) : ExtSpace Y₀ :=
  (v, 0)

def inr {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V) (j : Fin k) : ExtSpace Y₀ :=
  (Y₀ j, (j.val : ℝ) + 1)

lemma inl_injective {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V) :
    Function.Injective (inl Y₀) := by
  intro x y h
  exact (Prod.ext_iff.mp h).1

lemma inr_injective {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V) :
    Function.Injective (inr Y₀) := by
  intro i j h
  have h2 : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 := (Prod.ext_iff.mp h).2
  have hreal : (i.val : ℝ) = (j.val : ℝ) := by linarith
  exact Fin.ext (Nat.cast_injective hreal)

lemma dist_inl {k : ℕ} {V : Type*} [MetricSpace V] (Y₀ : KServer.Config k V) (x y : V) :
    dist (inl Y₀ x) (inl Y₀ y) = dist x y := by
  simp [inl, Prod.dist_eq, dist_nonneg]

def liftConfig {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V)
    (X : KServer.Config k V) : KServer.Config k (ExtSpace Y₀) :=
  fun i => inl Y₀ (X i)

lemma covers_liftConfig_iff {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V)
    (X : KServer.Config k V) (r : V) :
    Covers (liftConfig Y₀ X) (inl Y₀ r) ↔ Covers X r := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, inl_injective Y₀ hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg (inl Y₀) hi⟩

lemma moveCost_liftConfig {k : ℕ} {V : Type*} [MetricSpace V] (Y₀ : KServer.Config k V)
    (X Y : KServer.Config k V) :
    KServer.moveCost (liftConfig Y₀ X) (liftConfig Y₀ Y) = KServer.moveCost X Y := by
  unfold KServer.moveCost liftConfig
  exact Finset.sum_congr rfl (fun i _ => dist_inl Y₀ _ _)

lemma relocate_liftConfig {k : ℕ} {V : Type*} (Y₀ : KServer.Config k V)
    (X : KServer.Config k V) (i : Fin k) (r : V) :
    relocate (liftConfig Y₀ X) i (inl Y₀ r) = liftConfig Y₀ (relocate X i r) := by
  classical
  funext j
  unfold relocate liftConfig
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma normalizer_liftConfig {k : ℕ} {V : Type*} [MetricSpace V] (Y₀ : KServer.Config k V)
    (X : KServer.Config k V) (r : V) :
    normalizer (liftConfig Y₀ X) (inl Y₀ r) = normalizer X r := by
  unfold normalizer liftConfig
  exact Finset.sum_congr rfl (fun j _ => by rw [dist_inl])

lemma harmonicProbability_liftConfig {k : ℕ} {V : Type*} [MetricSpace V]
    (Y₀ : KServer.Config k V) (X : KServer.Config k V) (r : V) (i : Fin k) :
    harmonicProbability (liftConfig Y₀ X) (inl Y₀ r) i = harmonicProbability X r i := by
  classical
  unfold harmonicProbability
  simp [covers_liftConfig_iff, normalizer_liftConfig, liftConfig, dist_inl]

end ExtSpace
end ExtendedMetric

/-! ## Section 3: Electrical Networks & Minimum-Energy Flows (§4.1, §4.3, Appendix A) -/

section ElectricalNetwork

def IsFlowFor {k : ℕ} (F : Fin k → Fin k → ℝ) (a : Fin k → ℝ) : Prop :=
  (∀ i j, F i j = - F j i) ∧ (∀ i, ∑ j : Fin k, F i j = a i)

lemma isFlowFor_diag {k : ℕ} {F : Fin k → Fin k → ℝ} {a : Fin k → ℝ}
    (hF : IsFlowFor F a) (i : Fin k) : F i i = 0 := by
  linarith [hF.1 i i]

lemma exists_isFlowFor {k : ℕ} (hk : 1 ≤ k) {a : Fin k → ℝ} (ha : ∑ i : Fin k, a i = 0) :
    ∃ F : Fin k → Fin k → ℝ, IsFlowFor F a := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨fun i j => (a i - a j) / (k : ℝ), ?_, ?_⟩
  · intro i j; ring
  · intro i
    have hrew : ∀ j : Fin k, (a i - a j) / (k : ℝ) = a i / (k : ℝ) - a j / (k : ℝ) :=
      fun j => by ring
    simp_rw [hrew, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_div, ha, zero_div, sub_zero]
    field_simp [hk_ne]

noncomputable def flowEnergy {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (F : Fin k → Fin k → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin k, ∑ j : Fin k, dist (Y i) (Y j) * (F i j)^2

lemma flowEnergy_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (F : Fin k → Fin k → ℝ) :
    0 ≤ flowEnergy Y F := by
  unfold flowEnergy
  refine mul_nonneg (by norm_num) ?_
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg dist_nonneg (sq_nonneg _)))

noncomputable def elecEnergy {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (a : Fin k → ℝ) : ℝ :=
  sInf { v : ℝ | ∃ F : Fin k → Fin k → ℝ, IsFlowFor F a ∧ v = flowEnergy Y F }

lemma elecEnergy_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (a : Fin k → ℝ) :
    0 ≤ elecEnergy Y a := by
  unfold elecEnergy
  refine Real.sInf_nonneg ?_
  rintro v ⟨F, _, rfl⟩
  exact flowEnergy_nonneg Y F

lemma elecEnergy_bddBelow {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (a : Fin k → ℝ) :
    BddBelow { v : ℝ | ∃ F : Fin k → Fin k → ℝ, IsFlowFor F a ∧ v = flowEnergy Y F } :=
  ⟨0, by rintro v ⟨F, _, rfl⟩; exact flowEnergy_nonneg Y F⟩

lemma elecEnergy_le_flowEnergy {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {a : Fin k → ℝ} {F : Fin k → Fin k → ℝ}
    (hF : IsFlowFor F a) :
    elecEnergy Y a ≤ flowEnergy Y F :=
  csInf_le (elecEnergy_bddBelow Y a) ⟨F, hF, rfl⟩

lemma elecEnergy_neg {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (a : Fin k → ℝ) :
    elecEnergy Y (-a) = elecEnergy Y a := by
  unfold elecEnergy
  congr 1
  ext v
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨fun i j => - F i j, ⟨fun i j => by linarith [hF.1 i j], fun i => ?_⟩, ?_⟩
    · simp [Finset.sum_neg_distrib, hF.2 i]
    · unfold flowEnergy
      congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  · rintro ⟨F, hF, rfl⟩
    refine ⟨fun i j => - F i j, ⟨fun i j => by linarith [hF.1 i j], fun i => ?_⟩, ?_⟩
    · simp [Finset.sum_neg_distrib, hF.2 i]
    · unfold flowEnergy
      congr 1
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

noncomputable def conductance {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (i j : Fin k) : ℝ := by
  classical
  exact if i = j then 0 else 1 / dist (Y i) (Y j)

lemma conductance_symm {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (i j : Fin k) :
    conductance Y i j = conductance Y j i := by
  classical
  unfold conductance
  by_cases h : i = j
  · subst h; rfl
  · have h' : j ≠ i := Ne.symm h
    simp [h, h', dist_comm]

lemma conductance_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (i j : Fin k) :
    0 ≤ conductance Y i j := by
  classical
  unfold conductance
  split_ifs
  · exact le_rfl
  · exact div_nonneg zero_le_one dist_nonneg

lemma conductance_pos {k : ℕ} {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y) {i j : Fin k} (hij : i ≠ j) :
    0 < conductance Y i j := by
  classical
  unfold conductance
  rw [if_neg hij]
  exact div_pos one_pos (dist_pos.mpr (hY.ne hij))

noncomputable def laplacian {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun h i := ∑ j : Fin k, conductance Y i j * (h i - h j)
  map_add' h₁ h₂ := by
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  map_smul' c h := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

lemma sum_laplacian {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (h : Fin k → ℝ) :
    ∑ i : Fin k, laplacian Y h i = 0 := by
  change ∑ i : Fin k, ∑ j : Fin k, conductance Y i j * (h i - h j) = 0
  have hsplit : ∀ i : Fin k,
      (∑ j : Fin k, conductance Y i j * (h i - h j)) =
      (∑ j : Fin k, conductance Y i j * h i) - (∑ j : Fin k, conductance Y i j * h j) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => conductance Y i j * h j)]
  have hsymm :
      (∑ j : Fin k, ∑ i : Fin k, conductance Y i j * h j) =
      (∑ j : Fin k, ∑ i : Fin k, conductance Y j i * h j) :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by rw [conductance_symm]))
  rw [hsymm, sub_self]

lemma dirichlet_laplacian {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (h : Fin k → ℝ) :
    ∑ i : Fin k, h i * laplacian Y h i =
      (1 / 2 : ℝ) * ∑ i : Fin k, ∑ j : Fin k, conductance Y i j * (h i - h j)^2 := by
  have hlhs :
      (∑ i : Fin k, h i * laplacian Y h i) =
      ∑ i : Fin k, ∑ j : Fin k, h i * (conductance Y i j * (h i - h j)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change h i * (∑ j : Fin k, conductance Y i j * (h i - h j)) = _
    rw [Finset.mul_sum]
  rw [hlhs]
  have hswap :
      (∑ i : Fin k, ∑ j : Fin k, h i * (conductance Y i j * (h i - h j))) =
      ∑ i : Fin k, ∑ j : Fin k, - (h j * (conductance Y i j * (h i - h j))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [conductance_symm Y j i]
    ring
  linarith [show
    (∑ i : Fin k, ∑ j : Fin k, h i * (conductance Y i j * (h i - h j))) +
    (∑ i : Fin k, ∑ j : Fin k, - (h j * (conductance Y i j * (h i - h j)))) =
    ∑ i : Fin k, ∑ j : Fin k, conductance Y i j * (h i - h j)^2 by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)]

def zeroSumSubmodule (k : ℕ) : Submodule ℝ (Fin k → ℝ) where
  carrier := { a | ∑ i : Fin k, a i = 0 }
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ∑ i : Fin k, (a i + b i) = 0
    rw [Finset.sum_add_distrib, ha, hb, add_zero]
  smul_mem' c {a} ha := by
    change ∑ i : Fin k, c * a i = 0
    rw [← Finset.mul_sum, ha, mul_zero]

/-- Existence of a voltage-induced flow for any zero-sum excess vector on injective `Y`. -/
lemma exists_voltage_flow {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {a : Fin k → ℝ} (ha : ∑ i : Fin k, a i = 0) :
    ∃ (F : Fin k → Fin k → ℝ) (h : Fin k → ℝ),
      IsFlowFor F a ∧
      (∀ i j, F i j = conductance Y i j * (h i - h j)) ∧
      (∀ i j, dist (Y i) (Y j) * F i j = h i - h j) := by
  let L_W : zeroSumSubmodule k →ₗ[ℝ] zeroSumSubmodule k :=
    (laplacian Y).restrict (fun h _ => sum_laplacian Y h)
  have hinj : Function.Injective L_W := by
    rw [injective_iff_map_eq_zero]
    intro h hh0
    have hl : ∀ i : Fin k, laplacian Y h.1 i = 0 := by
      intro i
      exact congrFun (congrArg Subtype.val hh0) i
    have hdir := dirichlet_laplacian Y h.1
    simp only [hl, mul_zero, Finset.sum_const_zero] at hdir
    have hsum0 : ∑ i : Fin k, ∑ j : Fin k, conductance Y i j * (h.1 i - h.1 j)^2 = 0 := by
      linarith
    have hrow0 : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        ∑ j : Fin k, conductance Y i j * (h.1 i - h.1 j)^2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hsum0
      intro i _
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (conductance_nonneg Y i j) (sq_nonneg _))
    have hentry0 : ∀ i j : Fin k, conductance Y i j * (h.1 i - h.1 j)^2 = 0 := by
      intro i j
      have hr := hrow0 i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j' _ => mul_nonneg (conductance_nonneg Y i j') (sq_nonneg _))).mp hr j
        (Finset.mem_univ j)
    let i₀ : Fin k := ⟨0, hk⟩
    have hconst : ∀ j : Fin k, h.1 j = h.1 i₀ := by
      intro j
      by_cases hij : j = i₀
      · subst hij; rfl
      · have hpos := conductance_pos hY hij
        have he := hentry0 j i₀
        have hsq : (h.1 j - h.1 i₀)^2 = 0 := by
          rcases mul_eq_zero.mp he with hc | hs
          · linarith
          · exact hs
        linarith [sq_eq_zero_iff.mp hsq]
    have hsum_h : ∑ j : Fin k, h.1 j = 0 := h.2
    simp_rw [hconst] at hsum_h
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_h
    have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hi0 : h.1 i₀ = 0 := by
      rcases mul_eq_zero.mp hsum_h with h1 | h2
      · exact absurd h1 hk_ne
      · exact h2
    ext j
    rw [hconst j, hi0]
    rfl
  have hsurj : Function.Surjective L_W := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨⟨h, _⟩, hh⟩ := hsurj ⟨a, ha⟩
  let F : Fin k → Fin k → ℝ := fun i j => conductance Y i j * (h i - h j)
  refine ⟨F, h, ⟨?_, ?_⟩, fun _ _ => rfl, ?_⟩
  · intro i j
    dsimp only [F]
    rw [conductance_symm Y i j]
    ring
  · intro i
    exact congrFun (congrArg Subtype.val hh) i
  · intro i j
    classical
    dsimp only [F, conductance]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij]
      have hd : dist (Y i) (Y j) ≠ 0 := dist_ne_zero.mpr (hY.ne hij)
      field_simp [hd]

/-- Cross-term identity in Appendix A: `(1/2) ∑ i, ∑ j, d_{ij} F_{ij} G_{ij} = ∑ i, h_i b_i`. -/
lemma voltage_flow_cross_term {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {F G : Fin k → Fin k → ℝ} {h b : Fin k → ℝ}
    (hOhm : ∀ i j, dist (Y i) (Y j) * F i j = h i - h j)
    (hG : IsFlowFor G b) :
    (1 / 2 : ℝ) * (∑ i : Fin k, ∑ j : Fin k, dist (Y i) (Y j) * F i j * G i j) =
      ∑ i : Fin k, h i * b i := by
  simp_rw [hOhm]
  have hsplit : ∀ i : Fin k,
      (∑ j : Fin k, (h i - h j) * G i j) =
      h i * (∑ j : Fin k, G i j) - ∑ j : Fin k, h j * G i j := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [hsplit, Finset.sum_sub_distrib, hG.2]
  have hcol :
      (∑ i : Fin k, ∑ j : Fin k, h j * G i j) = - ∑ j : Fin k, h j * b j := by
    rw [Finset.sum_comm]
    have h1 : ∀ j : Fin k,
        (∑ i : Fin k, h j * G i j) = - (h j * b j) := by
      intro j
      rw [← Finset.mul_sum]
      have hskew : (∑ i : Fin k, G i j) = - (∑ i : Fin k, G j i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => hG.1 i j)
      rw [hskew, hG.2 j]
      ring
    simp_rw [h1, Finset.sum_neg_distrib]
  linarith

lemma flowEnergy_add_of_voltage {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {F G : Fin k → Fin k → ℝ} {h b : Fin k → ℝ}
    (hOhm : ∀ i j, dist (Y i) (Y j) * F i j = h i - h j)
    (hG : IsFlowFor G b) :
    flowEnergy Y (fun i j => F i j + G i j) =
      flowEnergy Y F + 2 * (∑ i : Fin k, h i * b i) + flowEnergy Y G := by
  have hexp :
      flowEnergy Y (fun i j => F i j + G i j) =
      flowEnergy Y F +
      2 * ((1 / 2 : ℝ) * ∑ i : Fin k, ∑ j : Fin k, dist (Y i) (Y j) * F i j * G i j) +
      flowEnergy Y G := by
    unfold flowEnergy
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hexp, voltage_flow_cross_term Y hOhm hG]

/-- A voltage-induced flow attains the minimum electrical energy `elecEnergy Y a`. -/
lemma elecEnergy_eq_of_voltage_flow {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {F : Fin k → Fin k → ℝ} {a h : Fin k → ℝ}
    (hF : IsFlowFor F a)
    (hOhm : ∀ i j, dist (Y i) (Y j) * F i j = h i - h j) :
    elecEnergy Y a = flowEnergy Y F := by
  refine le_antisymm (elecEnergy_le_flowEnergy Y hF) ?_
  refine le_csInf ⟨flowEnergy Y F, F, hF, rfl⟩ ?_
  rintro v ⟨F', hF', rfl⟩
  let G : Fin k → Fin k → ℝ := fun i j => F' i j - F i j
  have hG : IsFlowFor G (fun _ => 0) := by
    refine ⟨fun i j => by dsimp [G]; linarith [hF'.1 i j, hF.1 i j], fun i => ?_⟩
    dsimp [G]
    rw [Finset.sum_sub_distrib, hF'.2 i, hF.2 i, sub_self]
  have hFG : (fun i j => F i j + G i j) = F' := by
    ext i j; dsimp [G]; ring
  have hadd := flowEnergy_add_of_voltage Y hOhm hG
  rw [hFG] at hadd
  simp only [mul_zero, Finset.sum_const_zero] at hadd
  linarith [flowEnergy_nonneg Y G]

/-- Lemma 4.1 quadratic expansion: `E(a + b) = E(a) + 2 ∑ b_i h_i + E(b)`. -/
lemma elecEnergy_add_of_voltage_flow {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {F : Fin k → Fin k → ℝ} {a b h : Fin k → ℝ}
    (hF : IsFlowFor F a)
    (hOhm : ∀ i j, dist (Y i) (Y j) * F i j = h i - h j)
    (hb : ∑ i : Fin k, b i = 0) :
    elecEnergy Y (fun i => a i + b i) =
      elecEnergy Y a + 2 * (∑ i : Fin k, b i * h i) + elecEnergy Y b := by
  obtain ⟨G, hG, hGO, _, hGOhm⟩ := exists_voltage_flow hk hY hb
  have hFG_flow : IsFlowFor (fun i j => F i j + G i j) (fun i => a i + b i) := by
    refine ⟨fun i j => by linarith [hF.1 i j, hGO.1 i j], fun i => ?_⟩
    rw [Finset.sum_add_distrib, hF.2 i, hGO.2 i]
  have hFG_ohm : ∀ i j, dist (Y i) (Y j) * (F i j + G i j) = (h i + hG i) - (h j + hG j) := by
    intro i j
    have h1 := hOhm i j
    have h2 := hGOhm i j
    linarith
  rw [elecEnergy_eq_of_voltage_flow Y hFG_flow hFG_ohm,
    elecEnergy_eq_of_voltage_flow Y hF hOhm,
    elecEnergy_eq_of_voltage_flow Y hGO hGOhm,
    flowEnergy_add_of_voltage Y hOhm hGO]
  have hcomm : (∑ i : Fin k, h i * b i) = ∑ i : Fin k, b i * h i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hcomm]

/-- Sublevel-cut flow and voltage stability (Lemma 4.3, part 1). -/
lemma voltage_flow_bounds {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {F : Fin k → Fin k → ℝ} {a h : Fin k → ℝ}
    (hF : IsFlowFor F a)
    (hF_cond : ∀ i j, F i j = conductance Y i j * (h i - h j))
    (hOhm : ∀ i j, dist (Y i) (Y j) * F i j = h i - h j) :
    let T := ∑ u : Fin k, max (a u) 0
    (∀ i j : Fin k, |h i - h j| ≤ T * dist (Y i) (Y j)) ∧
    (∀ i : Fin k, ∑ j : Fin k, (F i j)^2 ≤ 2 * T^2) := by
  classical
  intro T
  have hcut_skew : ∀ S : Finset (Fin k), ∑ u ∈ S, ∑ v ∈ S, F u v = 0 := by
    intro S
    have hswap : (∑ u ∈ S, ∑ v ∈ S, F u v) = - (∑ u ∈ S, ∑ v ∈ S, F u v) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun v _ => hF.1 v u)
    linarith
  have hout : ∀ i : Fin k, ∑ j : Fin k, max (F i j) 0 ≤ T := by
    intro i
    let A : Finset (Fin k) := Finset.univ.filter (fun u => h i ≤ h u)
    let B : Finset (Fin k) := Finset.univ.filter (fun v => h v < h i)
    have hAB_compl : B = Aᶜ := by
      ext v; simp [A, B]
    have hiA : i ∈ A := by simp [A]
    have hnonneg_AB : ∀ u ∈ A, ∀ v ∈ B, 0 ≤ F u v := by
      intro u hu v hv
      have hu' : h i ≤ h u := (Finset.mem_filter.mp hu).2
      have hv' : h v < h i := (Finset.mem_filter.mp hv).2
      rw [hF_cond u v]
      exact mul_nonneg (conductance_nonneg Y u v) (by linarith)
    have hmax_i : (∑ j : Fin k, max (F i j) 0) = ∑ v ∈ B, F i v := by
      rw [← Finset.sum_add_sum_compl B]
      have hB : (∑ v ∈ B, max (F i v) 0) = ∑ v ∈ B, F i v :=
        Finset.sum_congr rfl (fun v hv => max_eq_left (hnonneg_AB i hiA v hv))
      have hBc : (∑ v ∈ Bᶜ, max (F i v) 0) = 0 := by
        refine Finset.sum_eq_zero (fun v hv => max_eq_right ?_)
        have hv' : h i ≤ h v := by
          have : ¬ h v < h i := by simpa [B] using hv
          linarith
        rw [hF_cond i v]
        exact mul_nonpos_of_nonneg_of_nonpos (conductance_nonneg Y i v) (by linarith)
      rw [hB, hBc, add_zero]
    have hle_AB : (∑ v ∈ B, F i v) ≤ ∑ u ∈ A, ∑ v ∈ B, F u v :=
      Finset.single_le_sum (fun u hu => Finset.sum_nonneg (hnonneg_AB u hu)) hiA
    have hAB_eq : (∑ u ∈ A, ∑ v ∈ B, F u v) = ∑ u ∈ A, a u := by
      have h1 : ∀ u ∈ A, a u = (∑ v ∈ A, F u v) + (∑ v ∈ B, F u v) := by
        intro u _
        rw [hAB_compl, Finset.sum_add_sum_compl, hF.2 u]
      have h2 := Finset.sum_congr rfl h1
      rw [Finset.sum_add_distrib, hcut_skew A, zero_add] at h2
      exact h2.symm
    have hA_le_T : (∑ u ∈ A, a u) ≤ T := by
      calc ∑ u ∈ A, a u
        _ ≤ ∑ u ∈ A, max (a u) 0 := Finset.sum_le_sum (fun u _ => le_max_left _ _)
        _ ≤ ∑ u ∈ Finset.univ, max (a u) 0 :=
          Finset.sum_le_univ_sum_of_nonneg (fun u => le_max_right _ _)
    linarith
  have hin : ∀ i : Fin k, ∑ j : Fin k, max (- F i j) 0 ≤ T := by
    intro i
    let A' : Finset (Fin k) := Finset.univ.filter (fun u => h i < h u)
    let B' : Finset (Fin k) := Finset.univ.filter (fun v => h v ≤ h i)
    have hAB'_compl : B' = A'ᶜ := by
      ext v; simp [A', B']
    have hiB' : i ∈ B' := by simp [B']
    have hnonneg_AB' : ∀ u ∈ A', ∀ v ∈ B', 0 ≤ F u v := by
      intro u hu v hv
      have hu' : h i < h u := (Finset.mem_filter.mp hu).2
      have hv' : h v ≤ h i := (Finset.mem_filter.mp hv).2
      rw [hF_cond u v]
      exact mul_nonneg (conductance_nonneg Y u v) (by linarith)
    have hmax_i : (∑ u : Fin k, max (- F i u) 0) = ∑ u ∈ A', F u i := by
      rw [← Finset.sum_add_sum_compl A']
      have hA' : (∑ u ∈ A', max (- F i u) 0) = ∑ u ∈ A', F u i := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        have hskew : - F i u = F u i := by linarith [hF.1 i u]
        rw [hskew]
        exact max_eq_left (hnonneg_AB' u hu i hiB')
      have hA'c : (∑ u ∈ A'ᶜ, max (- F i u) 0) = 0 := by
        refine Finset.sum_eq_zero (fun u hu => ?_)
        have hskew : - F i u = F u i := by linarith [hF.1 i u]
        rw [hskew]
        refine max_eq_right ?_
        have hu' : h u ≤ h i := by
          have : ¬ h i < h u := by simpa [A'] using hu
          linarith
        rw [hF_cond u i]
        exact mul_nonpos_of_nonneg_of_nonpos (conductance_nonneg Y u i) (by linarith)
      rw [hA', hA'c, add_zero]
    have hle_AB' : (∑ u ∈ A', F u i) ≤ ∑ u ∈ A', ∑ v ∈ B', F u v := by
      rw [Finset.sum_comm (s := A') (t := B')]
      exact Finset.single_le_sum (fun v hv => Finset.sum_nonneg (fun u hu => hnonneg_AB' u hu v hv)) hiB'
    have hAB'_eq : (∑ u ∈ A', ∑ v ∈ B', F u v) = ∑ u ∈ A', a u := by
      have h1 : ∀ u ∈ A', a u = (∑ v ∈ A', F u v) + (∑ v ∈ B', F u v) := by
        intro u _
        rw [hAB'_compl, Finset.sum_add_sum_compl, hF.2 u]
      have h2 := Finset.sum_congr rfl h1
      rw [Finset.sum_add_distrib, hcut_skew A', zero_add] at h2
      exact h2.symm
    have hA'_le_T : (∑ u ∈ A', a u) ≤ T := by
      calc ∑ u ∈ A', a u
        _ ≤ ∑ u ∈ A', max (a u) 0 := Finset.sum_le_sum (fun u _ => le_max_left _ _)
        _ ≤ ∑ u ∈ Finset.univ, max (a u) 0 :=
          Finset.sum_le_univ_sum_of_nonneg (fun u => le_max_right _ _)
    linarith
  have hT_nonneg : 0 ≤ T :=
    Finset.sum_nonneg (fun u _ => le_max_right _ _)
  have habs_le : ∀ i j : Fin k, |F i j| ≤ T := by
    intro i j
    rcases le_total 0 (F i j) with hpos | hneg
    · rw [abs_of_nonneg hpos, ← max_eq_left hpos]
      exact le_trans
        (Finset.single_le_sum (f := fun v => max (F i v) 0)
          (fun v _ => le_max_right _ _) (Finset.mem_univ j))
        (hout i)
    · rw [abs_of_nonpos hneg, ← max_eq_left (show 0 ≤ - F i j by linarith)]
      exact le_trans
        (Finset.single_le_sum (f := fun v => max (- F i v) 0)
          (fun v _ => le_max_right _ _) (Finset.mem_univ j))
        (hin i)
  refine ⟨?_, ?_⟩
  · intro i j
    rw [← hOhm i j, abs_mul, abs_of_nonneg dist_nonneg, mul_comm]
    exact mul_le_mul_of_nonneg_right (habs_le i j) dist_nonneg
  · intro i
    have hsum_abs : ∑ j : Fin k, |F i j| ≤ 2 * T := by
      have hdecomp : ∀ j : Fin k, |F i j| = max (F i j) 0 + max (- F i j) 0 := by
        intro j
        rcases le_total 0 (F i j) with hpos | hneg
        · rw [abs_of_nonneg hpos, max_eq_left hpos, max_eq_right (by linarith), add_zero]
        · rw [abs_of_nonpos hneg, max_eq_right hneg, max_eq_left (by linarith), zero_add]
      simp_rw [hdecomp, Finset.sum_add_distrib]
      linarith [hout i, hin i]
    calc ∑ j : Fin k, (F i j)^2
      _ = ∑ j : Fin k, |F i j| * |F i j| :=
        Finset.sum_congr rfl (fun j _ => by rw [← sq, sq_abs])
      _ ≤ ∑ j : Fin k, T * |F i j| :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (habs_le i j) (abs_nonneg _))
      _ = T * ∑ j : Fin k, |F i j| := (Finset.mul_sum _ _ _).symm
      _ ≤ T * (2 * T) := mul_le_mul_of_nonneg_left hsum_abs hT_nonneg
      _ = 2 * T^2 := by ring

/-- Energy stability under single-server adversary movement (Lemma 4.3, part 2). -/
lemma elecEnergy_relocate_le {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    (i₀ : Fin k) (p : M) {a : Fin k → ℝ} (ha : ∑ i : Fin k, a i = 0) :
    let T := ∑ u : Fin k, max (a u) 0
    elecEnergy (relocate Y i₀ p) a ≤ elecEnergy Y a + 2 * T^2 * dist (Y i₀) p := by
  classical
  intro T
  obtain ⟨F, h, hF, hF_cond, hOhm⟩ := exists_voltage_flow hk hY ha
  have hE_eq := elecEnergy_eq_of_voltage_flow Y hF hOhm
  have hsq_le := (voltage_flow_bounds Y hF hF_cond hOhm).2 i₀
  have hle_cand := elecEnergy_le_flowEnergy (relocate Y i₀ p) hF
  set δ := dist (Y i₀) p
  have hδ : 0 ≤ δ := dist_nonneg
  have hdist_diff : ∀ u v : Fin k,
      dist (relocate Y i₀ p u) (relocate Y i₀ p v) ≤
      dist (Y u) (Y v) + (if u = i₀ then δ else 0) + (if v = i₀ then δ else 0) := by
    intro u v
    unfold relocate
    by_cases hu : u = i₀ <;> by_cases hv : v = i₀
    · subst hu; subst hv
      simp only [Function.update_self, dist_self, ↓reduceIte]
      linarith
    · subst hu
      simp only [Function.update_self, Function.update_of_ne hv, ↓reduceIte, hv, add_zero]
      have := dist_triangle p (Y u) (Y v)
      rw [dist_comm p (Y u)] at this
      linarith
    · subst hv
      simp only [Function.update_self, Function.update_of_ne hu, ↓reduceIte, hu]
      have := dist_triangle (Y u) (Y v) p
      linarith
    · simp [hu, hv]
  have hflow_diff :
      flowEnergy (relocate Y i₀ p) F ≤ flowEnergy Y F + δ * (∑ v : Fin k, (F i₀ v)^2) := by
    unfold flowEnergy
    have hsum_le :
        (∑ u : Fin k, ∑ v : Fin k, dist (relocate Y i₀ p u) (relocate Y i₀ p v) * (F u v)^2) ≤
        ∑ u : Fin k, ∑ v : Fin k,
          (dist (Y u) (Y v) + (if u = i₀ then δ else 0) + (if v = i₀ then δ else 0)) * (F u v)^2 :=
      Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_right (hdist_diff u v) (sq_nonneg _)))
    have hrhs :
        (∑ u : Fin k, ∑ v : Fin k,
          (dist (Y u) (Y v) + (if u = i₀ then δ else 0) + (if v = i₀ then δ else 0)) * (F u v)^2) =
        (∑ u : Fin k, ∑ v : Fin k, dist (Y u) (Y v) * (F u v)^2) +
        2 * δ * (∑ v : Fin k, (F i₀ v)^2) := by
      have h1 : ∀ u v : Fin k,
          (dist (Y u) (Y v) + (if u = i₀ then δ else 0) + (if v = i₀ then δ else 0)) * (F u v)^2 =
          dist (Y u) (Y v) * (F u v)^2 +
          (if u = i₀ then δ * (F u v)^2 else 0) +
          (if v = i₀ then δ * (F u v)^2 else 0) := by
        intro u v; split_ifs <;> ring
      simp_rw [h1, Finset.sum_add_distrib]
      have hA :
          (∑ u : Fin k, ∑ v : Fin k, if u = i₀ then δ * (F u v)^2 else 0) =
          δ * ∑ v : Fin k, (F i₀ v)^2 := by
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
      have hB :
          (∑ u : Fin k, ∑ v : Fin k, if v = i₀ then δ * (F u v)^2 else 0) =
          δ * ∑ v : Fin k, (F i₀ v)^2 := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [hF.1 u i₀]
        ring
      linarith
    linarith
  have hmul : δ * (∑ v : Fin k, (F i₀ v)^2) ≤ δ * (2 * T^2) :=
    mul_le_mul_of_nonneg_left hsq_le hδ
  linarith

end ElectricalNetwork

/-! ## Section 4: Corrected Occupancy Potential & Harmonic Potential (§4.2–§5) -/

section HarmonicPotential

noncomputable def stdBasis {k : ℕ} (i : Fin k) : Fin k → ℝ := by
  classical
  exact fun j => if j = i then 1 else 0

lemma sum_stdBasis {k : ℕ} (i : Fin k) : ∑ j : Fin k, stdBasis i j = 1 := by
  classical
  simp [stdBasis]

noncomputable def spreadVec {k : ℕ} (i : Fin k) : Fin k → ℝ :=
  fun j => stdBasis i j - 1 / (k : ℝ)

lemma sum_spreadVec {k : ℕ} (hk : 1 ≤ k) (i : Fin k) :
    ∑ j : Fin k, spreadVec i j = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold spreadVec
  rw [Finset.sum_sub_distrib, sum_stdBasis, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one_div_cancel hk_ne, sub_self]

lemma posExcess_spreadVec_le_one {k : ℕ} (i : Fin k) :
    ∑ j : Fin k, max (spreadVec i j) 0 ≤ 1 := by
  classical
  have hle : ∀ j : Fin k, max (spreadVec i j) 0 ≤ stdBasis i j := by
    intro j
    unfold spreadVec stdBasis
    by_cases h : j = i
    · subst h
      simp only [↓reduceIte]
      have hk0 : 0 ≤ 1 / (k : ℝ) := by positivity
      exact max_le (by linarith) zero_le_one
    · simp only [h, ↓reduceIte, zero_sub]
      have hk0 : - (1 / (k : ℝ)) ≤ 0 := by
        have : 0 ≤ 1 / (k : ℝ) := by positivity
        linarith
      rw [max_eq_right hk0]
  exact le_trans (Finset.sum_le_sum (fun j _ => hle j)) (le_of_eq (sum_stdBasis i))

noncomputable def spreadEnergy {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (i : Fin k) : ℝ :=
  elecEnergy Y (spreadVec i)

noncomputable def corrEnergy {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) (q : Fin k → ℝ) : ℝ :=
  ((k : ℝ)^2 / 2) * (elecEnergy Y (fun j => q j - 1) + ∑ j : Fin k, q j * spreadEnergy Y j)

lemma corrEnergy_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (Y : KServer.Config k M) {q : Fin k → ℝ} (hq : ∀ j, 0 ≤ q j) :
    0 ≤ corrEnergy Y q := by
  unfold corrEnergy
  refine mul_nonneg (by positivity) (add_nonneg (elecEnergy_nonneg _ _) ?_)
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hq j) (elecEnergy_nonneg _ _))

noncomputable def occ {k : ℕ} (f : Fin k → Fin k) (i : Fin k) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun ℓ : Fin k => f ℓ = i)).card : ℝ)

lemma occ_nonneg {k : ℕ} (f : Fin k → Fin k) (i : Fin k) : 0 ≤ occ f i := by
  classical
  unfold occ
  positivity

lemma sum_occ {k : ℕ} (f : Fin k → Fin k) : ∑ i : Fin k, occ f i = (k : ℝ) := by
  classical
  unfold occ
  rw [← Nat.cast_sum]
  congr 1
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset (Fin k)))
    (fun x _ => Finset.mem_univ (f x))
  simpa using hcard.symm

lemma occ_update_eq {k : ℕ} (f : Fin k → Fin k) (ℓ s : Fin k) :
    occ (Function.update f ℓ s) = fun j => occ f j - stdBasis (f ℓ) j + stdBasis s j := by
  classical
  ext j
  unfold occ stdBasis
  let S₁ := Finset.univ.filter (fun m : Fin k => f m = j)
  let S₂ := Finset.univ.filter (fun m : Fin k => Function.update f ℓ s m = j)
  change (S₂.card : ℝ) = (S₁.card : ℝ) - (if j = f ℓ then 1 else 0) + (if j = s then 1 else 0)
  by_cases hjs : j = s <;> by_cases hjf : j = f ℓ
  · subst hjs
    have hS : S₂ = S₁ := by
      ext m
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hm : m = ℓ
      · subst hm; simp [hjf]
      · simp [hm]
    rw [hS]
    simp [hjf]
  · subst hjs
    have hnot : ℓ ∉ S₁ := by simp [S₁, Ne.symm hjf]
    have hS : S₂ = insert ℓ S₁ := by
      ext m
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hm : m = ℓ
      · subst hm; simp
      · simp [hm]
    rw [hS, Finset.card_insert_of_notMem hnot]
    push_cast
    simp [hjf]
  · subst hjf
    have hmem : ℓ ∈ S₁ := by simp [S₁]
    have hS : S₂ = S₁.erase ℓ := by
      ext m
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hm : m = ℓ
      · subst hm; simp [Ne.symm hjs]
      · simp [hm]
    rw [hS, Finset.card_erase_of_mem hmem]
    have h1 : 1 ≤ S₁.card := Finset.card_pos.mpr ⟨ℓ, hmem⟩
    rw [Nat.cast_sub h1]
    simp [hjs]
  · have hS : S₂ = S₁ := by
      ext m
      simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hm : m = ℓ
      · subst hm; simp [Ne.symm hjs, Ne.symm hjf]
      · simp [hm]
    rw [hS]
    simp [hjs, hjf]

/-- Common excess vector `a = q + e_s - (1 + 1/k) 1` from Claim 4.2. -/
noncomputable def commonExcess {k : ℕ} (q : Fin k → ℝ) (s : Fin k) : Fin k → ℝ :=
  fun j => q j + stdBasis s j - (1 + 1 / (k : ℝ))

lemma sum_commonExcess {k : ℕ} (hk : 1 ≤ k) {q : Fin k → ℝ}
    (hq_sum : ∑ j : Fin k, q j = (k : ℝ)) (s : Fin k) :
    ∑ j : Fin k, commonExcess q s j = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold commonExcess
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hq_sum, sum_stdBasis,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk_ne]
  ring

/-- Claim 4.2 (Serving Move Identity): `U_Y(q) - U_Y(q - e_i + e_s) = k^2 (h_i - h_s)`. -/
lemma corrEnergy_move_eq {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {q : Fin k → ℝ} (_hq_sum : ∑ j : Fin k, q j = (k : ℝ))
    (s : Fin k) {F : Fin k → Fin k → ℝ} {h : Fin k → ℝ}
    (hF : IsFlowFor F (commonExcess q s))
    (hOhm : ∀ u v, dist (Y u) (Y v) * F u v = h u - h v)
    (i : Fin k) :
    corrEnergy Y q - corrEnergy Y (fun j => q j - stdBasis i j + stdBasis s j) =
      (k : ℝ)^2 * (h i - h s) := by
  have hexpand : ∀ t : Fin k,
      elecEnergy Y (fun j => commonExcess q s j + (- spreadVec t j)) =
      elecEnergy Y (commonExcess q s) - 2 * h t +
        (2 / (k : ℝ)) * (∑ j : Fin k, h j) + spreadEnergy Y t := by
    intro t
    have hbt : ∑ j : Fin k, (- spreadVec t j) = 0 := by
      rw [Finset.sum_neg_distrib, sum_spreadVec hk t, neg_zero]
    rw [elecEnergy_add_of_voltage_flow hk hY hF hOhm hbt]
    have hneg : elecEnergy Y (- spreadVec t) = spreadEnergy Y t := elecEnergy_neg Y (spreadVec t)
    change _ = _
    rw [show elecEnergy Y (fun j => - spreadVec t j) = elecEnergy Y (- spreadVec t) from rfl, hneg]
    have hlin : (∑ j : Fin k, (- spreadVec t j) * h j) =
        - h t + (1 / (k : ℝ)) * (∑ j : Fin k, h j) := by
      classical
      unfold spreadVec stdBasis
      have hterm : ∀ j : Fin k,
          (- ((if j = t then (1 : ℝ) else 0) - 1 / (k : ℝ))) * h j =
          - (if j = t then h j else 0) + (1 / (k : ℝ)) * h j := by
        intro j; split_ifs <;> ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ t), ← Finset.mul_sum]
    rw [hlin]
    ring
  have h_old_vec : (fun j => q j - 1) = (fun j => commonExcess q s j + (- spreadVec s j)) := by
    ext j; unfold commonExcess spreadVec; ring
  have h_new_vec : (fun j => (q j - stdBasis i j + stdBasis s j) - 1) =
      (fun j => commonExcess q s j + (- spreadVec i j)) := by
    ext j; unfold commonExcess spreadVec; ring
  have hlin_diff :
      (∑ j : Fin k, q j * spreadEnergy Y j) -
      (∑ j : Fin k, (q j - stdBasis i j + stdBasis s j) * spreadEnergy Y j) =
      spreadEnergy Y i - spreadEnergy Y s := by
    classical
    rw [← Finset.sum_sub_distrib]
    have h1 : ∀ j : Fin k,
        q j * spreadEnergy Y j - (q j - stdBasis i j + stdBasis s j) * spreadEnergy Y j =
        (if j = i then spreadEnergy Y j else 0) - (if j = s then spreadEnergy Y j else 0) := by
      intro j; unfold stdBasis; split_ifs <;> ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ s)]
  unfold corrEnergy
  rw [← mul_sub, h_old_vec, h_new_vec, hexpand s, hexpand i]
  have hinner :
      (elecEnergy Y (commonExcess q s) - 2 * h s + 2 / (k : ℝ) * (∑ j : Fin k, h j) +
        spreadEnergy Y s + ∑ j : Fin k, q j * spreadEnergy Y j) -
      (elecEnergy Y (commonExcess q s) - 2 * h i + 2 / (k : ℝ) * (∑ j : Fin k, h j) +
        spreadEnergy Y i + ∑ j : Fin k, (q j - stdBasis i j + stdBasis s j) * spreadEnergy Y j) =
      2 * (h i - h s) := by
    linarith
  rw [hinner]
  ring

/-- Two-sided Lemma 4.4: `|U_Y(q) - U_Y(q - e_i + e_s)| ≤ k^3 dist (Y i) (Y s)`. -/
lemma abs_corrEnergy_move_le {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {q : Fin k → ℝ} (hq_nonneg : ∀ j, 0 ≤ q j) (hq_sum : ∑ j : Fin k, q j = (k : ℝ))
    (s : Fin k) {F : Fin k → Fin k → ℝ} {h : Fin k → ℝ}
    (hF : IsFlowFor F (commonExcess q s))
    (hF_cond : ∀ u v, F u v = conductance Y u v * (h u - h v))
    (hOhm : ∀ u v, dist (Y u) (Y v) * F u v = h u - h v)
    (i : Fin k) :
    |corrEnergy Y q - corrEnergy Y (fun j => q j - stdBasis i j + stdBasis s j)| ≤
      (k : ℝ)^3 * dist (Y i) (Y s) := by
  rw [corrEnergy_move_eq hk hY hq_sum s hF hOhm i, abs_mul, abs_of_nonneg (by positivity)]
  have hv := (voltage_flow_bounds Y hF hF_cond hOhm).1 i s
  have hT_le : ∑ j : Fin k, max (commonExcess q s j) 0 ≤ (k : ℝ) := by
    have hcoord : ∀ j : Fin k, max (commonExcess q s j) 0 ≤ q j := by
      classical
      intro j
      refine max_le ?_ (hq_nonneg j)
      unfold commonExcess stdBasis
      have hk0 : 0 ≤ 1 / (k : ℝ) := by positivity
      split_ifs <;> linarith
    exact le_trans (Finset.sum_le_sum (fun j _ => hcoord j)) (le_of_eq hq_sum)
  calc (k : ℝ)^2 * |h i - h s|
    _ ≤ (k : ℝ)^2 * ((∑ j : Fin k, max (commonExcess q s j) 0) * dist (Y i) (Y s)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ (k : ℝ)^2 * ((k : ℝ) * dist (Y i) (Y s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT_le dist_nonneg) (by positivity)
    _ = (k : ℝ)^3 * dist (Y i) (Y s) := by ring

noncomputable def assignVal {k : ℕ} {M : Type*} [MetricSpace M]
    (X Y : KServer.Config k M) (f : Fin k → Fin k) : ℝ :=
  corrEnergy Y (occ f) + (k : ℝ)^3 * ∑ ℓ : Fin k, dist (X ℓ) (Y (f ℓ))

lemma assignUniv_nonempty {k : ℕ} :
    (Finset.univ : Finset (Fin k → Fin k)).Nonempty :=
  ⟨id, Finset.mem_univ id⟩

noncomputable def phi {k : ℕ} (_hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    (X Y : KServer.Config k M) : ℝ :=
  Finset.univ.inf' assignUniv_nonempty (assignVal X Y)

lemma phi_le_assignVal {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    (X Y : KServer.Config k M) (f : Fin k → Fin k) :
    phi hk X Y ≤ assignVal X Y f := by
  unfold phi
  exact Finset.inf'_le _ (Finset.mem_univ f)

lemma exists_assignVal_eq_phi {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    (X Y : KServer.Config k M) :
    ∃ f : Fin k → Fin k, assignVal X Y f = phi hk X Y := by
  unfold phi
  obtain ⟨f, _, hf⟩ := Finset.exists_mem_eq_inf' assignUniv_nonempty (assignVal X Y)
  exact ⟨f, hf.symm⟩

lemma phi_nonneg {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    (X Y : KServer.Config k M) :
    0 ≤ phi hk X Y := by
  obtain ⟨f, hf⟩ := exists_assignVal_eq_phi hk X Y
  rw [← hf]
  unfold assignVal
  exact add_nonneg (corrEnergy_nonneg Y (occ_nonneg f))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => dist_nonneg)))

/-- Property 2.1 for `phi` on injective `Y`: single adversary server relocation increases `phi` by at most `2 k^4 δ`. -/
lemma phi_relocate_le {k : ℕ} (hk : 1 ≤ k) {M : Type*} [MetricSpace M]
    (X : KServer.Config k M) {Y : KServer.Config k M} (hY : Function.Injective Y)
    (i₀ : Fin k) (p : M) :
    phi hk X (relocate Y i₀ p) - phi hk X Y ≤ 2 * (k : ℝ)^4 * dist (Y i₀) p := by
  obtain ⟨f, hf⟩ := exists_assignVal_eq_phi hk X Y
  have hcand := phi_le_assignVal hk X (relocate Y i₀ p) f
  rw [← hf]
  set q := occ f
  set δ := dist (Y i₀) p
  have hδ : 0 ≤ δ := dist_nonneg
  have hq_sum : ∑ j : Fin k, q j = (k : ℝ) := sum_occ f
  have hq_minus_zero : ∑ j : Fin k, (q j - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hq_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sub_self]
  -- Bound positive excess of `q - 1` by `k - 1`
  let j₀ : Fin k := f ⟨0, hk⟩
  have hj₀_ge : 1 ≤ q j₀ := by
    classical
    change 1 ≤ ((Finset.univ.filter (fun ℓ => f ℓ = j₀)).card : ℝ)
    have hmem : (⟨0, hk⟩ : Fin k) ∈ Finset.univ.filter (fun ℓ => f ℓ = j₀) := by simp [j₀]
    have hpos : 1 ≤ (Finset.univ.filter (fun ℓ => f ℓ = j₀)).card :=
      Finset.card_pos.mpr ⟨⟨0, hk⟩, hmem⟩
    exact Nat.one_le_cast.mpr hpos
  have hT_imb : ∑ j : Fin k, max (q j - 1) 0 ≤ (k : ℝ) - 1 := by
    classical
    have hpt : ∀ j : Fin k, max (q j - 1) 0 ≤ q j - (if j = j₀ then 1 else 0) := by
      intro j
      by_cases hj : j = j₀
      · subst hj
        simp only [↓reduceIte]
        exact max_le le_rfl (by linarith)
      · simp only [hj, ↓reduceIte, sub_zero]
        exact max_le (by linarith) (occ_nonneg f j)
    calc ∑ j : Fin k, max (q j - 1) 0
      _ ≤ ∑ j : Fin k, (q j - (if j = j₀ then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun j _ => hpt j)
      _ = (∑ j : Fin k, q j) - 1 := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ j₀)]
      _ = (k : ℝ) - 1 := by rw [hq_sum]
  have hT_imb_nonneg : 0 ≤ ∑ j : Fin k, max (q j - 1) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hk1_nonneg : 0 ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    linarith
  have hE_imb :
      elecEnergy (relocate Y i₀ p) (fun j => q j - 1) ≤
      elecEnergy Y (fun j => q j - 1) + 2 * ((k : ℝ) - 1)^2 * δ := by
    have h1 := elecEnergy_relocate_le hk hY i₀ p hq_minus_zero
    dsimp only at h1
    have hsq : (∑ u : Fin k, max (q u - 1) 0)^2 ≤ ((k : ℝ) - 1)^2 :=
      sq_le_sq' (by linarith) hT_imb
    have hmul : 2 * (∑ u : Fin k, max (q u - 1) 0)^2 * δ ≤ 2 * ((k : ℝ) - 1)^2 * δ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hδ
    linarith
  have hE_spread : ∀ j : Fin k,
      spreadEnergy (relocate Y i₀ p) j ≤ spreadEnergy Y j + 2 * δ := by
    intro j
    have h1 := elecEnergy_relocate_le hk hY i₀ p (sum_spreadVec hk j)
    dsimp only at h1
    have hT := posExcess_spreadVec_le_one j
    have hT0 : 0 ≤ ∑ u : Fin k, max (spreadVec j u) 0 :=
      Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have hsq : (∑ u : Fin k, max (spreadVec j u) 0)^2 ≤ 1^2 :=
      sq_le_sq' (by linarith) hT
    have hmul : 2 * (∑ u : Fin k, max (spreadVec j u) 0)^2 * δ ≤ 2 * δ := by
      calc 2 * (∑ u : Fin k, max (spreadVec j u) 0)^2 * δ
        _ ≤ 2 * (1 : ℝ)^2 * δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) hδ
        _ = 2 * δ := by ring
    unfold spreadEnergy
    linarith
  have hU_diff : corrEnergy (relocate Y i₀ p) q - corrEnergy Y q ≤ (k : ℝ)^4 * δ := by
    have hlin :
        (∑ j : Fin k, q j * spreadEnergy (relocate Y i₀ p) j) ≤
        (∑ j : Fin k, q j * spreadEnergy Y j) + 2 * (k : ℝ) * δ := by
      calc ∑ j : Fin k, q j * spreadEnergy (relocate Y i₀ p) j
        _ ≤ ∑ j : Fin k, q j * (spreadEnergy Y j + 2 * δ) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hE_spread j) (occ_nonneg f j))
        _ = (∑ j : Fin k, q j * spreadEnergy Y j) + (∑ j : Fin k, q j) * (2 * δ) := by
          simp_rw [ mul_add, Finset.sum_add_distrib, ← Finset.sum_mul ]
        _ = (∑ j : Fin k, q j * spreadEnergy Y j) + 2 * (k : ℝ) * δ := by
          rw [hq_sum]; ring
    have hinner :
        (elecEnergy (relocate Y i₀ p) (fun j => q j - 1) +
          ∑ j : Fin k, q j * spreadEnergy (relocate Y i₀ p) j) -
        (elecEnergy Y (fun j => q j - 1) + ∑ j : Fin k, q j * spreadEnergy Y j) ≤
        2 * (k : ℝ)^2 * δ := by
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
      have hpoly : ((k : ℝ) - 1)^2 + (k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
      have hpolyδ : (2 * ((k : ℝ) - 1)^2 + 2 * (k : ℝ)) * δ ≤ 2 * (k : ℝ)^2 * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ
      linarith
    unfold corrEnergy
    rw [← mul_sub]
    have hscale := mul_le_mul_of_nonneg_left hinner (show 0 ≤ (k : ℝ)^2 / 2 by positivity)
    linarith [show ((k : ℝ)^2 / 2) * (2 * (k : ℝ)^2 * δ) = (k : ℝ)^4 * δ by ring]
  have hdist_diff :
      (∑ ℓ : Fin k, dist (X ℓ) (relocate Y i₀ p (f ℓ))) -
      (∑ ℓ : Fin k, dist (X ℓ) (Y (f ℓ))) ≤ (k : ℝ) * δ := by
    classical
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ ℓ : Fin k,
        dist (X ℓ) (relocate Y i₀ p (f ℓ)) - dist (X ℓ) (Y (f ℓ)) ≤ δ := by
      intro ℓ
      unfold relocate
      by_cases hℓ : f ℓ = i₀
      · rw [hℓ, Function.update_self]
        have := dist_triangle (X ℓ) (Y i₀) p
        linarith
      · rw [Function.update_of_ne hℓ]
        linarith
    calc ∑ ℓ : Fin k, (dist (X ℓ) (relocate Y i₀ p (f ℓ)) - dist (X ℓ) (Y (f ℓ)))
      _ ≤ ∑ _ℓ : Fin k, δ := Finset.sum_le_sum (fun ℓ _ => hterm ℓ)
      _ = (k : ℝ) * δ := by simp [nsmul_eq_mul]
  have hassign_diff : assignVal X (relocate Y i₀ p) f - assignVal X Y f ≤ 2 * (k : ℝ)^4 * δ := by
    unfold assignVal
    have h2 : (k : ℝ)^3 * (∑ ℓ : Fin k, dist (X ℓ) (relocate Y i₀ p (f ℓ))) -
        (k : ℝ)^3 * (∑ ℓ : Fin k, dist (X ℓ) (Y (f ℓ))) ≤ (k : ℝ)^4 * δ := by
      have : (k : ℝ)^3 * ((∑ ℓ : Fin k, dist (X ℓ) (relocate Y i₀ p (f ℓ))) -
          (∑ ℓ : Fin k, dist (X ℓ) (Y (f ℓ)))) ≤ (k : ℝ)^3 * ((k : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hdist_diff (by positivity)
      linarith [show (k : ℝ)^3 * ((k : ℝ) * δ) = (k : ℝ)^4 * δ by ring]
    linarith
  linarith

/-- Claim 5.2 pairwise current inequality: `F i j * (F i s - F j s) ≥ - F i s * F j s`. -/
lemma flow_pair_ineq {k : ℕ} {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {F : Fin k → Fin k → ℝ} {a h : Fin k → ℝ}
    (hF : IsFlowFor F a)
    (hOhm : ∀ u v, dist (Y u) (Y v) * F u v = h u - h v)
    {s i j : Fin k} (his : i ≠ s) (hjs : j ≠ s) :
    - (F i s * F j s) ≤ F i j * (F i s - F j s) := by
  by_cases hij : i = j
  · subst hij
    rw [isFlowFor_diag hF i, zero_mul]
    nlinarith [sq_nonneg (F i s)]
  · have hd_ij : 0 < dist (Y i) (Y j) := dist_pos.mpr (hY.ne hij)
    have hd_is : 0 < dist (Y i) (Y s) := dist_pos.mpr (hY.ne his)
    have hd_js : 0 < dist (Y j) (Y s) := dist_pos.mpr (hY.ne hjs)
    have hohm_diff : dist (Y i) (Y j) * F i j =
        dist (Y i) (Y s) * F i s - dist (Y j) (Y s) * F j s := by
      linarith [hOhm i j, hOhm i s, hOhm j s]
    set c := dist (Y i) (Y s) + dist (Y j) (Y s) - dist (Y i) (Y j)
    have hc0 : 0 ≤ c := by
      have := dist_triangle (Y i) (Y s) (Y j)
      rw [dist_comm (Y s) (Y j)] at this
      linarith
    have hc1 : c ≤ 2 * dist (Y i) (Y s) := by
      have := dist_triangle (Y j) (Y i) (Y s)
      rw [dist_comm (Y j) (Y i)] at this
      linarith
    have hc2 : c ≤ 2 * dist (Y j) (Y s) := by
      have := dist_triangle (Y i) (Y j) (Y s)
      linarith
    have hcsq : c^2 ≤ 4 * dist (Y i) (Y s) * dist (Y j) (Y s) := by
      have := mul_le_mul hc1 hc2 hc0 (by linarith)
      linarith [show c * c = c^2 by ring]
    have hquad4 :
        0 ≤ 4 * dist (Y i) (Y s) *
          (dist (Y i) (Y s) * (F i s)^2 + dist (Y j) (Y s) * (F j s)^2 - c * F i s * F j s) := by
      have hid :
          4 * dist (Y i) (Y s) *
            (dist (Y i) (Y s) * (F i s)^2 + dist (Y j) (Y s) * (F j s)^2 - c * F i s * F j s) =
          (2 * dist (Y i) (Y s) * F i s - c * F j s)^2 +
            (4 * dist (Y i) (Y s) * dist (Y j) (Y s) - c^2) * (F j s)^2 := by
        ring
      rw [hid]
      exact add_nonneg (sq_nonneg _)
        (mul_nonneg (by linarith) (sq_nonneg _))
    have hquad :
        0 ≤ dist (Y i) (Y s) * (F i s)^2 + dist (Y j) (Y s) * (F j s)^2 - c * F i s * F j s := by
      nlinarith
    have hlhs :
        dist (Y i) (Y j) * (F i j * (F i s - F j s) + F i s * F j s) =
        dist (Y i) (Y s) * (F i s)^2 + dist (Y j) (Y s) * (F j s)^2 - c * F i s * F j s := by
      calc dist (Y i) (Y j) * (F i j * (F i s - F j s) + F i s * F j s)
        _ = (dist (Y i) (Y j) * F i j) * (F i s - F j s) + dist (Y i) (Y j) * F i s * F j s := by
          ring
        _ = (dist (Y i) (Y s) * F i s - dist (Y j) (Y s) * F j s) * (F i s - F j s) +
            dist (Y i) (Y j) * F i s * F j s := by rw [hohm_diff]
        _ = dist (Y i) (Y s) * (F i s)^2 + dist (Y j) (Y s) * (F j s)^2 - c * F i s * F j s := by
          dsimp [c]; ring
    have hprod_nonneg : 0 ≤ F i j * (F i s - F j s) + F i s * F j s := by
      nlinarith
    linarith

/-- Lemma 5.1 (Weighted Current Bound): `∑_{i ≠ s} q_i F_{is} + k q_s ≥ 1 / k` for `k ≥ 2`. -/
lemma weighted_current_bound {k : ℕ} (hk2 : 2 ≤ k) {M : Type*} [MetricSpace M]
    {Y : KServer.Config k M} (hY : Function.Injective Y)
    {q : Fin k → ℝ} (hq_nonneg : ∀ j, 0 ≤ q j) (hq_sum : ∑ j : Fin k, q j = (k : ℝ))
    (s : Fin k) {F : Fin k → Fin k → ℝ} {h : Fin k → ℝ}
    (hF : IsFlowFor F (commonExcess q s))
    (hOhm : ∀ u v, dist (Y u) (Y v) * F u v = h u - h v) :
    1 / (k : ℝ) ≤ (∑ i ∈ Finset.univ.erase s, q i * F i s) + (k : ℝ) * q s := by
  classical
  let S := (Finset.univ : Finset (Fin k)).erase s
  set I := ∑ i ∈ S, F i s
  -- Conservation at s: I = 1 / k - q s
  have hcons_s : I = 1 / (k : ℝ) - q s := by
    have has := hF.2 s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), isFlowFor_diag hF s, zero_add] at has
    have hskew : (∑ j ∈ S, F s j) = - I := by
      dsimp [I]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j _ => hF.1 s j)
    rw [hskew] at has
    unfold commonExcess stdBasis at has
    simp only [↓reduceIte] at has
    linarith
  -- Conservation at i ∈ S: q i = (1 + 1/k) + F i s + ∑_{j ∈ S} F i j
  have hcons_i : ∀ i ∈ S, q i = (1 + 1 / (k : ℝ)) + F i s + ∑ j ∈ S, F i j := by
    intro i hi
    have his : i ≠ s := (Finset.mem_erase.mp hi).1
    have hai := hF.2 i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hai
    unfold commonExcess stdBasis at hai
    simp only [his, ↓reduceIte, add_zero] at hai
    linarith
  have hexpand :
      (∑ i ∈ S, q i * F i s) =
      (1 + 1 / (k : ℝ)) * I + (∑ i ∈ S, (F i s)^2) + ∑ i ∈ S, ∑ j ∈ S, F i j * F i s := by
    have h1 : ∀ i ∈ S,
        q i * F i s = (1 + 1 / (k : ℝ)) * F i s + (F i s)^2 + ∑ j ∈ S, F i j * F i s := by
      intro i hi
      rw [hcons_i i hi]
      simp_rw [add_mul, sq, Finset.sum_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Symmetrize double sum
  have hD_symm :
      (∑ i ∈ S, ∑ j ∈ S, F i j * F i s) =
      (1 / 2 : ℝ) * ∑ i ∈ S, ∑ j ∈ S, F i j * (F i s - F j s) := by
    have hswap :
        (∑ i ∈ S, ∑ j ∈ S, F i j * F i s) =
        ∑ i ∈ S, ∑ j ∈ S, (- F i j * F j s) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hF.1 j i]
    have hsum2 :
        (∑ i ∈ S, ∑ j ∈ S, F i j * F i s) + (∑ i ∈ S, ∑ j ∈ S, (- F i j * F j s)) =
        ∑ i ∈ S, ∑ j ∈ S, F i j * (F i s - F j s) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    linarith
  have hD_ge : - (I^2 / 2) ≤ (∑ i ∈ S, ∑ j ∈ S, F i j * F i s) := by
    rw [hD_symm]
    have hpair :
        (∑ i ∈ S, ∑ j ∈ S, - (F i s * F j s)) ≤
        ∑ i ∈ S, ∑ j ∈ S, F i j * (F i s - F j s) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj =>
        flow_pair_ineq hY hF hOhm (Finset.mem_erase.mp hi).1 (Finset.mem_erase.mp hj).1))
    have hI2 : (∑ i ∈ S, ∑ j ∈ S, - (F i s * F j s)) = - I^2 := by
      simp_rw [Finset.sum_neg_distrib]
      congr 1
      rw [sq]
      dsimp [I]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
    linarith
  have hsq_nonneg : 0 ≤ ∑ i ∈ S, (F i s)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq_le_k : q s ≤ (k : ℝ) := by
    rw [← hq_sum]
    exact Finset.single_le_sum (fun j _ => hq_nonneg j) (Finset.mem_univ s)
  have hqs0 : 0 ≤ q s := hq_nonneg s
  have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := Nat.ofNat_le_cast.mpr hk2
  have hk_ne : (k : ℝ) ≠ 0 := by linarith
  have halg :
      (1 + 1 / (k : ℝ)) * I - I^2 / 2 + (k : ℝ) * q s =
      1 / (k : ℝ) + 1 / (2 * (k : ℝ)^2) + q s * ((k : ℝ) - 1 - q s / 2) := by
    rw [hcons_s]
    field_simp [hk_ne]
    ring
  have hterm1 : 0 ≤ 1 / (2 * (k : ℝ)^2) := by positivity
  have hterm2 : 0 ≤ q s * ((k : ℝ) - 1 - q s / 2) :=
    mul_nonneg hqs0 (by linarith)
  linarith

/-- Property 2.2 for `phi` on injective `Y`: normalized potential decrease ≥ k on uncovered request,
giving expected online step inequality. -/
lemma phi_online_step {k : ℕ} (hk2 : 2 ≤ k) {M : Type*} [MetricSpace M]
    (X : KServer.Config k M) {Y : KServer.Config k M} (hY : Function.Injective Y)
    (r : M) (hcovY : Covers Y r) (hnotX : ¬ Covers X r) :
    ∑ ℓ : Fin k, harmonicProbability X r ℓ *
      (harmonicCost X r ℓ + phi (by omega) (harmonicNext X r ℓ) Y - phi (by omega) X Y) ≤ 0 := by
  classical
  have hk1 : 1 ≤ k := by omega
  rcases hcovY with ⟨s, hs⟩
  obtain ⟨f, hf⟩ := exists_assignVal_eq_phi hk1 X Y
  set q := occ f
  have hq_nonneg : ∀ j, 0 ≤ q j := occ_nonneg f
  have hq_sum : ∑ j : Fin k, q j = (k : ℝ) := sum_occ f
  obtain ⟨F, h, hF, hF_cond, hOhm⟩ := exists_voltage_flow hk1 hY (sum_commonExcess hk1 hq_sum s)
  -- Bound each server's normalized potential decrease
  have hserver : ∀ ℓ : Fin k,
      (if f ℓ = s then (k : ℝ)^3 else (k : ℝ)^2 * F (f ℓ) s) ≤
        (phi hk1 X Y - phi hk1 (relocate X ℓ r) Y) / dist (X ℓ) r := by
    intro ℓ
    have hdX_pos : 0 < dist (X ℓ) r := dist_pos_of_not_covers hnotX ℓ
    let f' := Function.update f ℓ s
    have hcand := phi_le_assignVal hk1 (relocate X ℓ r) Y f'
    have hdist_cancel :
        (∑ m : Fin k, dist (X m) (Y (f m))) -
        (∑ m : Fin k, dist (relocate X ℓ r m) (Y (f' m))) = dist (X ℓ) (Y (f ℓ)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ)]
      have hrest :
          (∑ m ∈ Finset.univ.erase ℓ, dist (relocate X ℓ r m) (Y (f' m))) =
          ∑ m ∈ Finset.univ.erase ℓ, dist (X m) (Y (f m)) := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hmℓ : m ≠ ℓ := (Finset.mem_erase.mp hm).1
        simp [relocate, f', hmℓ]
      have hhead : dist (relocate X ℓ r ℓ) (Y (f' ℓ)) = 0 := by
        simp [relocate, f', hs]
      linarith
    set Δ := corrEnergy Y q - corrEnergy Y (fun j => q j - stdBasis (f ℓ) j + stdBasis s j)
    have hdec_ge : Δ + (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) ≤
        phi hk1 X Y - phi hk1 (relocate X ℓ r) Y := by
      have hval_diff : assignVal X Y f - assignVal (relocate X ℓ r) Y f' =
          Δ + (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) := by
        unfold assignVal
        rw [occ_update_eq f ℓ s]
        linarith [show (k : ℝ)^3 * (∑ m : Fin k, dist (X m) (Y (f m))) -
            (k : ℝ)^3 * (∑ m : Fin k, dist (relocate X ℓ r m) (Y (f' m))) =
            (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) by
          rw [← mul_sub, hdist_cancel]]
      linarith [hf]
    by_cases hi : f ℓ = s
    · simp only [hi, ↓reduceIte]
      have hΔ0 : Δ = 0 := by
        dsimp [Δ]
        rw [hi, corrEnergy_move_eq hk1 hY hq_sum s hF hOhm s]
        ring
      have hd_eq : dist (X ℓ) (Y (f ℓ)) = dist (X ℓ) r := by rw [hi, hs]
      have hnum : (k : ℝ)^3 * dist (X ℓ) r ≤ phi hk1 X Y - phi hk1 (relocate X ℓ r) Y := by
        rw [hΔ0, zero_add, hd_eq] at hdec_ge
        exact hdec_ge
      exact (le_div_iff₀ hdX_pos).mpr hnum
    · simp only [hi, ↓reduceIte]
      have hdis_pos : 0 < dist (Y (f ℓ)) (Y s) := dist_pos.mpr (hY.ne hi)
      have hΔ_eq : Δ = (k : ℝ)^2 * (dist (Y (f ℓ)) (Y s) * F (f ℓ) s) := by
        dsimp [Δ]
        rw [corrEnergy_move_eq hk1 hY hq_sum s hF hOhm (f ℓ), hOhm (f ℓ) s]
      have hΔ_abs : |Δ| ≤ (k : ℝ)^3 * dist (Y (f ℓ)) (Y s) :=
        abs_corrEnergy_move_le hk1 hY hq_nonneg hq_sum s hF hF_cond hOhm (f ℓ)
      have htri_abs : |dist (Y (f ℓ)) (Y s) - dist (X ℓ) r| ≤ dist (X ℓ) (Y (f ℓ)) := by
        rw [hs, abs_sub_le_iff]
        constructor
        · have := dist_triangle (Y (f ℓ)) (X ℓ) r
          rw [dist_comm (Y (f ℓ)) (X ℓ)] at this
          linarith
        · have := dist_triangle (X ℓ) (Y (f ℓ)) r
          linarith
      have hprod_ge : - ((k : ℝ)^3 * dist (Y (f ℓ)) (Y s) * dist (X ℓ) (Y (f ℓ))) ≤
          Δ * (dist (Y (f ℓ)) (Y s) - dist (X ℓ) r) := by
        have h1 : |Δ * (dist (Y (f ℓ)) (Y s) - dist (X ℓ) r)| ≤
            ((k : ℝ)^3 * dist (Y (f ℓ)) (Y s)) * dist (X ℓ) (Y (f ℓ)) := by
          rw [abs_mul]
          exact mul_le_mul hΔ_abs htri_abs (abs_nonneg _) (by positivity)
        linarith [(abs_le.mp h1).1]
      have hcross : ((k : ℝ)^2 * F (f ℓ) s) * dist (X ℓ) r ≤
          Δ + (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) := by
        have hmul_pos : 0 < dist (Y (f ℓ)) (Y s) := hdis_pos
        have hkey :
            dist (Y (f ℓ)) (Y s) *
              (Δ + (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) - ((k : ℝ)^2 * F (f ℓ) s) * dist (X ℓ) r) =
            Δ * (dist (Y (f ℓ)) (Y s) - dist (X ℓ) r) +
              (k : ℝ)^3 * dist (Y (f ℓ)) (Y s) * dist (X ℓ) (Y (f ℓ)) := by
          rw [hΔ_eq]
          ring
        have hnn : 0 ≤ Δ + (k : ℝ)^3 * dist (X ℓ) (Y (f ℓ)) -
            ((k : ℝ)^2 * F (f ℓ) s) * dist (X ℓ) r := by
          nlinarith
        linarith
      exact (le_div_iff₀ hdX_pos).mpr (le_trans hcross hdec_ge)
  -- Sum over all servers ℓ ∈ Fin k and group by fiber f ℓ
  have hsum_norm : (k : ℝ) ≤
      ∑ ℓ : Fin k, (phi hk1 X Y - phi hk1 (relocate X ℓ r) Y) / dist (X ℓ) r := by
    have hfiber :
        (∑ ℓ : Fin k, if f ℓ = s then (k : ℝ)^3 else (k : ℝ)^2 * F (f ℓ) s) =
        (k : ℝ)^2 * ((∑ i ∈ Finset.univ.erase s, q i * F i s) + (k : ℝ) * q s) := by
      let g : Fin k → ℝ := fun i => if i = s then (k : ℝ)^3 else (k : ℝ)^2 * F i s
      change (∑ ℓ ∈ Finset.univ, g (f ℓ)) = _
      rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ)
        (fun x _ => Finset.mem_univ (f x))]
      have hfib_val : ∀ i : Fin k,
          (∑ ℓ ∈ Finset.univ.filter (fun x => f x = i), g (f ℓ)) = q i * g i := by
        intro i
        have hcongr :
            (∑ ℓ ∈ Finset.univ.filter (fun x => f x = i), g (f ℓ)) =
            ∑ _ℓ ∈ Finset.univ.filter (fun x => f x = i), g i :=
          Finset.sum_congr rfl (fun ℓ hℓ => by rw [(Finset.mem_filter.mp hℓ).2])
        rw [hcongr, Finset.sum_const, nsmul_eq_mul]
        rfl
      simp_rw [hfib_val]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have hs_val : q s * g s = (k : ℝ)^2 * ((k : ℝ) * q s) := by
        dsimp [g]; simp; ring
      have hrest_val :
          (∑ i ∈ Finset.univ.erase s, q i * g i) =
          (k : ℝ)^2 * ∑ i ∈ Finset.univ.erase s, q i * F i s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have his : i ≠ s := (Finset.mem_erase.mp hi).1
        dsimp [g]
        rw [if_neg his]
        ring
      linarith
    have hw := weighted_current_bound hk2 hY hq_nonneg hq_sum s hF hOhm
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    have hk_bound :
        (k : ℝ) ≤ (k : ℝ)^2 * ((∑ i ∈ Finset.univ.erase s, q i * F i s) + (k : ℝ) * q s) := by
      calc (k : ℝ)
        _ = (k : ℝ)^2 * (1 / (k : ℝ)) := by field_simp [hk_ne]
        _ ≤ (k : ℝ)^2 * ((∑ i ∈ Finset.univ.erase s, q i * F i s) + (k : ℝ) * q s) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
    exact le_trans (by linarith) (Finset.sum_le_sum (fun ℓ _ => hserver ℓ))
  -- Divide by `normalizer X r > 0`
  have hZ_pos : 0 < normalizer X r := normalizer_pos_of_not_covers hk1 hnotX
  have hZ_ne : normalizer X r ≠ 0 := hZ_pos.ne'
  have hexp_eq :
      (∑ ℓ : Fin k, harmonicProbability X r ℓ *
        (harmonicCost X r ℓ + phi hk1 (harmonicNext X r ℓ) Y - phi hk1 X Y)) =
      (normalizer X r)⁻¹ *
        ((k : ℝ) - ∑ ℓ : Fin k, (phi hk1 X Y - phi hk1 (relocate X ℓ r) Y) / dist (X ℓ) r) := by
    have hterm : ∀ ℓ : Fin k,
        harmonicProbability X r ℓ *
          (harmonicCost X r ℓ + phi hk1 (harmonicNext X r ℓ) Y - phi hk1 X Y) =
        (normalizer X r)⁻¹ *
          (1 - (phi hk1 X Y - phi hk1 (relocate X ℓ r) Y) / dist (X ℓ) r) := by
      intro ℓ
      have hd_ne : dist (X ℓ) r ≠ 0 := (dist_pos_of_not_covers hnotX ℓ).ne'
      unfold harmonicProbability
      rw [if_neg hnotX, harmonicCost_eq, if_neg hnotX]
      have hnext : harmonicNext X r ℓ = relocate X ℓ r := by simp [harmonicNext, hnotX]
      rw [hnext]
      field_simp [hZ_ne, hd_ne]
      ring
    simp_rw [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hexp_eq]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hZ_pos.le) (by linarith)

/-! ## Section 5: Infimal-Convolution Potential Envelope `psi` & Main Theorem -/

noncomputable def psi {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) : ℝ :=
  let ρ := 2 * (k : ℝ)^4
  sInf { v : ℝ | ∃ Z : KServer.Config k (ExtSpace Y₀),
    Function.Injective Z ∧
    v = phi (by omega) (ExtSpace.liftConfig Y₀ X) Z +
      ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z }

lemma psi_nonneg {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) :
    0 ≤ psi hk2 Y₀ X Y := by
  unfold psi
  refine Real.sInf_nonneg ?_
  rintro v ⟨Z, _, rfl⟩
  exact add_nonneg (phi_nonneg (by omega) _ _)
    (mul_nonneg (by positivity) (moveCost_nonneg _ _))

lemma psi_bddBelow {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) :
    BddBelow { v : ℝ | ∃ Z : KServer.Config k (ExtSpace Y₀),
      Function.Injective Z ∧
      v = phi (by omega) (ExtSpace.liftConfig Y₀ X) Z +
        (2 * (k : ℝ)^4) * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z } := by
  refine ⟨0, ?_⟩
  rintro v ⟨Z, _, rfl⟩
  exact add_nonneg (phi_nonneg (by omega) _ _)
    (mul_nonneg (by positivity) (moveCost_nonneg _ _))

lemma psi_set_nonempty {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) :
    { v : ℝ | ∃ Z : KServer.Config k (ExtSpace Y₀),
      Function.Injective Z ∧
      v = phi (by omega) (ExtSpace.liftConfig Y₀ X) Z +
        (2 * (k : ℝ)^4) * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z }.Nonempty :=
  ⟨_, ExtSpace.inr Y₀, ExtSpace.inr_injective Y₀, rfl⟩

lemma psi_le_of_injective {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) {Z : KServer.Config k (ExtSpace Y₀)}
    (hZ : Function.Injective Z) :
    psi hk2 Y₀ X Y ≤
      phi (by omega) (ExtSpace.liftConfig Y₀ X) Z +
        (2 * (k : ℝ)^4) * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z :=
  csInf_le (psi_bddBelow hk2 Y₀ X Y) ⟨Z, hZ, rfl⟩

lemma psi_adv_move {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y Y' : KServer.Config k V) :
    psi hk2 Y₀ X Y' - psi hk2 Y₀ X Y ≤ (2 * (k : ℝ)^4) * KServer.moveCost Y Y' := by
  set ρ := 2 * (k : ℝ)^4
  have hρ : 0 ≤ ρ := by positivity
  suffices h : psi hk2 Y₀ X Y' - ρ * KServer.moveCost Y Y' ≤ psi hk2 Y₀ X Y by linarith
  refine le_csInf (psi_set_nonempty hk2 Y₀ X Y) ?_
  rintro v ⟨Z, hZ, rfl⟩
  have hcand := psi_le_of_injective hk2 Y₀ X Y' hZ
  have htri := moveCost_triangle (ExtSpace.liftConfig Y₀ Y') (ExtSpace.liftConfig Y₀ Y) Z
  rw [ExtSpace.moveCost_liftConfig Y₀ Y' Y, moveCost_comm Y' Y] at htri
  have hmul : ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y') Z ≤
      ρ * (KServer.moveCost Y Y' + KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z) :=
    mul_le_mul_of_nonneg_left htri hρ
  linarith

lemma psi_online_move {k : ℕ} (hk2 : 2 ≤ k) {V : Type*} [MetricSpace V]
    (Y₀ X Y : KServer.Config k V) (r : V) (hcovY : Covers Y r) :
    ∑ i : Fin k, harmonicProbability X r i *
      (harmonicCost X r i + psi hk2 Y₀ (harmonicNext X r i) Y - psi hk2 Y₀ X Y) ≤ 0 := by
  classical
  have hk1 : 1 ≤ k := by omega
  by_cases hcovX : Covers X r
  · refine le_of_eq ?_
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hcost : harmonicCost X r i = 0 := by simp [harmonicCost_eq, hcovX]
    have hnext : harmonicNext X r i = X := by simp [harmonicNext, hcovX]
    rw [hcost, hnext]
    ring
  · -- Show ≤ η for every η > 0
    refine le_of_forall_pos_le_add (fun η hη => ?_)
    rw [zero_add]
    set ρ := 2 * (k : ℝ)^4
    have hρ : 0 ≤ ρ := by positivity
    obtain ⟨v, ⟨Z, hZ, rfl⟩, hv⟩ :=
      exists_lt_of_csInf_lt (psi_set_nonempty hk2 Y₀ X Y)
        (show psi hk2 Y₀ X Y < psi hk2 Y₀ X Y + η by linarith)
    rcases hcovY with ⟨s₀, hs₀⟩
    -- Ensure injective virtual configuration `Z'` covers `ExtSpace.inl Y₀ r` without increasing envelope value
    have hexZ' : ∃ Z' : KServer.Config k (ExtSpace Y₀),
        Function.Injective Z' ∧
        Covers Z' (ExtSpace.inl Y₀ r) ∧
        phi hk1 (ExtSpace.liftConfig Y₀ X) Z' + ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z' ≤
          phi hk1 (ExtSpace.liftConfig Y₀ X) Z + ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z := by
      by_cases hcovZ : Covers Z (ExtSpace.inl Y₀ r)
      · exact ⟨Z, hZ, hcovZ, le_rfl⟩
      · let Z' := relocate Z s₀ (ExtSpace.inl Y₀ r)
        have hZ'_inj : Function.Injective Z' := by
          intro a b hab
          unfold Z' relocate at hab
          by_cases ha : a = s₀ <;> by_cases hb : b = s₀
          · rw [ha, hb]
          · subst ha
            simp only [Function.update_self, Function.update_of_ne hb] at hab
            exact absurd hab.symm (fun hc => hcovZ ⟨b, hc⟩)
          · subst hb
            simp only [Function.update_self, Function.update_of_ne ha] at hab
            exact absurd hab (fun hc => hcovZ ⟨a, hc⟩)
          · simp only [Function.update_of_ne ha, Function.update_of_ne hb] at hab
            exact hZ hab
        have hZ'_cov : Covers Z' (ExtSpace.inl Y₀ r) := by
          exact ⟨s₀, by simp [Z', relocate]⟩
        have hphi_inc := phi_relocate_le hk1 (ExtSpace.liftConfig Y₀ X) hZ s₀ (ExtSpace.inl Y₀ r)
        have hmc_dec :
            KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z -
            KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z' =
            dist (Z s₀) (ExtSpace.inl Y₀ r) := by
          unfold KServer.moveCost
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀),
            ← Finset.add_sum_erase _ _ (Finset.mem_univ s₀)]
          have hrest :
              (∑ j ∈ Finset.univ.erase s₀, dist (ExtSpace.liftConfig Y₀ Y j) (Z' j)) =
              ∑ j ∈ Finset.univ.erase s₀, dist (ExtSpace.liftConfig Y₀ Y j) (Z j) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            have hjs : j ≠ s₀ := (Finset.mem_erase.mp hj).1
            simp [Z', relocate, hjs]
          have hheadZ' : dist (ExtSpace.liftConfig Y₀ Y s₀) (Z' s₀) = 0 := by
            simp [Z', relocate, ExtSpace.liftConfig, hs₀]
          have hheadZ : dist (ExtSpace.liftConfig Y₀ Y s₀) (Z s₀) =
              dist (Z s₀) (ExtSpace.inl Y₀ r) := by
            simp [ExtSpace.liftConfig, hs₀, dist_comm]
          linarith
        have htot :
            phi hk1 (ExtSpace.liftConfig Y₀ X) Z' +
              ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z' ≤
            phi hk1 (ExtSpace.liftConfig Y₀ X) Z +
              ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z := by
          have : ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z -
              ρ * KServer.moveCost (ExtSpace.liftConfig Y₀ Y) Z' =
              ρ * dist (Z s₀) (ExtSpace.inl Y₀ r) := by
            rw [← mul_sub, hmc_dec]
          linarith
        exact ⟨Z', hZ'_inj, hZ'_cov, htot⟩
    obtain ⟨Z', hZ'_inj, hZ'_cov, hZ'_val⟩ := hexZ'
    have hnotX' : ¬ Covers (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) := by
      rwa [ExtSpace.covers_liftConfig_iff]
    have hstep := phi_online_step hk2 (ExtSpace.liftConfig Y₀ X) hZ'_inj
      (ExtSpace.inl Y₀ r) hZ'_cov hnotX'
    have hterm_le : ∀ i : Fin k,
        harmonicProbability X r i *
          (harmonicCost X r i + psi hk2 Y₀ (harmonicNext X r i) Y - psi hk2 Y₀ X Y) ≤
        harmonicProbability (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i *
          (harmonicCost (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i +
            phi hk1 (harmonicNext (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i) Z' -
            phi hk1 (ExtSpace.liftConfig Y₀ X) Z') +
        harmonicProbability X r i * η := by
      intro i
      have hp_eq := (ExtSpace.harmonicProbability_liftConfig Y₀ X r i).symm
      have hp_nn := harmonicProbability_nonneg hk1 X r i
      have hcost_eq :
          harmonicCost X r i = harmonicCost (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i := by
        rw [harmonicCost_eq, harmonicCost_eq, if_neg hcovX, if_neg hnotX']
        simp [ExtSpace.liftConfig, ExtSpace.dist_inl]
      have hnext_eq :
          harmonicNext (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i =
          ExtSpace.liftConfig Y₀ (harmonicNext X r i) := by
        simp [harmonicNext, hcovX, hnotX', ExtSpace.relocate_liftConfig]
      have hpsi_next := psi_le_of_injective hk2 Y₀ (harmonicNext X r i) Y hZ'_inj
      have hdiff :
          psi hk2 Y₀ (harmonicNext X r i) Y - psi hk2 Y₀ X Y ≤
          phi hk1 (harmonicNext (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i) Z' -
            phi hk1 (ExtSpace.liftConfig Y₀ X) Z' + η := by
        rw [hnext_eq]
        linarith
      rw [← hp_eq, ← hcost_eq]
      nlinarith
    calc ∑ i : Fin k, harmonicProbability X r i *
          (harmonicCost X r i + psi hk2 Y₀ (harmonicNext X r i) Y - psi hk2 Y₀ X Y)
      _ ≤ ∑ i : Fin k,
          (harmonicProbability (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i *
            (harmonicCost (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i +
              phi hk1 (harmonicNext (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i) Z' -
              phi hk1 (ExtSpace.liftConfig Y₀ X) Z') +
          harmonicProbability X r i * η) :=
        Finset.sum_le_sum (fun i _ => hterm_le i)
      _ = (∑ i : Fin k,
            harmonicProbability (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i *
              (harmonicCost (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i +
                phi hk1 (harmonicNext (ExtSpace.liftConfig Y₀ X) (ExtSpace.inl Y₀ r) i) Z' -
                phi hk1 (ExtSpace.liftConfig Y₀ X) Z')) +
          (∑ i : Fin k, harmonicProbability X r i) * η := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ ≤ 0 + 1 * η := by
        rw [sum_harmonicProbability hk1 X r]
        linarith
      _ = η := by ring

theorem harmonic_competitive_main {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X₀ Y₀ : KServer.Config k V) :
    AdaptiveCompetitive X₀ Y₀ (2 * (k : ℝ)^4) := by
  by_cases hk2 : 2 ≤ k
  · exact adaptiveCompetitive_of_potential hk X₀ Y₀ (by positivity)
      (psi hk2 Y₀)
      (psi_nonneg hk2 Y₀)
      (psi_adv_move hk2 Y₀)
      (psi_online_move hk2 Y₀)
  · have hk1 : k = 1 := by omega
    exact harmonic_competitive_one hk1 X₀ Y₀

end HarmonicPotential

end HarmonicKServerProof

open HarmonicKServer.Competitive
open scoped BigOperators ENNReal
open MeasureTheory

theorem solution {k : ℕ} (hk : 1 ≤ k) {V : Type*} [MetricSpace V]
    (X₀ Y₀ : KServer.Config k V) :
    AdaptiveCompetitive X₀ Y₀ (2 * (k : ℝ)^4) :=
  HarmonicKServerProof.harmonic_competitive_main hk X₀ Y₀
