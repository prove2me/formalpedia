-- Prove2me | solution 1 for MirrorBP.JEA.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:58:54.8709+00:00
-- url     : https://prove2.me/submissions/1f578231-7022-4d0a-8f7a-c897f6023527

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA.Lemma4Aux

open Finset MirrorBP.JEA

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- Expected sum over `n` periods of a per-period reward `g q τ d` along the controlled chain. -/
noncomputable def expSum {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (g : (V → ℕ) → Ty → Decision V → ℝ) : ℕ → ℕ → History V Ty → (V → ℕ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, t, h, q =>
      ∑ τ, phi t τ * ∑ d, π.act t h q τ d *
        (g q τ d + expSum phi π g n (t + 1) (h ++ [(q, τ, d)]) (step q d))

theorem expSum_succ {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (g : (V → ℕ) → Ty → Decision V → ℝ) (n t : ℕ) (h : History V Ty) (q : V → ℕ) :
    expSum phi π g (n + 1) t h q = ∑ τ, phi t τ * ∑ d, π.act t h q τ d *
        (g q τ d + expSum phi π g n (t + 1) (h ++ [(q, τ, d)]) (step q d)) := rfl

theorem expPayoffFrom_eq {P D : Ty → Finset V} (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ)
    (π : Policy P D) : ∀ n t h q,
    expPayoffFrom w phi π n t h q = expSum phi π (fun _ τ d => pay w τ d) n t h q := by
  intro n
  induction n with
  | zero => intro t h q; rfl
  | succ n ih =>
    intro t h q
    rw [expPayoffFrom, expSum_succ]
    simp only [ih]

theorem expSum_congr {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (g g' : (V → ℕ) → Ty → Decision V → ℝ)
    (hg : ∀ q τ d, Feasible P D τ q d → g q τ d = g' q τ d) : ∀ n t h q,
    expSum phi π g n t h q = expSum phi π g' n t h q := by
  intro n
  induction n with
  | zero => intro t h q; rfl
  | succ n ih =>
    intro t h q
    rw [expSum_succ, expSum_succ]
    apply sum_congr rfl; intro τ _
    congr 1
    apply sum_congr rfl; intro d _
    by_cases hf : Feasible P D τ q d
    · rw [hg q τ d hf, ih]
    · rw [π.feasible _ _ _ _ _ hf]; simp

theorem expSum_sum {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D) {ι : Type}
    (I : Finset ι) (g : ι → (V → ℕ) → Ty → Decision V → ℝ) : ∀ n t h q,
    expSum phi π (fun q τ d => ∑ i ∈ I, g i q τ d) n t h q
      = ∑ i ∈ I, expSum phi π (g i) n t h q := by
  intro n
  induction n with
  | zero => intro t h q; simp [expSum]
  | succ n ih =>
    intro t h q
    simp only [expSum_succ, ih]
    simp only [← sum_add_distrib, mul_sum]
    conv_lhs => arg 2; ext τ; rw [sum_comm]
    rw [sum_comm]

theorem expSum_const_mul {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D) (c : ℝ)
    (g : (V → ℕ) → Ty → Decision V → ℝ) : ∀ n t h q,
    expSum phi π (fun q τ d => c * g q τ d) n t h q = c * expSum phi π g n t h q := by
  intro n
  induction n with
  | zero => intro t h q; simp [expSum]
  | succ n ih =>
    intro t h q
    simp only [expSum_succ, ih, mul_sum]
    apply sum_congr rfl; intro τ _
    apply sum_congr rfl; intro d _
    ring

theorem expSum_mono {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D)
    (g g' : (V → ℕ) → Ty → Decision V → ℝ)
    (hg : ∀ q τ d, Feasible P D τ q d → g q τ d ≤ g' q τ d) : ∀ n t h q,
    (∀ s, t ≤ s → s < t + n → ∀ τ, 0 ≤ phi s τ) →
    expSum phi π g n t h q ≤ expSum phi π g' n t h q := by
  intro n
  induction n with
  | zero => intro t h q _; rfl
  | succ n ih =>
    intro t h q hφ
    rw [expSum_succ, expSum_succ]
    apply sum_le_sum; intro τ _
    apply mul_le_mul_of_nonneg_left _ (hφ t le_rfl (by omega) τ)
    apply sum_le_sum; intro d _
    by_cases hf : Feasible P D τ q d
    · apply mul_le_mul_of_nonneg_left _ (π.nonneg _ _ _ _ _)
      have := ih (t + 1) (h ++ [(q, τ, d)]) (step q d) (fun s h1 h2 => hφ s (by omega) (by omega))
      linarith [hg q τ d hf]
    · rw [π.feasible _ _ _ _ _ hf]; simp

theorem expSum_zero {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D) : ∀ n t h q,
    expSum phi π (fun _ _ _ => 0) n t h q = 0 := by
  intro n
  induction n with
  | zero => intro t h q; rfl
  | succ n ih => intro t h q; simp [expSum_succ, ih]

theorem expSum_type {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D) (G : Ty → ℝ) :
    ∀ n t h q, (∀ s, t ≤ s → s < t + n → IsRate (phi s)) →
    expSum phi π (fun _ τ _ => G τ) n t h q = ∑ s ∈ range n, ∑ τ, phi (t + s) τ * G τ := by
  intro n
  induction n with
  | zero => intro t h q _; simp [expSum]
  | succ n ih =>
    intro t h q hr
    rw [expSum_succ, sum_range_succ']
    have hrt := hr t le_rfl (by omega)
    have hih : ∀ τ d, expSum phi π (fun _ τ _ => G τ) n (t + 1) (h ++ [(q, τ, d)]) (step q d)
        = ∑ s ∈ range n, ∑ τ, phi (t + (s + 1)) τ * G τ := by
      intro τ d
      rw [ih (t + 1) _ _ (fun s h1 h2 => hr s (by omega) (by omega))]
      apply sum_congr rfl; intro s _
      rw [show t + 1 + s = t + (s + 1) by ring]
    simp only [hih, mul_add, sum_add_distrib, ← sum_mul, π.sum_one, one_mul, hrt.2]
    simp only [Nat.add_zero]
    ring

theorem step_mem {P D : Ty → Finset V} (K : ℕ) (τ : Ty) (q : V → ℕ) (d : Decision V)
    (hf : Feasible P D τ q d) (hq : q ∈ StateSpace V K) : step q d ∈ StateSpace V K := by
  rcases d with _ | ⟨j, k⟩
  · simpa [step] using hq
  · have hj : 0 < q j := hf.2.2
    simp only [StateSpace, Set.mem_setOf_eq] at hq ⊢
    simp only [step, Pi.add_apply, Pi.sub_apply]
    rw [sum_add_distrib, Finset.sum_tsub_distrib]
    · simp [Finset.sum_pi_single', hq]
      have : q j ≤ ∑ i, q i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
      omega
    · intro i _
      by_cases hij : i = j
      · subst hij; simp; omega
      · simp [hij]

/-- Telescoping: the expected decrease of `H` over `n` periods lies in `[H q − K, H q]`
when `0 ≤ H ≤ K` on `Ω_K`. -/
theorem expSum_tele {P D : Ty → Finset V} (phi : ℕ → Ty → ℝ) (π : Policy P D) (K : ℕ)
    (H : (V → ℕ) → ℝ) (hH : ∀ q ∈ StateSpace V K, 0 ≤ H q ∧ H q ≤ K) : ∀ n t h q,
    q ∈ StateSpace V K → (∀ s, t ≤ s → s < t + n → IsRate (phi s)) →
    H q - K ≤ expSum phi π (fun q _ d => H q - H (step q d)) n t h q ∧
      expSum phi π (fun q _ d => H q - H (step q d)) n t h q ≤ H q := by
  intro n
  induction n with
  | zero =>
    intro t h q hq _
    simp only [expSum]
    have := hH q hq
    constructor <;> linarith
  | succ n ih =>
    intro t h q hq hr
    rw [expSum_succ]
    have hrt := hr t le_rfl (by omega)
    -- inner bounds for each type
    have hin : ∀ τ, H q - K ≤ ∑ d, π.act t h q τ d *
          (H q - H (step q d) + expSum phi π (fun q _ d => H q - H (step q d)) n (t + 1)
            (h ++ [(q, τ, d)]) (step q d)) ∧
        ∑ d, π.act t h q τ d *
          (H q - H (step q d) + expSum phi π (fun q _ d => H q - H (step q d)) n (t + 1)
            (h ++ [(q, τ, d)]) (step q d)) ≤ H q := by
      intro τ
      constructor
      · calc H q - K = ∑ d, π.act t h q τ d * (H q - K) := by
              rw [← sum_mul, π.sum_one, one_mul]
          _ ≤ _ := by
            apply sum_le_sum; intro d _
            by_cases hf : Feasible P D τ q d
            · apply mul_le_mul_of_nonneg_left _ (π.nonneg _ _ _ _ _)
              have := (ih (t + 1) (h ++ [(q, τ, d)]) (step q d) (step_mem K τ q d hf hq)
                (fun s h1 h2 => hr s (by omega) (by omega))).1
              linarith
            · rw [π.feasible _ _ _ _ _ hf]; simp
      · calc _ ≤ ∑ d, π.act t h q τ d * H q := by
              apply sum_le_sum; intro d _
              by_cases hf : Feasible P D τ q d
              · apply mul_le_mul_of_nonneg_left _ (π.nonneg _ _ _ _ _)
                have := (ih (t + 1) (h ++ [(q, τ, d)]) (step q d) (step_mem K τ q d hf hq)
                  (fun s h1 h2 => hr s (by omega) (by omega))).2
                linarith
              · rw [π.feasible _ _ _ _ _ hf]; simp
          _ = H q := by rw [← sum_mul, π.sum_one, one_mul]
    constructor
    · calc H q - K = ∑ τ, phi t τ * (H q - K) := by rw [← sum_mul, hrt.2, one_mul]
        _ ≤ _ := sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hin τ).1 (hrt.1 τ)
    · calc _ ≤ ∑ τ, phi t τ * H q :=
            sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hin τ).2 (hrt.1 τ)
        _ = H q := by rw [← sum_mul, hrt.2, one_mul]

/-- The indicator that the type is `τ0` and the decision serves it with `(j, k)`. -/
noncomputable def ind (j : V) (τ0 : Ty) (k : V) : (V → ℕ) → Ty → Decision V → ℝ :=
  fun _ τ d => if τ = τ0 ∧ d = some (j, k) then 1 else 0

theorem relObj_le (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) (φ : Ty → ℝ) (r : ℝ)
    (z : V → Ty → V → ℝ) (hz : relaxedFeasZ P D φ r z) : objZ P D w z ≤ ∑ τ, φ τ := by
  unfold objZ
  apply sum_le_sum; intro τ _
  calc ∑ j ∈ P τ, ∑ k ∈ D τ, w j τ k * z j τ k ≤ ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k := by
        apply sum_le_sum; intro j hj
        apply sum_le_sum; intro k hk
        have h1 : w j τ k ≤ 1 := le_trans (le_abs_self _) (hw τ j hj k hk)
        have h2 := hz.1.2 τ j hj k hk
        nlinarith
    _ ≤ φ τ := hz.1.1 τ


theorem ind_sum_none (P D : Ty → Finset V) (c : V → Ty → V → ℝ) (q : V → ℕ) (τ' : Ty) :
    ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * ind j τ k q τ' none = 0 := by
  simp [ind]

theorem ind_sum_some (P D : Ty → Finset V) (c : V → Ty → V → ℝ) (q : V → ℕ) (τ' : Ty)
    (j0 k0 : V) (hj : j0 ∈ P τ') (hk : k0 ∈ D τ') :
    ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * ind j τ k q τ' (some (j0, k0)) = c j0 τ' k0 := by
  have : ∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * ind j τ k q τ' (some (j0, k0))
      = if τ = τ' then c j0 τ' k0 else 0 := by
    intro τ
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, sum_eq_single j0, sum_eq_single k0]
      · simp [ind]
      · intro k _ hk'; simp [ind, Ne.symm hk']
      · intro hk'; exact absurd hk hk'
      · intro j _ hj'
        apply sum_eq_zero; intro k _; simp [ind, Ne.symm hj']
      · intro hj'; exact absurd hj hj'
    · rw [if_neg hτ]
      apply sum_eq_zero; intro j _; apply sum_eq_zero; intro k _
      simp [ind, Ne.symm hτ]
  rw [sum_congr rfl (fun τ _ => this τ)]
  simp

theorem ind_demand (P D : Ty → Finset V) (q : V → ℕ) (τ τ' : Ty) (d : Decision V)
    (hf : Feasible P D τ' q d) :
    ∑ j ∈ P τ, ∑ k ∈ D τ, ind j τ k q τ' d
      ≤ (if τ' = τ then 1 else 0) := by
  rcases d with _ | ⟨j0, k0⟩
  · simp only [ind, reduceCtorEq, and_false, if_false, sum_const_zero]
    split_ifs <;> norm_num
  · by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, sum_eq_single j0, sum_eq_single k0]
      · simp [ind]
      · intro k _ hk'; simp [ind, Ne.symm hk']
      · intro hk'; exact absurd hf.2.1 hk'
      · intro j _ hj'
        apply sum_eq_zero; intro k _; simp [ind, Ne.symm hj']
      · intro hj'; exact absurd hf.1 hj'
    · rw [if_neg hτ]
      apply le_of_eq; apply sum_eq_zero; intro j _; apply sum_eq_zero; intro k _
      simp [ind, hτ]

theorem step_cast (q : V → ℕ) (j0 k0 : V) (hj : 0 < q j0) (i : V) :
    ((step q (some (j0, k0)) i : ℕ) : ℝ)
      = q i - (if i = j0 then 1 else 0) + (if i = k0 then 1 else 0) := by
  simp only [step, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : i = j0
  · subst h1
    have : 1 ≤ q i := hj
    by_cases h2 : i = k0
    · subst h2; simp; rw [Nat.cast_sub this]; simp
    · simp [h2]; rw [Nat.cast_sub this]; simp
  · by_cases h2 : i = k0
    · subst h2; simp [h1]
    · simp [h1, h2]

end MirrorBP.JEA.Lemma4Aux

open Finset MirrorBP.JEA

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (T K : ℕ) (hT : 0 < T) (hrate : ∀ t < T, IsRate (phi t))
    (π : Policy P D) (q : V → ℕ) (hq : q ∈ StateSpace V K) :
    expPayoff w phi π T q / T ≤ relaxedValue P D w (phibar phi T) ((K : ℝ) / T) := by
  open Lemma4Aux in
  have hr : ∀ s, 0 ≤ s → s < 0 + T → IsRate (phi s) := fun s _ hs => hrate s (by omega)
  have hφ0 : ∀ s, 0 ≤ s → s < 0 + T → ∀ τ, 0 ≤ phi s τ := fun s h1 h2 τ => (hr s h1 h2).1 τ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  let E : ((V → ℕ) → Ty → Decision V → ℝ) → ℝ := fun g => Lemma4Aux.expSum phi π g T 0 [] q
  let z : V → Ty → V → ℝ := fun j τ k => (1 / (T : ℝ)) * E (Lemma4Aux.ind j τ k)
  -- objective
  have hobj : objZ P D w z = expPayoff w phi π T q / T := by
    have e1 : objZ P D w z = (1 / (T : ℝ)) * E (fun q' τ' d => ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
        w j τ k * Lemma4Aux.ind j τ k q' τ' d) := by
      simp only [E, Lemma4Aux.expSum_sum, Lemma4Aux.expSum_const_mul, objZ, z, mul_sum]
      apply sum_congr rfl; intro τ _; apply sum_congr rfl; intro j _; apply sum_congr rfl
      intro k _; ring
    have e2 : E (fun q' τ' d => ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
        w j τ k * Lemma4Aux.ind j τ k q' τ' d) = E (fun _ τ' d => pay w τ' d) := by
      apply Lemma4Aux.expSum_congr
      intro q' τ' d hf
      rcases d with _ | ⟨j0, k0⟩
      · rw [Lemma4Aux.ind_sum_none]; rfl
      · rw [Lemma4Aux.ind_sum_some P D w q' τ' j0 k0 hf.1 hf.2.1]; rfl
    rw [e1, e2]
    simp only [E, expPayoff, Lemma4Aux.expPayoffFrom_eq]
    ring
  -- nonnegativity
  have hz0 : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, 0 ≤ z j τ k := by
    intro τ j _ k _
    have := Lemma4Aux.expSum_mono phi π (fun _ _ _ => 0) (Lemma4Aux.ind j τ k)
      (fun q' τ' d _ => by unfold Lemma4Aux.ind; split_ifs <;> norm_num) T 0 [] q hφ0
    rw [Lemma4Aux.expSum_zero] at this
    exact mul_nonneg (by positivity) this
  -- demand
  have hdem : ∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k ≤ phibar phi T τ := by
    intro τ
    have e1 : ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k
        = (1 / (T : ℝ)) * E (fun q' τ' d => ∑ j ∈ P τ, ∑ k ∈ D τ, Lemma4Aux.ind j τ k q' τ' d) := by
      simp only [E, Lemma4Aux.expSum_sum, z, mul_sum]
    have e2 := Lemma4Aux.expSum_mono phi π
      (fun q' τ' d => ∑ j ∈ P τ, ∑ k ∈ D τ, Lemma4Aux.ind j τ k q' τ' d)
      (fun _ τ' _ => if τ' = τ then 1 else 0)
      (fun q' τ' d hf => Lemma4Aux.ind_demand P D q' τ τ' d hf) T 0 [] q hφ0
    rw [Lemma4Aux.expSum_type phi π _ T 0 [] q hr] at e2
    have e3 : ∑ s ∈ range T, ∑ τ', phi (0 + s) τ' * (if τ' = τ then (1 : ℝ) else 0)
        = ∑ s ∈ range T, phi s τ := by
      apply sum_congr rfl; intro s _; simp
    rw [e3] at e2
    rw [e1]
    unfold phibar
    exact mul_le_mul_of_nonneg_left e2 (by positivity)
  -- flow balance
  have hflow : ∀ S : Finset V, |netOut P D z S| ≤ (K : ℝ) / T := by
    intro S
    let H : (V → ℕ) → ℝ := fun q' => ∑ i ∈ S, (q' i : ℝ)
    have e1 : netOut P D z S = (1 / (T : ℝ)) * E (fun q' τ' d => ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
        ((if j ∈ S then 1 else 0) - (if k ∈ S then 1 else 0)) * Lemma4Aux.ind j τ k q' τ' d) := by
      simp only [E, Lemma4Aux.expSum_sum, Lemma4Aux.expSum_const_mul, netOut, z, mul_sum]
      apply sum_congr rfl; intro τ _; apply sum_congr rfl; intro j _; apply sum_congr rfl
      intro k _; ring
    have e2 : E (fun q' τ' d => ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ,
        ((if j ∈ S then 1 else 0) - (if k ∈ S then 1 else 0)) * Lemma4Aux.ind j τ k q' τ' d)
        = E (fun q' _ d => H q' - H (step q' d)) := by
      apply Lemma4Aux.expSum_congr
      intro q' τ' d hf
      rcases d with _ | ⟨j0, k0⟩
      · rw [Lemma4Aux.ind_sum_none]; simp [step]
      · rw [Lemma4Aux.ind_sum_some P D (fun j _ k => ((if j ∈ S then 1 else 0) -
          (if k ∈ S then 1 else 0) : ℝ)) q' τ' j0 k0 hf.1 hf.2.1]
        simp only [H]
        rw [← sum_sub_distrib]
        simp only [Lemma4Aux.step_cast q' j0 k0 hf.2.2]
        simp only [sub_add, sub_sub_cancel, sum_sub_distrib, sum_ite_eq', ite_mem]
    have hH : ∀ q' ∈ StateSpace V K, 0 ≤ H q' ∧ H q' ≤ K := by
      intro q' hq'
      constructor
      · exact sum_nonneg fun i _ => by positivity
      · have : H q' ≤ ∑ i, (q' i : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _ => by positivity)
        have hs : ∑ i, (q' i : ℝ) = K := by
          have := hq'; simp only [StateSpace, Set.mem_setOf_eq] at this
          exact_mod_cast this
        linarith
    have tele := Lemma4Aux.expSum_tele phi π K H hH T 0 [] q hq hr
    have hHq := hH q hq
    rw [e1, e2, abs_le]
    simp only [E]
    have hT1 : (0 : ℝ) < 1 / T := by positivity
    constructor
    · have := mul_le_mul_of_nonneg_left (show -(K : ℝ) ≤ Lemma4Aux.expSum phi π
        (fun q' _ d => H q' - H (step q' d)) T 0 [] q by linarith [tele.1]) hT1.le
      have e : 1 / (T : ℝ) * -(K : ℝ) = -((K : ℝ) / T) := by ring
      linarith
    · have := mul_le_mul_of_nonneg_left (show Lemma4Aux.expSum phi π
        (fun q' _ d => H q' - H (step q' d)) T 0 [] q ≤ K by linarith [tele.2]) hT1.le
      have e : 1 / (T : ℝ) * (K : ℝ) = (K : ℝ) / T := by ring
      linarith
  -- conclude
  have hfeas : relaxedFeasZ P D (phibar phi T) ((K : ℝ) / T) z := ⟨⟨hdem, hz0⟩, hflow⟩
  have hbdd : BddAbove (objZ P D w '' {z | relaxedFeasZ P D (phibar phi T) ((K : ℝ) / T) z}) := by
    refine ⟨∑ τ, phibar phi T τ, ?_⟩
    rintro _ ⟨z', hz', rfl⟩
    exact Lemma4Aux.relObj_le P D w hw _ _ z' hz'
  rw [← hobj]
  exact le_csSup hbdd ⟨z, hfeas, rfl⟩
