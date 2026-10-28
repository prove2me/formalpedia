-- Prove2me | solution 1 for OAI.Thorp.mixingTime_isTheta_log_q3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:04:11.505627+00:00
-- url     : https://prove2.me/submissions/acd6a576-63ef-40c2-b1a5-bca0f3efbbe8

import Mathlib
import Definitions.Def_ThorpRemaining
import Definitions.Def_OAIQ3Th000

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PairAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem sum_sign {α : Type uα} [Fintype α] [DecidableEq α] (i : α) :
    ∑ c : α → Bool, sign (c i) = 0 := by
  have h := Equiv.sum_comp (toggleCoin i) (fun c : α → Bool => sign (c i))
  simp only [toggleCoin_apply, Function.update_self, sign_not, Finset.sum_neg_distrib] at h
  linarith

theorem sum_sign_pair {α : Type uα} [Fintype α] [DecidableEq α] (i j : α) :
    (∑ c : α → Bool, sign (c i) * sign (c j)) =
      if i = j then (Fintype.card (α → Bool) : ℝ) else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · have he := Equiv.sum_comp (toggleCoin i) (fun c : α → Bool => sign (c i) * sign (c j))
    simp only [toggleCoin_apply, Function.update_self,
      Function.update_of_ne (Ne.symm h), sign_not, neg_mul,
      Finset.sum_neg_distrib] at he
    rw [ite_eq_right h]
    linarith

theorem mean_signed_sum_sq {α : Type uα} [Fintype α] [DecidableEq α] (a : α → ℝ) :
    mean (fun c : α → Bool => (∑ i, sign (c i) * a i) ^ 2) = ∑ i, a i ^ 2 := by
  have hs :
      (∑ c : α → Bool, (∑ i, sign (c i) * a i) ^ 2) =
        (Fintype.card (α → Bool) : ℝ) * ∑ i, a i ^ 2 := by
    calc
      _ = ∑ c : α → Bool, ∑ i, ∑ j,
          (sign (c i) * sign (c j)) * (a i * a j) := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, (∑ c : α → Bool, sign (c i) * sign (c j)) * (a i * a j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp only [sum_sign_pair, ite_mul, zero_mul]
        simp [Finset.mul_sum, pow_two]
  unfold mean
  rw [hs]
  have hcard : (Fintype.card (α → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hcard

theorem pairUpdate_difference (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 - (pairUpdate free₀ free₁ a b coin).2 =
      sign coin * (if free₀ && free₁ then 0 else a - b) := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate, sign]

theorem pairUpdate_difference_sq (free₀ free₁ : Bool) (a b : ℝ)
    (ha : free₀ = false → a = 0) (hb : free₁ = false → b = 0) :
    (if free₀ && free₁ then (0 : ℝ) else a - b) ^ 2 =
      (if free₁ then 0 else a ^ 2) + (if free₀ then 0 else b ^ 2) := by
  cases free₀ <;> cases free₁ <;> simp_all

theorem mean_oddCoefficient_sq {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (w : Bool × α → ℝ) (ε : α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (hε : ∀ i, ε i ^ 2 = 1) :
    mean (fun c : α → Bool => oddCoefficient ε (flow B w c) ^ 2) =
      ∑ i, ((if B (true, i) then 0 else w (false, i) ^ 2) +
        (if B (false, i) then 0 else w (true, i) ^ 2)) := by
  have he (c : α → Bool) :
      oddCoefficient ε (flow B w c) =
        ∑ i, sign (c i) * (ε i *
          (if B (false, i) && B (true, i) then 0 else w (false, i) - w (true, i))) := by
    unfold oddCoefficient
    apply Finset.sum_congr rfl
    intro i _
    simp only [flow, Bool.false_eq_true, ↓reduceIte]
    rw [pairUpdate_difference]
    ring
  simp_rw [he]
  rw [mean_signed_sum_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, hε, one_mul]
  exact pairUpdate_difference_sq _ _ _ _ (hw _) (hw _)

end Conditional

namespace Conditional

theorem flow_uniform {α : Type uα} (B : Bool × α → Bool) (r : ℝ)
    (c : α → Bool) (x : Bool × α) :
    flow B (fun y => if B y then r else 0) c x =
      if B (pairMap c x) then r else 0 := by
  rcases x with ⟨b, i⟩
  cases b <;> cases h₀ : B (false, i) <;> cases h₁ : B (true, i) <;>
    cases hc : c i <;> simp [flow, pairUpdate, pairMap, h₀, h₁, hc]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Walsh
attribute [-instance] _root_.OAI.Thorp.Conditional.prefixZeroDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uκ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem character_symm {ι : Type uι} [Fintype ι] (a x : ι → Bool) :
    character a x = character x a := by
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> cases x i <;> rfl

theorem sum_character_pair {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) :
    (∑ x : ι → Bool, character a x * character b x) =
      if a = b then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have hlocal (u v : Bool) :
      (∑ x : Bool, (if u then sign x else (1 : ℝ)) * (if v then sign x else 1)) =
        if u = v then 2 else 0 := by
    cases u <;> cases v <;> norm_num [sign]
  have hf : (∑ x : ι → Bool, character a x * character b x) =
      ∏ i, (if a i = b i then (2 : ℝ) else 0) := by
    calc
      _ = ∑ x : ι → Bool, ∏ i,
          (if a i then sign (x i) else (1 : ℝ)) * (if b i then sign (x i) else 1) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.prod_mul_distrib).symm
      _ = ∏ i, ∑ x : Bool,
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1) :=
        (Fintype.prod_sum (fun (i : ι) (x : Bool) =>
          (if a i then sign x else (1 : ℝ)) * (if b i then sign x else 1))).symm
      _ = _ := by simp only [hlocal]
  rw [hf]
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, a i = b i := fun he => h (funext he)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sum_character_pair_dual {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) :
    (∑ a : ι → Bool, character a x * character a y) =
      if x = y then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  calc
    _ = ∑ a : ι → Bool, character x a * character y a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [character_symm a x, character_symm a y]
    _ = _ := sum_character_pair x y

theorem parseval {ι : Type uι} [Fintype ι] [DecidableEq ι] (w : (ι → Bool) → ℝ) :
    mean (fun a : ι → Bool => coefficient w a ^ 2) = ∑ x, w x ^ 2 := by
  have hs :
      (∑ a : ι → Bool, coefficient w a ^ 2) =
        (Fintype.card (ι → Bool) : ℝ) * ∑ x, w x ^ 2 := by
    calc
      _ = ∑ a : ι → Bool, ∑ x, ∑ y,
          (character a x * character a y) * (w x * w y) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [coefficient, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ x, ∑ y, (∑ a : ι → Bool, character a x * character a y) * (w x * w y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by
        simp only [sum_character_pair_dual, ite_mul, zero_mul]
        simp [Finset.mul_sum, pow_two]
  unfold mean
  rw [hs]
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ _ hcard

theorem character_cons (d : ℕ) (h b : Bool) (a x : Position d) :
    character (Fin.cons h a) (Fin.cons b x) =
      (if h then sign b else 1) * character a x := by
  simp [character, Fin.prod_univ_succ]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Support
attribute [-instance] _root_.OAI.Thorp.Conditional.prefixZeroDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

theorem fairMass_nonneg {Ω : Type uΩ} {α : Type uα} [Fintype Ω] (f : Ω → α) (a : α) :
    0 ≤ fairMass f a := by
  classical
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (Nat.cast_nonneg _)

theorem fairMass_sum {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (f : Ω → α) : ∑ a, fairMass f a = 1 := by
  classical
  unfold fairMass
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem sum_sub_le_tv {α : Type uα} [Fintype α] [DecidableEq α]
    (μ ν : α → ℝ) (hm : ∑ a, μ a = ∑ a, ν a) (s : Finset α) :
    (∑ a ∈ s, (μ a - ν a)) ≤ tv μ ν := by
  have h0 : ∑ a, (μ a - ν a) = 0 := by rw [Finset.sum_sub_distrib, hm, sub_self]
  have hsplit := s.sum_add_sum_compl (fun a => μ a - ν a)
  have hsplitabs := s.sum_add_sum_compl (fun a => |μ a - ν a|)
  have h₁ : (∑ a ∈ s, (μ a - ν a)) ≤ ∑ a ∈ s, |μ a - ν a| :=
    Finset.sum_le_sum (fun a _ => le_abs_self (μ a - ν a))
  have h₂ : -(∑ a ∈ sᶜ, (μ a - ν a)) ≤ ∑ a ∈ sᶜ, |μ a - ν a| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun a _ => neg_le_abs (μ a - ν a))
  unfold tv
  linarith

theorem fairMass_tv_lower {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Nonempty α] (f : Ω → α) :
    1 - (Fintype.card Ω : ℝ) / Fintype.card α ≤ tv (fairMass f)
      (fun _ => 1 / Fintype.card α) := by
  classical
  let s : Finset α := Finset.univ.image f
  have hm : ∑ a, fairMass f a = ∑ a : α, (1 / Fintype.card α : ℝ) := by
    rw [fairMass_sum]
    simp [Fintype.card_ne_zero]
  have hz (a : α) (ha : a ∉ s) : fairMass f a = 0 := by
    unfold fairMass
    have hne (ω : Ω) : f ω ≠ a := by
      intro h
      apply ha
      exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, h⟩
    simp [hne]
  have hs : ∑ a ∈ s, fairMass f a = 1 := by
    rw [← fairMass_sum f]
    exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hz a ha)
  have hbound := sum_sub_le_tv (fairMass f) (fun _ => 1 / Fintype.card α) hm s
  rw [Finset.sum_sub_distrib, hs] at hbound
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div] at hbound
  have hc : (s.card : ℝ) ≤ Fintype.card Ω := by
    exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := f))
  have hd : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hc hd
  linarith

theorem distance_support_lower (d t : ℕ) :
    1 - (2 : ℝ) ^ (2 ^ d * t) / ((2 ^ (d + 1)).factorial : ℝ) ≤
      distance (d + 1) t := by
  let : Nonempty (State (d + 1)) := ⟨Equiv.refl _⟩
  have h := fairMass_tv_lower (run (d + 1) t)
  change 1 - _ / _ ≤ tv (fairMass (run (d + 1) t))
    (fun _ => 1 / Fintype.card (State (d + 1)))
  simpa only [card_history_succ, card_state, Nat.cast_pow, Nat.cast_ofNat] using h

theorem supportThreshold_le_of_distance {d t : ℕ} (hd : 1 ≤ d)
    (ht : distance d t ≤ 1 / 4) : supportThreshold d ≤ (t : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hfact : (0 : ℝ) < ((2 ^ (k + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hlower := distance_support_lower k t
  have hdiv : (3 : ℝ) / 4 ≤ 2 ^ (2 ^ k * t) / ((2 ^ (k + 1)).factorial : ℝ) := by
    linarith
  have hpow : 3 * ((2 ^ (k + 1)).factorial : ℝ) / 4 ≤ (2 : ℝ) ^ (2 ^ k * t) := by
    have h := (le_div_iff₀ hfact).mp hdiv
    nlinarith
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 3 * ((2 ^ (k + 1)).factorial : ℝ) / 4)
    (by positivity : (0 : ℝ) < 2 ^ (2 ^ k * t))).mpr hpow
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  simp only [mul_one] at hlog
  unfold supportThreshold
  apply Int.ceil_le.mpr
  push_cast
  have hden : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hscale := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 / 2 ^ (k + 1))
  have hid : (2 / (2 : ℝ) ^ (k + 1)) * ((2 ^ k * t : ℕ) : ℝ) = t := by
    push_cast
    rw [pow_succ]
    field_simp
  rwa [hid] at hscale

theorem supportThreshold_le_mixingTime {d : ℕ} (hd : 1 ≤ d)
    (hex : ∃ t, distance d t ≤ 1 / 4) : supportThreshold d ≤ (mixingTime d : ℤ) := by
  apply supportThreshold_le_of_distance hd
  exact Nat.sInf_mem hex

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_SpectralDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem half_weight_sum (d : ℕ) :
    (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) = 1 - (1 / 2 : ℝ) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem half_weight_geometric_identity (γ : ℝ) (d t : ℕ) (hdt : d ≤ t) :
    (2 * γ - 1) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) =
      γ ^ t - (1 / 2 : ℝ) ^ d * γ ^ (t - d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : d ≤ t := by omega
    have ht : t - d = (t - 1 - d) + 1 := by omega
    have ht' : t - (d + 1) = t - 1 - d := by omega
    rw [Finset.sum_range_succ, mul_add, ih hd, ht, ht', pow_succ, pow_succ]
    ring

theorem half_weight_geometric_bound (β γ : ℝ) (d t : ℕ)
    (hγ : 0 ≤ γ) (hrel : 1 - β ≤ 2 * γ - 1) (hdt : d ≤ t) :
    (1 - β) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) ≤ γ ^ t := by
  have hs : 0 ≤ ∑ j ∈ Finset.range d,
      (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j) := by positivity
  calc
    _ ≤ (2 * γ - 1) *
        (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j)) :=
      mul_le_mul_of_nonneg_right hrel hs
    _ = γ ^ t - (1 / 2 : ℝ) ^ d * γ ^ (t - d) :=
      half_weight_geometric_identity γ d t hdt
    _ ≤ γ ^ t := sub_le_self _ (by positivity)

theorem spectral_track_unroll (d : ℕ) (H : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hstep : ∀ t j, j < d → H (t + 1) j =
      H t (j + 1) + (1 / 2 : ℝ) ^ (j + 1) * b t)
    (t j k : ℕ) (hjk : j + k ≤ d) (hkt : k ≤ t) :
    H t j = H (t - k) (j + k) +
      ∑ r ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + r + 1) * b (t - 1 - r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ t := by omega
    have hjk' : j + k ≤ d := by omega
    rw [ih hjk' hk, Finset.sum_range_succ]
    have ht : t - k = (t - 1 - k) + 1 := by omega
    have hj : j + k < d := by omega
    rw [ht, hstep _ _ hj]
    have ht' : t - (k + 1) = t - 1 - k := by omega
    rw [ht']
    simp only [Nat.add_assoc]
    ring

theorem energy_of_spectral_tracks (d : ℕ) (H : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hstep : ∀ t j, j < d → H (t + 1) j =
      H t (j + 1) + (1 / 2 : ℝ) ^ (j + 1) * b t)
    (hzero : ∀ t, H t d = 0) (t : ℕ) (ht : d ≤ t) :
    H t 0 = ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j) := by
  simpa only [zero_add, hzero] using
    spectral_track_unroll d H b hstep t 0 d (by omega) ht

theorem scalar_decay (d : ℕ) (E b : ℕ → ℝ) (β γ η : ℝ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hrel : 1 - β ≤ 2 * γ - 1) (hη : 0 ≤ η)
    (hE : ∀ t, E t ≤ 1)
    (henergy : ∀ t, d ≤ t → E t =
      ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j))
    (hnoise : ∀ s, d ≤ s → b s ≤ (1 - β) * E s + η) :
    ∀ t, E t ≤ γ ^ t / γ ^ (2 * d) + η / β := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t ≤ 2 * d
    · have hp : γ ^ (2 * d) ≤ γ ^ t := pow_le_pow_of_le_one hγ.le hγ₁ ht
      have hquot : (1 : ℝ) ≤ γ ^ t / γ ^ (2 * d) :=
        (le_div_iff₀ (pow_pos hγ _)).mpr (by simpa using hp)
      have hc : 0 ≤ η / β := div_nonneg hη hβ.le
      linarith [hE t]
    · have hdt : d ≤ t := by omega
      rw [henergy t hdt]
      have hbound :
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) * b (t - 1 - j)) ≤
          ∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) *
            ((1 - β) * (γ ^ (t - 1 - j) / γ ^ (2 * d) + η / β) + η) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjd := Finset.mem_range.mp hj
        have hsd : d ≤ t - 1 - j := by omega
        have hst : t - 1 - j < t := by omega
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (hnoise _ hsd).trans
          (add_le_add (mul_le_mul_of_nonneg_left (ih _ hst)
            (show 0 ≤ 1 - β by linarith)) (le_refl η))
      have hconstant : (1 - β) * (η / β) + η = η / β := by
        field_simp
        ring
      have hsplit :
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1) *
            ((1 - β) * (γ ^ (t - 1 - j) / γ ^ (2 * d) + η / β) + η)) =
          ((1 - β) * (∑ j ∈ Finset.range d,
            (1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j))) / γ ^ (2 * d) +
          (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) * (η / β) := by
        calc
          _ = ∑ j ∈ Finset.range d,
              (((1 - β) * ((1 / 2 : ℝ) ^ (j + 1) * γ ^ (t - 1 - j))) /
                γ ^ (2 * d) + (1 / 2 : ℝ) ^ (j + 1) * (η / β)) := by
            apply Finset.sum_congr rfl
            intro j _
            linear_combination (1 / 2 : ℝ) ^ (j + 1) * hconstant
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
              ← Finset.sum_mul]
      rw [hsplit] at hbound
      have hgeom := half_weight_geometric_bound β γ d t hγ.le hrel hdt
      have hgeom' := div_le_div_of_nonneg_right hgeom (pow_nonneg hγ.le (2 * d))
      have hc : (∑ j ∈ Finset.range d, (1 / 2 : ℝ) ^ (j + 1)) * (η / β) ≤ η / β := by
        rw [half_weight_sum]
        have hz : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
        have hηβ : 0 ≤ η / β := div_nonneg hη hβ.le
        nlinarith
      linarith

theorem eight_block_geometric_choice : (31 / 32 : ℝ) ^ 198 ≤ (1 / 2 : ℝ) ^ 8 := by
  norm_num

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ConditionalFlow
attribute [-instance] _root_.OAI.Thorp.Conditional.prefixZeroDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem physicalFlow_uniform (d : ℕ) (B : Position (d + 1) → Bool)
    (r : ℝ) (c : Coins (d + 1)) (x : Position (d + 1)) :
    physicalFlow d B (fun y => if B y then r else 0) c x =
      if physicalFree d B c x then r else 0 := by
  obtain ⟨p, rfl⟩ := (scatterPosition d).surjective x
  rw [physicalFlow_scatter, physicalFree_scatter]
  exact flow_uniform _ r c p

theorem expectedEnergy_le_one (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedEnergy d v t ≤ 1 := by
  unfold expectedEnergy mean
  have hc : (0 : ℝ) < Fintype.card (History (d + 1) t) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _ω : History (d + 1) t, (1 : ℝ) :=
      Finset.sum_le_sum (fun ω _ => (iterateState d v t ω).energy_le_one)
    _ = _ := by simp

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FiniteExpectation
attribute [-instance] _root_.OAI.Thorp.Conditional.prefixZeroDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uι uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_congr {Ω : Type uΩ} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    mean f = mean g := by
  unfold mean
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

theorem mean_zero {Ω : Type uΩ} [Fintype Ω] : mean (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [mean]

theorem mean_const {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    mean (fun _ : Ω => a) = a := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hc]

theorem mean_add {Ω : Type uΩ} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω + g ω) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul_const {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => f ω * a) = mean f * a := by
  simp only [mean, ← Finset.sum_mul]
  ring

theorem mean_const_mul {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => a * f ω) = a * mean f := by
  simpa only [mul_comm] using mean_mul_const f a

theorem mean_sum {Ω : Type uΩ} {ι : Type uι} [Fintype Ω] (s : Finset ι) (f : Ω → ι → ℝ) :
    mean (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, mean (fun ω => f ω i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem mean_nonneg {Ω : Type uΩ} [Fintype Ω] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => hf ω)) (Nat.cast_nonneg _)

theorem mean_le_mean {Ω : Type uΩ} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    mean f ≤ mean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem mean_equiv {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) : mean (f ∘ e) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

theorem mean_prod {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (f : Ω × Ω' → ℝ) : mean f = mean (fun ω => mean (fun ω' => f (ω, ω'))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem mean_comm {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω'] (f : Ω → Ω' → ℝ) :
    mean (fun ω => mean (f ω)) = mean (fun ω' => mean (fun ω => f ω ω')) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem mean_history_succ (d t : ℕ) (f : History d (t + 1) → ℝ) :
    mean f = mean (fun ω : History d t => mean (fun c : Coins d => f (Fin.snoc ω c))) := by
  have h := mean_equiv (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins d)) f
  rw [mean_prod] at h
  rw [← h, mean_comm]
  rfl

end Conditional

namespace Conditional

theorem iterateState_free (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (iterateState d v t ω).free x = v.free ((run (d + 1) t ω).symm x) := by
  induction t generalizing x with
  | zero => simp only [iterateState, run_zero]; rfl
  | succ t ih =>
    change (iterateState d v t (fun i => ω i.castSucc)).free
      ((step (d + 1) (ω (Fin.last t))).symm x) = _
    rw [ih, run_succ]
    rfl

theorem iterateState_freeCount (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) : freeCount (iterateState d v t ω).free = freeCount v.free := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  simp only [iterateState_free]
  exact Equiv.sum_comp (run (d + 1) t ω).symm (fun x => if v.free x then (1 : ℝ) else 0)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_WalshFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem scatterPosition_eq_snoc (d : ℕ) (b : Bool) (x : Position d) :
    scatterPosition d (b, x) = Fin.snoc x b := by
  rw [Fin.snoc_eq_cons_rotate]
  ext i
  simp only [scatterPosition, splitPosition, Equiv.trans_apply, Equiv.symm_symm,
    Fin.consEquiv_apply, rotate, Equiv.piCongrLeft_apply]
  simp

theorem character_snoc (d : ℕ) (h b : Bool) (a x : Position d) :
    character (Fin.snoc a h) (Fin.snoc x b) =
      character a x * (if h then sign b else 1) := by
  simp [character, Fin.prod_univ_castSucc]

theorem coefficient_physicalFlow_even (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (a : Position d) :
    coefficient (physicalFlow d B w c) (Fin.snoc a false) =
      coefficient w (Fin.cons false a) := by
  unfold coefficient
  rw [← Equiv.sum_comp (scatterPosition d)
    (fun x => physicalFlow d B w c x * character (Fin.snoc a false) x)]
  rw [← Equiv.sum_comp (splitPosition d).symm
    (fun x => w x * character (Fin.cons false a) x)]
  simp only [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [physicalFlow_scatter]
  simp only [scatterPosition_eq_snoc, character_snoc,
    Bool.false_eq_true, ↓reduceIte, mul_one]
  change flow _ _ c (true, x) * character a x +
    flow _ _ c (false, x) * character a x =
    w (Fin.cons true x) * character (Fin.cons false a) (Fin.cons true x) +
    w (Fin.cons false x) * character (Fin.cons false a) (Fin.cons false x)
  rw [character_cons, character_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [← add_mul, ← add_mul]
  congr 1
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm, Function.comp_apply,
    splitPosition, Equiv.symm_symm, Fin.consEquiv, Equiv.coe_fn_mk] using
    pairUpdate_sum (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)

theorem coefficient_physicalFlow_odd (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (a : Position d) :
    coefficient (physicalFlow d B w c) (Fin.snoc a true) =
      oddCoefficient (character a) (flow (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c) := by
  unfold coefficient
  rw [← Equiv.sum_comp (scatterPosition d)
    (fun x => physicalFlow d B w c x * character (Fin.snoc a true) x)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  unfold oddCoefficient
  apply Finset.sum_congr rfl
  intro x _
  simp only [physicalFlow_scatter]
  simp only [scatterPosition_eq_snoc, character_snoc,
    ↓reduceIte, sign, Bool.false_eq_true]
  ring

theorem mean_coefficient_physicalFlow_odd_sq (d : ℕ)
    (B : Position (d + 1) → Bool) (w : Position (d + 1) → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (a : Position d) :
    mean (fun c : Coins (d + 1) =>
      coefficient (physicalFlow d B w c) (Fin.snoc a true) ^ 2) =
        oneFreeEnergy d B w := by
  simp_rw [coefficient_physicalFlow_odd]
  exact mean_oddCoefficient_sq _ _ _ (fun p => hw ((splitPosition d).symm p))
    (character_sq a)

end Conditional

namespace Conditional

theorem prefixZero_full {d : ℕ} (a : Position d) :
    prefixZero d a ↔ a = fun _ => false := by
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h
    subst a
    intro i _
    rfl

theorem prefixZero_cons (j d : ℕ) (h : Bool) (a : Position d) :
    prefixZero (j + 1) (Fin.cons h a) ↔ h = false ∧ prefixZero j a := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · simpa using hp 0 (by simp)
    · intro i hi
      simpa using hp i.succ (by simpa using hi)
  · rintro ⟨rfl, hp⟩ i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro _; rfl
    · intro hi
      exact hp k (by simpa using hi)

theorem prefixZero_snoc (j d : ℕ) (hj : j ≤ d) (h : Bool) (a : Position d) :
    prefixZero j (Fin.snoc a h) ↔ prefixZero j a := by
  constructor
  · intro hp i hi
    simpa using hp i.castSucc hi
  · intro hp i hi
    have hid : i.val < d := lt_of_lt_of_le hi hj
    rw [Fin.snoc, dite_eq_left hid]
    exact hp _ hi

theorem prefixZero_count (j d : ℕ) (hj : j ≤ d) :
    (∑ a : Position d, if prefixZero j a then (1 : ℝ) else 0) = 2 ^ (d - j) := by
  classical
  induction d generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ d ih =>
    cases j with
    | zero => simp [Fintype.card_pi, Fintype.card_bool]
    | succ j =>
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
        (fun a => if prefixZero (j + 1) a then (1 : ℝ) else 0)]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, Fintype.sum_bool,
        prefixZero_cons]
      simpa using ih j (by omega)

@[simp] theorem bandEnergy_zero (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w 0 = (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
  have hp := parseval w
  unfold mean at hp
  have hc : (Fintype.card (Position d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, coefficient w a ^ 2) =
      (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
    rw [div_eq_iff hc] at hp
    linarith
  simpa [bandEnergy] using hsum

@[simp] theorem bandEnergy_full (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w d = (∑ x, w x) ^ 2 := by
  classical
  simp [bandEnergy, prefixZero_full]

theorem bandEnergy_cons (d j : ℕ) (w : Position (d + 1) → ℝ) :
    bandEnergy (d + 1) w (j + 1) =
      ∑ a : Position d, if prefixZero j a then coefficient w (Fin.cons false a) ^ 2 else 0 := by
  classical
  unfold bandEnergy
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
    (fun a => if prefixZero (j + 1) a then coefficient w a ^ 2 else 0)]
  simp [Fintype.sum_prod_type, prefixZero_cons, Fin.consEquiv]

theorem mean_indicator {Ω : Type uΩ} [Fintype Ω] (p : Prop) [Decidable p] (f : Ω → ℝ) :
    mean (fun ω => if p then f ω else 0) = if p then mean f else 0 := by
  by_cases hp : p <;> simp [hp, mean_zero]

theorem mean_bandEnergy_physicalFlow (d j : ℕ) (hj : j ≤ d)
    (B : Position (d + 1) → Bool) (w : Position (d + 1) → ℝ)
    (hw : ∀ x, B x = false → w x = 0) :
    mean (fun c : Coins (d + 1) => bandEnergy (d + 1) (physicalFlow d B w c) j) =
      bandEnergy (d + 1) w (j + 1) + 2 ^ (d - j) * oneFreeEnergy d B w := by
  classical
  have hs (c : Coins (d + 1)) :
      bandEnergy (d + 1) (physicalFlow d B w c) j =
        (∑ a : Position d, if prefixZero j a then
          coefficient (physicalFlow d B w c) (Fin.snoc a true) ^ 2 else 0) +
        (∑ a : Position d, if prefixZero j a then
          coefficient w (Fin.cons false a) ^ 2 else 0) := by
    unfold bandEnergy
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool))
      (fun a => if prefixZero j a then coefficient (physicalFlow d B w c) a ^ 2 else 0)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.snocEquiv, Equiv.coe_fn_mk,
      prefixZero_snoc j d hj, coefficient_physicalFlow_even]
  simp_rw [hs]
  rw [mean_add, mean_sum, mean_const, bandEnergy_cons]
  simp_rw [mean_indicator, mean_coefficient_physicalFlow_odd_sq d B w hw]
  have hcount :
      (∑ a : Position d, if prefixZero j a then oneFreeEnergy d B w else 0) =
        2 ^ (d - j) * oneFreeEnergy d B w := by
    rw [← prefixZero_count j d hj, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hcount, add_comm]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FreshCoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_div_const {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    mean (fun ω => f ω / a) = mean f / a := by
  simpa only [div_eq_mul_inv] using mean_mul_const f a⁻¹

@[simp] theorem expectedBand_zero (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t 0 = expectedEnergy d v t := by
  unfold expectedBand expectedEnergy
  apply mean_congr
  intro ω
  rw [bandEnergy_zero]
  simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]

@[simp] theorem expectedBand_full (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t (d + 1) = 0 := by
  unfold expectedBand
  have hz (ω : History (d + 1) t) :
      bandEnergy (d + 1) (iterateState d v t ω).weight (d + 1) / 2 ^ (d + 1) = 0 := by
    rw [bandEnergy_full, (iterateState d v t ω).mass_zero]
    simp
  simp_rw [hz]
  exact mean_zero

theorem two_pow_ratio (d j : ℕ) (hj : j ≤ d) :
    (2 : ℝ) ^ (d - j) / 2 ^ (d + 1) = (1 / 2 : ℝ) ^ (j + 1) := by
  have hd : d + 1 = (d - j) + (j + 1) := by omega
  rw [hd, pow_add, div_mul_eq_div_div, div_self (by positivity), div_pow, one_pow]

theorem expectedBand_succ (d : ℕ) (v : CenteredState (d + 1)) (t j : ℕ)
    (hj : j < d + 1) :
    expectedBand d v (t + 1) j = expectedBand d v t (j + 1) +
      (1 / 2 : ℝ) ^ (j + 1) * expectedNoise d v t := by
  unfold expectedBand expectedNoise
  rw [mean_history_succ]
  have hstep (ω : History (d + 1) t) :
      mean (fun c : Coins (d + 1) =>
        bandEnergy (d + 1) (iterateState d v (t + 1) (Fin.snoc ω c)).weight j /
          2 ^ (d + 1)) =
      bandEnergy (d + 1) (iterateState d v t ω).weight (j + 1) / 2 ^ (d + 1) +
        (1 / 2 : ℝ) ^ (j + 1) *
          oneFreeEnergy d (iterateState d v t ω).free (iterateState d v t ω).weight := by
    simp only [iterateState, Fin.snoc_last, Fin.snoc_castSucc, nextState]
    rw [mean_div_const, mean_bandEnergy_physicalFlow d j (by omega)
      _ _ (iterateState d v t ω).supported, add_div]
    rw [← div_mul_eq_mul_div, two_pow_ratio d j (by omega)]
  simp_rw [hstep]
  rw [mean_add, mean_const_mul]

theorem expectedEnergy_recurrence (d : ℕ) (v : CenteredState (d + 1))
    (t : ℕ) (ht : d + 1 ≤ t) :
    expectedEnergy d v t = ∑ j ∈ Finset.range (d + 1),
      (1 / 2 : ℝ) ^ (j + 1) * expectedNoise d v (t - 1 - j) := by
  simpa only [expectedBand_zero] using
    energy_of_spectral_tracks (d + 1) (expectedBand d v) (expectedNoise d v)
      (expectedBand_succ d v) (expectedBand_full d v) t ht

end Conditional

namespace Conditional

theorem mean_product_bits {ι : Type uι} [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    mean (fun c : ι → Bool => ∏ i, f i (c i)) =
      ∏ i, (f i false + f i true) / 2 := by
  classical
  unfold mean
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, add_comm (f _ true)]
  rw [Finset.prod_div_distrib]
  simp [Fintype.card_pi, Fintype.card_bool]

theorem local_balance_factor (u v h : Bool) :
    mean (fun c : Bool => (5 / 4 : ℝ) ^ (u.toNat + v.toNat) *
      (4 / 5 : ℝ) ^ (4 * (if h ^^ c then v else u).toNat)) ≤
        (9 / 10 : ℝ) ^ (u.toNat + v.toNat) := by
  cases u <;> cases v <;> cases h <;> norm_num [mean, Fintype.sum_bool]

theorem balance_exponential_mean {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (h : Bool) :
    mean (fun c : α → Bool => (5 / 4 : ℝ) ^ pairFreeCount B *
      (4 / 5 : ℝ) ^ (4 * pairHalfCount B c h)) ≤
        (9 / 10 : ℝ) ^ pairFreeCount B := by
  classical
  have hprod (c : α → Bool) :
      (5 / 4 : ℝ) ^ pairFreeCount B * (4 / 5 : ℝ) ^ (4 * pairHalfCount B c h) =
      ∏ i, ((5 / 4 : ℝ) ^ ((B (false, i)).toNat + (B (true, i)).toNat) *
        (4 / 5 : ℝ) ^ (4 * (B (h ^^ c i, i)).toNat)) := by
    simp only [pairFreeCount, pairHalfCount, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum,
      Finset.prod_mul_distrib]
  simp_rw [hprod]
  rw [mean_product_bits (fun i (c : Bool) =>
    (5 / 4 : ℝ) ^ ((B (false, i)).toNat + (B (true, i)).toNat) *
        (4 / 5 : ℝ) ^ (4 * (B (h ^^ c, i)).toNat))]
  rw [pairFreeCount, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    have hlocal := local_balance_factor (B (false, i)) (B (true, i)) h
    have hbit (c : Bool) : B (h ^^ c, i) = if h ^^ c then B (true, i) else B (false, i) := by
      cases (h ^^ c) <;> rfl
    simp only [hbit]
    cases h <;> simpa [mean, Fintype.sum_bool, add_comm] using hlocal

theorem pair_half_balance {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) (h : Bool) :
    mean (fun c : α → Bool =>
      if 4 * pairHalfCount B c h < pairFreeCount B then (1 : ℝ) else 0) ≤
        (9 / 10 : ℝ) ^ pairFreeCount B := by
  apply le_trans (mean_le_mean (fun c => ?_)) (balance_exponential_mean B h)
  by_cases hc : 4 * pairHalfCount B c h < pairFreeCount B
  · rw [ite_eq_left hc]
    have hp : (5 / 4 : ℝ) ^ (4 * pairHalfCount B c h) ≤
        (5 / 4 : ℝ) ^ pairFreeCount B :=
      pow_le_pow_right₀ (by norm_num) hc.le
    have hr : (4 / 5 : ℝ) = (5 / 4 : ℝ)⁻¹ := by norm_num
    rw [hr, inv_pow, ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using hp)
  · rw [ite_eq_right hc]
    positivity

theorem pair_both_half_balance {α : Type uα} [Fintype α] [DecidableEq α]
    (B : Bool × α → Bool) :
    mean (fun c : α → Bool =>
      if (4 * pairHalfCount B c false < pairFreeCount B) ∨
        (4 * pairHalfCount B c true < pairFreeCount B) then (1 : ℝ) else 0) ≤
          2 * (9 / 10 : ℝ) ^ pairFreeCount B := by
  have hm : mean (fun c : α → Bool =>
      if (4 * pairHalfCount B c false < pairFreeCount B) ∨
        (4 * pairHalfCount B c true < pairFreeCount B) then (1 : ℝ) else 0) ≤
      mean (fun c : α → Bool =>
        (if 4 * pairHalfCount B c false < pairFreeCount B then (1 : ℝ) else 0) +
        (if 4 * pairHalfCount B c true < pairFreeCount B then (1 : ℝ) else 0)) := by
    apply mean_le_mean
    intro c
    split_ifs <;> norm_num at *
    all_goals omega
  rw [mean_add] at hm
  linarith [pair_half_balance B false, pair_half_balance B true]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_HalfHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem iterateState_raw (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) :
    (iterateState d v t ω).raw = rawIterate d v.raw t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change rawNext d (iterateState d v t (fun i => ω i.castSucc)).raw (ω (Fin.last t)) = _
    rw [ih]
    rfl

theorem rawIterate_free (d : ℕ) (v : RawState (d + 1)) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (rawIterate d v t ω).free x = v.free ((run (d + 1) t ω).symm x) := by
  induction t generalizing x with
  | zero => simp only [rawIterate, run_zero]; rfl
  | succ t ih =>
    change (rawIterate d v t (fun i => ω i.castSucc)).free
      ((step (d + 1) (ω (Fin.last t))).symm x) = _
    rw [ih, run_succ]
    rfl

theorem mean_bool (f : Bool → ℝ) : mean f = (f false + f true) / 2 := by
  simp [mean, add_comm]

theorem pairUpdate_mean_fst (u v : Bool) (a b : ℝ) :
    mean (fun c : Bool => (pairUpdate u v a b c).1) = (a + b) / 2 := by
  cases u <;> cases v <;> simp [mean_bool, pairUpdate]

theorem pairUpdate_mean_snd (u v : Bool) (a b : ℝ) :
    mean (fun c : Bool => (pairUpdate u v a b c).2) = (a + b) / 2 := by
  cases u <;> cases v <;> simp [mean_bool, pairUpdate]
  all_goals ring

theorem mean_sign {α : Type uα} [Fintype α] [DecidableEq α] (i : α) :
    mean (fun c : α → Bool => sign (c i)) = 0 := by
  simp [mean, sum_sign]

theorem mean_coin_eval {α : Type uα} [Fintype α] [DecidableEq α]
    (i : α) (f : Bool → ℝ) : mean (fun c : α → Bool => f (c i)) = mean f := by
  have hfun (b : Bool) : f b = (f false + f true) / 2 +
      sign b * ((f false - f true) / 2) := by
    cases b <;> simp [sign] <;> ring
  calc
    _ = mean (fun c : α → Bool => (f false + f true) / 2 +
        sign (c i) * ((f false - f true) / 2)) := mean_congr (fun c => hfun (c i))
    _ = mean f := by
      rw [mean_add, mean_const, mean_mul_const]
      simp only [mean_sign, zero_mul, add_zero, mean_bool]

theorem mean_physicalFlow_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (x : Position d) (b : Bool) :
    mean (fun c : Coins (d + 1) => physicalFlow d B w c (Fin.snoc x b)) =
      (w (Fin.cons false x) + w (Fin.cons true x)) / 2 := by
  rw [← scatterPosition_eq_snoc]
  simp only [physicalFlow_scatter]
  cases b
  · change mean (fun c : Position d → Bool =>
      (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1) = _
    rw [mean_coin_eval x (fun c => (pairUpdate (B (Fin.cons false x))
      (B (Fin.cons true x)) (w (Fin.cons false x)) (w (Fin.cons true x)) c).1),
      pairUpdate_mean_fst]
  · change mean (fun c : Position d → Bool =>
      (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2) = _
    rw [mean_coin_eval x (fun c => (pairUpdate (B (Fin.cons false x))
      (B (Fin.cons true x)) (w (Fin.cons false x)) (w (Fin.cons true x)) c).2),
      pairUpdate_mean_snd]

end Conditional

namespace Conditional

theorem mean_physicalFlow (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (x : Position (d + 1)) :
    mean (fun c : Coins (d + 1) => physicalFlow d B w c x) =
      meanLayer (d + 1) w x := by
  conv_lhs => rw [← Fin.snoc_init_self x]
  rw [mean_physicalFlow_snoc]
  change _ = mean (fun b : Bool => w (Fin.cons b (Fin.init x)))
  exact (mean_bool (fun b : Bool => w (Fin.cons b (Fin.init x)))).symm

theorem init_cons (d : ℕ) (b : Bool) (x : Position (d + 1)) :
    (Fin.init (Fin.cons b x : Position (d + 2)) : Position (d + 1)) =
      (Fin.cons b (Fin.init x) : Position (d + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem meanLayer_lift (d : ℕ) (w : Position d → ℝ) :
    meanLayer (d + 1) (fun x => w (Fin.init x)) =
      fun x => meanLayer d w (Fin.init x) := by
  funext x
  cases d with
  | zero =>
    have hall (b : Bool) : Fin.init (Fin.cons b (Fin.init x) : Position 1) = Fin.init x :=
      Subsingleton.elim _ _
    simp only [meanLayer, firstMean, hall, mean_const]
  | succ d =>
    simp only [meanLayer, firstMean, init_cons]

theorem mean_iterations_dimension (d t : ℕ) (w : Position (d + 1) → ℝ)
    (x : Position (d + 1)) :
    (meanLayer (d + 1))^[t + 1] w x =
      (meanLayer d)^[t] (firstMean d w) (Fin.init x) := by
  have hs : Function.Semiconj (fun w : Position d → ℝ => fun x : Position (d + 1) => w (Fin.init x))
      (meanLayer d) (meanLayer (d + 1)) := fun w => (meanLayer_lift d w).symm
  rw [Function.iterate_succ_apply]
  exact (congrFun (hs.iterate_right t (firstMean d w)) x).symm

theorem mean_firstMean (d : ℕ) (w : Position (d + 1) → ℝ) :
    mean (firstMean d w) = mean w := by
  have h := mean_equiv (splitPosition d).symm w
  rw [mean_prod] at h
  rw [← h, mean_comm]
  rfl

theorem mean_iterations_sweep (d : ℕ) (w : Position d → ℝ) (x : Position d) :
    (meanLayer d)^[d] w x = mean w := by
  induction d with
  | zero =>
    change w x = mean w
    have hw : w = fun _ => w x := funext (fun y => congrArg w (Subsingleton.elim y x))
    rw [hw, mean_const]
  | succ d ih =>
    rw [mean_iterations_dimension, ih, mean_firstMean]

theorem mean_rawIterate_weight (d : ℕ) (v : RawState (d + 1)) (t : ℕ)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) t => (rawIterate d v t ω).weight x) =
      (meanLayer (d + 1))^[t] v.weight x := by
  induction t generalizing x with
  | zero => simp [rawIterate, mean_const]
  | succ t ih =>
    rw [mean_history_succ]
    have hi (ω : History (d + 1) t) :
        mean (fun c : Coins (d + 1) =>
          (rawIterate d v (t + 1) (Fin.snoc ω c)).weight x) =
            meanLayer (d + 1) (rawIterate d v t ω).weight x := by
      simp only [rawIterate, Fin.snoc_castSucc, Fin.snoc_last, rawNext]
      exact mean_physicalFlow _ _ _ _
    simp_rw [hi]
    change mean (fun ω : History (d + 1) t =>
      mean (fun b : Bool => (rawIterate d v t ω).weight (Fin.cons b (Fin.init x)))) = _
    rw [mean_comm]
    simp_rw [ih]
    rw [Function.iterate_succ_apply']
    rfl

theorem mean_rawIterate_sweep (d : ℕ) (v : RawState (d + 1))
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) => (rawIterate d v (d + 1) ω).weight x) =
      mean v.weight := by
  rw [mean_rawIterate_weight, mean_iterations_sweep]

theorem rawIterate_indicator (d : ℕ) (B : Position (d + 1) → Bool) (t : ℕ)
    (ω : History (d + 1) t) (x : Position (d + 1)) :
    (rawIterate d ⟨B, fun y => if B y then 1 else 0⟩ t ω).weight x =
      if (rawIterate d ⟨B, fun y => if B y then 1 else 0⟩ t ω).free x then 1 else 0 := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    change physicalFlow d _ (rawIterate d _ t (fun i => ω i.castSucc)).weight
      (ω (Fin.last t)) x = _
    rw [funext (ih (fun i => ω i.castSucc))]
    exact physicalFlow_uniform _ _ _ _ _

theorem mean_free_after_sweep (d : ℕ) (B : Position (d + 1) → Bool)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) =>
      if B ((run (d + 1) (d + 1) ω).symm x) then (1 : ℝ) else 0) =
        (freeCount B : ℝ) / Fintype.card (Position (d + 1)) := by
  let v : RawState (d + 1) := ⟨B, fun y => if B y then 1 else 0⟩
  have h (ω : History (d + 1) (d + 1)) :
      (if B ((run (d + 1) (d + 1) ω).symm x) then (1 : ℝ) else 0) =
        (rawIterate d v (d + 1) ω).weight x := by
    rw [rawIterate_indicator, rawIterate_free]
  simp_rw [h]
  rw [mean_rawIterate_sweep]
  change (∑ y, if B y then (1 : ℝ) else 0) / _ = _
  rw [sum_free_indicator]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_NoiseEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

 theorem insertBit_cons (d : ℕ) (k : Fin (d + 1)) (h b : Bool) (x : Position d) :
    insertBit (d + 1) k.succ h (Fin.cons b x) = Fin.cons b (insertBit d k h x) := by
  change Fin.insertNth (α := fun _ => Bool) k.succ h (Fin.cons b x) = _
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [insertBit]
  · change Fin.cons b x = Fin.cons b (insertBit d k h x) ∘ k.succ.succAbove
    erw [Fin.cons_comp_succ_succAbove]
    simp [insertBit]

 theorem insertBit_snoc (d : ℕ) (k : Fin (d + 1)) (h b : Bool) (x : Position d) :
    insertBit (d + 1) k.castSucc h (Fin.snoc x b) = Fin.snoc (insertBit d k h x) b := by
  change Fin.insertNth (α := fun _ => Bool) k.castSucc h (Fin.snoc x b) = _
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [insertBit]
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Fin.removeNth, Fin.succAbove_ne_last_last, insertBit]
    · simp [Fin.removeNth, Fin.castSucc_succAbove_castSucc, insertBit]

 theorem physicalFree_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Position d → Bool) (x : Position d) (b : Bool) :
    physicalFree d B c (Fin.snoc x b) = B (Fin.cons (b ^^ c x) x) := by
  erw [← scatterPosition_eq_snoc, physicalFree_scatter]
  rfl

 theorem physicalFlow_snoc (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Position d → Bool) (x : Position d) (b : Bool) :
    physicalFlow d B w c (Fin.snoc x b) =
      if b then (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2
      else (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
        (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1 := by
  erw [← scatterPosition_eq_snoc, physicalFlow_scatter]
  rfl

theorem rawNext_half (d : ℕ) (k : Fin (d + 1)) (h : Bool)
    (v : RawState (d + 2)) (c : Position (d + 1) → Bool) :
    halfRaw (d + 1) k.castSucc h (rawNext (d + 1) v c) =
      rawNext d (halfRaw (d + 1) k.succ h v) (fun x => c (insertBit d k h x)) := by
  apply RawState.ext
  · funext x
    obtain ⟨⟨b, y⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool)).surjective x
    change physicalFree (d + 1) v.free c (insertBit (d + 1) k.castSucc h (Fin.snoc y b)) =
      physicalFree d (fun z => v.free (insertBit (d + 1) k.succ h z))
        (fun z => c (insertBit d k h z)) (Fin.snoc y b)
    erw [insertBit_snoc, physicalFree_snoc, physicalFree_snoc, insertBit_cons]
  · funext x
    obtain ⟨⟨b, y⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool)).surjective x
    change physicalFlow (d + 1) v.free v.weight c
      (insertBit (d + 1) k.castSucc h (Fin.snoc y b)) =
      physicalFlow d (fun z => v.free (insertBit (d + 1) k.succ h z))
        (fun z => v.weight (insertBit (d + 1) k.succ h z))
        (fun z => c (insertBit d k h z)) (Fin.snoc y b)
    erw [insertBit_snoc, physicalFlow_snoc, physicalFlow_snoc]
    simp only [insertBit_cons]

end Conditional

namespace Conditional

theorem halfMarker_next (d t : ℕ) (ht : t ≤ d) :
    halfMarker d (t + 1) = (coinHalfMarker d t).castSucc := by
  apply Fin.ext; simp only [halfMarker, coinHalfMarker, Fin.val_castSucc]; omega

theorem halfMarker_previous (d t : ℕ) (ht : t ≤ d) :
    halfMarker d t = (coinHalfMarker d t).succ := by
  apply Fin.ext; simp only [halfMarker, coinHalfMarker, Fin.val_succ]; omega

theorem rawIterate_half (d t : ℕ) (ht : t ≤ d + 1) (h : Bool)
    (v : RawState (d + 2)) (ω : History (d + 2) t) :
    halfRaw (d + 1) (halfMarker d t) h (rawIterate (d + 1) v t ω) =
      rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) t (halfHistory d t h ω) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change halfRaw (d + 1) (halfMarker d (t + 1)) h
      (rawNext (d + 1) (rawIterate (d + 1) v t (fun i => ω i.castSucc)) (ω (Fin.last t))) = _
    erw [halfMarker_next d t (by omega), rawNext_half,
      ← halfMarker_previous d t (by omega), ih (by omega)]
    rfl

theorem mean_half_product (d t : ℕ) (f g : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t false ω) *
      g (halfHistory d t true ω)) = mean f * mean g := by
  have he := mean_equiv (splitHalfHistory d t) (fun p => f p.1 * g p.2)
  change mean (fun ω : History (d + 2) t => f (halfHistory d t false ω) *
      g (halfHistory d t true ω)) = _ at he
  erw [he, mean_prod]
  simp_rw [mean_const_mul]
  exact mean_mul_const _ _

theorem mean_opposite_half_product (d t : ℕ) (h : Bool)
    (f g : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t h ω) *
      g (halfHistory d t (!h) ω)) = mean f * mean g := by
  cases h
  · exact mean_half_product d t f g
  · simp only [Bool.not_true]
    simpa only [mul_comm] using mean_half_product d t g f

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_EnergyDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_rawFree_sweep (d : ℕ) (v : RawState (d + 1)) (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) =>
      if (rawIterate d v (d + 1) ω).free x then (1 : ℝ) else 0) =
        (freeCount v.free : ℝ) / Fintype.card (Position (d + 1)) := by
  simp only [rawIterate_free]
  exact mean_free_after_sweep d v.free x

theorem rawIterate_half_weight (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (ω : History (d + 2) (d + 1)) (x : Position (d + 1)) :
    (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) =
      (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1)
        (halfHistory d (d + 1) h ω)).weight x := by
  have hz := congrArg (fun u : RawState (d + 1) => u.weight x)
    (rawIterate_half d (d + 1) le_rfl h v ω)
  simpa only [halfMarker_end, halfRaw, insertBit_zero] using hz

theorem rawIterate_half_free (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (ω : History (d + 2) (d + 1)) (x : Position (d + 1)) :
    (rawIterate (d + 1) v (d + 1) ω).free (Fin.cons h x) =
      (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1)
        (halfHistory d (d + 1) h ω)).free x := by
  have hz := congrArg (fun u : RawState (d + 1) => u.free x)
    (rawIterate_half d (d + 1) le_rfl h v ω)
  simpa only [halfMarker_end, halfRaw, insertBit_zero] using hz

theorem mean_half_single (d t : ℕ) (h : Bool) (f : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t h ω)) = mean f := by
  simpa only [mean_const, mul_one] using
    mean_opposite_half_product d t h f (fun _ => (1 : ℝ))

theorem mean_half_factorization (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 2) (d + 1) =>
      (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) ^ 2 *
        (if (rawIterate (d + 1) v (d + 1) ω).free (Fin.cons (!h) x) then (1 : ℝ) else 0)) =
      ((freeCount (halfRaw (d + 1) (Fin.last (d + 1)) (!h) v).free : ℝ) /
        Fintype.card (Position (d + 1))) *
      mean (fun ω : History (d + 2) (d + 1) =>
        (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) ^ 2) := by
  simp_rw [rawIterate_half_weight, rawIterate_half_free]
  rw [mean_opposite_half_product d (d + 1) h
    (fun ω => (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1) ω).weight x ^ 2)
    (fun ω => if (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) (!h) v)
      (d + 1) ω).free x then (1 : ℝ) else 0)]
  rw [mean_rawFree_sweep, mean_half_single d (d + 1) h
    (fun ω => (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1) ω).weight x ^ 2),
    mul_comm]

 theorem halfEnergy_nonneg (d : ℕ) (v : RawState (d + 1)) (h : Bool) :
    0 ≤ halfEnergy d v h := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

 theorem rawEnergy_halves (d : ℕ) (v : RawState (d + 1)) :
    rawEnergy v = halfEnergy d v false + halfEnergy d v true := by
  unfold rawEnergy halfEnergy
  have he := Equiv.sum_comp (splitPosition d).symm (fun x => v.weight x ^ 2)
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

 theorem oneFreeEnergy_partner (d : ℕ) (v : RawState (d + 1)) :
    oneFreeEnergy d v.free v.weight + partnerEnergy d v false + partnerEnergy d v true =
      rawEnergy v := by
  rw [rawEnergy_halves]
  unfold oneFreeEnergy partnerEnergy halfEnergy
  simp only [Bool.not_false, Bool.not_true, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases v.free (Fin.cons false x) <;> cases v.free (Fin.cons true x) <;> simp [add_comm]

 theorem mean_half_energy_factorization (d : ℕ) (v : RawState (d + 2)) (h : Bool) :
    mean (fun ω : History (d + 2) (d + 1) =>
      partnerEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω) h) =
      startHalfDensity (d + 1) v (!h) *
        mean (fun ω : History (d + 2) (d + 1) =>
          halfEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω) h) := by
  unfold partnerEnergy halfEnergy startHalfDensity
  rw [mean_sum, mean_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact mean_half_factorization d v h x

theorem noise_bound_balanced_halves (d : ℕ) (v : RawState (d + 2))
    (β : ℝ) (hb : ∀ h, β ≤ startHalfDensity (d + 1) v h) :
    mean (fun ω : History (d + 2) (d + 1) =>
      oneFreeEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω).free
        (rawIterate (d + 1) v (d + 1) ω).weight) ≤
      (1 - β) * mean (fun ω : History (d + 2) (d + 1) =>
        rawEnergy (rawIterate (d + 1) v (d + 1) ω)) := by
  have hid := mean_congr (fun ω : History (d + 2) (d + 1) =>
    oneFreeEnergy_partner (d + 1) (rawIterate (d + 1) v (d + 1) ω))
  rw [mean_add, mean_add, mean_half_energy_factorization,
    mean_half_energy_factorization] at hid
  have he := mean_congr (fun ω : History (d + 2) (d + 1) =>
    rawEnergy_halves (d + 1) (rawIterate (d + 1) v (d + 1) ω))
  rw [mean_add] at he
  have hfalse := mul_le_mul_of_nonneg_right (hb true)
    (mean_nonneg (fun ω : History (d + 2) (d + 1) =>
      halfEnergy_nonneg (d + 1) (rawIterate (d + 1) v (d + 1) ω) false))
  have htrue := mul_le_mul_of_nonneg_right (hb false)
    (mean_nonneg (fun ω : History (d + 2) (d + 1) =>
      halfEnergy_nonneg (d + 1) (rawIterate (d + 1) v (d + 1) ω) true))
  simp only [Bool.not_false, Bool.not_true] at hid
  rw [he] at hid ⊢
  nlinarith

end Conditional

namespace Conditional

theorem mean_history_add (d s t : ℕ) (f : History d (s + t) → ℝ) :
    mean f = mean (fun a : History d s =>
      mean (fun b : History d t => f (Fin.append a b))) := by
  have he := mean_equiv (splitHistory d s t).symm f
  rw [mean_prod] at he
  exact he.symm

theorem iterateState_append (d s t : ℕ) (v : CenteredState (d + 1))
    (a : History (d + 1) s) (b : History (d + 1) t) :
    iterateState d v (s + t) (Fin.append a b) = iterateState d (iterateState d v s a) t b := by
  induction t with
  | zero =>
    have hz : Fin.append a b = a := by funext i; exact Fin.append_left a b i
    rw [hz]; rfl
  | succ t ih =>
    obtain ⟨⟨c, b⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins (d + 1))).surjective b
    erw [Fin.append_snoc, iterateState_snoc, iterateState_snoc, ih]

theorem expectedEnergy_add (d s t : ℕ) (v : CenteredState (d + 1)) :
    expectedEnergy d v (s + t) = mean (fun a : History (d + 1) s =>
      expectedEnergy d (iterateState d v s a) t) := by
  unfold expectedEnergy
  rw [mean_history_add]
  simp_rw [iterateState_append]

theorem expectedNoise_add (d s t : ℕ) (v : CenteredState (d + 1)) :
    expectedNoise d v (s + t) = mean (fun a : History (d + 1) s =>
      expectedNoise d (iterateState d v s a) t) := by
  unfold expectedNoise
  rw [mean_history_add]
  simp_rw [iterateState_append]

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MarginalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem freeCount_eq_sum {α : Type uα} [Fintype α] (B : α → Bool) :
    freeCount B = ∑ x, (B x).toNat := by
  classical
  calc
    freeCount B = ∑ x, if B x = true then (1 : ℕ) else 0 := (Finset.sum_boole _ _).symm
    _ = _ := Finset.sum_congr rfl (fun x _ => by cases B x <;> rfl)

theorem pairFreeCount_physical (d : ℕ) (B : Position (d + 1) → Bool) :
    pairFreeCount (B ∘ (splitPosition d).symm) = freeCount B := by
  rw [freeCount_eq_sum]
  have he := Equiv.sum_comp (splitPosition d).symm (fun x => (B x).toNat)
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [pairFreeCount, Function.comp_apply, Finset.sum_add_distrib]
  exact Nat.add_comm _ _

theorem halfCount_after_step (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool) :
    freeCount (halfRaw d (Fin.last d) h (rawNext d v c)).free =
      pairHalfCount (v.free ∘ (splitPosition d).symm) c h := by
  rw [freeCount_eq_sum]
  unfold halfRaw rawNext pairHalfCount
  simp only [insertBit_last]
  apply Finset.sum_congr rfl
  intro x _
  erw [physicalFree_snoc]
  rfl

theorem halfDensity_after_step (d : ℕ) (v : RawState (d + 1))
    (c : Coins (d + 1)) (h : Bool)
    (hm : Fintype.card (Position (d + 1)) ≤ 8 * freeCount v.free)
    (hc : freeCount v.free ≤ 4 * pairHalfCount (v.free ∘ (splitPosition d).symm) c h) :
    (1 / 16 : ℝ) ≤ startHalfDensity d (rawNext d v c) h := by
  unfold startHalfDensity
  rw [halfCount_after_step]
  have hn : Fintype.card (Position (d + 1)) = 2 * Fintype.card (Position d) := by
    simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
  rw [hn] at hm
  have hm' : (2 : ℝ) * Fintype.card (Position d) ≤ 8 * (freeCount v.free : ℝ) := by
    exact_mod_cast hm
  have hc' : (freeCount v.free : ℝ) ≤
      4 * (pairHalfCount (v.free ∘ (splitPosition d).symm) c h : ℝ) := by exact_mod_cast hc
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := Position d))).mpr
  nlinarith

theorem partnerEnergy_nonneg (d : ℕ) (v : RawState (d + 1)) (h : Bool) :
    0 ≤ partnerEnergy d v h := by
  unfold partnerEnergy
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num))

theorem oneFreeEnergy_le (d : ℕ) (v : RawState (d + 1)) :
    oneFreeEnergy d v.free v.weight ≤ rawEnergy v := by
  have hid := oneFreeEnergy_partner d v
  linarith [partnerEnergy_nonneg d v false, partnerEnergy_nonneg d v true]

theorem expectedNoise_le_energy (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedNoise d v t ≤ expectedEnergy d v t := by
  apply mean_le_mean
  intro ω
  exact oneFreeEnergy_le d (iterateState d v t ω).raw

theorem noise_bound_balanced_state (d : ℕ) (v : CenteredState (d + 2))
    (β : ℝ) (hb : ∀ h, β ≤ startHalfDensity (d + 1) v.raw h) :
    expectedNoise (d + 1) v (d + 1) ≤ (1 - β) * expectedEnergy (d + 1) v (d + 1) := by
  have he := noise_bound_balanced_halves d v.raw β hb
  simp_rw [← iterateState_raw] at he
  exact he

theorem mean_history_one (d : ℕ) (f : History d 1 → ℝ) :
    mean f = mean (fun c : Coins d => f (fun _ => c)) :=
  (mean_equiv (singleHistory d) f).symm

theorem expectedEnergy_first (d t : ℕ) (v : CenteredState (d + 1)) :
    expectedEnergy d v (t + 1) =
      mean (fun c : Coins (d + 1) => expectedEnergy d (nextState d v c) t) := by
  rw [Nat.add_comm t 1, expectedEnergy_add, mean_history_one]
  rfl

theorem expectedNoise_first (d t : ℕ) (v : CenteredState (d + 1)) :
    expectedNoise d v (t + 1) =
      mean (fun c : Coins (d + 1) => expectedNoise d (nextState d v c) t) := by
  rw [Nat.add_comm t 1, expectedNoise_add, mean_history_one]
  rfl

theorem expectedNoise_dimension (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) :
    expectedNoise (d + 1) v (d + 2) ≤ (15 / 16 : ℝ) * expectedEnergy (d + 1) v (d + 2) +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  let B := v.free ∘ (splitPosition (d + 1)).symm
  let bad (c : Coins (d + 2)) : Prop :=
    4 * pairHalfCount B c false < pairFreeCount B ∨
    4 * pairHalfCount B c true < pairFreeCount B
  have hlocal (c : Coins (d + 2)) :
      expectedNoise (d + 1) (nextState (d + 1) v c) (d + 1) ≤
      (15 / 16 : ℝ) * expectedEnergy (d + 1) (nextState (d + 1) v c) (d + 1) +
        (if bad c then 1 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hle := expectedNoise_le_energy (d + 1) (nextState (d + 1) v c) (d + 1)
      have hone := expectedEnergy_le_one (d + 1) (nextState (d + 1) v c) (d + 1)
      linarith
    · rw [ite_eq_right hc, add_zero]
      have hb (h : Bool) : (1 / 16 : ℝ) ≤
          startHalfDensity (d + 1) (nextState (d + 1) v c).raw h := by
        apply halfDensity_after_step (d + 1) v.raw c h hm
        have hf : ¬ 4 * pairHalfCount B c false < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.1
        have ht : ¬ 4 * pairHalfCount B c true < freeCount v.free := by
          simpa only [B, pairFreeCount_physical] using not_or.mp hc |>.2
        change freeCount v.free ≤ 4 * pairHalfCount B c h
        cases h
        · exact Nat.le_of_not_gt hf
        · exact Nat.le_of_not_gt ht
      convert noise_bound_balanced_state d (nextState (d + 1) v c) (1 / 16) hb using 1; norm_num
  have hmean := mean_le_mean hlocal
  rw [mean_add, mean_const_mul, ← expectedNoise_first, ← expectedEnergy_first] at hmean
  have hbad := pair_both_half_balance B
  have hbad' : mean (fun c : Coins (d + 2) => if bad c then (1 : ℝ) else 0) ≤
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
    change mean (fun c : Position (d + 1) → Bool => if bad c then (1 : ℝ) else 0) ≤ _
    simpa only [bad, B, pairFreeCount_physical] using hbad
  exact hmean.trans (add_le_add (le_refl _) hbad')

theorem expectedNoise_bound (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free)
    (s : ℕ) (hs : d + 2 ≤ s) :
    expectedNoise (d + 1) v s ≤ (15 / 16 : ℝ) * expectedEnergy (d + 1) v s +
      2 * (9 / 10 : ℝ) ^ freeCount v.free := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [Nat.add_comm (d + 2) a, expectedNoise_add, expectedEnergy_add]
  have he := mean_le_mean (fun ω : History (d + 2) a =>
    expectedNoise_dimension d (iterateState (d + 1) v a ω)
      (by simpa only [iterateState_freeCount] using hm))
  simpa only [iterateState_freeCount, mean_add, mean_const_mul, mean_const] using he

end Conditional

namespace Conditional

theorem expectedEnergy_decay (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) (t : ℕ) :
    expectedEnergy (d + 1) v t ≤
      (31 / 32 : ℝ) ^ t / (31 / 32 : ℝ) ^ (2 * (d + 2)) +
        32 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := scalar_decay (d + 2) (expectedEnergy (d + 1) v)
    (expectedNoise (d + 1) v) (1 / 16) (31 / 32)
    (2 * (9 / 10 : ℝ) ^ freeCount v.free)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) (expectedEnergy_le_one (d + 1) v)
    (expectedEnergy_recurrence (d + 1) v)
    (by intro s hs; convert expectedNoise_bound d v hm s hs using 1; norm_num) t
  convert he using 1 <;> first | rfl | ring

theorem expectedEnergy_200 (d : ℕ) (v : CenteredState (d + 2))
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount v.free) :
    expectedEnergy (d + 1) v (200 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ freeCount v.free := by
  have he := expectedEnergy_decay d v hm (200 * (d + 2))
  have hp : (31 / 32 : ℝ) ^ (200 * (d + 2)) / (31 / 32 : ℝ) ^ (2 * (d + 2)) =
      (31 / 32 : ℝ) ^ (198 * (d + 2)) := by
    have hn : 200 * (d + 2) = 198 * (d + 2) + 2 * (d + 2) := by omega
    rw [hn, pow_add, mul_div_cancel_right₀ _ (by positivity)]
  rw [hp] at he
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (31 / 32) ^ 198)
    eight_block_geometric_choice (d + 2)
  rw [← pow_mul, ← pow_mul] at hpow
  exact he.trans (add_le_add hpow (le_refl _))

theorem centeredPoint_energy_200 (d : ℕ) (B : Position (d + 2) → Bool)
    (tag : Position (d + 2)) (ht : B tag = true)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * freeCount B) :
    expectedEnergy (d + 1) (initialState (d + 2) B tag ht) (200 * (d + 2)) ≤
      (1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ freeCount B :=
  expectedEnergy_200 d _ hm

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MaskedResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_maskedCoin {α : Type uα} [Fintype α] [DecidableEq α]
    (mask : α → Bool) (f : (α → Bool) → ℝ) :
    mean (fun c : α → Bool => mean (fun r : α → Bool => f (maskedCoin mask c r))) =
      mean f := by
  have he := mean_equiv (maskSwap mask) (fun p => f p.1)
  change mean (fun p : (α → Bool) × (α → Bool) => f (maskedCoin mask p.1 p.2)) = _ at he
  rw [mean_prod, mean_prod] at he
  simpa only [mean_const] using he

theorem step_cons (d : ℕ) (c : Position d → Bool) (b : Bool) (x : Position d) :
    step (d + 1) c (Fin.cons b x) = scatterPosition d (b ^^ c x, x) := by
  simp [step, scatterPosition, splitPosition, pairSwitch]

theorem masked_step_occupied (d : ℕ) (B : Position (d + 1) → Bool)
    (c r : Position d → Bool) (x : Position (d + 1)) (hx : B x = false) :
    step (d + 1) (maskedCoin (freePairMask d B) c r) x = step (d + 1) c x := by
  obtain ⟨⟨b, y⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change B (Fin.cons b y) = false at hx
  change step (d + 1) (maskedCoin (freePairMask d B) c r) (Fin.cons b y) =
    step (d + 1) c (Fin.cons b y)
  rw [step_cons, step_cons]
  cases b <;> simp [maskedCoin, freePairMask, hx]

theorem physicalFlow_resampling (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Position d → Bool) (y : Position (d + 1)) :
    physicalFlow d B w c y = mean (fun r : Position d → Bool =>
      w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y)) := by
  obtain ⟨⟨b, x⟩, rfl⟩ := (scatterPosition d).surjective y
  have hs : mean (fun r : Position d → Bool =>
      w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm
        (scatterPosition d (b, x)))) =
      mean (fun r : Position d → Bool =>
        w (Fin.cons (b ^^ maskedCoin (freePairMask d B) c r x) x)) := by
    apply mean_congr
    intro r
    exact congrArg w (step_symm_scatter d (maskedCoin (freePairMask d B) c r) (b, x))
  rw [hs]
  erw [physicalFlow_scatter]
  change (if b then (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).2
    else (pairUpdate (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)).1) =
    mean (fun r : Position d → Bool =>
      w (Fin.cons (b ^^ (if freePairMask d B x then r x else c x)) x))
  rw [mean_coin_eval x (fun z => w (Fin.cons (b ^^ (if freePairMask d B x then z else c x)) x))]
  cases h0 : B (Fin.cons false x) <;> cases h1 : B (Fin.cons true x) <;>
    cases b <;> cases c x <;>
    simp [pairUpdate, freePairMask, h0, h1, mean_bool] <;> ring

theorem masked_step_exposed {ι : Type uι} (d : ℕ) (B : Position (d + 1) → Bool)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false) (c r : Position d → Bool) :
    (step (d + 1) (maskedCoin (freePairMask d B) c r)) ∘ e = (step (d + 1) c) ∘ e := by
  funext i
  exact masked_step_occupied d B c r (e i) (he i)

theorem physicalFlow_joint {ι : Type uι} (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (e : ι → Position (d + 1))
    (he : ∀ i, B (e i) = false) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun c : Position d → Bool => ∑ y, physicalFlow d B w c y * f ((step (d + 1) c) ∘ e) y) =
      mean (fun c : Position d → Bool => ∑ x, w x * f ((step (d + 1) c) ∘ e) (step (d + 1) c x)) := by
  calc
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ y, w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y) *
          f ((step (d + 1) c) ∘ e) y)) := by
      apply mean_congr
      intro c
      rw [mean_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [mean_mul_const, physicalFlow_resampling]
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, w x * f ((step (d + 1) c) ∘ e)
          (step (d + 1) (maskedCoin (freePairMask d B) c r) x))) := by
      apply mean_congr
      intro c
      apply mean_congr
      intro r
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp (step (d + 1) (maskedCoin (freePairMask d B) c r))
          (fun y => w ((step (d + 1) (maskedCoin (freePairMask d B) c r)).symm y) *
            f ((step (d + 1) c) ∘ e) y)).symm
    _ = mean (fun c : Position d → Bool => mean (fun r : Position d → Bool =>
        ∑ x, w x * f ((step (d + 1) (maskedCoin (freePairMask d B) c r)) ∘ e)
          (step (d + 1) (maskedCoin (freePairMask d B) c r) x))) := by
      apply mean_congr
      intro c
      apply mean_congr
      intro r
      rw [masked_step_exposed d B e he c r]
    _ = _ := by
      exact mean_maskedCoin (freePairMask d B) (fun c => ∑ x, w x *
        f ((step (d + 1) c) ∘ e) (step (d + 1) c x))

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ConditionalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem flow_joint_identity {ι : Type uι} (d : ℕ) (v : RawState (d + 1))
    (e : ι → Position (d + 1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      ∑ x, v.weight x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (rawIterate d v t ω).weight y * f ((run (d + 1) t ω) ∘ e) y) := by
  induction t generalizing f with
  | zero => simp only [run_zero, rawIterate]; rfl
  | succ t ih =>
    let F (e' : ι → Position (d + 1)) (x : Position (d + 1)) : ℝ :=
      mean (fun c : Coins (d + 1) => f ((step (d + 1) c) ∘ e') (step (d + 1) c x))
    have hleft :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ x, v.weight x * f ((run (d + 1) (t + 1) ω) ∘ e) (run (d + 1) (t + 1) ω x)) =
        mean (fun ω : History (d + 1) t =>
          ∑ x, v.weight x * F ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [run_snoc]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      rfl
    have hright :
        mean (fun ω : History (d + 1) (t + 1) =>
          ∑ y, (rawIterate d v (t + 1) ω).weight y * f ((run (d + 1) (t + 1) ω) ∘ e) y) =
        mean (fun ω : History (d + 1) t =>
          ∑ y, (rawIterate d v t ω).weight y * F ((run (d + 1) t ω) ∘ e) y) := by
      rw [mean_history_succ]
      apply mean_congr
      intro ω
      simp only [run_snoc, rawIterate_snoc]
      change mean (fun c : Position d → Bool =>
        ∑ y, physicalFlow d (rawIterate d v t ω).free (rawIterate d v t ω).weight c y *
          f ((step (d + 1) c) ∘ ((run (d + 1) t ω) ∘ e)) y) = _
      rw [physicalFlow_joint d (rawIterate d v t ω).free (rawIterate d v t ω).weight
        ((run (d + 1) t ω) ∘ e) (by
          intro i
          simp only [Function.comp_apply, rawIterate_free, Equiv.symm_apply_apply]
          exact he i)]
      rw [mean_sum]
      simp_rw [mean_const_mul]
      rfl
    exact hleft.trans ((ih F).trans hright.symm)

theorem centered_joint_identity {ι : Type uι} (d : ℕ) (v : CenteredState (d + 1))
    (e : ι → Position (d + 1)) (he : ∀ i, v.free (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      ∑ x, v.weight x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (iterateState d v t ω).weight y * f ((run (d + 1) t ω) ∘ e) y) := by
  have hh := flow_joint_identity d v.raw e he t f
  simp_rw [← iterateState_raw] at hh
  exact hh

theorem centeredPoint_test {α : Type uα} [Fintype α] [DecidableEq α]
    (B : α → Bool) (tag : α) (f : α → ℝ) :
    (∑ x, centeredPoint B tag x * f x) =
      f tag - (1 / (freeCount B : ℝ)) * (∑ x, if B x then f x else 0) := by
  simp only [centeredPoint, sub_mul, mul_assoc, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ite_mul, one_mul, zero_mul]
  simp

theorem tagged_deviation_identity {ι : Type uι} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ) :
    mean (fun ω : History (d + 1) t =>
      f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0)) =
    mean (fun ω : History (d + 1) t =>
      ∑ y, (iterateState d (initialState (d + 1) B tag ht) t ω).weight y *
        f ((run (d + 1) t ω) ∘ e) y) := by
  rw [← centered_joint_identity d (initialState (d + 1) B tag ht) e he t f]
  apply mean_congr
  intro ω
  change _ = ∑ x, centeredPoint B tag x * f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω x)
  rw [centeredPoint_test]
  congr 2
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp (run (d + 1) t ω)
      (fun y => if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0)).symm

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_TaggedDeviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα uι

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_sub {Ω : Type uΩ} [Fintype Ω] (f g : Ω → ℝ) :
    mean (fun ω => f ω - g ω) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem abs_mean_le {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) :
    |mean f| ≤ mean (fun ω => |f ω|) := by
  unfold mean
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (Fintype.card Ω) : (0 : ℝ) ≤ Fintype.card Ω)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem mean_sq_le {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun ω => f ω ^ 2) := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ f (fun _ => (1 : ℝ))
  simpa only [mul_one, one_pow, Finset.expect_const (Finset.univ_nonempty),
    Finset.expect_eq_sum_div_card, Finset.card_univ, mean] using h

theorem mean_l1_le_sqrt {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (w : Ω → α → ℝ) :
    mean (fun ω => ∑ x, |w ω x|) ≤
      Real.sqrt ((Fintype.card α : ℝ) * mean (fun ω => ∑ x, w ω x ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ mean (fun ω => (∑ x, |w ω x|) ^ 2) := mean_sq_le _
    _ ≤ mean (fun ω => (Fintype.card α : ℝ) * ∑ x, w ω x ^ 2) := by
      apply mean_le_mean
      intro ω
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : α => (1 : ℝ)) (fun x => |w ω x|)
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, sq_abs] using h
    _ = _ := mean_const_mul _ _

theorem mean_weighted_test_le {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (w f : Ω → α → ℝ) (hf : ∀ ω x, |f ω x| ≤ 1) :
    |mean (fun ω => ∑ x, w ω x * f ω x)| ≤
      Real.sqrt ((Fintype.card α : ℝ) * mean (fun ω => ∑ x, w ω x ^ 2)) := by
  calc
    _ ≤ mean (fun ω => |∑ x, w ω x * f ω x|) := abs_mean_le _
    _ ≤ mean (fun ω => ∑ x, |w ω x|) := by
      apply mean_le_mean
      intro ω
      calc
        _ ≤ ∑ x, |w ω x * f ω x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum (fun x _ => by
          rw [abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf ω x) (abs_nonneg _))
    _ ≤ _ := mean_l1_le_sqrt w

theorem tagged_deviation_bound {ι : Type uι} (d : ℕ)
    (B : Position (d + 1) → Bool) (tag : Position (d + 1)) (ht : B tag = true)
    (e : ι → Position (d + 1)) (he : ∀ i, B (e i) = false)
    (t : ℕ) (f : (ι → Position (d + 1)) → Position (d + 1) → ℝ)
    (hf : ∀ e' y, |f e' y| ≤ 1) :
    |mean (fun ω : History (d + 1) t =>
      f ((run (d + 1) t ω) ∘ e) (run (d + 1) t ω tag) -
        (1 / (freeCount B : ℝ)) *
          (∑ y, if B ((run (d + 1) t ω).symm y) then f ((run (d + 1) t ω) ∘ e) y else 0))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1) B tag ht) t) := by
  rw [tagged_deviation_identity d B tag ht e he]
  exact mean_weighted_test_le _ _ (fun ω y => hf _ y)

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_TaggedCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem freeOf_perm {α : Type uα} [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (g : Equiv.Perm α) (y : α) :
    freeOf (g ∘ e) y = freeOf e (g.symm y) := by
  simp [freeOf, ← g.eq_symm_apply]

theorem freeCount_perm {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (g : Equiv.Perm α) : freeCount (freeOf (g ∘ e)) = freeCount (freeOf e) := by
  apply Nat.cast_injective (R := ℝ)
  rw [← sum_free_indicator, ← sum_free_indicator]
  simp only [freeOf_perm]
  exact Equiv.sum_comp g.symm (fun x => if freeOf e x then (1 : ℝ) else 0)

theorem freeCount_freeOf {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k → α) (he : Function.Injective e) : freeCount (freeOf e) = Fintype.card α - k := by
  have hs : Finset.univ.filter (fun x => freeOf e x = true) = (Finset.univ.image e)ᶜ := by
    ext x
    simp [freeOf]
  unfold freeCount
  rw [hs, Finset.card_compl, Finset.card_image_of_injective _ he]
  simp

theorem completeTest_bound {α : Type uα} [Fintype α] [DecidableEq α] {k : ℕ}
    (f : (Fin (k + 1) → α) → ℝ) (hf : ∀ e, |f e| ≤ 1) (e : Fin k → α) :
    |completeTest f e| ≤ 1 := by
  unfold completeTest
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (freeCount (freeOf e) : ℝ))]
  have hs : |∑ y, if freeOf e y then f (Fin.snoc e y) else 0| ≤ freeCount (freeOf e) := by
    calc
      _ ≤ ∑ y, |if freeOf e y then f (Fin.snoc e y) else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, if freeOf e y then (1 : ℝ) else 0 := Finset.sum_le_sum (fun y _ => by
        by_cases h : freeOf e y = true
        · simpa only [h, ↓reduceIte] using hf (Fin.snoc e y)
        · simp [h])
      _ = _ := sum_free_indicator _
  have hh := mul_le_mul_of_nonneg_left hs
    (by positivity : (0 : ℝ) ≤ 1 / (freeCount (freeOf e) : ℝ))
  by_cases hz : freeCount (freeOf e) = 0
  · simp [hz]
  · have hn : (freeCount (freeOf e) : ℝ) ≠ 0 := by exact_mod_cast hz
    simpa [hn] using hh

theorem uniform_tagged_completion {α : Type uα} [Fintype α] [DecidableEq α]
    {k : ℕ} (e : Fin k → α) (tag : α) (ht : freeOf e tag = true)
    (f : (Fin k → α) → α → ℝ) :
    mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) =
    mean (fun g : Equiv.Perm α => (1 / (freeCount (freeOf e) : ℝ)) *
      ∑ y, if freeOf (g ∘ e) y then f (g ∘ e) y else 0) := by
  have hm : (freeCount (freeOf e) : ℝ) ≠ 0 := by
    exact_mod_cast (freeCount_pos _ tag ht).ne'
  have hs (x : α) (hx : freeOf e x = true) :
      mean (fun g : Equiv.Perm α => f (g ∘ e) (g x)) =
        mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) := by
    have heq : (Equiv.swap tag x) ∘ e = e := by
      funext i
      exact Equiv.swap_apply_of_ne_of_ne ((freeOf_true e tag).mp ht i)
        ((freeOf_true e x).mp hx i)
    have h := mean_equiv (Equiv.mulRight (Equiv.swap tag x))
      (fun g : Equiv.Perm α => f (g ∘ e) (g tag))
    convert h using 1
    apply mean_congr
    intro g
    change f (g ∘ e) (g x) = f (g ∘ ((Equiv.swap tag x) ∘ e)) (g (Equiv.swap tag x tag))
    rw [heq, Equiv.swap_apply_left]
  symm
  calc
    _ = mean (fun g : Equiv.Perm α => (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, if freeOf e x then f (g ∘ e) (g x) else 0) := by
      apply mean_congr
      intro g
      congr 1
      simp only [freeOf_perm]
      exact (Equiv.sum_comp g (fun y => if freeOf e (g.symm y) then f (g ∘ e) y else 0)).symm.trans
        (by simp only [Equiv.symm_apply_apply])
    _ = (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, mean (fun g : Equiv.Perm α => if freeOf e x then f (g ∘ e) (g x) else 0) := by
      rw [mean_const_mul, mean_sum]
    _ = (1 / (freeCount (freeOf e) : ℝ)) *
        ∑ x, if freeOf e x then mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      cases hx : freeOf e x
      · simp [mean_zero]
      · simpa only [hx, ↓reduceIte] using hs x hx
    _ = _ := by
      have hid (x : α) : (if freeOf e x then mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) else 0) =
          (if freeOf e x then (1 : ℝ) else 0) * mean (fun g : Equiv.Perm α => f (g ∘ e) (g tag)) := by
        cases freeOf e x <;> simp
      simp_rw [hid]
      rw [← Finset.sum_mul, sum_free_indicator]
      field_simp

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PrefixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem prefix_one_step_bound (d t k : ℕ) (e : Fin (k + 1) → Position (d + 1))
    (he : Function.Injective e) (f : (Fin (k + 1) → Position (d + 1)) → ℝ)
    (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 1) t => f ((run (d + 1) t ω) ∘ e)) -
      mean (fun ω : History (d + 1) t => completeTest f ((run (d + 1) t ω) ∘ Fin.init e))| ≤
    Real.sqrt ((Fintype.card (Position (d + 1)) : ℝ) *
      expectedEnergy d (initialState (d + 1) (freeOf (Fin.init e)) (e (Fin.last k))
        (by
          apply (freeOf_true _ _).mpr
          intro i hi
          exact Fin.castSucc_ne_last i (he hi))) t) := by
  have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
    apply (freeOf_true _ _).mpr
    intro i hi
    exact Fin.castSucc_ne_last i (he hi)
  have hh := tagged_deviation_bound d (freeOf (Fin.init e)) (e (Fin.last k)) ht
    (Fin.init e) (freeOf_exposed _) t (fun z y => f (Fin.snoc z y)) (fun z y => hf _)
  convert hh using 1
  congr 1
  rw [← mean_sub]
  apply mean_congr
  intro ω
  rw [← Fin.comp_snoc, Fin.snoc_init_self]
  unfold completeTest
  rw [freeCount_perm]
  simp only [freeOf_perm]

theorem uniform_prefix_step {α : Type uα} [Fintype α] [DecidableEq α]
    (k : ℕ) (e : Fin (k + 1) → α) (he : Function.Injective e)
    (f : (Fin (k + 1) → α) → ℝ) :
    mean (fun g : Equiv.Perm α => f (g ∘ e)) =
      mean (fun g : Equiv.Perm α => completeTest f (g ∘ Fin.init e)) := by
  have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
    apply (freeOf_true _ _).mpr
    intro i hi
    exact Fin.castSucc_ne_last i (he hi)
  have h := uniform_tagged_completion (Fin.init e) (e (Fin.last k)) ht
    (fun z y => f (Fin.snoc z y))
  simpa only [← Fin.comp_snoc, Fin.snoc_init_self, completeTest, freeCount_perm] using h

theorem prefix_test_bound (d m : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * m)
    (k : ℕ) (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e)
    (f : (Fin k → Position (d + 2)) → ℝ) (hf : ∀ z, |f z| ≤ 1) :
    |mean (fun ω : History (d + 2) (200 * (d + 2)) => f ((run (d + 2) (200 * (d + 2)) ω) ∘ e)) -
      mean (fun g : State (d + 2) => f (g ∘ e))| ≤
    (k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
  induction k with
  | zero =>
    have hz (g : State (d + 2)) : g ∘ e = e := by funext i; exact Fin.elim0 i
    simp only [hz, mean_const, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k ih =>
    have he0 : Function.Injective (Fin.init e) := by
      intro i j hij
      exact Fin.castSucc_inj.mp (he hij)
    have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
      apply (freeOf_true _ _).mpr
      intro i hi
      exact Fin.castSucc_ne_last i (he hi)
    have hcount : m ≤ freeCount (freeOf (Fin.init e)) := by
      rw [freeCount_freeOf _ he0]
      omega
    have henergy := centeredPoint_energy_200 d (freeOf (Fin.init e)) (e (Fin.last k)) ht (by omega)
    have hpower : (9 / 10 : ℝ) ^ freeCount (freeOf (Fin.init e)) ≤ (9 / 10 : ℝ) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcount
    have hz := prefix_one_step_bound (d + 1) (200 * (d + 2)) k e he f hf
    have hestimate :
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          expectedEnergy (d + 1) (initialState (d + 2) (freeOf (Fin.init e)) (e (Fin.last k)) ht)
            (200 * (d + 2))) ≤
        Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact henergy.trans (by linarith)
    have hnext := ih (by omega) (Fin.init e) he0 (completeTest f) (completeTest_bound f hf)
    rw [uniform_prefix_step k e he f]
    have htri := abs_sub_le
      (mean (fun ω : History (d + 2) (200 * (d + 2)) => f ((run (d + 2) (200 * (d + 2)) ω) ∘ e)))
      (mean (fun ω : History (d + 2) (200 * (d + 2)) => completeTest f ((run (d + 2) (200 * (d + 2)) ω) ∘ Fin.init e)))
      (mean (fun g : State (d + 2) => completeTest f (g ∘ Fin.init e)))
    have hz' := hz.trans hestimate
    push_cast
    nlinarith

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MarginalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uΩ uα uΩ'

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem fairMass_test {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [Fintype α]
    (a : Ω → α) (f : α → ℝ) :
    (∑ x, fairMass a x * f x) = mean (fun ω => f (a ω)) := by
  classical
  unfold fairMass mean
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem fairMass_tv_le_of_test {Ω : Type uΩ} {Ω' : Type uΩ'} {α : Type uα} [Fintype Ω] [Fintype Ω'] [Fintype α]
    (a : Ω → α) (b : Ω' → α) (δ : ℝ)
    (h : ∀ f : α → ℝ, (∀ x, |f x| ≤ 1) →
      |mean (fun ω => f (a ω)) - mean (fun ω => f (b ω))| ≤ δ) :
    tv (fairMass a) (fairMass b) ≤ δ / 2 := by
  classical
  let f : α → ℝ := fun x => if 0 ≤ fairMass a x - fairMass b x then 1 else -1
  have hf : ∀ x, |f x| ≤ 1 := by intro x; dsimp [f]; split_ifs <;> norm_num
  have hh := h f hf
  rw [← fairMass_test, ← fairMass_test, ← Finset.sum_sub_distrib] at hh
  have hid (x : α) : fairMass a x * f x - fairMass b x * f x = |fairMass a x - fairMass b x| := by
    dsimp [f]
    split_ifs with hx
    · rw [abs_of_nonneg hx]; ring
    · rw [abs_of_neg (lt_of_not_ge hx)]; ring
  simp_rw [hid] at hh
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at hh
  unfold tv
  linarith

theorem marginal_tv_200 (d m k : ℕ)
    (hm : Fintype.card (Position (d + 2)) ≤ 8 * m)
    (hk : k + m ≤ Fintype.card (Position (d + 2)))
    (e : Fin k → Position (d + 2)) (he : Function.Injective e) :
    tv (fairMass (fun ω : History (d + 2) (200 * (d + 2)) =>
          (run (d + 2) (200 * (d + 2)) ω) ∘ e))
      (fairMass (fun g : State (d + 2) => g ∘ e)) ≤
    ((k : ℝ) / 2) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)) := by
  have h := fairMass_tv_le_of_test
    (fun ω : History (d + 2) (200 * (d + 2)) => (run (d + 2) (200 * (d + 2)) ω) ∘ e)
    (fun g : State (d + 2) => g ∘ e)
    ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d + 2)) : ℝ) *
      ((1 / 2 : ℝ) ^ (8 * (d + 2)) + 32 * (9 / 10 : ℝ) ^ m)))
    (prefix_test_bound d m hm k hk e he)
  convert h using 1 <;> first | rfl | ring

end Conditional

namespace Conditional

theorem marginalRate_tendsto : Tendsto marginalRate atTop (nhds 0) := by
  have h₁ := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)
  have h₂ := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hh := ((h₁.add h₂).const_mul 3136).sqrt
  unfold marginalRate
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Function.comp_def,
    add_zero, mul_zero, Real.sqrt_zero] using hh

theorem marginal_tv_rate (d : ℕ) (e : Fin (7 * 2 ^ d) → Position (d + 1 + 2))
    (he : Function.Injective e) :
    tv (fairMass (fun ω : History (d + 1 + 2) (200 * (d + 1 + 2)) =>
          (run (d + 1 + 2) (200 * (d + 1 + 2)) ω) ∘ e))
      (fairMass (fun g : State (d + 1 + 2) => g ∘ e)) ≤ marginalRate d := by
  have hc : Fintype.card (Position (d + 1 + 2)) = 8 * 2 ^ d := by
    simp only [card_position, pow_add]
    norm_num
    omega
  have hh := marginal_tv_200 (d + 1) (2 ^ d) (7 * 2 ^ d)
    (by rw [hc]) (by rw [hc]; omega) e he
  simp only [Nat.add_assoc] at hh
  have hbound :
      (((7 * 2 ^ d : ℕ) : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Position (d + 1 + 2)) : ℝ) *
          ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d))) ≤ marginalRate d := by
    unfold marginalRate
    apply Real.le_sqrt_of_sq_le
    have hp : (1 / 2 : ℝ) ^ (8 * (d + 3)) ≤ (1 / 2 : ℝ) ^ (8 * d) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hid : (2 ^ d : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (8 * d) = (1 / 32 : ℝ) ^ d := by
      rw [← pow_mul, Nat.mul_comm d 3, pow_mul, pow_mul, ← mul_pow]
      norm_num
    have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (2 ^ d : ℝ) ^ 3)
    rw [hid] at hp'
    have hsq :
        (((7 * 2 ^ d : ℕ) : ℝ) / 2 *
          Real.sqrt ((Fintype.card (Position (d + 1 + 2)) : ℝ) *
            ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d)))) ^ 2 =
        98 * (2 ^ d : ℝ) ^ 3 *
          ((1 / 2 : ℝ) ^ (8 * (d + 3)) + 32 * (9 / 10 : ℝ) ^ (2 ^ d)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), hc]
      push_cast
      ring
    rw [hsq]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) d]
  have hone := le_trans hh hbound
  exact hone

end Conditional

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Reachability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Reachability
open Conditional

theorem step_false (d : ℕ) : step (d + 1) (zeroCoins d) = rotate (d + 1) := by
  ext x i
  simp only [step, Equiv.trans_apply, Fin.consEquiv_symm_apply, pairSwitch, zeroCoins, Bool.xor_false]
  change (rotate (d + 1)) (Fin.cons (x 0) (Fin.tail x)) i = _
  rw [Fin.cons_self_tail]

theorem run_false (d t : ℕ) :
    run (d + 1) t (fun _ => zeroCoins d) = rotate (d + 1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [run_succ]
    change step (d + 1) (zeroCoins d) * run (d + 1) t (fun _ => zeroCoins d) = _
    rw [step_false, ih, pow_succ']

theorem rotate_inv_pow (d : ℕ) :
    rotate (d + 1) ^ (orderOf (rotate (d + 1)) - 1) = (rotate (d + 1))⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]

theorem inverse_conj_mem (d : ℕ) {g : State (d + 1)} (hg : g ∈ returnGroup d) :
    (rotate (d + 1))⁻¹ * g * rotate (d + 1) ∈ returnGroup d := by
  rw [mem_returnGroup] at hg ⊢
  rcases hg with ⟨t, ht, ω, rfl⟩
  refine ⟨(1 + t) + (orderOf (rotate (d + 1)) - 1), ?_,
    Fin.append (Fin.append (fun _ => zeroCoins d) ω) (fun _ => zeroCoins d), ?_⟩
  · have hp := orderOf_pos (rotate (d + 1))
    have he : (1 + t) + (orderOf (rotate (d + 1)) - 1) = t + orderOf (rotate (d + 1)) := by omega
    rw [he]; exact dvd_add ht (dvd_refl _)
  · rw [run_append, run_append, run_false, run_false, pow_one, rotate_inv_pow, mul_assoc]

theorem inverse_conj_pow_mem (d t : ℕ) {g : State (d + 1)} (hg : g ∈ returnGroup d) :
    (rotate (d + 1) ^ t)⁻¹ * g * rotate (d + 1) ^ t ∈ returnGroup d := by
  induction t with
  | zero => simpa using hg
  | succ t ih =>
    have h := inverse_conj_mem d ih
    simpa only [pow_succ, mul_inv_rev, mul_assoc] using h

theorem canceled_step_mem (d : ℕ) (c : Coins (d + 1)) :
    (rotate (d + 1))⁻¹ * step (d + 1) c ∈ returnGroup d := by
  rw [mem_returnGroup]
  refine ⟨1 + (orderOf (rotate (d + 1)) - 1), ?_,
    Fin.append (fun _ => c) (fun _ => zeroCoins d), ?_⟩
  · rw [Nat.add_sub_of_le (orderOf_pos _)]
  · rw [run_append, run_false, rotate_inv_pow, run_succ, run_zero, mul_one]

end Reachability

namespace Reachability
open Conditional

theorem first_pair_swap (d : ℕ) (s : Position d) :
    (rotate (d + 1))⁻¹ * step (d + 1) (fun x => decide (x = s)) =
      Equiv.swap (Fin.cons false s) (Fin.cons true s) := by
  classical
  apply Equiv.Perm.ext
  intro x
  obtain ⟨⟨b, t⟩, rfl⟩ := (splitPosition d).symm.surjective x
  have hc : ((rotate (d + 1))⁻¹ * step (d + 1) (fun x => decide (x = s)))
      ((splitPosition d).symm (b, t)) =
      (splitPosition d).symm (b ^^ decide (t = s), t) := by
    simp [step, splitPosition, pairSwitch]
  rw [hc]
  change (Fin.cons (b ^^ decide (t = s)) t : Position (d + 1)) =
    Equiv.swap (Fin.cons false s) (Fin.cons true s) (Fin.cons b t)
  by_cases ht : t = s
  · subst t; cases b <;> simp
  · have hf : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons false s := by
      intro h; apply ht; simpa using congrArg Fin.tail h
    have htr : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons true s := by
      intro h; apply ht; simpa using congrArg Fin.tail h
    simp [ht, Equiv.swap_apply_of_ne_of_ne hf htr]

theorem first_pair_mem (d : ℕ) (s : Position d) :
    Equiv.swap (Fin.cons false s) (Fin.cons true s) ∈ returnGroup d := by
  classical
  rw [← first_pair_swap]
  exact canceled_step_mem d _

theorem first_edge_mem (d : ℕ) (x y : Position (d + 1))
    (h : Fin.tail x = Fin.tail y) : Equiv.swap x y ∈ returnGroup d := by
  classical
  rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y]
  rw [h]
  cases hx : x 0 <;> cases hy : y 0
  · simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem
  · exact first_pair_mem d _
  · rw [Equiv.swap_comm]; exact first_pair_mem d _
  · simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem

theorem rotate_pow_apply (d t : ℕ) (x : Position d) (j : Fin d) :
    (rotate d ^ t) x j = x ((finRotate d ^ t) j) := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    simp only [rotate, Equiv.piCongrLeft_apply, Equiv.symm_symm] at *
    simp only [ih, pow_succ, Equiv.Perm.mul_apply]
    simp

theorem finRotate_pow_zero (d : ℕ) (i : Fin (d + 1)) :
    (finRotate (d + 1) ^ i.val) 0 = i := by
  rw [Equiv.Perm.coe_pow, ← finCycle_eq_finRotate_iterate]
  simp

theorem edge_swap_mem (d : ℕ) (i : Fin (d + 1)) (x y : Position (d + 1))
    (h : ∀ j, j ≠ i → x j = y j) : Equiv.swap x y ∈ returnGroup d := by
  classical
  have ht : Fin.tail ((rotate (d + 1) ^ i.val) x) =
      Fin.tail ((rotate (d + 1) ^ i.val) y) := by
    funext j
    simp only [Fin.tail, rotate_pow_apply]
    apply h
    intro he
    have hz : j.succ = 0 := (finRotate (d + 1) ^ i.val).injective
      (he.trans (finRotate_pow_zero d i).symm)
    exact Fin.succ_ne_zero j hz
  have hm := inverse_conj_pow_mem d i.val (first_edge_mem d _ _ ht)
  rw [Equiv.mul_swap_eq_swap_mul, mul_assoc, inv_mul_cancel, mul_one] at hm
  simpa using hm

theorem cube_connected (d : ℕ) (R : Position d → Position d → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ x y z, R x y → R y z → R x z)
    (hedge : ∀ (i : Fin d) x y, (∀ j, j ≠ i → x j = y j) → R x y)
    (x y : Position d) : R x y := by
  induction d with
  | zero => have : x = y := Subsingleton.elim _ _; subst y; exact hrefl x
  | succ d ih =>
    let z : Position (d + 1) := Fin.cons (y 0) (Fin.tail x)
    apply htrans x z y
    · apply hedge 0
      intro j hj
      obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      rfl
    · have hh := ih (fun a b => R (Fin.cons (y 0) a) (Fin.cons (y 0) b))
        (fun a => hrefl _) (fun a b c hab hbc => htrans _ _ _ hab hbc)
        (fun i a b hab => hedge i.succ _ _ (by
          intro j
          refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
          exact hab j (by intro he; subst j; exact hj rfl)))
        (Fin.tail x) (Fin.tail y)
      simpa only [Fin.cons_self_tail] using hh

theorem all_swap_mem (d : ℕ) (x y : Position (d + 1)) :
    Equiv.swap x y ∈ returnGroup d := by
  classical
  apply cube_connected (d + 1) (fun x y => Equiv.swap x y ∈ returnGroup d)
    (fun x => by simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem) ?_ (edge_swap_mem d) x y
  intro a b c hab hbc
  by_cases hac : a = c
  · subst c; simpa only [Equiv.swap_self, Equiv.Perm.one_def] using (returnGroup d).one_mem
  by_cases hab' : a = b
  · subst b; exact hbc
  by_cases hbc' : b = c
  · subst c; exact hab
  have hh := (returnGroup d).mul_mem ((returnGroup d).mul_mem hab hbc) hab
  rw [Equiv.mul_swap_eq_swap_mul (Equiv.swap a b) b c, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc'),
    mul_assoc, Equiv.swap_mul_self, mul_one] at hh
  exact hh

theorem returnGroup_eq_top (d : ℕ) : returnGroup d = ⊤ := by
  apply top_unique
  intro g hg
  clear hg
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact (returnGroup d).one_mem
  | swap_mul g x y _ hg => exact (returnGroup d).mul_mem (all_swap_mem d x y) hg

theorem attainable_return (d : ℕ) (g : State (d + 1)) :
    ∃ t, orderOf (rotate (d + 1)) ∣ t ∧ ∃ ω : History (d + 1) t, run (d + 1) t ω = g := by
  have hg : g ∈ returnGroup d := by rw [returnGroup_eq_top]; trivial
  rwa [mem_returnGroup] at hg

end Reachability

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uΩ uΩ' uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace FiniteLaw
open Conditional

variable {G : Type uG} [Fintype G] [Group G]

theorem conv_fairMass {Ω : Type uΩ} {Ω' : Type uΩ'} [Fintype Ω] [Fintype Ω']
    (a : Ω → G) (b : Ω' → G) :
    conv (fairMass a) (fairMass b) = fairMass (fun p : Ω × Ω' => a p.1 * b p.2) := by
  classical
  funext z
  unfold conv
  rw [fairMass_test]
  change mean (fun ω => mean (fun ω' => if b ω' = (a ω)⁻¹ * z then 1 else 0)) =
    mean (fun p : Ω × Ω' => if a p.1 * b p.2 = z then 1 else 0)
  rw [mean_prod]
  apply mean_congr
  intro ω
  apply mean_congr
  intro ω'
  rw [eq_inv_mul_iff_mul_eq]

theorem sum_inv_mul (f : G → ℝ) (z : G) : ∑ g, f (g⁻¹ * z) = ∑ g, f g := by
  exact Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight z)) f

theorem sum_mul_left (f : G → ℝ) (g : G) : ∑ z, f (g * z) = ∑ z, f z :=
  Equiv.sum_comp (Equiv.mulLeft g) f

theorem tv_conv_contract (μ ν : G → ℝ) (hμ : ∑ g, μ g = 1)
    (hν : ∑ g, ν g = 1) (c : ℝ) (hc : ∀ g, c ≤ μ g) :
    tv (conv μ ν) (fun _ => (1 : ℝ) / Fintype.card G) ≤
      (1 - (Fintype.card G : ℝ) * c) * tv ν (fun _ => (1 : ℝ) / Fintype.card G) := by
  let u : ℝ := 1 / Fintype.card G
  have hu : ∑ _ : G, u = 1 := by simp [u, Fintype.card_ne_zero]
  have hcenter (z : G) : ∑ g, (ν (g⁻¹ * z) - u) = 0 := by
    rw [Finset.sum_sub_distrib, sum_inv_mul, hν, hu, sub_self]
  have hid (z : G) : conv μ ν z - u = ∑ g, (μ g - c) * (ν (g⁻¹ * z) - u) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hcenter, mul_zero, sub_zero]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, one_mul, conv]
  have hb : ∑ z, |conv μ ν z - u| ≤
      (1 - (Fintype.card G : ℝ) * c) * ∑ z, |ν z - u| := by
    calc
      _ = ∑ z, |∑ g, (μ g - c) * (ν (g⁻¹ * z) - u)| := by simp_rw [hid]
      _ ≤ ∑ z, ∑ g, (μ g - c) * |ν (g⁻¹ * z) - u| := by
        apply Finset.sum_le_sum
        intro z _
        have h := Finset.abs_sum_le_sum_abs (fun g => (μ g - c) * (ν (g⁻¹ * z) - u)) Finset.univ
        simpa only [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hc _))] using h
      _ = (∑ g, (μ g - c)) * ∑ z, |ν z - u| := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum, sum_mul_left (fun z => |ν z - u|)]
      _ = _ := by simp [Finset.sum_sub_distrib, hμ]
  unfold tv
  change (1 / 2 : ℝ) * (∑ z, |conv μ ν z - u|) ≤ _
  nlinarith

omit [Fintype G] [Group G] in

theorem fairMass_lower_of_surjective {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]
    (a : Ω → G) (ha : Function.Surjective a) (g : G) :
    1 / (Fintype.card Ω : ℝ) ≤ fairMass a g := by
  classical
  obtain ⟨ω, hω⟩ := ha g
  unfold fairMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.single_le_sum (f := fun ω => if a ω = g then (1 : ℝ) else 0)
    (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ ω)
  simpa only [hω, ↓reduceIte] using h

end FiniteLaw

theorem fairMass_eq_mean {Ω : Type uΩ} {α : Type uα} [Fintype Ω] [DecidableEq α] (f : Ω → α) (a : α) :
    fairMass f a = Conditional.mean (fun ω => if f ω = a then (1 : ℝ) else 0) := by
  classical
  unfold fairMass Conditional.mean
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  dsimp only
  split_ifs <;> rfl

theorem law_add (d s t : ℕ) :
    law d (s + t) = FiniteLaw.conv (law d t) (law d s) := by
  classical
  rw [law, law, law, FiniteLaw.conv_fairMass]
  funext z
  rw [fairMass_eq_mean, fairMass_eq_mean]
  rw [Conditional.mean_history_add, Conditional.mean_prod, Conditional.mean_comm]
  simp only [Reachability.run_append]

namespace Reachability

theorem exists_surjective_run (d : ℕ) :
    ∃ T : ℕ, Function.Surjective (run (d + 1) T) := by
  classical
  choose t ht ω hω using attainable_return d
  let T : ℕ := ∑ g : State (d + 1), t g
  have hT : orderOf (rotate (d + 1)) ∣ T := Finset.dvd_sum (fun g _ => ht g)
  refine ⟨T, fun g => ?_⟩
  have hle : t g ≤ T := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  have hdvd : orderOf (rotate (d + 1)) ∣ T - t g := Nat.dvd_sub hT (ht g)
  have hid : run (d + 1) (T - t g) (fun _ => zeroCoins d) = 1 := by
    rw [run_false]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hh : ∃ a : History (d + 1) (t g + (T - t g)),
      run (d + 1) (t g + (T - t g)) a = g := by
    refine ⟨Fin.append (ω g) (fun _ => zeroCoins d), ?_⟩
    rw [run_append, hid, one_mul, hω]
  have he : t g + (T - t g) = T := by omega
  rw [he] at hh
  exact hh

end Reachability

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_MixingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

theorem exists_mixing_time_succ (d : ℕ) : ∃ t : ℕ, distance (d + 1) t ≤ 1 / 4 := by
  classical
  obtain ⟨T, hT⟩ := Reachability.exists_surjective_run d
  let c : ℝ := 1 / Fintype.card (History (d + 1) T)
  let r : ℝ := 1 - (Fintype.card (State (d + 1)) : ℝ) * c
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hminor (g : State (d + 1)) : c ≤ law (d + 1) T g :=
    FiniteLaw.fairMass_lower_of_surjective _ hT g
  have hr : 0 ≤ r := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hminor g)
    simp only [law, fairMass_sum] at hh
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using sub_nonneg.mpr hh
  have hrlt : r < 1 := by
    dsimp [r]
    have hn : (0 : ℝ) < Fintype.card (State (d + 1)) := by positivity
    nlinarith
  have hcontract (s : ℕ) : distance (d + 1) (s + T) ≤ r * distance (d + 1) s := by
    unfold distance uniform
    rw [law_add]
    exact FiniteLaw.tv_conv_contract _ _ (fairMass_sum _) (fairMass_sum _) c hminor
  have hgeom (n : ℕ) : distance (d + 1) (n * T) ≤ r ^ n * distance (d + 1) 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul]
      calc
        _ ≤ r * distance (d + 1) (n * T) := hcontract _
        _ ≤ r * (r ^ n * distance (d + 1) 0) := mul_le_mul_of_nonneg_left ih hr
        _ = _ := by rw [pow_succ']; ring
  have hlim : Tendsto (fun n : ℕ => r ^ n * distance (d + 1) 0) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hrlt).mul_const (distance (d + 1) 0)
  have hev : ∀ᶠ n : ℕ in atTop, r ^ n * distance (d + 1) 0 < 1 / 4 :=
    hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n * T, (hgeom n).trans hn.le⟩

theorem exists_mixing_time {d : ℕ} (hd : 1 ≤ d) : ∃ t : ℕ, distance d t ≤ 1 / 4 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact exists_mixing_time_succ k

theorem exact_support_lower {d : ℕ} (hd : 1 ≤ d) :
    supportThreshold d ≤ (mixingTime d : ℤ) :=
  supportThreshold_le_mixingTime hd (exists_mixing_time hd)

theorem log_factorial_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh := Real.pow_div_factorial_le_exp (n : ℝ) hpos.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / (n.factorial : ℝ)) hh
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at hlog
  linarith

theorem supportThreshold_bounds (d : ℕ) :
    2 * (d : ℝ) - 6 ≤ (supportThreshold d : ℝ) ∧
      (supportThreshold d : ℝ) ≤ 2 * (d : ℝ) := by
  let n : ℕ := 2 ^ d
  have hn : 0 < n := by dsimp [n]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hl2pos : 0 < Real.log 2 := by linarith
  have hlfrac : -(1 / 3 : ℝ) ≤ Real.log (3 / 4 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
    norm_num at hh ⊢
    exact hh
  have hlogn : Real.log (n : ℝ) = (d : ℝ) * Real.log 2 := by
    simp only [n, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlow := log_factorial_lower n hn
  have hupp : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
    have hh : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    simpa only [Real.log_pow] using Real.log_le_log hfact hh
  have hprod : Real.log (3 * (n.factorial : ℝ) / 4) =
      Real.log (3 / 4 : ℝ) + Real.log (n.factorial : ℝ) := by
    rw [show 3 * (n.factorial : ℝ) / 4 = (3 / 4) * n.factorial by ring]
    exact Real.log_mul (by norm_num) hfact.ne'
  have hlowlog : (n : ℝ) * ((d : ℝ) * Real.log 2) - n - 1 / 3 ≤
      Real.log (3 * (n.factorial : ℝ) / 4) := by
    rw [hprod, ← hlogn]
    linarith
  have hupplog : Real.log (3 * (n.factorial : ℝ) / 4) ≤
      (n : ℝ) * ((d : ℝ) * Real.log 2) := by
    rw [hprod, ← hlogn]
    have hh : Real.log (3 / 4 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    linarith
  let a : ℝ := (2 / (n : ℝ)) * Real.logb 2 (3 * (n.factorial : ℝ) / 4)
  have ha_low : 2 * (d : ℝ) - 6 ≤ a := by
    dsimp [a]
    rw [Real.logb]
    have he : (2 / (n : ℝ)) *
        (Real.log (3 * (n.factorial : ℝ) / 4) / Real.log 2) =
        (2 * Real.log (3 * (n.factorial : ℝ) / 4)) / ((n : ℝ) * Real.log 2) := by ring
    rw [he]
    apply (le_div_iff₀ (mul_pos hnR hl2pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ n)]
  have ha_upp : a ≤ 2 * (d : ℝ) := by
    dsimp [a]
    rw [Real.logb]
    have hscale := mul_le_mul_of_nonneg_left hupplog (by positivity : (0 : ℝ) ≤ 2 / n / Real.log 2)
    have hid : (2 / (n : ℝ) / Real.log 2) * ((n : ℝ) * ((d : ℝ) * Real.log 2)) = 2 * d := by
      field_simp
    rw [hid] at hscale
    calc
      _ = (2 / (n : ℝ) / Real.log 2) * Real.log (3 * (n.factorial : ℝ) / 4) := by ring
      _ ≤ 2 * (d : ℝ) := hscale
  have hceil : supportThreshold d = ⌈a⌉ := by
    simp only [supportThreshold, a, n, Nat.cast_pow, Nat.cast_ofNat]
  rw [hceil]
  constructor
  · exact ha_low.trans (Int.le_ceil a)
  · have hh : ⌈a⌉ ≤ (2 * d : ℤ) := Int.ceil_le.mpr (by exact_mod_cast ha_upp)
    exact_mod_cast hh

theorem orderFunction_isBigO_mixingTime :
    Asymptotics.IsBigO atTop orderFunction (fun d : ℕ => (mixingTime d : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.eventually_atTop.2 ⟨6, fun d hd => ?_⟩⟩
  have hs := (supportThreshold_bounds d).1
  have hl : (supportThreshold d : ℝ) ≤ mixingTime d := by
    exact_mod_cast exact_support_lower (by omega : 1 ≤ d)
  have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
  simp only [orderFunction, Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg d), abs_of_nonneg (Nat.cast_nonneg (mixingTime d))]
  linarith

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Parity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Parity
open Conditional

theorem sign_mul (d : ℕ) (g h : State d) : sign d (g * h) = sign d g * sign d h := by
  simp [sign]

theorem step_toggle (d : ℕ) (s : Position d) (c : Coins (d + 1)) :
    step (d + 1) (toggleCoin s c) =
      step (d + 1) c * Equiv.swap (Fin.cons false s) (Fin.cons true s) := by
  classical
  change Position d → Bool at c
  apply Equiv.Perm.ext
  intro x
  obtain ⟨⟨b, t⟩, rfl⟩ := (splitPosition d).symm.surjective x
  change (rotate (d + 1)) (Fin.cons (b ^^ toggleCoin s c t) t) =
    step (d + 1) c (Equiv.swap (Fin.cons false s) (Fin.cons true s) (Fin.cons b t))
  by_cases ht : t = s
  · subst t
    cases b <;> simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    · change rotate (d + 1) (Fin.cons (false ^^ toggleCoin s c s) s) =
        rotate (d + 1) (Fin.cons (true ^^ c s) s)
      have hh : toggleCoin s c s = !(c s) := by
        change Function.update c s (!(c s)) s = !(c s)
        simp
      rw [hh]
      simp
    · change rotate (d + 1) (Fin.cons (true ^^ toggleCoin s c s) s) =
        rotate (d + 1) (Fin.cons (false ^^ c s) s)
      have hh : toggleCoin s c s = !(c s) := by
        change Function.update c s (!(c s)) s = !(c s)
        simp
      rw [hh]
      simp
  · have hf : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons false s := by
      intro he; apply ht; simpa using congrArg Fin.tail he
    have htr : (Fin.cons b t : Position (d + 1)) ≠ Fin.cons true s := by
      intro he; apply ht; simpa using congrArg Fin.tail he
    rw [Equiv.swap_apply_of_ne_of_ne hf htr]
    change rotate (d + 1) (Fin.cons (b ^^ toggleCoin s c t) t) =
      rotate (d + 1) (Fin.cons (b ^^ c t) t)
    have hh : toggleCoin s c t = c t := by
      change Function.update c s (!(c s)) t = c t
      exact Function.update_of_ne ht _ _
    rw [hh]

theorem sign_step_toggle (d : ℕ) (s : Position d) (c : Coins (d + 1)) :
    sign (d + 1) (step (d + 1) (toggleCoin s c)) =
      -sign (d + 1) (step (d + 1) c) := by
  classical
  rw [step_toggle, sign_mul]
  have hne : (Fin.cons false s : Position (d + 1)) ≠ Fin.cons true s := by
    intro he
    have hh := congrFun he 0
    simp at hh
  simp [sign, Equiv.Perm.sign_swap hne]

theorem mean_sign_step (d : ℕ) :
    mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) = 0 := by
  classical
  let s : Position d := fun _ => false
  have hh := mean_equiv (toggleCoin s)
    (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c))
  change mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) (toggleCoin s c))) =
    mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) at hh
  simp_rw [sign_step_toggle] at hh
  have hn : mean (fun c : Coins (d + 1) => -sign (d + 1) (step (d + 1) c)) =
      -mean (fun c : Coins (d + 1) => sign (d + 1) (step (d + 1) c)) := by
    simp only [mean, Finset.sum_neg_distrib, neg_div]
  rw [hn] at hh
  linarith

theorem mean_sign_run (d t : ℕ) :
    mean (fun ω : History (d + 1) (t + 1) => sign (d + 1) (run (d + 1) (t + 1) ω)) = 0 := by
  rw [mean_history_succ]
  simp only [run_snoc, sign_mul, mean_mul_const, mean_sign_step, zero_mul, mean_zero]

theorem law_sign_zero (d t : ℕ) :
    (∑ g : State (d + 1), law (d + 1) (t + 1) g * sign (d + 1) g) = 0 := by
  rw [law, fairMass_test]
  exact mean_sign_run d t

end Parity

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Classification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Cells (ofPartition p)) = n := by
  rw [card_cells_eq_sum, rowLens_ofPartition]
  simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum

lemma of_toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) :
    ofPartition (toPartition D n hn) = D := by
  have hs : (D.rowLens : Multiset ℕ).sort (· ≥ ·) = D.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ D.rowLens_sorted.pairwise
  unfold ofPartition toPartition
  simp only [hs]
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_LinearExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

omit [PartialOrder A] in

lemma labelByKey (k : A → ℕ) (hk : Function.Injective k) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, e x < e y ↔ k x < k y := by
  let e : A ≃ Set.range k := Equiv.ofInjective k hk
  let : Fintype (Set.range k) := Fintype.ofEquiv A e
  let o := (Fintype.orderIsoFinOfCardEq (Set.range k) (Fintype.card_congr e.symm)).symm
  exact ⟨e.trans o.toEquiv, fun x y => o.lt_iff_lt⟩

omit [PartialOrder A] in

lemma labelByRank (r : A → ℕ) :
    ∃ e : A ≃ Fin (Fintype.card A), ∀ x y, r x < r y → e x < e y := by
  let b := Fintype.equivFin A
  let k (x : A) := r x * (Fintype.card A + 1) + (b x).val
  have hk : Function.Injective k := by
    intro x y h
    have hx := (b x).isLt
    have hy := (b y).isLt
    have hr : r x = r y := by
      change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
      nlinarith
    apply b.injective
    apply Fin.ext
    change r x * (Fintype.card A + 1) + (b x).val = r y * (Fintype.card A + 1) + (b y).val at h
    rw [hr] at h
    omega
  obtain ⟨e, he⟩ := labelByKey A k hk
  refine ⟨e, fun x y hxy => (he x y).mpr ?_⟩
  dsimp [k]
  have hx := (b x).isLt
  nlinarith

lemma fiberPerm_le_extensions (r : A → ℕ) (hr : StrictMono r) :
    Fintype.card (Thorp.Specht.fiberGroup r) ≤ Fintype.card (Extensions A) := by
  obtain ⟨e, he⟩ := labelByRank A r
  let F (g : Thorp.Specht.fiberGroup r) : Extensions A := ⟨g.val.trans e, by
    intro x y hxy
    apply he
    rw [g.property x, g.property y]
    exact hr hxy⟩
  apply Fintype.card_le_of_injective F
  intro g h hgh
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply e.injective
  exact congrArg (fun z : Extensions A => z.val x) hgh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma tabloid_card_mul (r : α → ℕ) :
    Fintype.card (Tabloid r) * Fintype.card (fiberGroup r) = (Fintype.card α).factorial := by
  let G := Equiv.Perm α
  let b := baseTabloid r
  let e : MulAction.orbit G b ≃ Tabloid r := {
    toFun := Subtype.val
    invFun := fun f => ⟨f, by
      obtain ⟨g, hg⟩ := f.property
      refine ⟨g⁻¹, ?_⟩
      apply Subtype.ext
      funext x
      change r ((g⁻¹ : Equiv.Perm α)⁻¹ x) = f.val x
      rw [inv_inv]
      exact (congrFun hg x).symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let u : MulAction.stabilizer G b ≃ fiberGroup r := {
    toFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mp g.property⟩
    invFun := fun g => ⟨g.val, (stabilizes_tabloid_iff r g.val b).mpr g.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, ← Fintype.card_congr u,
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group, Fintype.card_perm]

lemma tabloid_card_le (r : α → ℕ) (m : ℕ) (hr : ∀ x, r x < m) :
    Fintype.card (Tabloid r) ≤ m ^ Fintype.card α := by
  have hb (f : Tabloid r) (x : α) : f.val x < m := by
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    exact hr (g x)
  let F (f : Tabloid r) : α → Fin m := fun x => ⟨f.val x, hb f x⟩
  have hi : Function.Injective F := by
    intro f h hfh
    apply Subtype.ext
    funext x
    exact congrArg Fin.val (congrFun hfh x)
  have hh := Fintype.card_le_of_injective F hi
  simpa only [Fintype.card_fun, Fintype.card_fin] using hh

end Thorp.Specht

namespace Thorp.Young
open scoped Classical
variable (A : Type uA) [Fintype A] [PartialOrder A]

theorem rank_extension_bound (r : A → ℕ) (hr : StrictMono r) (m : ℕ) (hm : ∀ x, r x < m) :
    (Fintype.card A).factorial ≤ m ^ Fintype.card A * Fintype.card (Extensions A) := by
  rw [← Thorp.Specht.tabloid_card_mul r]
  exact Nat.mul_le_mul (Thorp.Specht.tabloid_card_le r m hm) (fiberPerm_le_extensions A r hr)

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma extensions_card_orderIso {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) : Fintype.card (Extensions A) = Fintype.card (Extensions B) := by
  let c := finCongr (Fintype.card_congr e.toEquiv)
  let F : Extensions A ≃ Extensions B := {
    toFun := fun l => ⟨(e.symm.toEquiv.trans l.val).trans c, fun _ _ h => l.property (e.symm.strictMono h)⟩
    invFun := fun l => ⟨(e.toEquiv.trans l.val).trans c.symm, fun _ _ h => l.property (e.strictMono h)⟩
    left_inv := by intro l; apply Subtype.ext; ext x; simp [c]
    right_inv := by intro l; apply Subtype.ext; ext x; simp [c] }
  exact Fintype.card_congr F

lemma rank_strictMono (D : YoungDiagram) : StrictMono (fun x : Cells D => x.val.1 + x.val.2) := by
  intro x y hxy
  have hle := hxy.le
  have hn : x.val ≠ y.val := fun h => hxy.ne (Subtype.ext h)
  have he : x.val.1 ≠ y.val.1 ∨ x.val.2 ≠ y.val.2 := by
    by_contra hh
    push Not at hh
    exact hn (Prod.ext hh.1 hh.2)
  change x.val.1 + x.val.2 < y.val.1 + y.val.2
  rcases he with he | he <;> have := hle.1 <;> have := hle.2 <;> omega

lemma coord_lt_longest (D : YoungDiagram) (x : Cells D) :
    x.val.1 < longest D ∧ x.val.2 < longest D := by
  constructor
  · exact (YoungDiagram.mem_iff_lt_colLen.mp (D.up_left_mem le_rfl (Nat.zero_le _) x.property)).trans_le (le_max_right _ _)
  · exact (YoungDiagram.mem_iff_lt_rowLen.mp (D.up_left_mem (Nat.zero_le _) le_rfl x.property)).trans_le (le_max_left _ _)

theorem factorial_le_rank_degree {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Cells D) :
    n.factorial ≤ (2 * longest D) ^ n * Module.finrank ℂ (Thorp.Specht.module D t).toSubmodule := by
  have hh := rank_extension_bound (Cells D) (fun x => x.val.1 + x.val.2) (rank_strictMono D)
    (2 * longest D) (fun x => by have := coord_lt_longest D x; omega)
  have hc : Fintype.card (Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  rw [hc] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Thorp.Specht.extensions_card_le_degree D t))

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ExtensionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma extensions_card_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨c⟩ := extensions_nonempty (sᶜ : Set A)
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions s) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr e.val c.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions s) (x : s) : (F e x).val = (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions s) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (c.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions s) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact e.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (e.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (c.property hxy) _
  let f (e : Extensions s) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  simpa only [hFs] using hh

lemma extensions_card_compl_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions (sᶜ : Set A)) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions (sᶜ : Set A)) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr a.val e.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions (sᶜ : Set A)) (x : s) : (F e x).val = (a.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions (sᶜ : Set A)) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions (sᶜ : Set A)) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact a.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (a.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (e.property hxy) _
  let f (e : Extensions (sᶜ : Set A)) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  have h := congrArg (fun z : ℕ => z - Fintype.card s) hh
  simpa only [hFc, Nat.add_sub_cancel_left] using h

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma choose_le_extensions_split (s : Set A)
    (hs : ∀ x y : A, x < y → (x ∈ s ↔ y ∈ s)) :
    (Fintype.card A).choose (Fintype.card s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  obtain ⟨b⟩ := extensions_nonempty (sᶜ : Set A)
  let I := {S : Finset (Fin (Fintype.card A)) // S.card = Fintype.card s}
  have hi : Fintype.card I = (Fintype.card A).choose (Fintype.card s) := by
    calc
      Fintype.card I = ((Finset.univ : Finset (Fin (Fintype.card A))).powersetCard (Fintype.card s)).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext S
        simp
      _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let P (S : I) : Set (Fin (Fintype.card A)) := S.val
  have hP (S : I) : Fintype.card (P S) = Fintype.card s := by
    simpa [P] using S.property
  have hC (S : I) : Fintype.card ((P S)ᶜ : Set (Fin (Fintype.card A))) =
      Fintype.card (sᶜ : Set A) := by
    have h₁ := Fintype.card_congr (Equiv.Set.sumCompl (P S))
    have h₂ := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum, Fintype.card_fin, hP] at h₁ h₂
    omega
  let ea (S : I) := (Fintype.orderIsoFinOfCardEq (P S) (hP S))
  let eb (S : I) := (Fintype.orderIsoFinOfCardEq ((P S)ᶜ : Set _) (hC S))
  let F (S : I) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans
      (Equiv.sumCongr (a.val.trans (ea S).toEquiv) (b.val.trans (eb S).toEquiv))).trans
        (Equiv.Set.sumCompl (P S))
  have hFa (S : I) (x : s) : F S x = (ea S (a.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFb (S : I) (x : (sᶜ : Set A)) : F S x = (eb S (b.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hFm (S : I) (x : A) : F S x ∈ P S ↔ x ∈ s := by
    by_cases hx : x ∈ s
    · rw [hFa S ⟨x, hx⟩]
      exact iff_of_true (ea S (a.val ⟨x, hx⟩)).property hx
    · rw [hFb S ⟨x, hx⟩]
      exact iff_of_false (eb S (b.val ⟨x, hx⟩)).property hx
  have hF (S : I) : StrictMono (F S) := by
    intro x y hxy
    by_cases hx : x ∈ s
    · have hy := (hs x y hxy).mp hx
      rw [hFa S ⟨x, hx⟩, hFa S ⟨y, hy⟩]
      exact (ea S).strictMono (a.property hxy)
    · have hy : y ∉ s := fun h => hx ((hs x y hxy).mpr h)
      rw [hFb S ⟨x, hx⟩, hFb S ⟨y, hy⟩]
      exact (eb S).strictMono (b.property hxy)
  let f (S : I) : Extensions A := ⟨F S, hF S⟩
  rw [← hi]
  apply Fintype.card_le_of_injective f
  intro S T hST
  apply Subtype.ext
  ext z
  obtain ⟨x, rfl⟩ := (F S).surjective z
  have he : F S x = F T x := congrArg (fun e : Extensions A => e.val x) hST
  change F S x ∈ P S ↔ F S x ∈ P T
  rw [hFm, he, hFm]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma topPrefix_lower (D : YoungDiagram) (u : ℕ) : IsLowerSet (topPrefix D u) := by
  intro y x hxy hy
  change y.val.1 = 0 ∧ y.val.2 < u at hy
  change x.val.1 = 0 ∧ x.val.2 < u
  exact ⟨by have := hxy.1; omega, lt_of_le_of_lt hxy.2 hy.2⟩

lemma card_topPrefix (D : YoungDiagram) (u : ℕ) (hu : u ≤ D.rowLen 0) :
    Fintype.card (topPrefix D u) = u := by
  let e : topPrefix D u ≃ Fin u := {
    toFun := fun x => ⟨x.val.val.2, x.property.2⟩
    invFun := fun j => ⟨⟨(0, j), YoungDiagram.mem_iff_lt_rowLen.mpr (j.isLt.trans_le hu)⟩, rfl, j.isLt⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.1.symm rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin u)

lemma card_lower_add (D : YoungDiagram) :
    D.rowLen 0 + Fintype.card (Lower D) = Fintype.card (Cells D) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun x : Cells D => x.val.1 = 0))
  simpa only [Fintype.card_sum, card_row_subtype] using h

lemma lower_col_lt (D : YoungDiagram) (x : Lower D) : x.val.val.2 < Fintype.card (Lower D) := by
  let f : Fin (x.val.val.2 + 1) → Lower D := fun j =>
    ⟨⟨(1, j), D.up_left_mem (i2 := x.val.val.1) (j2 := x.val.val.2) (by have := x.property; omega) (by have := j.isLt; omega) x.val.property⟩, by simp⟩
  have hf : Function.Injective f := by
    intro j k hjk
    exact Fin.ext (congrArg (fun z : Lower D => z.val.val.2) hjk)
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hh
  omega

theorem choose_row_le_extensions (D : YoungDiagram)
    (hu : Fintype.card (Lower D) ≤ D.rowLen 0) :
    (D.rowLen 0).choose (Fintype.card (Lower D)) ≤ Fintype.card (Extensions (Cells D)) := by
  let u := Fintype.card (Lower D)
  let s := topPrefix D u
  let A := (sᶜ : Set (Cells D))
  let r : Set A := {x | x.val.val.1 ≠ 0}
  have hc : Fintype.card A = D.rowLen 0 := by
    have hh := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum] at hh
    have hs : Fintype.card s = u := card_topPrefix D u hu
    have hl := card_lower_add D
    change D.rowLen 0 + u = Fintype.card (Cells D) at hl
    change Fintype.card s + Fintype.card A = Fintype.card (Cells D) at hh
    omega
  let e : r ≃ Lower D := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, fun h => x.property h.1⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hr : Fintype.card r = u := Fintype.card_congr e
  have hsplit : ∀ x y : A, x < y → (x ∈ r ↔ y ∈ r) := by
    intro x y hxy
    have h₁ := hxy.le.1
    have h₂ := hxy.le.2
    change x.val.val.1 ≠ 0 ↔ y.val.val.1 ≠ 0
    constructor
    · intro hx hy; exact hx (by omega)
    · intro hy hx
      have hcol := lower_col_lt D ⟨y.val, hy⟩
      have hp := x.property
      change ¬(x.val.val.1 = 0 ∧ x.val.val.2 < u) at hp
      change y.val.val.2 < u at hcol
      exact hp ⟨hx, lt_of_le_of_lt h₂ hcol⟩
  have hh := choose_le_extensions_split r hsplit
  have hrN : Nat.card r = u := by simpa only [Fintype.card_eq_nat_card] using hr
  have hcN : Nat.card A = D.rowLen 0 := by simpa only [Fintype.card_eq_nat_card] using hc
  have hh' : (D.rowLen 0).choose u ≤ Fintype.card (Extensions A) := by
    simpa only [Fintype.card_eq_nat_card, hrN, hcN] using hh
  exact hh'.trans (extensions_card_compl_ideal s (topPrefix_lower D u))

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PartitionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma idealDiagram_extensions_le (D : YoungDiagram) (s : Set (Cells D)) (hs : IsLowerSet s) :
    Fintype.card (Extensions (Cells (idealDiagram D s hs))) ≤ Fintype.card (Extensions (Cells D)) := by
  rw [extensions_card_orderIso (idealCells D s hs)]
  exact extensions_card_ideal s hs

theorem exists_trimLower (D : YoungDiagram) (k : ℕ) (hk : k ≤ Fintype.card (Lower D)) :
    ∃ E : YoungDiagram, E.rowLen 0 = D.rowLen 0 ∧ Fintype.card (Lower E) = k ∧
      Fintype.card (Extensions (Cells E)) ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨e⟩ := extensions_nonempty (Lower D)
  let s : Set (Cells D) := {x | ∀ h : x.val.1 ≠ 0, (e.val ⟨x, h⟩).val < k}
  have hs : IsLowerSet s := by
    intro y x hxy hy hx
    have hy' : y.val.1 ≠ 0 := by have := hxy.1; omega
    exact lt_of_le_of_lt (e.property.monotone (show (⟨x, hx⟩ : Lower D) ≤ ⟨y, hy'⟩ from hxy)) (hy hy')
  let E := idealDiagram D s hs
  have htop : E.rowLen 0 = D.rowLen 0 := by
    apply eq_of_forall_lt_iff
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_iff_lt_rowLen]
    change (0, j) ∈ idealDiagram D s hs ↔ (0, j) ∈ D
    rw [mem_idealDiagram]
    exact ⟨fun h => h.choose, fun h => ⟨h, fun hn => (hn rfl).elim⟩⟩
  let f : Lower E ≃ Fin k := {
    toFun := fun x =>
      let z := idealCells D s hs x.val
      ⟨(e.val ⟨z.val, x.property⟩).val, z.property x.property⟩
    invFun := fun j =>
      let z := e.val.symm ⟨j.val, j.isLt.trans_le hk⟩
      ⟨(idealCells D s hs).symm ⟨z.val, by
        intro h
        have hh : (⟨z.val, h⟩ : Lower D) = z := rfl
        rw [hh, Equiv.apply_symm_apply]
        exact j.isLt⟩, z.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply (idealCells D s hs).injective
      apply Subtype.ext
      have hh := e.val.symm_apply_apply ⟨(idealCells D s hs x.val).val, x.property⟩
      simpa only [OrderIso.apply_symm_apply] using congrArg Subtype.val hh
    right_inv := by
      intro j
      apply Fin.ext
      simpa only [OrderIso.apply_symm_apply] using congrArg Fin.val (e.val.apply_symm_apply ⟨j.val, j.isLt.trans_le hk⟩) }
  exact ⟨E, htop, (Fintype.card_congr f).trans (Fintype.card_fin k), idealDiagram_extensions_le D s hs⟩

theorem choose_le_extensions (D : YoungDiagram) (k : ℕ)
    (hk : k ≤ Fintype.card (Lower D)) (hL : k ≤ D.rowLen 0) :
    (D.rowLen 0).choose k ≤ Fintype.card (Extensions (Cells D)) := by
  obtain ⟨E, htop, hsize, hle⟩ := exists_trimLower D k hk
  have hh := choose_row_le_extensions E (by rw [hsize, htop]; exact hL)
  rw [htop, hsize] at hh
  exact hh.trans hle

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma partition_count_le_pow (n : ℕ) : Fintype.card (Nat.Partition n) ≤ 2 ^ n := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition n) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

lemma rectangle_card_le (D : YoungDiagram) (x : Cells D) :
    (x.val.1 + 1) * (x.val.2 + 1) ≤ Fintype.card (Cells D) := by
  let f : Fin (x.val.1 + 1) × Fin (x.val.2 + 1) → Cells D := fun p =>
    ⟨(p.1, p.2), D.up_left_mem (i2 := x.val.1) (j2 := x.val.2)
      (by have := p.1.isLt; omega) (by have := p.2.isLt; omega) x.property⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z : Cells D => z.val.1) hpq
    · exact congrArg (fun z : Cells D => z.val.2) hpq
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma cell_small_coord (D : YoungDiagram) (x : Cells D) :
    x.val.1 < Nat.sqrt (Fintype.card (Cells D)) ∨ x.val.2 < Nat.sqrt (Fintype.card (Cells D)) := by
  by_contra h
  push Not at h
  have hh := rectangle_card_le D x
  have hs := Nat.lt_succ_sqrt' (Fintype.card (Cells D))
  have hm := Nat.mul_le_mul (Nat.succ_le_succ h.1) (Nat.succ_le_succ h.2)
  nlinarith

lemma rowLen_le_card (D : YoungDiagram) (i : ℕ) : D.rowLen i ≤ Fintype.card (Cells D) := by
  rw [← card_row_subtype D i]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ Fintype.card (Cells D) := by
  rw [← card_column D j]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

theorem partition_count_le_sqrt_pow (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ (n + 1) ^ (2 * Nat.sqrt n) := by
  let F (p : Nat.Partition n) : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) :=
    (fun i => ⟨(ofPartition p).rowLen i, by
      have := rowLen_le_card (ofPartition p) i
      rw [card_ofPartition] at this
      omega⟩,
     fun j => ⟨(ofPartition p).colLen j, by
      have := colLen_le_card (ofPartition p) j
      rw [card_ofPartition] at this
      omega⟩)
  have hf : Function.Injective F := by
    intro p q hpq
    apply ofPartition_injective
    apply YoungDiagram.ext
    ext z
    have aux (p q : Nat.Partition n) (hpq : F p = F q) (hz : z ∈ ofPartition p) : z ∈ ofPartition q := by
      have hs := cell_small_coord (ofPartition p) ⟨z, hz⟩
      rw [card_ofPartition] at hs
      rcases hs with hs | hs
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.1 ⟨z.1, hs⟩).val) hpq
        change (ofPartition p).rowLen z.1 = (ofPartition q).rowLen z.1 at he
        apply YoungDiagram.mem_iff_lt_rowLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_rowLen.mp hz
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.2 ⟨z.2, hs⟩).val) hpq
        change (ofPartition p).colLen z.2 = (ofPartition q).colLen z.2 at he
        apply YoungDiagram.mem_iff_lt_colLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_colLen.mp hz
    exact ⟨aux p q hpq, aux q p hpq.symm⟩
  have hh := Fintype.card_le_of_injective F hf
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add] using hh

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma pow_le_choose_mul (a k : ℕ) : a ^ k ≤ (k * a).choose k := by
  let X := Fin k × Fin a
  let S := {s : Finset X // s.card = k}
  let f (v : Fin k → Fin a) : S := ⟨Finset.univ.image (fun i => (i, v i)), by
    rw [Finset.card_image_of_injective _ (by intro i j h; exact congrArg Prod.fst h), Finset.card_univ, Fintype.card_fin]⟩
  have hf : Function.Injective f := by
    intro v w hvw
    funext i
    have he := congrArg Subtype.val hvw
    have hm : (i, v i) ∈ (f w).val := by rw [← he]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hS : Fintype.card S = (k * a).choose k := by
    calc
      _ = ((Finset.univ : Finset X).powersetCard k).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext s
        simp
      _ = _ := by simp [X]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_fin, hS] using hh

lemma pow_le_choose_of_mul_le (a k L : ℕ) (h : a * k ≤ L) : a ^ k ≤ L.choose k := by
  exact (pow_le_choose_mul a k).trans (Nat.choose_le_choose k (by simpa only [Nat.mul_comm] using h))

lemma sub_add_one_le_choose (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : n - k + 1 ≤ n.choose k := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkn
  simp only [Nat.add_sub_cancel_left]
  induction r with
  | zero => simp
  | succ r ih =>
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [show j + 1 + (r + 1) = (j + 1 + r) + 1 by omega, Nat.choose_succ_succ]
      have hp : 1 ≤ (j + 1 + r).choose j := Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero (by omega))
      simp only [Nat.succ_eq_add_one] at ih ⊢
      omega

end Thorp.Young

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma rowTail_ext {D E : YoungDiagram} (hrow : D.rowLen 0 = E.rowLen 0) (ht : rowTail D = rowTail E) : D = E := by
  apply YoungDiagram.ext
  ext p
  rcases p with ⟨i, j⟩
  cases i with
  | zero => simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hrow]
  | succ i => simp only [YoungDiagram.mem_cells, ← mem_rowTail, ht]

lemma orient_rowLen (D : YoungDiagram) : (orient D).rowLen 0 = longest D := by
  unfold orient longest
  split_ifs with h
  · exact (max_eq_left h).symm
  · rw [YoungDiagram.rowLen_transpose, max_eq_right (by omega)]

lemma orient_card (D : YoungDiagram) : Fintype.card (Cells (orient D)) = Fintype.card (Cells D) := by
  unfold orient
  split_ifs
  · rfl
  · exact (Fintype.card_congr (transposeCells D).toEquiv).symm

lemma orient_extensions (D : YoungDiagram) :
    Fintype.card (Extensions (Cells (orient D))) = Fintype.card (Extensions (Cells D)) := by
  by_cases h : D.colLen 0 ≤ D.rowLen 0
  · exact congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E))) (show orient D = D by simp [orient, h])
  · exact (congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E)))
      (show orient D = D.transpose by simp [orient, h])).trans
      (extensions_card_orderIso (transposeCells D)).symm

lemma recover_orientation (D : YoungDiagram) :
    (if orientation D then orient D else (orient D).transpose) = D := by
  unfold orientation orient
  split_ifs <;> simp_all

lemma longest_le_card (D : YoungDiagram) : longest D ≤ Fintype.card (Cells D) :=
  max_le (rowLen_le_card D 0) (colLen_le_card D 0)

theorem defect_count_le (n u : ℕ) :
    Fintype.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤
      2 * Fintype.card (Nat.Partition u) := by
  let T := {p : Nat.Partition n // n - longest (ofPartition p) = u}
  have hcard (p : T) : Fintype.card (Cells (rowTail (orient (ofPartition p.val)))) = u := by
    rw [Fintype.card_congr (rowTailCells _)]
    have hh := card_lower_add (orient (ofPartition p.val))
    rw [orient_rowLen, orient_card, card_ofPartition] at hh
    have hp := p.property
    omega
  let f (p : T) : Bool × Nat.Partition u :=
    (orientation (ofPartition p.val), toPartition (rowTail (orient (ofPartition p.val))) u (hcard p))
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply ofPartition_injective
    have hflag : orientation (ofPartition p.val) = orientation (ofPartition q.val) := congrArg Prod.fst hpq
    have ht : rowTail (orient (ofPartition p.val)) = rowTail (orient (ofPartition q.val)) := by
      have he := congrArg (fun z : Bool × Nat.Partition u => ofPartition z.2) hpq
      simpa only [f, of_toPartition] using he
    have hr : (orient (ofPartition p.val)).rowLen 0 = (orient (ofPartition q.val)).rowLen 0 := by
      simp only [orient_rowLen]
      have hp := p.property
      have hq := q.property
      have hp' := longest_le_card (ofPartition p.val)
      have hq' := longest_le_card (ofPartition q.val)
      rw [card_ofPartition] at hp' hq'
      omega
    have ho := rowTail_ext hr ht
    rw [← recover_orientation (ofPartition p.val), ← recover_orientation (ofPartition q.val), hflag, ho]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_bool] using hh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma diagram_card {n : ℕ} (p : NShape n) : Fintype.card (Cells (ofPartition p)) = n := by
  simpa only [Fintype.card_fin] using card_ofPartition p

lemma defect_add_longest {n : ℕ} (p : NShape n) : defect p + longest (ofPartition p) = n := by
  have h := longest_le_card (ofPartition p)
  rw [diagram_card] at h
  exact Nat.sub_add_cancel h

lemma choose_longest_le_degree {n : ℕ} (p : NShape n) (k : ℕ)
    (hk : k ≤ defect p) (hL : k ≤ longest (ofPartition p)) :
    (longest (ofPartition p)).choose k ≤ degree p := by
  have hc : Fintype.card (Lower (orient (ofPartition p))) = defect p := by
    have hh := card_lower_add (orient (ofPartition p))
    rw [orient_rowLen, orient_card, diagram_card] at hh
    have hd := defect_add_longest p
    omega
  have hh := choose_le_extensions (orient (ofPartition p)) k (by rwa [hc]) (by rwa [orient_rowLen])
  rw [orient_rowLen, orient_extensions] at hh
  exact hh.trans (extensions_le_degree p)

lemma small_defect_degree {n : ℕ} (p : NShape n) (h : 4 * defect p ≤ n) :
    3 ^ defect p ≤ degree p := by
  have hd := defect_add_longest p
  exact (pow_le_choose_of_mul_le 3 _ _ (by omega)).trans
    (choose_longest_le_degree p _ le_rfl (by omega))

lemma fixed_defect_degree {n : ℕ} (p : NShape n) (hp : 0 < defect p) (h : 2 * defect p ≤ n) :
    n - 2 * defect p + 1 ≤ degree p := by
  have hd := defect_add_longest p
  have hh := sub_add_one_le_choose (longest (ofPartition p)) (defect p) hp (by omega)
  have he : longest (ofPartition p) - defect p = n - 2 * defect p := by omega
  rw [he] at hh
  exact hh.trans (choose_longest_le_degree p _ le_rfl (by omega))

lemma factorial_third_bound (n : ℕ) : ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  rcases n with _ | n
  · norm_num
  have hn : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (n + 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have he : (n + 1 : ℝ) / 3 ≤ (n + 1) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1) Real.exp_one_lt_three.le
  have hh := Stirling.le_factorial_stirling (n + 1)
  push_cast at hh
  simpa only [Nat.cast_add, Nat.cast_one] using (pow_le_pow_left₀ (by positivity) he (n+1)).trans
    ((le_mul_of_one_le_left (by positivity) hs).trans hh)

lemma small_longest_degree {n : ℕ} (p : NShape n) (hn : 0 < n)
    (hL : 8 * longest (ofPartition p) ≤ n) :
    (4 / 3 : ℝ) ^ n ≤ degree p := by
  have hf := factorial_le_rank_degree (ofPartition p) (canonicalTableau p)
  have hf' : (n.factorial : ℝ) ≤ (2 * (longest (ofPartition p) : ℝ)) ^ n * (degree p : ℝ) := by
    exact_mod_cast hf
  have he : (2 * (longest (ofPartition p) : ℝ)) ≤ (n : ℝ) / 4 := by
    have hh : (8 : ℝ) * longest (ofPartition p) ≤ n := by exact_mod_cast hL
    linarith
  have hd : (0 : ℝ) ≤ degree p := Nat.cast_nonneg _
  have hh := (factorial_third_bound n).trans (hf'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he n) hd))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : ((n : ℝ) / 3) ^ n = ((n : ℝ) / 4) ^ n * (4 / 3 : ℝ)^n := by rw [← mul_pow]; congr 1; ring
  rw [hid] at hh
  exact le_of_mul_le_mul_left hh (pow_pos (by positivity : (0 : ℝ) < n / 4) n)

lemma bulk_degree {n : ℕ} (p : NShape n) (hn : 0 < n) (hu : n < 4 * defect p) :
    (2 : ℝ) ^ (n / 16) ≤ degree p := by
  by_cases hL : 8 * longest (ofPartition p) ≤ n
  · have hh : (2 : ℝ) ^ (n / 16) ≤ (4 / 3 : ℝ)^n := by
      have hbase : (2 : ℝ) ≤ (4 / 3 : ℝ)^16 := by norm_num
      calc
        _ ≤ ((4 / 3 : ℝ)^16)^(n/16) := pow_le_pow_left₀ (by norm_num) hbase _
        _ = (4 / 3 : ℝ)^(16 * (n/16)) := by rw [pow_mul]
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    exact hh.trans (small_longest_degree p hn hL)
  · have hd := defect_add_longest p
    have hk : n / 16 ≤ defect p := by omega
    have hm : 2 * (n / 16) ≤ longest (ofPartition p) := by omega
    exact_mod_cast (pow_le_choose_of_mul_le 2 _ _ hm).trans
      (choose_longest_le_degree p _ hk (by omega))

lemma defect_card_bound (n u : ℕ) :
    Fintype.card {p : NShape n // defect p = u} ≤ 2 ^ (u + 1) := by
  have hh : Nat.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤ 2 ^ (u+1) := by
    rw [← Fintype.card_eq_nat_card]
    calc
      _ ≤ 2 * Fintype.card (Nat.Partition u) := defect_count_le n u
      _ ≤ 2 * 2^u := Nat.mul_le_mul_left 2 (partition_count_le_pow u)
      _ = _ := by ring
  rw [Fintype.card_eq_nat_card]
  change Nat.card {p : Nat.Partition (Fintype.card (Fin n)) // n - longest (ofPartition p) = u} ≤ _
  have he (m k : ℕ) (h : m = k) :
      Nat.card {p : Nat.Partition m // n - longest (ofPartition p) = u} =
      Nat.card {p : Nat.Partition k // n - longest (ofPartition p) = u} := by subst k; rfl
  exact (he _ _ (Fintype.card_fin n)).trans_le hh

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ReciprocalDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open Filter Topology

namespace Thorp.Analysis

lemma sqrt_log_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log (n + 1) ≤ c * Real.sqrt (n + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp ht
  have he := h.eventually (gt_mem_nhds hc)
  filter_upwards [he] with n hn
  dsimp only [Function.comp_apply] at hn
  rw [← Real.sqrt_eq_rpow] at hn
  exact ((div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))).mp hn).le

lemma partition_exponential_decay :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * Nat.sqrt n) / (4 : ℝ) ^ (n / 16)) atTop (𝓝 0) := by
  have hc : 0 < Real.log 4 / 256 := by positivity
  have he := sqrt_log_small (Real.log 4 / 256) hc
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.log 4 / 64) * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) _ ht
  filter_upwards [he, eventually_ge_atTop 32] with n hn hn32
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n + 1) := by
    apply Real.le_sqrt_of_sq_le
    have hh : ((Nat.sqrt n : ℝ)^2) ≤ n := by exact_mod_cast (show (Nat.sqrt n)^2 ≤ n by simpa only [pow_two] using Nat.sqrt_le n)
    linarith
  have hdiv : (n : ℝ) / 32 ≤ (n / 16 : ℕ) := by
    have hh : n ≤ 32 * (n / 16) := by omega
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr (by exact_mod_cast (by omega : n ≤ n / 16 * 32))
  have hp : 2 * (Nat.sqrt n : ℝ) * Real.log (n + 1) ≤ (Real.log 4 / 64) * n := by
    have hl : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by linarith)
    have h₁ := mul_le_mul_of_nonneg_right hs hl
    have h₂ := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg ((n : ℝ) + 1))
    have hh := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have hc0 : 0 ≤ Real.log 4 / 256 := hc.le
    have hsq : Real.sqrt (n + 1) * ((Real.log 4 / 256) * Real.sqrt (n + 1)) = (Real.log 4 / 256) * (n + 1) := by calc
      _ = (Real.log 4 / 256) * (Real.sqrt (n + 1))^2 := by ring
      _ = _ := by rw [hh]
    rw [hsq] at h₂
    have h₃ := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ 2 * n by linarith) hc0
    linarith only [h₁, h₂, h₃]
  have hq : -(Real.log 4 / 64) * n ≥
      (2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 4 := by
    push_cast
    have hh := mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    linarith
  calc
    _ = Real.exp ((2 * Nat.sqrt n : ℕ) * Real.log (n + 1) - (n / 16 : ℕ) * Real.log 4) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ _ := Real.exp_le_exp.mpr hq

end Thorp.Analysis

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

variable {n : ℕ}

lemma inverseDegree_nonneg (p : NShape n) : 0 ≤ inverseDegree p := by unfold inverseDegree; positivity
lemma slice_nonneg (n u : ℕ) : 0 ≤ slice n u := Finset.sum_nonneg (fun _ _ => inverseDegree_nonneg _)
lemma smallSlice_nonneg (n u : ℕ) : 0 ≤ smallSlice n u := by unfold smallSlice; split_ifs; exact slice_nonneg _ _; rfl

lemma slice_bound (n u : ℕ) (K : ℝ) (hK : 0 < K)
    (hk : ∀ p : NShape n, defect p = u → K ≤ degree p) :
    slice n u ≤ (2 : ℝ)^(u+1) / K^2 := by
  have hI (p : {p : NShape n // defect p = u}) : inverseDegree p.val ≤ (K^2)⁻¹ := by
    apply inv_anti₀ (pow_pos hK 2)
    exact pow_le_pow_left₀ hK.le (hk p.val p.property) 2
  calc
    _ ≤ ∑ _ : {p : NShape n // defect p = u}, (K^2)⁻¹ := Finset.sum_le_sum (fun p _ => hI p)
    _ = (Fintype.card {p : NShape n // defect p = u} : ℝ) * (K^2)⁻¹ := by simp
    _ ≤ (2 : ℝ)^(u+1) * (K^2)⁻¹ := mul_le_mul_of_nonneg_right (by exact_mod_cast defect_card_bound n u) (by positivity)
    _ = _ := rfl

lemma smallSlice_bound (n u : ℕ) : smallSlice n u ≤ 2 * (2 / 9 : ℝ)^u := by
  unfold smallSlice
  split_ifs with h
  · have hk : ∀ p : NShape n, defect p = u → (3 : ℝ)^u ≤ degree p := by
      intro p hp
      have hh := small_defect_degree p (by rw [hp]; exact h.2)
      rw [hp] at hh
      exact_mod_cast hh
    have hh := slice_bound n u (3^u) (by positivity) hk
    have he : (2 : ℝ)^(u+1) / (3^u)^2 = 2 * (2/9 :ℝ)^u := by
      rw [pow_succ, div_pow]
      have hp : ((3 : ℝ)^u) ^ 2 = 9^u := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      rw [hp]
      ring
    exact hh.trans_eq he
  · positivity

lemma smallSlice_tendsto (u : ℕ) : Tendsto (fun n => smallSlice n u) atTop (𝓝 0) := by
  by_cases hu : 0 < u
  · have ht : Tendsto (fun n : ℕ => ((n - 2*u + 1 : ℕ) : ℝ)) atTop atTop := by
      exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        ((tendsto_add_atTop_nat 1).comp (tendsto_sub_atTop_nat (2*u)))
    have hi : Tendsto (fun n : ℕ => (((n - 2*u + 1 : ℕ) : ℝ)^2)⁻¹) atTop (𝓝 0) := by
      apply tendsto_inv_atTop_zero.comp
      simpa only [pow_two] using ht.atTop_mul_atTop₀ ht
    have he := hi.const_mul ((2 : ℝ)^(u+1))
    rw [mul_zero] at he
    apply squeeze_zero' (Eventually.of_forall (fun n => smallSlice_nonneg n u)) _ he
    filter_upwards [eventually_ge_atTop (4*u)] with n hn
    rw [smallSlice, ite_eq_left ⟨hu, hn⟩]
    exact slice_bound n u _ (by positivity) (fun p hp => by
      have hh := fixed_defect_degree p (by rwa [hp]) (by rw [hp]; omega)
      rw [hp] at hh
      exact_mod_cast hh)
  · simp only [smallSlice, hu, false_and, ↓reduceIte]
    exact tendsto_const_nhds

lemma smallSum_tendsto : Tendsto (fun n => ∑' u, smallSlice n u) atTop (𝓝 0) := by
  have hs : Summable (fun u : ℕ => 2 * (2/9 : ℝ)^u) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(2/9 : ℝ)‖ < 1)).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hs smallSlice_tendsto
    (Eventually.of_forall (fun n u => by rw [Real.norm_of_nonneg (smallSlice_nonneg n u)]; exact smallSlice_bound n u))
  simpa only [tsum_zero] using h

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
open Filter Topology Thorp.Young

lemma smallSlice_as_sum (n u : ℕ) :
    smallSlice n u = ∑ p : NShape n,
      if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0 := by
  unfold smallSlice slice
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = u)) (by simp), Finset.sum_filter]
  by_cases h : 0 < u ∧ 4 * u ≤ n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : defect p = u
    · simp only [hp, h.1, h.2, true_and, ↓reduceIte]
    · simp only [hp, false_and, ↓reduceIte]
  · rw [ite_eq_right h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with hp
    · exact (h (by simpa only [hp.1] using hp.2)).elim
    · rfl

lemma smallSlice_support (n u : ℕ) (hu : u ∉ Finset.range (n+1)) : smallSlice n u = 0 := by
  unfold smallSlice
  have hh : ¬(0 < u ∧ 4*u ≤ n) := by have := (Finset.mem_range.not.mp hu); omega
  exact ite_eq_right hh

lemma smallSum_eq (n : ℕ) :
    (∑' u, smallSlice n u) = ∑ p : NShape n,
      if 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0 := by
  rw [tsum_eq_sum (smallSlice_support n)]
  simp_rw [smallSlice_as_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hd : defect p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by have := defect_add_longest p; omega)
  have he (u : ℕ) : (if defect p = u ∧ 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0) =
      if defect p = u then (if 0 < defect p ∧ 4 * defect p ≤ n then inverseDegree p else 0) else 0 := by
    split_ifs <;> tauto
  simp only [he, Finset.sum_ite_eq, hd, ↓reduceIte]

lemma bulkSum_bound (n : ℕ) (hn : 0 < n) :
    (∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) ≤
      ((n : ℝ)+1)^(2*Nat.sqrt n) / (4:ℝ)^(n/16) := by
  have hb (p : NShape n) : (if n < 4*defect p then inverseDegree p else 0) ≤ ((4:ℝ)^(n/16))⁻¹ := by
    by_cases hp : n < 4*defect p
    · rw [ite_eq_left hp]
      have hh := bulk_degree p hn hp
      have he : ((2 : ℝ)^(n/16))^2 = (4:ℝ)^(n/16) := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      apply inv_anti₀ (by positivity)
      change (4:ℝ)^(n/16) ≤ (degree p : ℝ)^2
      rw [← he]
      exact pow_le_pow_left₀ (by positivity) hh 2
    · rw [ite_eq_right hp]; positivity
  have hc : Fintype.card (NShape n) ≤ (n+1)^(2*Nat.sqrt n) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card (Nat.Partition (Fintype.card (Fin n))) ≤ _
    rw [Fintype.card_fin, ← Fintype.card_eq_nat_card]
    exact partition_count_le_sqrt_pow n
  calc
    _ ≤ ∑ _ : NShape n, ((4:ℝ)^(n/16))⁻¹ := Finset.sum_le_sum (fun p _ => hb p)
    _ = (Fintype.card (NShape n) : ℝ) * ((4:ℝ)^(n/16))⁻¹ := by simp
    _ ≤ ((n:ℝ)+1)^(2*Nat.sqrt n) * ((4:ℝ)^(n/16))⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := rfl

lemma exceptionalReciprocalSum_split (n : ℕ) : exceptionalReciprocalSum n =
    (∑' u, smallSlice n u) + (∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) := by
  rw [smallSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp_all
  all_goals omega

theorem exceptionalReciprocalSum_tendsto : Tendsto exceptionalReciprocalSum atTop (𝓝 0) := by
  have hb : Tendsto (fun n => ∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => Finset.sum_nonneg (fun p _ => by split_ifs; exact inverseDegree_nonneg p; rfl)))
      ((eventually_gt_atTop 0).mono (fun n hn => bulkSum_bound n hn)) Thorp.Analysis.partition_exponential_decay
  have he : exceptionalReciprocalSum = (fun n => (∑' u, smallSlice n u) + ∑ p : NShape n, if n < 4 * defect p then inverseDegree p else 0) := funext exceptionalReciprocalSum_split
  rw [he]
  simpa only [zero_add] using smallSum_tendsto.add hb

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Reynolds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uV uW uE uI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma reynolds_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    ∃ c : ℂ, reynolds ρ ρ A = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (reynoldsMap ρ ρ A)
  refine ⟨c, ?_⟩
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  exact hh.symm

lemma trace_reynolds (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (reynolds ρ ρ A) = LinearMap.trace ℂ V A := by
  simp only [reynolds, map_smul, map_sum]
  have hh (g : G) : LinearMap.trace ℂ V (ρ g ∘ₗ A ∘ₗ ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_comp_comm']
    rw [LinearMap.comp_assoc]
    have he : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by
      change ρ g⁻¹ * ρ g = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [he, LinearMap.comp_id]
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma reynolds_eq_trace (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V ≠ 0) (A : Module.End ℂ V) :
    reynolds ρ ρ A = (LinearMap.trace ℂ V A / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, hc⟩ := reynolds_scalar ρ A
  have ht := trace_reynolds ρ A
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hD : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hV
  rw [hc, ← ht, mul_div_cancel_right₀ _ hD]

section Unitary
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma inner_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) (x y : E) :
    ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  have hh := hu g x (ρ g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh.symm

theorem coefficient_second_moment (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (v w : E) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E := by
  have hh := congrArg (fun A : Module.End ℂ E => ⟪w, A w⟫_ℂ)
    (reynolds_eq_trace ρ hE (InnerProductSpace.rankOne ℂ v v).toLinearMap)
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    inner_smul_right, inner_sum, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, map_smul, inner_inv ρ hu,
    InnerProductSpace.trace_rankOne, LinearMap.id_apply] at hh
  have hc (g : G) : ⟪ρ g v, w⟫_ℂ * ⟪w, ρ g v⟫_ℂ = (‖⟪w, ρ g v⟫_ℂ‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm (ρ g v) w, Complex.conj_mul', Complex.ofReal_pow]
  simp only [hc, inner_self_eq_norm_sq_to_K] at hh
  have hr : (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 / Module.finrank ℂ E * ‖w‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using hh
  simpa only [div_mul_eq_mul_div] using hr

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

lemma integrated_delta (ρ : Representation ℂ G V) : integrated ρ delta = 1 := by
  simp [integrated, delta]

lemma integrated_sum {I : Type uI} (ρ : Representation ℂ G V) (s : Finset I) (f : I → G → ℂ) :
    integrated ρ (∑ i ∈ s, f i) = ∑ i ∈ s, integrated ρ (f i) := by
  simp only [integrated, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

lemma integrated_sub (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (f - k) = integrated ρ f - integrated ρ k := by
  simp only [integrated, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma integrated_convolution (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (convolution f k) = integrated ρ f * integrated ρ k := by
  simp only [integrated, convolution, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have he := Equiv.sum_comp (Equiv.mulLeft g) (fun x => (f g * k (g⁻¹ * x)) • ρ x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul]

lemma integrated_central (ρ : Representation ℂ G V) (f : G → ℂ)
    (hf : ∀ g h, f (h * g * h⁻¹) = f g) (h : G) :
    integrated ρ f * ρ h = ρ h * integrated ρ f := by
  rw [integrated, Finset.sum_mul, Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h |>.trans (Equiv.mulRight h⁻¹))
    (fun g => (f g • ρ g) * ρ h)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hf,
    smul_mul_assoc, mul_smul_comm, ← map_mul, inv_mul_cancel_right]

lemma central_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (f : G → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g) :
    ∃ c : ℂ, integrated ρ f = c • LinearMap.id := by
  let A : Representation.IntertwiningMap ρ ρ :=
    (integrated ρ f).intertwiningMap_of_isIntertwiningMap ρ ρ (by
      intro g v
      exact congrArg (fun A : Module.End ℂ V => A v) (integrated_central ρ f hf g))
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective A
  exact ⟨c, (congrArg Representation.IntertwiningMap.toLinearMap hc).symm⟩

lemma trace_integrated (ρ : Representation ℂ G V) (f : G → ℂ) :
    LinearMap.trace ℂ V (integrated ρ f) = ∑ g, f g * ρ.character g := by
  simp only [integrated, map_sum, map_smul, smul_eq_mul, Representation.character]

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FourierFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE uV

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

attribute [instance] Family.finiteIndex Family.normed Family.innerSpace Family.finiteDim Family.irreducible

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma orthogonal (i j : F.Index) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹ =
      if i = j then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Fintype.card_eq_nat_card, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (F.distinct j i h).symm, fun h => by subst j; exact ⟨Representation.Equiv.refl _⟩⟩

lemma integrated_faithful (f : G → ℂ) (hf : ∀ i, integrated (F.rep i) f = 0) : f = 0 := by
  funext x
  have hh : ∑ i, (F.degree i : ℂ) * LinearMap.trace ℂ (F.Space i)
      (integrated (F.rep i) f * F.rep i x⁻¹) = 0 := by simp [hf]
  simp only [integrated, Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, smul_eq_mul] at hh
  change ∑ i, (F.degree i : ℂ) * ∑ g, f g * (F.rep i).character (g * x⁻¹) = 0 at hh
  simp_rw [Finset.mul_sum] at hh
  rw [Finset.sum_comm] at hh
  have he (g : G) : ∑ i, (F.degree i : ℂ) * (f g * (F.rep i).character (g * x⁻¹)) =
      f g * (if g * x⁻¹ = 1 then (Fintype.card G : ℂ) else 0) := by
    rw [← F.regular]
    simp only [Finset.mul_sum, degree]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [he, mul_inv_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hh
  exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast Fintype.card_ne_zero)

lemma integrated_injective (f k : G → ℂ) (h : ∀ i, integrated (F.rep i) f = integrated (F.rep i) k) : f = k := by
  apply sub_eq_zero.mp
  apply F.integrated_faithful
  intro i
  rw [integrated_sub, h i, sub_self]

lemma kernel_central (i : F.Index) (g h : G) : F.kernel i (h * g * h⁻¹) = F.kernel i g := by
  simp only [kernel, mul_inv_rev, inv_inv]
  rw [← mul_assoc, Representation.char_conj]

lemma integrated_kernel (i j : F.Index) : integrated (F.rep j) (F.kernel i) = if i = j then 1 else 0 := by
  obtain ⟨c, hc⟩ := central_scalar (F.rep j) (F.kernel i) (F.kernel_central i)
  have ht := congrArg (LinearMap.trace ℂ (F.Space j)) hc
  rw [trace_integrated, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hh : ∑ g, F.kernel i g * (F.rep j).character g =
      (F.degree i : ℂ) * (if j = i then 1 else 0) := by
    rw [← F.orthogonal j i]
    simp only [kernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  rw [hh] at ht
  have hd : (F.degree j : ℂ) ≠ 0 := by exact_mod_cast (F.positive j).ne'
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, mul_one] at ht ⊢
    have he : c = 1 := (mul_right_cancel₀ hd (ht.symm.trans (one_mul _).symm))
    simpa only [he, one_smul, Module.End.one_eq_id] using hc
  · simp only [ite_eq_right (Ne.symm hij), mul_zero] at ht
    have he : c = 0 := (mul_eq_zero.mp ht.symm).resolve_right hd
    simp only [ite_eq_right hij, hc, he, zero_smul]

lemma kernel_convolution (i j : F.Index) : convolution (F.kernel i) (F.kernel j) =
    if i = j then F.kernel i else 0 := by
  apply F.integrated_injective
  intro k
  rw [integrated_convolution, F.integrated_kernel, F.integrated_kernel]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, integrated_kernel]
    split_ifs <;> simp
  · rw [ite_eq_right hij]
    simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    by_cases hik : i = k
    · subst k; simp [Ne.symm hij]
    · simp [hik]

lemma kernel_sum : (∑ i, F.kernel i) = delta := by
  apply F.integrated_injective
  intro j
  rw [integrated_sum, integrated_delta]
  simp only [integrated_kernel, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] in
lemma character_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  let b := stdOrthonormalBasis ℂ E
  simp only [Representation.character, LinearMap.trace_eq_sum_inner _ b, map_sum,
    inner_inv ρ hu, inner_conj_symm]

omit [FiniteDimensional ℂ E] in
lemma integrated_symmetric (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (f : G → ℂ) (hf : ∀ g, conj (f g⁻¹) = f g) : (integrated ρ f).IsSymmetric := by
  intro x y
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  have he := Equiv.sum_comp (Equiv.inv G) (fun g => conj (f g) * ⟪ρ g x, y⟫_ℂ)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.inv_apply, hf]
  rw [← inner_inv ρ hu, inv_inv]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma kernel_star (i : F.Index) (g : G) : conj (F.kernel i g⁻¹) = F.kernel i g := by
  simp only [kernel, inv_inv, map_mul, map_inv₀, map_natCast, character_inv _ (F.unitary i)]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

lemma kernel_sum_sq (s : Finset F.Index) :
    (Fintype.card G : ℝ) * ∑ g, ‖∑ i ∈ s, F.kernel i g‖ ^ 2 = ∑ i ∈ s, (F.degree i : ℝ) ^ 2 := by
  have hh (i j : F.Index) : (Fintype.card G : ℂ) * ∑ g, conj (F.kernel i g) * F.kernel j g =
      if i = j then (F.degree i : ℂ) ^ 2 else 0 := by
    have hc : ∀ g, conj (F.kernel i g) =
        (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g := by
      intro g
      calc
        _ = F.kernel i g⁻¹ := by simpa only [inv_inv] using F.kernel_star i g⁻¹
        _ = _ := by rw [kernel, inv_inv]
    simp_rw [hc]
    simp only [kernel]
    have he : (Fintype.card G : ℂ) * ∑ g,
        ((F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g) *
          ((F.degree j : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep j).character g⁻¹) =
        (F.degree i : ℂ) * (F.degree j : ℂ) *
          ((Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      field_simp
    rw [he, F.orthogonal]
    split_ifs with h
    · subst j; ring
    · ring
  have he : (Fintype.card G : ℂ) * ∑ g, conj (∑ i ∈ s, F.kernel i g) * (∑ i ∈ s, F.kernel i g) =
      ∑ i ∈ s, (F.degree i : ℂ) ^ 2 := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    have hz (i : F.Index) : ∑ g, (Fintype.card G : ℂ) * (conj (F.kernel i g) * F.kernel j g) =
        if i = j then (F.degree i : ℂ)^2 else 0 := by rw [← Finset.mul_sum, hh]
    simp only [hz, Finset.sum_ite_eq', hj, ↓reduceIte]
  simp only [Complex.conj_mul'] at he
  apply Complex.ofReal_injective
  push_cast
  exact he

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_JointProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

lemma complex_cauchy {I : Type uI} (s : Finset I) (a b : I → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have ht : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem coefficient_evaluation (ρ : Representation ℂ G E) (s : Finset F.Index)
    (v w : E) (hv : (∑ i ∈ s, F.projector ρ i) v = v) :
    (Fintype.card G : ℝ) * ‖⟪w, v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 := by
  have he : ⟪w, v⟫_ℂ = ∑ g, (∑ i ∈ s, F.kernel i g) * ⟪w, ρ g v⟫_ℂ := by
    conv_lhs => rw [← hv]
    conv_lhs => rw [show ∑ i ∈ s, F.projector ρ i = integrated ρ (∑ i ∈ s, F.kernel i) by
      simp only [projector, integrated_sum]]
    simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right,
      Finset.sum_apply]
  have hh := mul_le_mul_of_nonneg_left
    (complex_cauchy Finset.univ (fun g => ∑ i ∈ s, F.kernel i g) (fun g => ⟪w, ρ g v⟫_ℂ))
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  rw [← he, ← mul_assoc, F.kernel_sum_sq] at hh
  exact hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_sum : (∑ a : I → F.Index, F.jointKernel a) = delta := by
  funext g
  simp only [Finset.sum_apply, jointKernel]
  rw [← Fintype.prod_sum (fun i (j : F.Index) => F.kernel j (g i))]
  have hh (i : I) : ∑ j : F.Index, F.kernel j (g i) = if g i = 1 then 1 else 0 :=
    by simpa only [Finset.sum_apply, delta] using congrFun F.kernel_sum (g i)
  simp only [hh]
  by_cases hg : g = 1
  · subst g; simp [delta]
  · have hn : ∃ i, g i ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨i, hi⟩ := hn
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    simp [delta, hg]

lemma jointKernel_convolution (a b : I → F.Index) :
    convolution (F.jointKernel a) (F.jointKernel b) = if a = b then F.jointKernel a else 0 := by
  funext g
  simp only [convolution, jointKernel, Pi.mul_apply, Pi.inv_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (h : H) => F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i))]
  have hh (i : I) : ∑ h, F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i) =
      if a i = b i then F.kernel (a i) (g i) else 0 := by
    have he := congrFun (F.kernel_convolution (a i) (b i)) (g i)
    simpa only [convolution, ite_apply, Pi.zero_apply] using he
  simp only [hh]
  by_cases hab : a = b
  · subst b; simp only [↓reduceIte, jointKernel]
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hn; push Not at hn; exact hab (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma jointKernel_star (a : I → F.Index) (g : I → H) :
    conj (F.jointKernel a g⁻¹) = F.jointKernel a g := by
  simp only [jointKernel, map_prod, Pi.inv_apply, F.kernel_star]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma jointProjector_mul (ρ : Representation ℂ (I → H) E) (a b : I → F.Index) :
    F.jointProjector ρ a * F.jointProjector ρ b = if a = b then F.jointProjector ρ a else 0 := by
  rw [jointProjector, jointProjector, ← integrated_convolution, jointKernel_convolution]
  split_ifs <;> simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma jointProjector_idempotent (ρ : Representation ℂ (I → H) E) (a : I → F.Index) :
    IsIdempotentElem (F.jointProjector ρ a) := by
  simpa only [IsIdempotentElem, ↓reduceIte] using F.jointProjector_mul ρ a a

lemma jointProjector_sum (ρ : Representation ℂ (I → H) E) : ∑ a, F.jointProjector ρ a = 1 := by
  simp only [jointProjector]
  rw [← integrated_sum, F.jointKernel_sum, integrated_delta]

omit [Fintype I] in
lemma tensorList_character (a : I → F.Index) (l : List I) (g : I → H) :
    Representation.character (F.tensorList a l).ρ g = (l.map (fun i => (F.rep (a i)).character (g i))).prod := by
  induction l with
  | nil =>
    change LinearMap.trace ℂ ℂ (1 : Module.End ℂ ℂ) = 1
    simp
  | cons i l ih =>
    change (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ).character g = _
    rw [Representation.char_tensor ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ]
    change (F.rep (a i)).character (g i) * Representation.character (F.tensorList a l).ρ g = _
    rw [ih]
    rfl

lemma tensorFamily_character (a : I → F.Index) (g : I → H) :
    Representation.character (F.tensorFamily a).ρ g = ∏ i, (F.rep (a i)).character (g i) := by
  rw [tensorFamily, tensorList_character]
  exact Finset.prod_map_toList _ _

lemma jointKernel_formula (a : I → F.Index) (g : I → H) :
    F.jointKernel a g = (∏ i, (F.degree (a i) : ℂ)) * (Fintype.card (I → H) : ℂ)⁻¹ *
      Representation.character (F.tensorFamily a).ρ g⁻¹ := by
  simp only [jointKernel, kernel, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, tensorFamily_character, Pi.inv_apply, Fintype.card_fun, Nat.cast_pow, inv_pow]

lemma trace_jointProjector [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) : LinearMap.trace ℂ E (F.jointProjector ρ a) =
      (∏ i, (F.degree (a i) : ℂ)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
  let : Invertible (Nat.card (I → H) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [jointProjector, trace_integrated]
  simp only [jointKernel_formula]
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Finset.mul_sum, Fintype.card_eq_nat_card]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem joint_degree_le [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    (∏ i, F.degree (a i)) ≤ Module.finrank ℂ E := by
  have hp := F.jointProjector_idempotent ρ a
  have ht := F.trace_jointProjector ρ a
  rw [(LinearMap.IsIdempotentElem.isProj_range _ hp).trace] at ht
  have hm : Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) ≠ 0 := by
    intro hz
    have hh := F.trace_jointProjector ρ a
    rw [hz, Nat.cast_zero, mul_zero] at hh
    exact ha (LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hp hh)
  have hn : Module.finrank ℂ (LinearMap.range (F.jointProjector ρ a)) =
      (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
    exact_mod_cast ht
  calc
    _ ≤ (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
    _ = _ := hn.symm
    _ ≤ Module.finrank ℂ E := Submodule.finrank_le _

end Thorp.Fourier.Family

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ProductProjectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {H : Type uH} {I : Type uI} {E : Type uE} [Group H] [Fintype H] [Fintype I] [AddCommGroup E] [Module ℂ E]

lemma integrated_single_mul (ρ : Representation ℂ (I → H) E) (i : I) (k : H → ℂ) (f : (I → H) → ℂ) :
    integrated (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) k * integrated ρ f =
      integrated ρ (fun g => ∑ h, k h * f (Pi.mulSingle i h⁻¹ * g)) := by
  simp only [integrated, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have he := Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i h))
    (fun g : I → H => (k h * f (Pi.mulSingle i h⁻¹ * g)) • ρ g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  have hi : Pi.mulSingle i h⁻¹ = (Pi.mulSingle i h : I → H)⁻¹ :=
    (map_inv (MonoidHom.mulSingle (fun _ : I => H) i) h).symm.symm
  simp only [Equiv.coe_mulLeft, hi, inv_mul_cancel_left, smul_mul_smul,
    MonoidHom.comp_apply, MonoidHom.mulSingle_apply, map_mul]

end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_single (a : I → F.Index) (i : I) (h : H) (g : I → H) :
    F.jointKernel a (Pi.mulSingle i h * g) =
      F.kernel (a i) (h * g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) := by
  rw [jointKernel, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp only [Pi.mulSingle_eq_of_ne hji, one_mul]

lemma jointKernel_split (a : I → F.Index) (i : I) (g : I → H) :
    F.jointKernel a g = F.kernel (a i) (g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => F.kernel (a j) (g j)) (Finset.mem_univ i)).symm

lemma jointKernel_single_convolution (a : I → F.Index) (i : I) (b : F.Index) (g : I → H) :
    ∑ h, F.kernel b h * F.jointKernel a (Pi.mulSingle i h⁻¹ * g) =
      if b = a i then F.jointKernel a g else 0 := by
  simp only [F.jointKernel_single, ← mul_assoc, ← Finset.sum_mul]
  change convolution (F.kernel b) (F.kernel (a i)) (g i) * _ = _
  rw [F.kernel_convolution]
  split_ifs with hb
  · simp only [hb]
    exact (F.jointKernel_split a i g).symm
  · simp

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma projector_jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (b : F.Index) :
    F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b * F.jointProjector ρ a =
      if b = a i then F.jointProjector ρ a else 0 := by
  rw [projector, jointProjector, integrated_single_mul]
  simp only [F.jointKernel_single_convolution]
  split_ifs <;> simp only [integrated, zero_smul, Finset.sum_const_zero]

lemma low_fixes_joint (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (s : Finset F.Index) (ha : a i ∈ s) :
    (∑ b ∈ s, F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) * F.jointProjector ρ a =
      F.jointProjector ρ a := by
  rw [Finset.sum_mul]
  simp only [F.projector_jointProjector, Finset.sum_ite_eq', ha, ↓reduceIte]

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical

lemma norm_sum_sq_of_orthogonal {J : Type uJ} {E : Type uE} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : J → E)
    (hv : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have he : ⟪∑ i, v i, ∑ i, v i⟫_ℂ = ∑ i, ⟪v i, v i⟫_ℂ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => hv j i hji) (by simp)
  have hr := congrArg Complex.re he
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re] using hr

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

lemma leastFactor_le (a : I → F.Index) (i : I) :
    F.degree (a (F.leastFactor a)) ≤ F.degree (a i) :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun i => F.degree (a i)) Finset.univ_nonempty)).2 i (Finset.mem_univ i)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_symmetric (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (a : I → F.Index) :
    (F.jointProjector ρ a).IsSymmetric := integrated_symmetric ρ hu _ (F.jointKernel_star a)

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a b : I → F.Index) (hab : a ≠ b) (x y : E) :
    ⟪F.jointProjector ρ a x, F.jointProjector ρ b y⟫_ℂ = 0 := by
  rw [F.jointProjector_symmetric ρ hu a]
  change ⟪x, (F.jointProjector ρ a * F.jointProjector ρ b) y⟫_ℂ = 0
  rw [F.jointProjector_mul, ite_eq_right hab]
  simp

omit [FiniteDimensional ℂ E] in
lemma splitVector_sum (ρ : Representation ℂ (I → H) E) (v : E) :
    ∑ i, F.splitVector ρ v i = v := by
  simp only [splitVector]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← LinearMap.sum_apply, F.jointProjector_sum]
  rfl

omit [FiniteDimensional ℂ E] in
lemma splitVector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (v : E) (i j : I) (hij : i ≠ j) :
    ⟪F.splitVector ρ v i, F.splitVector ρ v j⟫_ℂ = 0 := by
  simp only [splitVector, sum_inner, inner_sum]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hai hbj
  · exact F.jointProjector_orthogonal ρ hu b a (by intro h; subst b; exact hij (hai.symm.trans hbj)) v v
  all_goals simp

omit [FiniteDimensional ℂ E] in
lemma splitVector_sq_sum (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (v : E) :
    ∑ i, ‖F.splitVector ρ v i‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← norm_sum_sq_of_orthogonal _ (F.splitVector_orthogonal ρ hu v), F.splitVector_sum]

lemma leastFactor_pow_le (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    F.degree (a (F.leastFactor a)) ^ Fintype.card I ≤ Module.finrank ℂ E := by
  calc
    _ = ∏ _ : I, F.degree (a (F.leastFactor a)) := by simp
    _ ≤ ∏ i, F.degree (a i) := Finset.prod_le_prod' (fun i _ => F.leastFactor_le a i)
    _ ≤ _ := F.joint_degree_le ρ a ha

lemma splitVector_low (ρ : Representation ℂ (I → H) E) (v : E) (i : I) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
      F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) (F.splitVector ρ v i) =
        F.splitVector ρ v i := by
  unfold splitVector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hai : F.leastFactor a = i
  · simp only [ite_eq_left hai]
    by_cases ha : F.jointProjector ρ a = 0
    · simp [ha]
    · have hb : a i ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [hai] using F.leastFactor_pow_le ρ a ha
      exact congrArg (fun f : Module.End ℂ E => f v) (F.low_fixes_joint ρ a i _ hb)
  · simp [hai]

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_CosetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uH uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

lemma coset_sum_reindex (φ : H →* G) (ν f : G → ℝ) :
    ∑ g, ν g * ∑ h, f (g * φ h) = ∑ g, (∑ h, ν (g * φ h)) * f g := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g h => ν (g * φ h) * f g)]
  have he := Equiv.sum_comp (Equiv.inv H) (fun h => ∑ g, ν (g * φ h) * f g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  have hh := Equiv.sum_comp (Equiv.mulRight ((φ h)⁻¹)) (fun g => ν g * f (g * φ h))
  rw [← hh]
  simp only [Equiv.coe_mulRight, Equiv.inv_apply, map_inv, inv_mul_cancel_right]

lemma weighted_coset_bound (φ : H →* G) (ν f : G → ℝ) (S C : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (hf : ∀ g, 0 ≤ f g) (hS : 0 ≤ S)
    (heval : ∀ g, (Fintype.card H : ℝ) * f g ≤ S * ∑ h, f (g * φ h))
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ C) :
    (Fintype.card H : ℝ) * ∑ g, ν g * f g ≤ S * C * ∑ g, f g := by
  calc
    _ = ∑ g, ν g * ((Fintype.card H : ℝ) * f g) := by rw [Finset.mul_sum]; congr 1; funext g; ring
    _ ≤ ∑ g, ν g * (S * ∑ h, f (g * φ h)) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (heval g) (hν g))
    _ = S * ∑ g, (∑ h, ν (g * φ h)) * f g := by
      rw [← coset_sum_reindex φ ν f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ S * ∑ g, C * f g := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_right (hcoset g) (hf g))) hS
    _ = _ := by rw [← Finset.mul_sum]; ring

namespace Family
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma coset_coefficient_evaluation (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (φ : H →* G) (s : Finset F.Index) (v w : E)
    (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) (g : G) :
    (Fintype.card H : ℝ) * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ h, ‖⟪w, ρ (g * φ h) v⟫_ℂ‖ ^ 2 := by
  have he := F.coefficient_evaluation (ρ.comp φ) s v (ρ g⁻¹ w) hv
  have hh (x : E) : ⟪ρ g⁻¹ w, x⟫_ℂ = ⟪w, ρ g x⟫_ℂ := by
    simpa only [inv_inv] using (inner_inv ρ hu g⁻¹ w x).symm
  simpa only [hh, MonoidHom.comp_apply, map_mul, Module.End.mul_apply] using he

theorem weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (φ : H →* G) (s : Finset F.Index) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ B * (Fintype.card H : ℝ) / Fintype.card G)
    (v w : E) (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      B * (∑ i ∈ s, (F.degree i : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  have hh := weighted_coset_bound φ ν (fun g => ‖⟪w, ρ g v⟫_ℂ‖ ^ 2)
    (∑ i ∈ s, (F.degree i : ℝ)^2) (B * (Fintype.card H : ℝ) / Fintype.card G)
    hν (fun _ => sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (F.coset_coefficient_evaluation ρ hu φ s v w hv) hcoset
  have hcG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hd : (Module.finrank ℂ E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hs := coefficient_second_moment ρ hu hE v w
  have hs' : ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      (Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E) := by
    calc
      _ = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2) := by field_simp
      _ = _ := by rw [hs]
  rw [hs'] at hh
  have he : (∑ i ∈ s, (F.degree i : ℝ)^2) * (B * (Fintype.card H : ℝ) / Fintype.card G) *
      ((Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E)) =
      (Fintype.card H : ℝ) * (B * (∑ i ∈ s, (F.degree i : ℝ)^2) /
        Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2)) := by field_simp
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hcH).mp hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical

lemma norm_weighted_sum_sq {J : Type uJ} [Fintype J] (ν : J → ℝ) (f : J → ℂ)
    (hν : ∀ j, 0 ≤ ν j) (h1 : ∑ j, ν j = 1) :
    ‖∑ j, (ν j : ℂ) * f j‖ ^ 2 ≤ ∑ j, ν j * ‖f j‖ ^ 2 := by
  have ht : ‖∑ j, (ν j : ℂ) * f j‖ ≤ ∑ j, ν j * ‖f j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν _)] using
      norm_sum_le Finset.univ (fun j => (ν j : ℂ) * f j)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := ν) (g := fun j => ν j * ‖f j‖ ^ 2) (r := fun j => ν j * ‖f j‖)
    (fun j _ => hν j) (fun j _ => mul_nonneg (hν j) (sq_nonneg _))
    (fun j _ => by nlinarith [sq_nonneg (ν j * ‖f j‖)])
  rw [h1, one_mul] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc

namespace Family
variable {G H I : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  [Fintype I] [Nonempty I] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem split_weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v w : E) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  let z := F.splitVector (ρ.comp ψ) v
  let s := Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E)
  let S : ℝ := ∑ b ∈ s, (F.degree b : ℝ)^2
  have hz : ∑ i, z i = v := F.splitVector_sum (ρ.comp ψ) v
  have hz2 : ∑ i, ‖z i‖ ^ 2 = ‖v‖ ^ 2 := F.splitVector_sq_sum (ρ.comp ψ) (fun g => hu (ψ g)) v
  have hpoint (g : G) : ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
    have hh := complex_cauchy Finset.univ (fun _ : I => 1) (fun i => ⟪w, ρ g (z i)⟫_ℂ)
    simpa only [one_mul, norm_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ← inner_sum, ← map_sum, hz] using hh
  have hi (i : I) : ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 ≤
      B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) := by
    exact F.weighted_coefficient ρ hu hE (ψ.comp (MonoidHom.mulSingle (fun _ : I => H) i))
      s ν B hν (hcoset i) (z i) w (F.splitVector_low (ρ.comp ψ) v i)
  calc
    _ ≤ ∑ g, ν g * ((Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hpoint g) (hν g))
    _ = (Fintype.card I : ℝ) * ∑ i, ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card I : ℝ) * ∑ i, B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hz2]
      dsimp [S, s]
      ring

theorem integrated_norm_sq (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v : E) :
    ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * ‖v‖ ^ 2 := by
  let A := integrated ρ (fun g => (ν g : ℂ))
  let R := (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E
  have hc : ‖⟪A v, A v⟫_ℂ‖ ^ 2 ≤ R * (‖v‖ ^ 2 * ‖A v‖ ^ 2) := by
    calc
      _ = ‖∑ g, (ν g : ℂ) * ⟪A v, ρ g v⟫_ℂ‖ ^ 2 := by
        congr 2
        simp only [A, integrated, LinearMap.sum_apply, LinearMap.smul_apply,
          inner_sum, inner_smul_right]
      _ ≤ ∑ g, ν g * ‖⟪A v, ρ g v⟫_ℂ‖ ^ 2 := norm_weighted_sum_sq ν _ hν h1
      _ ≤ _ := F.split_weighted_coefficient ρ hu hE ψ ν B hν hcoset v (A v)
  have hinner : ‖⟪A v, A v⟫_ℂ‖ = ‖A v‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
  rw [hinner] at hc
  have hR : 0 ≤ R := by positivity
  by_cases hz : ‖A v‖ ^ 2 = 0
  · change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    rw [hz]
    exact mul_nonneg hR (sq_nonneg _)
  · have hp : 0 < ‖A v‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    nlinarith

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FourierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)

lemma reciprocalSum_nonneg : 0 ≤ F.reciprocalSum :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _))

lemma low_degree_sq (D : ℕ) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2)^2 ≤
      (D : ℝ) * F.reciprocalSum ^ 2 := by
  let s := Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D)
  have hpos (b : F.Index) : (0 : ℝ) < F.degree b := by exact_mod_cast F.positive b
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun b => (F.degree b : ℝ)^2) (f := fun b => ((F.degree b : ℝ)^2)⁻¹)
    (g := fun b => (F.degree b : ℝ)^6)
    (fun b _ => inv_nonneg.mpr (sq_nonneg _)) (fun b _ => pow_nonneg (hpos b).le _)
    (fun b _ => by apply le_of_eq; field_simp)
  have hsmall : ∑ b ∈ s, ((F.degree b : ℝ)^2)⁻¹ ≤ F.reciprocalSum :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => inv_nonneg.mpr (sq_nonneg _))
  have hlarge : ∑ b ∈ s, (F.degree b : ℝ)^6 ≤ (D : ℝ) * F.reciprocalSum := by
    calc
      _ ≤ ∑ b ∈ s, (D : ℝ) * ((F.degree b : ℝ)^2)⁻¹ := by
        apply Finset.sum_le_sum
        intro b hb
        have hh : (F.degree b : ℝ)^8 ≤ D := by exact_mod_cast (Finset.mem_filter.mp hb).2
        apply (le_mul_inv_iff₀ (pow_pos (hpos b) 2)).mpr
        calc
          _ = (F.degree b : ℝ)^8 := by ring
          _ ≤ _ := hh
      _ = (D : ℝ) * ∑ b ∈ s, ((F.degree b : ℝ)^2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg _)
  calc
    _ ≤ _ := hcs
    _ ≤ F.reciprocalSum * ((D : ℝ) * F.reciprocalSum) :=
      mul_le_mul hsmall hlarge (Finset.sum_nonneg (fun b _ => pow_nonneg (hpos b).le _)) F.reciprocalSum_nonneg
    _ = _ := by ring

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma norm_integrated_sq (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (f : G → ℂ) (v : E) :
    ((‖integrated ρ f v‖ ^ 2 : ℝ) : ℂ) =
      ∑ g, ∑ h, conj (f g) * f h * ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [Complex.ofReal_pow, ← RCLike.ofReal_eq_complex_ofReal, ← inner_self_eq_norm_sq_to_K]
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro h _
  rw [map_mul, Module.End.mul_apply, inner_inv ρ hu]
  ring

lemma hsSq_integrated (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (f : G → ℂ) :
    (hsSq (integrated ρ f) : ℂ) =
      ∑ g, ∑ h, conj (f g) * f h * ρ.character (g⁻¹ * h) := by
  simp only [hsSq, Complex.ofReal_sum, norm_integrated_sq ρ hu]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [← Finset.mul_sum]
  congr 1
  exact (LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)).symm

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

theorem parseval (f : G → ℂ) :
    (Fintype.card G : ℝ) * ∑ g, ‖f g‖ ^ 2 =
      ∑ i, (F.degree i : ℝ) * hsSq (integrated (F.rep i) f) := by
  apply Complex.ofReal_injective
  push_cast
  symm
  simp only [hsSq_integrated _ (F.unitary _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]
  have he (h : G) : ∑ i, (F.degree i : ℂ) *
      (conj (f g) * f h * (F.rep i).character (g⁻¹ * h)) =
      conj (f g) * f h * (if g⁻¹ * h = 1 then (Fintype.card G : ℂ) else 0) := by
    rw [← F.regular, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [degree]
    ring
  simp only [he, inv_mul_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Complex.conj_mul']
  ring

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma power_norm_sq (A : Module.End ℂ E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ v, ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2) (k : ℕ) (v : E) :
    ‖(A ^ k) v‖ ^ 2 ≤ R ^ k * ‖v‖ ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ' A k, Module.End.mul_apply, pow_succ' R k]
      exact (hA _).trans (by nlinarith [mul_le_mul_of_nonneg_left ih hR])

lemma eight_degree_bound (D : ℝ) (hD : 0 < D) (B S C : ℝ)
    (hs : S ^ 2 ≤ D * C ^ 2) :
    D ^ 2 * (8 * B * S / D) ^ 8 ≤ (8 * B * C) ^ 8 * (D ^ 2)⁻¹ := by
  have hh := pow_le_pow_left₀ (sq_nonneg S) hs 4
  have hscalar : 0 ≤ (8 * B)^8 := by positivity
  have ht := mul_le_mul_of_nonneg_left hh hscalar
  apply (le_mul_inv_iff₀ (pow_pos hD 2)).mpr
  field_simp
  field_simp at ht
  nlinarith

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma l1_sq_le_parseval (f : G → ℝ) :
    (∑ g, |f g|)^2 ≤ ∑ i, (F.degree i : ℝ) * hsSq (integrated (F.rep i) (fun g => (f g : ℂ))) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : G => (1 : ℝ)) (fun g => |f g|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at hc
  have hp := F.parseval (fun g => (f g : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  exact hc.trans_eq hp

end Family
end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_VectorOrbits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uE uX uH uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

variable {G : Type uG} [Group G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma cyclic_scalar_mem (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) (v : E) (hv : v ∈ cyclic ρ e) :
    ∃ c : ℂ, c • e = v := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨g, rfl⟩ := hv; exact ⟨χ g, (he g).symm⟩
  | zero => exact ⟨0, zero_smul _ _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := ihx
    obtain ⟨b, rfl⟩ := ihy
    exact ⟨a+b, add_smul _ _ _⟩
  | smul a x hx ih =>
    obtain ⟨b, rfl⟩ := ih
    exact ⟨a*b, mul_smul _ _ _⟩

lemma cyclic_scalar_action (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) (g : G) (v : (cyclic ρ e).toSubmodule) :
    (cyclic ρ e).toRepresentation g v = χ g • v := by
  obtain ⟨a, ha⟩ := cyclic_scalar_mem ρ e χ he v.val v.property
  apply Subtype.ext
  change ρ g v.val = χ g • v.val
  rw [← ha, map_smul, he, smul_comm]

lemma cyclic_scalar_finrank (ρ : Representation ℂ G E) (e : E) (χ : G → ℂ)
    (he : ∀ g, ρ g e = χ g • e) : Module.finrank ℂ (cyclic ρ e).toSubmodule ≤ 1 := by
  apply finrank_le_one (⟨e, self_mem_cyclic ρ e⟩ : (cyclic ρ e).toSubmodule)
  intro v
  obtain ⟨a, ha⟩ := cyclic_scalar_mem ρ e χ he v.val v.property
  exact ⟨a, Subtype.ext ha⟩

namespace PermutationSpace
variable {X : Type uX} {H : Type uH} [Fintype X] [MulAction G X] [Group H] [Fintype H]
omit [Fintype X] in
lemma translate_alternator (ι : H →* G) (χ : H →* ℂ) (a : H)
    (v : EuclideanSpace ℂ X) :
    rep (ι a) (alternator ι χ v) = χ a⁻¹ • alternator ι χ v := by
  simp only [alternator_apply, map_sum, Finset.smul_sum]
  simp only [map_smul]
  have hh := Equiv.sum_comp (Equiv.mulLeft a)
    (fun h => χ a⁻¹ • (χ h • (rep (ι h) v : EuclideanSpace ℂ X)))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, smul_smul, map_mul]
  rw [show χ a⁻¹ * (χ a * χ h) = χ h by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]]
  rfl
end PermutationSpace

lemma row_zero_of_full (D : YoungDiagram) (h : D.rowLen 0 = Fintype.card (Cells D)) :
    ∀ x : Cells D, x.val.1 = 0 := by
  have hc : Fintype.card (Lower D) = 0 := by have hh := card_lower_add D; omega
  have he : IsEmpty (Lower D) := Fintype.card_eq_zero_iff.mp hc
  intro x
  by_contra hx
  exact he.false ⟨x, hx⟩

lemma col_zero_of_full (D : YoungDiagram) (h : D.colLen 0 = Fintype.card (Cells D)) :
    ∀ x : Cells D, x.val.2 = 0 := by
  have hc : D.transpose.rowLen 0 = Fintype.card (Cells D.transpose) := by
    rw [YoungDiagram.rowLen_transpose, ← Fintype.card_congr (transposeCells D).toEquiv, h]
  intro x
  exact row_zero_of_full D.transpose hc (transposeCells D x)

variable {α : Type uα} [Fintype α]

omit [Fintype α] in
lemma row_rep_action (D : YoungDiagram) (t : α ≃ Cells D)
    (h : ∀ x : Cells D, x.val.1 = 0) (g : Equiv.Perm α)
    (v : EuclideanSpace ℂ (Tabloid (tableauRow D t))) : tabloidRep D t g v = v := by
  ext f
  change v (g⁻¹ • f) = v f
  apply congrArg (fun a => v a)
  apply Subtype.ext
  funext x
  obtain ⟨a, ha⟩ := f.property
  simp only [tabloid_smul_apply, ha, Function.comp_apply, tableauRow, h]

lemma column_poly_action (D : YoungDiagram) (t : α ≃ Cells D)
    (h : ∀ x : Cells D, x.val.2 = 0) (g : Equiv.Perm α) :
    tabloidRep D t g (polytabloid D t) = complexSign g • polytabloid D t := by
  have hg : g ∈ fiberGroup (tableauCol D t) := by intro x; simp only [tableauCol, h]
  have hh := PermutationSpace.translate_alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype) ⟨g, hg⟩
    (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ))
  change tabloidRep D t g (polytabloid D t) = complexSign g⁻¹ • polytabloid D t at hh
  rwa [complexSign_inv] at hh

lemma exceptional_action {n : ℕ} (p : NShape n) (hp : defect p = 0) :
    degree p = 1 ∧ ((∀ g v, family p g v = v) ∨
      (∀ g v, family p g v = complexSign g • v)) := by
  let D := ofPartition p
  let t := canonicalTableau p
  have hL : longest D = Fintype.card (Cells D) := by
    have hh := defect_add_longest p
    rw [hp, zero_add] at hh
    exact hh.trans (diagram_card p).symm
  have hor : D.rowLen 0 = Fintype.card (Cells D) ∨ D.colLen 0 = Fintype.card (Cells D) := by
    unfold longest at hL
    rcases le_total (D.colLen 0) (D.rowLen 0) with h | h
    · exact Or.inl (by rwa [max_eq_left h] at hL)
    · exact Or.inr (by rwa [max_eq_right h] at hL)
  rcases hor with hr | hc
  · have he : ∀ g, tabloidRep D t g (polytabloid D t) = (1 : ℂ) • polytabloid D t := by
      intro g; rw [one_smul]; exact row_rep_action D t (row_zero_of_full D hr) g _
    have hd := cyclic_scalar_finrank (tabloidRep D t) (polytabloid D t) (fun _ => 1) he
    refine ⟨Nat.le_antisymm hd (degree_pos p), Or.inl ?_⟩
    intro g v
    apply Subtype.ext
    exact row_rep_action D t (row_zero_of_full D hr) g v.val
  · have he := column_poly_action D t (col_zero_of_full D hc)
    have hd := cyclic_scalar_finrank (tabloidRep D t) (polytabloid D t) complexSign he
    refine ⟨Nat.le_antisymm hd (degree_pos p), Or.inr ?_⟩
    exact cyclic_scalar_action (tabloidRep D t) (polytabloid D t) complexSign he

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma sum_rep_invariant (ρ : Representation ℂ G E) (g : G) (v : E) :
    ρ g (∑ h, ρ h v) = ∑ h, ρ h v := by
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => ρ h v)

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma invariant_finrank_le_one (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (v : E) (hv : v ≠ 0) (hinv : ∀ g, ρ g v = v) : Module.finrank ℂ E ≤ 1 := by
  let A : Representation.IntertwiningMap (Representation.trivial ℂ G ℂ) ρ := {
    toLinearMap := LinearMap.toSpanSingleton ℂ E v
    isIntertwining' := by intro g; ext; simp [Representation.trivial, hinv] }
  have hA : A ≠ 0 := by
    intro ha
    have hh := DFunLike.congr_fun ha 1
    exact hv (by simpa [A] using hh)
  have hs := (Representation.IsIrreducible.surjective_or_eq_zero A).resolve_right hA
  exact finrank_le_one v hs

omit [FiniteDimensional ℂ E] in
lemma integrated_uniform_zero (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hd : 1 < Module.finrank ℂ E) :
    integrated ρ (fun _ => (Fintype.card G : ℂ)⁻¹) = 0 := by
  have hz (v : E) : (∑ h, ρ h v) = 0 := by
    by_contra hn
    have hh := invariant_finrank_le_one ρ _ hn (fun g => sum_rep_invariant ρ g v)
    omega
  ext v
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, ← Finset.smul_sum, hz, smul_zero,
    LinearMap.zero_apply]

omit [FiniteDimensional ℂ E] in
lemma integrated_scalar (ρ : Representation ℂ G E) (χ : G → ℂ)
    (hχ : ∀ g v, ρ g v = χ g • v) (f : G → ℂ) :
    integrated ρ f = (∑ g, f g * χ g) • LinearMap.id := by
  ext v
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, hχ, smul_smul,
    Finset.sum_smul, LinearMap.id_apply]

lemma hsSq_scalar (c : ℂ) : hsSq (c • (LinearMap.id : Module.End ℂ E)) =
    (Module.finrank ℂ E : ℝ) * ‖c‖^2 := by
  simp [hsSq, norm_smul, (stdOrthonormalBasis ℂ E).norm_eq_one]

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_PermutationCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma degree_gt_one {n : ℕ} (p : NShape n) (hn : 16 ≤ n) (hp : 0 < defect p) :
    1 < degree p := by
  by_cases hs : 4 * defect p ≤ n
  · have hh := small_defect_degree p hs
    have h3 : 3 ≤ 3 ^ defect p := by simpa using Nat.pow_le_pow_right (by omega : 0 < 3) (show 1 ≤ defect p by omega)
    omega
  · have hb := bulk_degree p (by omega) (by omega)
    have h2 : (2 : ℝ) ≤ (2 : ℝ)^(n/16) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ n/16 by omega)
    have : (1 : ℝ) < degree p := lt_of_lt_of_le (by norm_num) (h2.trans hb)
    exact_mod_cast this

lemma full_reciprocal_bound (n : ℕ) :
    (symmetricFamily n).reciprocalSum ≤ 2 + exceptionalReciprocalSum n := by
  have hzero : slice n 0 ≤ 2 := by
    have h := slice_bound n 0 1 (by norm_num) (fun p _ => by exact_mod_cast degree_pos p)
    norm_num at h
    exact h
  have he : (symmetricFamily n).reciprocalSum = slice n 0 + exceptionalReciprocalSum n := by
    unfold slice
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : NShape n => defect p = 0)) (by simp), Finset.sum_filter]
    unfold exceptionalReciprocalSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    change inverseDegree p = _
    by_cases hp : defect p = 0
    · simp only [hp, lt_self_iff_false, ↓reduceIte, add_zero]
    · simp only [hp, Nat.pos_of_ne_zero hp, ↓reduceIte, zero_add]
  rw [he]
  linarith

lemma exceptional_count (n : ℕ) : Fintype.card {p : NShape n // defect p = 0} ≤ 2 := by
  simpa using defect_card_bound n 0

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical

variable {α : Type} [Fintype α]

lemma complexSign_permCongr {β : Type} [Fintype β] (e : α ≃ β) (g : Equiv.Perm α) :
    complexSign (e.permCongr g) = complexSign g := by
  simp only [complexSign, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.sign_permCongr]

lemma complexSign_norm (g : Equiv.Perm α) : ‖complexSign g‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> simp [complexSign, h]

lemma complexSign_eq [DecidableEq α] (g : Equiv.Perm α) :
    complexSign g = (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) := by
  change (((@Equiv.Perm.sign α (Classical.typeDecidableEq α) _ g : ℤˣ) : ℤ) : ℂ) = _
  rw [Subsingleton.elim (Classical.typeDecidableEq α) (inferInstance : DecidableEq α)]

lemma complexSign_sum [DecidableEq α] [Nontrivial α] : (∑ g : Equiv.Perm α, complexSign g) = 0 := by
  obtain ⟨a, ha⟩ := Equiv.Perm.sign_surjective α (-1)
  have he : complexSign a = -1 := by rw [complexSign_eq, ha]; simp
  have hh := Equiv.sum_comp (Equiv.mulLeft a) (fun g : Equiv.Perm α => complexSign g)
  simp only [Equiv.coe_mulLeft, map_mul, he, neg_one_mul, Finset.sum_neg_distrib] at hh
  linear_combination - (1/2 : ℂ) * hh

lemma permutation_exceptional_action [DecidableEq α] (p : NShape (Fintype.card α)) (hp : defect p = 0) :
    (permutationFamily α).degree p = 1 ∧
      ((∀ (g : Equiv.Perm α) (v : Space (α:=Fin (Fintype.card α)) p), (permutationFamily α).rep p g v = v) ∨
       (∀ (g : Equiv.Perm α) (v : Space (α:=Fin (Fintype.card α)) p), (permutationFamily α).rep p g v = complexSign g • v)) := by
  obtain ⟨hd, htr | hsign⟩ := exceptional_action p hp
  · exact ⟨hd, Or.inl fun g v => htr _ v⟩
  · refine ⟨hd, Or.inr ?_⟩
    intro g v
    change family p ((Fintype.equivFin α).permCongr g) v = _
    rw [hsign, complexSign_permCongr]

end Thorp.Specht

namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Group G] [Fintype G]

lemma realConv_nonneg (μ ν : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hν : ∀ g, 0 ≤ ν g) :
    ∀ g, 0 ≤ realConv μ ν g := fun _ => Finset.sum_nonneg (fun h _ => mul_nonneg (hμ h) (hν _))

lemma realConv_sum (μ ν : G → ℝ) : ∑ g, realConv μ ν g = (∑ g, μ g) * (∑ g, ν g) := by
  unfold realConv
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) ν

lemma realPower_nonneg (ν : G → ℝ) (hν : ∀ g, 0 ≤ ν g) (k : ℕ) : ∀ g, 0 ≤ realPower ν k g := by
  induction k with
  | zero => intro g; simp only [realPower]; split_ifs <;> norm_num
  | succ k ih => exact realConv_nonneg ν (realPower ν k) hν ih

lemma realPower_sum (ν : G → ℝ) (hν : ∑ g, ν g = 1) (k : ℕ) : ∑ g, realPower ν k g = 1 := by
  induction k with
  | zero => simp [realPower]
  | succ k ih => rw [realPower, realConv_sum, hν, ih, mul_one]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma integrated_realConv (ρ : Representation ℂ G E) (μ ν : G → ℝ) :
    integrated ρ (fun g => (realConv μ ν g : ℂ)) = integrated ρ (fun g => (μ g : ℂ)) *
      integrated ρ (fun g => (ν g : ℂ)) := by
  rw [← integrated_convolution]
  congr 1
  funext g
  simp only [realConv, convolution, Complex.ofReal_sum, Complex.ofReal_mul]

lemma integrated_realPower (ρ : Representation ℂ G E) (ν : G → ℝ) (k : ℕ) :
    integrated ρ (fun g => (realPower ν k g : ℂ)) = (integrated ρ (fun g => (ν g : ℂ)))^k := by
  induction k with
  | zero =>
    rw [pow_zero]
    have he : (fun g => (realPower ν 0 g : ℂ)) = delta := by funext g; simp only [realPower, delta]; split_ifs <;> norm_num
    rw [he, integrated_delta]
  | succ k ih => rw [realPower, integrated_realConv, ih, pow_succ']

lemma integrated_real_sub (ρ : Representation ℂ G E) (μ ν : G → ℝ) :
    integrated ρ (fun g => ((μ g - ν g : ℝ) : ℂ)) =
      integrated ρ (fun g => (μ g : ℂ)) - integrated ρ (fun g => (ν g : ℂ)) := by
  simp only [integrated, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]

end Thorp.Fourier

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_ConvolutionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma hsSq_power_le (A : Module.End ℂ E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ v, ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2) (k : ℕ) :
    hsSq (A ^ k) ≤ (Module.finrank ℂ E : ℝ) * R ^ k := by
  unfold hsSq
  calc
    _ ≤ ∑ i, R ^ k * ‖stdOrthonormalBasis ℂ E i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => power_norm_sq A R hR hA k _)
    _ = _ := by simp [(stdOrthonormalBasis ℂ E).norm_eq_one, mul_comm]

lemma Family.eight_transform_bound (F : Family H) (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hd : 0 < Module.finrank ℂ E) (ψ : (Fin 8 → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) :
    (Module.finrank ℂ E : ℝ) * hsSq (integrated ρ (fun g => (realPower ν 8 g : ℂ))) ≤
      (8 * B * F.reciprocalSum)^8 * ((Module.finrank ℂ E : ℝ)^2)⁻¹ := by
  let S : ℝ := ∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ Module.finrank ℂ E), (F.degree b : ℝ)^2
  let R : ℝ := 8 * B * S / Module.finrank ℂ E
  have hD : (0 : ℝ) < Module.finrank ℂ E := by exact_mod_cast hd
  have hR : 0 ≤ R := by dsimp [R, S]; positivity
  have hA (v : E) : ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤ R * ‖v‖ ^ 2 := by
    simpa only [R, S, Fintype.card_fin, Nat.cast_ofNat] using F.integrated_norm_sq ρ hu (Nat.ne_of_gt hd) ψ ν B hν h1 hB (by
      intro i g
      convert hcoset i g using 1
      apply Finset.sum_congr rfl
      intro h _
      congr 4
      exact Subsingleton.elim _ _) v
  rw [integrated_realPower]
  calc
    _ ≤ (Module.finrank ℂ E : ℝ) * ((Module.finrank ℂ E : ℝ) * R^8) :=
      mul_le_mul_of_nonneg_left (hsSq_power_le _ R hR hA 8) hD.le
    _ = (Module.finrank ℂ E : ℝ)^2 * R^8 := by ring
    _ ≤ _ := eight_degree_bound _ hD B S F.reciprocalSum (F.low_degree_sq _)

omit [FiniteDimensional ℂ E] in
lemma integrated_uniform_real (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hd : 1 < Module.finrank ℂ E) :
    integrated ρ (fun _ => (((Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using integrated_uniform_zero ρ hd

omit [FiniteDimensional ℂ E] in
lemma centered_trivial (ρ : Representation ℂ G E) (hρ : ∀ g v, ρ g v = v)
    (ν : G → ℝ) (h1 : ∑ g, ν g = 1) :
    integrated ρ (fun g => ((realPower ν 8 g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) = 0 := by
  rw [integrated_real_sub]
  have htr (g : G) (v : E) : ρ g v = (1 : ℂ) • v := by simpa using hρ g v
  rw [integrated_scalar ρ (fun _ => 1) htr, integrated_scalar ρ (fun _ => 1) htr]
  simp only [mul_one, ← Complex.ofReal_sum, realPower_sum ν h1, Complex.ofReal_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_ne_zero]

omit [FiniteDimensional ℂ E] in
lemma centered_character (ρ : Representation ℂ G E) (χ : G → ℂ)
    (hρ : ∀ g v, ρ g v = χ g • v) (hχ : ∑ g, χ g = 0)
    (ν : G → ℝ) :
    integrated ρ (fun g => ((realPower ν 8 g - (Fintype.card G : ℝ)⁻¹ : ℝ) : ℂ)) =
      (∑ g, (ν g : ℂ) * χ g)^8 • LinearMap.id := by
  rw [integrated_real_sub, integrated_realPower, integrated_scalar ρ χ hρ,
    integrated_scalar ρ χ hρ]
  simp only [← Finset.mul_sum, hχ, mul_zero, zero_smul, sub_zero]
  simp only [smul_pow, show (LinearMap.id : Module.End ℂ E) = 1 from rfl, one_pow]

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

theorem permutation_eight_bound (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (ν : Equiv.Perm α → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α)) :
    (∑ g, |realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹|)^2 ≤
      2 * ‖∑ g, (ν g : ℂ) * complexSign g‖^16 +
        (8 * B * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α) := by
  let F := permutationFamily α
  let H := permutationFamily β
  let bias : ℝ := ‖∑ g, (ν g : ℂ) * complexSign g‖^16
  let K : ℝ := (8 * B * H.reciprocalSum)^8
  let f : Equiv.Perm α → ℝ := fun g => realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹
  have hp (p : F.Index) :
      (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) ≤
        if defect p = 0 then bias else K * inverseDegree p := by
    by_cases hz : defect p = 0
    · rw [ite_eq_left hz]
      obtain ⟨hd, htr | hsign⟩ := permutation_exceptional_action (α:=α) p hz
      · have hh := centered_trivial (F.rep p) htr ν h1
        change integrated (F.rep p) (fun g => (f g : ℂ)) = 0 at hh
        rw [hh]
        simp only [hsSq, LinearMap.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero, mul_zero]
        exact pow_nonneg (norm_nonneg _) _
      · have hh := centered_character (F.rep p) complexSign hsign (complexSign_sum (α:=α)) ν
        change integrated (F.rep p) (fun g => (f g : ℂ)) = _ at hh
        rw [hh, hsSq_scalar]
        change (F.degree p : ℝ) * ((F.degree p : ℝ) * ‖(∑ g, (ν g : ℂ) * complexSign g)^8‖^2) ≤ bias
        rw [show F.degree p = 1 from hd]
        simp only [Nat.cast_one, one_mul, norm_pow, ← pow_mul]
        exact le_rfl
    · rw [ite_eq_right hz]
      have hgt : 1 < Module.finrank ℂ (F.Space p) := degree_gt_one p hn (Nat.pos_of_ne_zero hz)
      have hu := integrated_uniform_real (F.rep p) hgt
      have he : integrated (F.rep p) (fun g => (f g : ℂ)) =
          integrated (F.rep p) (fun g => (realPower ν 8 g : ℂ)) := by
        rw [show (fun g => (f g : ℂ)) = (fun g => ((realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ : ℝ) : ℂ)) from rfl,
          integrated_real_sub, hu, sub_zero]
      rw [he]
      exact H.eight_transform_bound (F.rep p) (F.unitary p) (by omega) ψ ν B hν h1 hB hcoset
  have hs : (∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p) =
      (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias +
        K * exceptionalReciprocalSum (Fintype.card α) := by
    rw [show (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) * bias =
      ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else 0 by rw [← Finset.sum_filter]; simp [Fintype.card_subtype],
      exceptionalReciprocalSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hz : defect p = 0
    · simp only [hz, lt_self_iff_false, ↓reduceIte, mul_zero, add_zero]
    · simp only [hz, Nat.pos_of_ne_zero hz, ↓reduceIte, zero_add]
  have hc : (Fintype.card {p : NShape (Fintype.card α) // defect p = 0} : ℝ) ≤ 2 := by
    exact_mod_cast exceptional_count (Fintype.card α)
  calc
    _ ≤ ∑ p, (F.degree p : ℝ) * hsSq (integrated (F.rep p) (fun g => (f g : ℂ))) := F.l1_sq_le_parseval f
    _ ≤ ∑ p : NShape (Fintype.card α), if defect p = 0 then bias else K * inverseDegree p :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = _ := hs
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)) le_rfl

end Thorp.Specht

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Trimming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY uΩ uI uG uH uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Trim
open scoped Classical

variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

lemma push_sum (μ : X → ℝ) (f : X → Y) : ∑ y, push μ f y = ∑ x, μ x := by
  unfold push
  rw [Finset.sum_comm]
  simp

lemma push_test (μ : X → ℝ) (f : X → Y) (s : Y → ℝ) :
    ∑ y, push μ f y * s y = ∑ x, μ x * s (f x) := by
  unfold push
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
lemma push_fairMass {Ω : Type uΩ} [Fintype Ω] (a : Ω → X) (f : X → Y) :
    push (fairMass a) f = fairMass (f ∘ a) := by
  funext y
  have he (x : X) : (if f x = y then fairMass a x else 0) =
      (∑ ω, if a ω = x then (if f x = y then (1:ℝ) else 0) else 0) / Fintype.card Ω := by
    by_cases h : f x = y <;> simp [h, fairMass]
  unfold push
  simp_rw [he]
  rw [← Finset.sum_div]
  unfold fairMass
  congr 1
  rw [Finset.sum_comm]
  simp

lemma push_bad_mass (μ υ : X → ℝ) (f : X → Y)
    (hm : ∑ x, μ x = ∑ x, υ x) :
    (∑ x, if 2 * push υ f (f x) < push μ f (f x) then μ x else 0) ≤
      2 * tv (push μ f) (push υ f) := by
  let s := Finset.univ.filter (fun y => 2 * push υ f y < push μ f y)
  have he : (∑ x, if 2 * push υ f (f x) < push μ f (f x) then μ x else 0) =
      ∑ y ∈ s, push μ f y := by
    rw [Finset.sum_filter]
    have ht := push_test μ f (fun y => if 2 * push υ f y < push μ f y then 1 else 0)
    simpa only [mul_ite, mul_one, mul_zero] using ht.symm
  have ht := sum_sub_le_tv (push μ f) (push υ f) (by simp only [push_sum, hm]) s
  have hs : ∑ y ∈ s, push μ f y ≤ 2 * ∑ y ∈ s, (push μ f y - push υ f y) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun y hy => by have hh := (Finset.mem_filter.mp hy).2; linarith)
  rw [he]
  linarith

lemma uniform_eq_fairMass_id : (fun _ : X => (Fintype.card X : ℝ)⁻¹) = fairMass id := by
  funext x
  simp [fairMass]

variable {I : Type uI} [Fintype I]
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

omit [Fintype I] [Fintype G] in
lemma cosetMass_right (ψ : (I → H) →* G) (μ : G → ℝ) (i : I) (g : G) (a : H) :
    cosetMass ψ μ i (g * ψ (Pi.mulSingle i a)) = cosetMass ψ μ i g := by
  unfold cosetMass
  have he (h : H) : g * ψ (Pi.mulSingle i a) * ψ (Pi.mulSingle i h) =
      g * ψ (Pi.mulSingle i (a * h)) := by rw [Pi.mulSingle_mul, map_mul, mul_assoc]
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.mulLeft a) (fun h => μ (g * ψ (Pi.mulSingle i h)))

omit [Fintype I] in
lemma discarded_nonneg (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) :
    0 ≤ discarded ψ μ := Finset.sum_nonneg (fun g _ => by split_ifs <;> first | exact hμ _ | exact le_rfl)

omit [Fintype I] in
lemma kept_add_discarded (ψ : (I → H) →* G) (μ : G → ℝ) :
    (∑ g, kept ψ μ g) + discarded ψ μ = ∑ g, μ g := by
  rw [discarded, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  unfold kept
  split_ifs <;> ring

lemma discarded_bound (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (A : I → Type uA) [∀ i, Fintype (A i)] (f : ∀ i, G → A i)
    (hM : ∀ i g, push μ (f i) (f i g) = cosetMass ψ μ i g)
    (hU : ∀ i g, push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) =
      (Fintype.card H : ℝ) / Fintype.card G) :
    discarded ψ μ ≤ 2 * ∑ i, tv (push μ (f i)) (push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i)) := by
  have hu : (∑ _ : G, (Fintype.card G : ℝ)⁻¹) = 1 := by simp [Fintype.card_ne_zero]
  have hpoint (g : G) : (if good ψ μ g then 0 else μ g) ≤
      ∑ i, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
        then μ g else 0 := by
    simp only [hM, hU]
    by_cases hg : good ψ μ g
    · rw [ite_eq_left hg]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hμ _ | exact le_rfl)
    · rw [ite_eq_right hg]
      have ⟨i, hi⟩ : ∃ i, 2 * ((Fintype.card H : ℝ) / Fintype.card G) < cosetMass ψ μ i g := by
        simpa only [good, not_forall, not_le] using hg
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun i => if 2 * ((Fintype.card H : ℝ) / Fintype.card G) < cosetMass ψ μ i g then μ g else 0)
        (fun j _ => by split_ifs <;> first | exact hμ _ | exact le_rfl) (Finset.mem_univ i)
      simpa only [ite_eq_left hi] using hh
  calc
    _ ≤ ∑ g, ∑ i, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
          then μ g else 0 := Finset.sum_le_sum (fun g _ => hpoint g)
    _ = ∑ i, ∑ g, if 2 * push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i) (f i g) < push μ (f i) (f i g)
          then μ g else 0 := Finset.sum_comm
    _ ≤ ∑ i, 2 * tv (push μ (f i)) (push (fun _ : G => (Fintype.card G : ℝ)⁻¹) (f i)) :=
      Finset.sum_le_sum (fun i _ => push_bad_mass _ _ (f i) (h1.trans hu.symm))
    _ = _ := by rw [Finset.mul_sum]

end Trim

namespace Trim
open scoped Classical
variable {I : Type uI} {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

lemma normalized_nonneg (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (hδ : discarded ψ μ < 1) (g : G) : 0 ≤ normalized ψ μ g := by
  unfold normalized kept
  exact div_nonneg (by split_ifs <;> first | exact hμ _ | exact le_rfl) (by linarith)

lemma normalized_sum (ψ : (I → H) →* G) (μ : G → ℝ) (h1 : ∑ g, μ g = 1)
    (hδ : discarded ψ μ < 1) : ∑ g, normalized ψ μ g = 1 := by
  have hk : ∑ g, kept ψ μ g = 1 - discarded ψ μ := by
    have hh := kept_add_discarded ψ μ
    rw [h1] at hh
    linarith
  simp only [normalized, ← Finset.sum_div, hk]
  exact div_self (by linarith)

lemma normalized_tv (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (hδ : discarded ψ μ < 1) :
    tv μ (normalized ψ μ) = discarded ψ μ := by
  have hden : 0 < 1 - discarded ψ μ := by linarith
  have hd0 := discarded_nonneg ψ μ hμ
  have hpt (g : G) : |μ g - normalized ψ μ g| =
      normalized ψ μ g - μ g + 2 * (if good ψ μ g then 0 else μ g) := by
    by_cases hg : good ψ μ g
    · have he : normalized ψ μ g = μ g / (1 - discarded ψ μ) := by simp only [normalized, kept, ite_eq_left hg]
      have hle : μ g ≤ normalized ψ μ g := by rw [he]; apply (le_div_iff₀ hden).mpr; nlinarith [hμ g]
      rw [abs_of_nonpos (sub_nonpos.mpr hle), ite_eq_left hg]
      ring
    · simp only [normalized, kept, ite_eq_right hg, zero_div, sub_zero, abs_of_nonneg (hμ g)]
      ring
  unfold tv
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    normalized_sum ψ μ h1 hδ, h1]
  change (1/2 : ℝ) * (1-1+2*discarded ψ μ) = discarded ψ μ
  ring

lemma normalized_coset (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (hδ : discarded ψ μ ≤ 1/2) (i : I) (g : G) :
    cosetMass ψ (normalized ψ μ) i g ≤ 4 * (Fintype.card H : ℝ) / Fintype.card G := by
  have hden : 0 < 1 - discarded ψ μ := by linarith
  have hu : 0 ≤ (Fintype.card H : ℝ) / Fintype.card G := by positivity
  by_cases hg : cosetMass ψ μ i g ≤ 2 * ((Fintype.card H : ℝ) / Fintype.card G)
  · have hle : cosetMass ψ (normalized ψ μ) i g ≤ cosetMass ψ μ i g / (1-discarded ψ μ) := by
      simp only [cosetMass, normalized, ← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ hden.le
      apply Finset.sum_le_sum
      intro h _
      unfold kept
      split_ifs <;> simp [hμ]
    apply hle.trans
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ 1-discarded ψ μ by linarith) (show 0 ≤ 4*((Fintype.card H : ℝ)/Fintype.card G) by positivity)
    rw [mul_div_assoc]
    nlinarith
  · have hz (h : H) : normalized ψ μ (g * ψ (Pi.mulSingle i h)) = 0 := by
      have hn : ¬ good ψ μ (g * ψ (Pi.mulSingle i h)) := by
        intro hh
        have hi := hh i
        rw [cosetMass_right] at hi
        exact hg hi
      simp only [normalized, kept, ite_eq_right hn, zero_div]
    simp only [cosetMass, hz, Finset.sum_const_zero]
    positivity

lemma normalized_bias (ψ : (I → H) →* G) (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g)
    (h1 : ∑ g, μ g = 1) (hδ : discarded ψ μ < 1) (χ : G → ℂ)
    (hχ : ∀ g, ‖χ g‖ ≤ 1) (hb : ∑ g, (μ g : ℂ) * χ g = 0) :
    ‖∑ g, (normalized ψ μ g : ℂ) * χ g‖ ≤ 2 * discarded ψ μ := by
  have he : (∑ g, (normalized ψ μ g : ℂ) * χ g) =
      ∑ g, ((normalized ψ μ g - μ g : ℝ) : ℂ) * χ g := by
    simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, hb, sub_zero]
  rw [he]
  calc
    _ ≤ ∑ g, ‖((normalized ψ μ g - μ g : ℝ) : ℂ) * χ g‖ := norm_sum_le _ _
    _ ≤ ∑ g, |normalized ψ μ g - μ g| := by
      apply Finset.sum_le_sum
      intro g _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hχ g) (abs_nonneg (normalized ψ μ g - μ g))
    _ = 2 * tv μ (normalized ψ μ) := by simp only [tv, abs_sub_comm]; ring
    _ = _ := by rw [normalized_tv ψ μ hμ h1 hδ]

end Trim

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_FourierPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Fourier
open scoped Classical
variable {G : Type} [Fintype G] [Group G]

omit [Group G] in
lemma tv_triangle (μ ν η : G → ℝ) : tv μ η ≤ tv μ ν + tv ν η := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun g _ => by simpa only [sub_add_sub_cancel] using abs_add_le (μ g-ν g) (ν g-η g))

lemma tv_realConv_left (μ ν η : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1) :
    tv (realConv μ ν) (realConv μ η) ≤ tv ν η := by
  have hb : (∑ z, |realConv μ ν z - realConv μ η z|) ≤ ∑ z, |ν z-η z| := by
    calc
      _ = ∑ z, |∑ g, μ g * (ν (g⁻¹*z)-η (g⁻¹*z))| := by
        simp only [realConv, mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ z, ∑ g, μ g * |ν (g⁻¹*z)-η (g⁻¹*z)| := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [abs_mul, abs_of_nonneg (hμ _)] using
          Finset.abs_sum_le_sum_abs (fun g => μ g * (ν (g⁻¹*z)-η (g⁻¹*z))) Finset.univ
      _ = (∑ g, μ g) * ∑ z, |ν z-η z| := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun z => |ν z-η z|)
      _ = _ := by rw [h1, one_mul]
  exact mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)

lemma tv_realConv_right (μ ν η : G → ℝ) (hη : ∀ g, 0 ≤ η g) (h1 : ∑ g, η g = 1) :
    tv (realConv μ η) (realConv ν η) ≤ tv μ ν := by
  have hb : (∑ z, |realConv μ η z - realConv ν η z|) ≤ ∑ z, |μ z-ν z| := by
    calc
      _ = ∑ z, |∑ g, (μ g-ν g) * η (g⁻¹*z)| := by
        simp only [realConv, sub_mul, Finset.sum_sub_distrib]
      _ ≤ ∑ z, ∑ g, |μ g-ν g| * η (g⁻¹*z) := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [abs_mul, abs_of_nonneg (hη _)] using
          Finset.abs_sum_le_sum_abs (fun g => (μ g-ν g) * η (g⁻¹*z)) Finset.univ
      _ = (∑ g, |μ g-ν g|) * ∑ z, η z := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) η
      _ = _ := by rw [h1, mul_one]
  exact mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)

lemma tv_realConv (μ ν μ' ν' : G → ℝ) (hμ' : ∀ g, 0 ≤ μ' g) (hμ1 : ∑ g, μ' g = 1)
    (hν : ∀ g, 0 ≤ ν g) (hν1 : ∑ g, ν g = 1) :
    tv (realConv μ ν) (realConv μ' ν') ≤ tv μ μ' + tv ν ν' := by
  exact (tv_triangle _ (realConv μ' ν) _).trans
    (add_le_add (tv_realConv_right μ μ' ν hν hν1) (tv_realConv_left μ' ν ν' hμ' hμ1))

lemma tv_realPower (μ ν : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hν : ∀ g, 0 ≤ ν g) (hν1 : ∑ g, ν g = 1) (k : ℕ) :
    tv (realPower μ k) (realPower ν k) ≤ (k : ℝ) * tv μ ν := by
  induction k with
  | zero => simp [realPower, tv]
  | succ k ih =>
      calc
        _ ≤ tv μ ν + tv (realPower μ k) (realPower ν k) :=
          tv_realConv μ (realPower μ k) ν (realPower ν k) hν hν1 (realPower_nonneg μ hμ k) (realPower_sum μ hμ1 k)
        _ ≤ tv μ ν + (k : ℝ) * tv μ ν := add_le_add_right ih _
        _ = _ := by push_cast; ring

end Fourier

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_BlockEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uβ uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα}

lemma complementIn_injective (e : α ≃ I × β) (i : I) :
    Function.Injective (complementIn (β:=β) e i) := by
  intro x y h
  have hh := e.symm.injective h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun p : I × β => p.2) hh)

end Thorp.Block

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_BlockFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uβ uα uK

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα} [Fintype I] [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β]

lemma push_restriction (e : α ≃ I × β) (i : I) (μ : Equiv.Perm α → ℝ) (g : Equiv.Perm α) :
    Trim.push μ (restriction e i) (restriction e i g) = Trim.cosetMass (embedding e) μ i g := by
  calc
    _ = ∑ k : {k : Equiv.Perm α // restriction e i k = restriction e i g}, μ k.val := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun k : Equiv.Perm α => restriction e i k = restriction e i g)) (by simp),
        Finset.sum_filter]
      unfold Trim.push
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> rfl
    _ = _ := (Equiv.sum_comp (fiberEquiv e i g) (fun k => μ k.val)).symm

variable {K : Type uK} [Fintype K]

omit [Fintype I] [Fintype β] [Fintype α] [DecidableEq α] [DecidableEq β] [Fintype K] in
lemma orderedRestriction_eq_iff (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (g k : Equiv.Perm α) : orderedRestriction e i o g = orderedRestriction e i o k ↔
      restriction e i g = restriction e i k := by
  constructor
  · intro h
    funext x
    obtain ⟨k,rfl⟩ := o.surjective x
    exact congrFun h k
  · intro h
    unfold orderedRestriction
    rw [h]

omit [Fintype K] in
lemma push_orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (μ : Equiv.Perm α → ℝ) (g : Equiv.Perm α) :
    Trim.push μ (orderedRestriction e i o) (orderedRestriction e i o g) =
      Trim.cosetMass (embedding e) μ i g := by
  rw [← push_restriction e i μ g]
  unfold Trim.push
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : restriction e i k = restriction e i g
  · have ho := (orderedRestriction_eq_iff e i o k g).mpr hk
    simp only [ite_eq_left hk, ite_eq_left ho]
  · have ho := mt (orderedRestriction_eq_iff e i o k g).mp hk
    simp only [ite_eq_right hk, ite_eq_right ho]

omit [Fintype K] in
lemma uniform_orderedRestriction (e : α ≃ I × β) (i : I) (o : K ≃ complement (β:=β) i)
    (g : Equiv.Perm α) :
    Trim.push (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹)
      (orderedRestriction e i o) (orderedRestriction e i o g) =
      (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
  rw [push_orderedRestriction]
  simp only [Trim.cosetMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

lemma discarded_ordered_bound [DecidableEq K] (e : α ≃ I × β) (o : ∀ i, K ≃ complement (β:=β) i)
    (μ : Equiv.Perm α → ℝ) (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1) :
    Trim.discarded (embedding e) μ ≤
      2 * ∑ i, tv (Trim.push μ (orderedRestriction e i (o i)))
        (Trim.push (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) (orderedRestriction e i (o i))) := by
  exact Trim.discarded_bound (embedding e) μ hμ h1 (fun _ : I => K → α)
    (fun i => orderedRestriction e i (o i))
    (fun i g => push_orderedRestriction e i (o i) μ g)
    (fun i g => uniform_orderedRestriction e i (o i) g)

end Block

lemma law_nonneg (d t : ℕ) (g : State d) : 0 ≤ law d t g := fairMass_nonneg (run d t) g

lemma law_sum (d t : ℕ) : ∑ g, law d t g = 1 := fairMass_sum (run d t)

namespace Block
open scoped Classical

lemma domain_injective (d : ℕ) (i : Fin 8) : Function.Injective (domain d i) :=
  (complementIn_injective _ _).comp (ordering d i).injective

lemma push_law_ordered (d : ℕ) (i : Fin 8) :
    Trim.push (law (d+1+2) (200*(d+1+2))) (orderedRestriction (eightEquiv d) i (ordering d i)) =
      fairMass (fun ω : History (d+1+2) (200*(d+1+2)) => run (d+1+2) (200*(d+1+2)) ω ∘ domain d i) := by
  simpa only [law, Function.comp_def, orderedRestriction, restriction, domain] using
    Trim.push_fairMass (run (d+1+2) (200*(d+1+2))) (orderedRestriction (eightEquiv d) i (ordering d i))

lemma push_uniform_ordered (d : ℕ) (i : Fin 8) :
    Trim.push (fun _ : State (d+1+2) => (Fintype.card (State (d+1+2)) : ℝ)⁻¹)
      (orderedRestriction (eightEquiv d) i (ordering d i)) =
      fairMass (fun g : State (d+1+2) => g ∘ domain d i) := by
  rw [Trim.uniform_eq_fairMass_id]
  simpa only [Function.comp_def, orderedRestriction, restriction, domain, id_eq] using
    Trim.push_fairMass (id : State (d+1+2) → State (d+1+2)) (orderedRestriction (eightEquiv d) i (ordering d i))

lemma discarded_nonneg (d : ℕ) : 0 ≤ discarded d :=
  Trim.discarded_nonneg _ _ (law_nonneg _ _)

lemma discarded_le (d : ℕ) : discarded d ≤ 16 * Conditional.marginalRate d := by
  have h := discarded_ordered_bound (eightEquiv d) (ordering d) (law (d+1+2) (200*(d+1+2)))
    (law_nonneg (d+1+2) (200*(d+1+2))) (law_sum (d+1+2) (200*(d+1+2)))
  simp only [push_law_ordered, push_uniform_ordered] at h
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Conditional.marginal_tv_rate d (domain d i) (domain_injective d i))
  have hc : (∑ _ : Fin 8, Conditional.marginalRate d) = 8 * Conditional.marginalRate d := by simp
  rw [hc] at hb
  exact h.trans (by linarith)

lemma discarded_tendsto : Tendsto discarded atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using Conditional.marginalRate_tendsto.const_mul 16)
    discarded_nonneg discarded_le

end Block

end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_BlockLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp
open scoped Classical

theorem law_realPower (d t k : ℕ) :
    law d (k*t) = Fourier.realPower (law d t) k := by
  induction k with
  | zero =>
      funext g
      simp only [Nat.zero_mul, law, run, List.ofFn_zero, List.reverse_nil, List.prod_nil,
        fairMass, Fourier.realPower]
      by_cases hg : g = 1
      · subst g
        simp
      · simp [hg, Ne.symm hg]
  | succ k ih =>
      rw [Nat.succ_mul, law_add, ih]
      rfl

namespace Specht
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

theorem trimmed_eight_tv (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (μ : Equiv.Perm α → ℝ)
    (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1)
    (hb : ∑ g, (μ g : ℂ) * complexSign g = 0)
    (hδ : Trim.discarded ψ μ ≤ 1/2) :
    tv (realPower μ 8) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) ≤
      8 * Trim.discarded ψ μ + (1/2 : ℝ) * Real.sqrt
        (2 * (2 * Trim.discarded ψ μ)^16 +
          (32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α)) := by
  let ν := Trim.normalized ψ μ
  have hd : Trim.discarded ψ μ < 1 := by linarith
  have hν : ∀ g, 0 ≤ ν g := Trim.normalized_nonneg ψ μ hμ hd
  have hν1 : ∑ g, ν g = 1 := Trim.normalized_sum ψ μ h1 hd
  have hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      4 * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
    intro i g
    convert Trim.normalized_coset ψ μ hμ hδ i g using 1
    apply Finset.sum_congr rfl
    intro h _
    congr 4
    exact Subsingleton.elim _ _
  have hpar := Trim.normalized_bias ψ μ hμ h1 hd complexSign
    (fun g => (complexSign_norm g).le) hb
  have hfour := permutation_eight_bound hn ψ ν 4 hν hν1 (by norm_num) hcoset
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hpar 16
  have hsq : (∑ g, |realPower ν 8 g - (Fintype.card (Equiv.Perm α) : ℝ)⁻¹|)^2 ≤
      2 * (2 * Trim.discarded ψ μ)^16 +
        (32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α) := by
    norm_num only [show (8:ℝ)*4 = 32 by norm_num] at hfour
    exact hfour.trans (by gcongr)
  have hnorm := Real.le_sqrt_of_sq_le hsq
  calc
    _ ≤ tv (realPower μ 8) (realPower ν 8) +
        tv (realPower ν 8) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) := tv_triangle _ _ _
    _ ≤ 8 * Trim.discarded ψ μ + _ := add_le_add
      (by simpa only [ν, Nat.cast_ofNat, Trim.normalized_tv ψ μ hμ h1 hd] using tv_realPower μ ν hμ h1 hν hν1 8)
      (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0:ℝ) ≤ 1/2))

end Specht
end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_EightBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp
open scoped Classical

lemma law_complexSign_zero (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    (∑ g : State d, (law d t g : ℂ) * Specht.complexSign g) = 0 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have h := congrArg (fun x : ℝ => (x : ℂ)) (Parity.law_sign_zero d t)
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, Parity.sign,
    Specht.complexSign_eq, Complex.ofReal_intCast] using h

namespace Block
open Thorp.Fourier Thorp.Specht

lemma exceptional_cube_tendsto :
    Tendsto (fun d : ℕ => exceptionalReciprocalSum (2^d)) atTop (nhds 0) :=
  exceptionalReciprocalSum_tendsto.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

lemma fullRate_tendsto : Tendsto fullRate atTop (nhds 0) := by
  change Tendsto (fun d : ℕ => 8 * discarded d + (1/2 : ℝ) * Real.sqrt
    (2 * (2 * discarded d)^16 + (96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))) atTop (nhds 0)
  have he := exceptional_cube_tendsto.comp (tendsto_add_atTop_nat 3)
  have hb := ((discarded_tendsto.const_mul 2).pow 16).const_mul 2
  have hs := (hb.add (he.const_mul ((96:ℝ)^8))).sqrt
  simpa only [Nat.add_assoc, Function.comp_def, mul_zero, zero_pow (by decide : 16 ≠ 0),
    add_zero, Real.sqrt_zero] using (discarded_tendsto.const_mul 8).add (hs.const_mul (1/2 : ℝ))

lemma reciprocal_atMost_three :
    ∀ᶠ d : ℕ in atTop, (permutationFamily (Position d)).reciprocalSum ≤ 3 := by
  have he : ∀ᶠ d : ℕ in atTop, exceptionalReciprocalSum (2^d) < 1 :=
    (tendsto_order.1 exceptional_cube_tendsto).2 1 (by norm_num)
  filter_upwards [he] with d hd
  have h := full_reciprocal_bound (2^d)
  have hc : (permutationFamily (Position d)).reciprocalSum = (symmetricFamily (2^d)).reciprocalSum := by
    change (symmetricFamily (Fintype.card (Position d))).reciprocalSum = _
    rw [card_position]
  rw [hc]
  linarith

lemma distance_eight_eventually :
    ∀ᶠ d : ℕ in atTop, distance (d+1+2) (1600*(d+1+2)) ≤ fullRate d := by
  have hd : ∀ᶠ d : ℕ in atTop, discarded d ≤ 1/2 :=
    ((tendsto_order.1 discarded_tendsto).2 (1/2) (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hd, reciprocal_atMost_three, eventually_ge_atTop 1] with d hδ hR hd1
  have hn : 16 ≤ Fintype.card (Position (d+1+2)) := by
    rw [card_position]
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^(d+1+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let : Nontrivial (Position (d+1+2)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hbound := trimmed_eight_tv hn (embedding (eightEquiv d)) (law (d+1+2) (200*(d+1+2)))
    (law_nonneg (d+1+2) (200*(d+1+2))) (law_sum (d+1+2) (200*(d+1+2)))
    (law_complexSign_zero _ _ (by omega) (by omega)) hδ
  have hpower : law (d+1+2) (1600*(d+1+2)) = realPower (law (d+1+2) (200*(d+1+2))) 8 := by
    rw [show 1600*(d+1+2) = 8 * (200*(d+1+2)) by omega]
    exact law_realPower (d+1+2) (200*(d+1+2)) 8
  change tv (law (d+1+2) (1600*(d+1+2)))
    (fun _ => 1 / (Fintype.card (State (d+1+2)) : ℝ)) ≤ fullRate d
  simp only [one_div]
  rw [hpower]
  apply hbound.trans
  unfold fullRate
  refine add_le_add (le_refl _) ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  refine add_le_add (le_refl _) ?_
  rw [card_position]
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun p _ => by
    change 0 ≤ (if 0 < defect p then inverseDegree p else 0)
    split_ifs <;> first | exact inverseDegree_nonneg p | exact le_rfl))
  apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (permutationFamily (Position d)).reciprocalSum_nonneg)
  linarith

lemma full_mixing_shift :
    Tendsto (fun d : ℕ => distance (d+1+2) (1600*(d+1+2))) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun d => by unfold distance tv; positivity))
    distance_eight_eventually fullRate_tendsto

end Block
end Thorp

end

end OAI
end

section
-- module Solutions.OAIQ3_Thorp.ThorpShuffle_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

theorem full_mixing :
    Tendsto (fun d : ℕ => distance d (1600 * d)) atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  simpa only [Nat.add_assoc] using Block.full_mixing_shift

theorem mixingTime_isBigO_orderFunction :
    Asymptotics.IsBigO atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1600, ?_⟩
  have he : ∀ᶠ d : ℕ in atTop, distance d (1600*d) < 1/4 :=
    full_mixing.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1/4))
  filter_upwards [he] with d hd
  have ht : mixingTime d ≤ 1600*d := Nat.sInf_le hd.le
  simp only [orderFunction, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (mixingTime d)),
    abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)]
  exact_mod_cast ht

theorem mixingTime_isTheta_orderFunction :
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ)) orderFunction :=
  ⟨mixingTime_isBigO_orderFunction, orderFunction_isBigO_mixingTime⟩

theorem mixingTime_isTheta_log_q3_oai :
    Asymptotics.IsTheta atTop (fun d : ℕ => (mixingTime d : ℝ))
      (fun d : ℕ => Real.log (2^d : ℝ)) := by
  have h := Asymptotics.IsTheta.const_mul_right
    (show Real.log 2 ≠ 0 from (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne')
    mixingTime_isTheta_orderFunction
  simpa only [orderFunction, Real.log_pow, mul_comm] using h

end Thorp

end

end OAI
end

theorem solution : type_of% @OAI.Thorp.mixingTime_isTheta_log_q3_oai := @OAI.Thorp.mixingTime_isTheta_log_q3_oai
