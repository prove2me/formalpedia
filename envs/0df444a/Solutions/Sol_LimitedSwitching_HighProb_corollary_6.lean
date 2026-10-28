-- Prove2me | solution 1 for LimitedSwitching.HighProb.corollary_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-28T10:32:45.072471+00:00
-- url     : https://prove2.me/submissions/cc9685c0-ef4f-4bb0-95e0-92b7dc8775e8

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting



section
namespace PriorFPL
namespace PriorSwitching
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Aux_lemma17
open LimitedSwitching.HighProb

theorem argmin_le {n : ℕ} [NeZero n] (v : Fin n → ℝ) (j : Fin n) :
    v (argminFin v) ≤ v j := by
  have hmem : argminFin v ∈
      Finset.univ.filter (fun i => v i = Finset.univ.inf' Finset.univ_nonempty v) := by
    unfold argminFin
    exact Finset.min'_mem _ _
  rw [Finset.mem_filter] at hmem
  rw [hmem.2]
  exact Finset.inf'_le _ (Finset.mem_univ j)

theorem btl {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ s ∈ Finset.range (T + 1),
        ℓ s (argminFin (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun s => ℓ s _) (T + 1)]
    have h := argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j)
      (argminFin (fun j => ∑ s ∈ Finset.range (T + 1 + 1), ℓ s j))
    linarith

end Aux_lemma17

open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (i : Fin n) :
    ∑ t ∈ Finset.range (T + 1),
        ℓ t (argminFin (fun j => ∑ s ∈ Finset.range (t + 1), ℓ s j))
      ≤ ∑ t ∈ Finset.range (T + 1), ℓ t i := by
  have h1 := Aux_lemma17.btl ℓ T
  have h2 := Aux_lemma17.argmin_le (fun j => ∑ s ∈ Finset.range (T + 1), ℓ s j) i
  linarith

end PriorSwitching

open LimitedSwitching.HighProb
namespace Queelius.Switching

lemma sum_shift (f : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T+1), f (s+1) = ∑ t ∈ Finset.Icc 1 (T+1), f t := by
  apply Finset.sum_bij (fun s _ => s+1)
  · intro s hs
    simp only [Finset.mem_range] at hs
    simp only [Finset.mem_Icc]
    omega
  · intro s hs t ht he
    omega
  · intro t ht
    simp only [Finset.mem_Icc] at ht
    refine ⟨t-1, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro s hs
    rfl

lemma sum_no_zero (f : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T+1), (if s=0 then 0 else f s) = ∑ t ∈ Finset.Icc 1 T, f t := by
  have hsub : Finset.Icc 1 T ⊆ Finset.range (T+1) := by
    intro t ht
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  calc
    _ = ∑ t ∈ Finset.Icc 1 T, (if t=0 then 0 else f t) := by
      symm
      apply Finset.sum_subset hsub
      intro t ht hn
      have he : t=0 := by
        simp only [Finset.mem_range] at ht
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      simp [he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [Finset.mem_Icc] at ht
      simp [show t≠0 by omega]

lemma switch_count_bound {n : ℕ} (a : ℕ → Fin n) (T : ℕ) :
    ((Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))).card ≤ switches T a + 1 := by
  let S := (Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))
  let U := (Finset.Icc 2 T).filter (fun t => a t ≠ a (t-1))
  have hsub : S.image (fun t => t+1) ⊆ insert (T+1) U := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have ht' := Finset.mem_filter.mp ht
    have htt := Finset.mem_Icc.mp ht'.1
    by_cases he : t+1=T+1
    · simp [he]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa using Ne.symm ht'.2
  have hc : (S.image (fun t => t+1)).card = S.card :=
    Finset.card_image_of_injective S (by intro i j h; dsimp only at h; omega)
  have hh := Finset.card_le_card hsub
  rw [hc] at hh
  have hi := Finset.card_insert_le (T+1) U
  change S.card ≤ U.card+1
  omega

lemma loss_error_bound {n : ℕ} (a : ℕ → Fin n) (ℓ : ℕ → Fin n → ℝ) (T : ℕ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i - ℓ t j| ≤ M) :
    ∑ t ∈ Finset.Icc 1 T, (ℓ t (a t) - ℓ t (a (t+1))) ≤
      M*((switches T a : ℝ)+1) := by
  let S := (Finset.Icc 1 T).filter (fun t => a t ≠ a (t+1))
  have hsum : (∑ t ∈ Finset.Icc 1 T, (ℓ t (a t)-ℓ t (a (t+1)))) ≤
      ∑ t ∈ Finset.Icc 1 T, (if a t ≠ a (t+1) then M else 0) := by
    apply Finset.sum_le_sum
    intro t ht
    by_cases he : a t = a (t+1)
    · simp [he]
    · simp only [if_pos he]
      exact le_trans (le_abs_self _) (hM t ht _ _)
  have heq : (∑ t ∈ Finset.Icc 1 T, (if a t ≠ a (t+1) then M else 0)) = (S.card : ℝ)*M := by
    rw [← Finset.sum_filter]
    simp [S]
  rw [heq] at hsum
  have hc : (S.card : ℝ) ≤ (switches T a : ℝ)+1 := by
    exact_mod_cast switch_count_bound a T
  nlinarith

theorem comparator_bound {n : ℕ} [NeZero n] (P ℓ : ℕ → Fin n → ℝ) (T : ℕ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i-ℓ t j| ≤ M)
    (i : Fin n) :
    (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ t)) - (∑ t ∈ Finset.Icc 1 T, ℓ t i) ≤
      M*((switches T (fplPlay P ℓ) : ℝ)+1) +
        (⨆ j, ∑ t ∈ Finset.Icc 1 (T+1), P t j) -
        ∑ t ∈ Finset.Icc 1 (T+1), P t (fplPlay P ℓ t) := by
  have hb := PriorSwitching.solution (fun s j => (if s=0 then 0 else ℓ s j) + P (s+1) j) T i
  change (∑ s ∈ Finset.range (T+1),
      ((if s=0 then 0 else ℓ s (fplPlay P ℓ (s+1))) + P (s+1) (fplPlay P ℓ (s+1)))) ≤
      ∑ s ∈ Finset.range (T+1), ((if s=0 then 0 else ℓ s i) + P (s+1) i) at hb
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hb
  rw [sum_no_zero, sum_shift (fun t => P t (fplPlay P ℓ t)) T,
    sum_no_zero, sum_shift (fun t => P t i) T] at hb
  have hp : (∑ t ∈ Finset.Icc 1 (T+1), P t i) ≤
      (⨆ j, ∑ t ∈ Finset.Icc 1 (T+1), P t j) := le_ciSup (Finite.bddAbove_range (fun j => ∑ t ∈ Finset.Icc 1 (T+1), P t j)) i
  have he : (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ t)) =
      (∑ t ∈ Finset.Icc 1 T, ℓ t (fplPlay P ℓ (t+1))) +
      ∑ t ∈ Finset.Icc 1 T, (ℓ t (fplPlay P ℓ t)-ℓ t (fplPlay P ℓ (t+1))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have herr := loss_error_bound (fplPlay P ℓ) ℓ T M hM0 hM
  linarith

end Queelius.Switching

open LimitedSwitching.HighProb in
theorem solution {n : ℕ} [NeZero n] (P : ℕ → Fin n → ℝ) (ℓ : ℕ → Fin n → ℝ) (T : ℕ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i-ℓ t j| ≤ M) :
    regret T ℓ (fplPlay P ℓ) ≤ M*((switches T (fplPlay P ℓ) : ℝ)+1) +
      (⨆ i, ∑ t ∈ Finset.Icc 1 (T+1), P t i) -
      ∑ t ∈ Finset.Icc 1 (T+1), P t (fplPlay P ℓ t) := by
  let i := argminFin (fun j => ∑ t ∈ Finset.Icc 1 T, ℓ t j)
  have hmin : (⨅ j, ∑ t ∈ Finset.Icc 1 T, ℓ t j) = ∑ t ∈ Finset.Icc 1 T, ℓ t i := by
    apply le_antisymm
    · exact ciInf_le (Finite.bddBelow_range _) i
    · apply le_ciInf
      intro j
      exact PriorSwitching.Aux_lemma17.argmin_le (fun j => ∑ t ∈ Finset.Icc 1 T, ℓ t j) j
  unfold regret
  rw [hmin]
  exact Queelius.Switching.comparator_bound P ℓ T M hM0 hM i


namespace Queelius.Switching.Controls

theorem zero_horizon {n : ℕ} [NeZero n] (ℓ : ℕ → Fin n → ℝ) (a : ℕ → Fin n) :
    regret 0 ℓ a = 0 := by simp [regret]

theorem constant_action_switches {n : ℕ} (i : Fin n) (T : ℕ) :
    switches T (fun _ => i) = 0 := by simp [switches]

theorem terminal_switch :
    switches 1 (fun t : ℕ => (if t ≤ 1 then 0 else 1 : Fin 2)) = 0 ∧
    switches 2 (fun t : ℕ => (if t ≤ 1 then 0 else 1 : Fin 2)) = 1 ∧
    ((Finset.Icc 1 1).filter (fun t : ℕ =>
      (if t ≤ 1 then 0 else 1 : Fin 2) ≠ (if t+1 ≤ 1 then 0 else 1 : Fin 2))).card = 1 := by
  decide

end Queelius.Switching.Controls

end PriorFPL
end

open LimitedSwitching.HighProb
namespace Queelius.FPLStarEpoch

noncomputable def perturb {n : ℕ} (R : Fin n → ℝ) (ε : ℝ) (t : ℕ) (i : Fin n) : ℝ :=
  if t=1 then -R i/ε else 0

lemma past_sum (f : ℕ → ℝ) (k : ℕ) :
    (∑ s ∈ Finset.range (k+1), if s=0 then 0 else f s) = ∑ s : Fin k, f (s.val+1) := by
  rw [Finset.sum_range_succ']
  simp [Finset.sum_range]

lemma perturb_prefix {n : ℕ} (R : Fin n → ℝ) (ε : ℝ) (k : ℕ) (i : Fin n) :
    (∑ s ∈ Finset.range (k+1), perturb R ε (s+1) i) = -R i/ε := by
  simp [perturb]

lemma actions_equal {n : ℕ} [NeZero n] (R : Fin n → ℝ) (ε : ℝ)
    (ℓ : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    play (fplStar ε) R ℓ t = fplPlay (perturb R ε) ℓ t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  change argminFin (fun i => -R i/ε + ∑ s : Fin k, ℓ (s.val+1) i) =
    argminFin (fun i => ∑ s ∈ Finset.range (k+1),
      ((if s=0 then 0 else ℓ s i)+perturb R ε (s+1) i))
  congr 1
  funext i
  rw [Finset.sum_add_distrib,past_sum,perturb_prefix]
  ring

lemma regret_equal {n : ℕ} [NeZero n] (R : Fin n → ℝ) (ε : ℝ)
    (ℓ : ℕ → Fin n → ℝ) (T : ℕ) :
    regret T ℓ (play (fplStar ε) R ℓ) = regret T ℓ (fplPlay (perturb R ε) ℓ) := by
  unfold regret
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [actions_equal R ε ℓ t (Finset.mem_Icc.mp ht).1]

lemma switches_equal {n : ℕ} [NeZero n] (R : Fin n → ℝ) (ε : ℝ)
    (ℓ : ℕ → Fin n → ℝ) (T : ℕ) :
    switches T (play (fplStar ε) R ℓ) = switches T (fplPlay (perturb R ε) ℓ) := by
  unfold switches
  congr 1
  apply Finset.filter_congr
  intro t ht
  have h := Finset.mem_Icc.mp ht
  rw [actions_equal R ε ℓ t (by omega), actions_equal R ε ℓ (t-1) (by omega)]

lemma perturb_total {n : ℕ} (R : Fin n → ℝ) (ε : ℝ) (T : ℕ) (i : Fin n) :
    (∑ t ∈ Finset.Icc 1 (T+1), perturb R ε t i) = -R i/ε := by
  simp [perturb]

lemma perturb_played {n : ℕ} (R : Fin n → ℝ) (ε : ℝ) (T : ℕ) (a : ℕ → Fin n) :
    (∑ t ∈ Finset.Icc 1 (T+1), perturb R ε t (a t)) = -R (a 1)/ε := by
  simp [perturb]

lemma loss_difference {n : ℕ} (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (T : ℕ) : ∀ t ∈ Finset.Icc 1 T, ∀ i j, |ℓ t i-ℓ t j| ≤ 1 := by
  intro t ht i j
  have hi := hℓ t (Finset.mem_Icc.mp ht).1 i
  have hj := hℓ t (Finset.mem_Icc.mp ht).1 j
  rw [abs_le]
  constructor <;> linarith [hi.1,hi.2,hj.1,hj.2]

theorem per_epoch_bound {n : ℕ} [NeZero n] (R : Fin n → ℝ) (hR : ∀ i, 0 ≤ R i)
    (ε : ℝ) (hε : 0 < ε) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) (T : ℕ) :
    regret T ℓ (play (fplStar ε) R ℓ) ≤
      (switches T (play (fplStar ε) R ℓ) : ℝ)+1 +
        Finset.univ.sup' Finset.univ_nonempty R / ε := by
  have h := PriorFPL.solution (perturb R ε) ℓ T 1 (by norm_num) (loss_difference ℓ hℓ T)
  rw [perturb_played] at h
  have hm : (⨆ i, ∑ t ∈ Finset.Icc 1 (T+1), perturb R ε t i) ≤ 0 := by
    apply ciSup_le
    intro i
    rw [perturb_total]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hR i)) hε.le
  have hx : R (fplPlay (perturb R ε) ℓ 1) ≤ Finset.univ.sup' Finset.univ_nonempty R :=
    Finset.le_sup' R (Finset.mem_univ _)
  have hd := div_le_div_of_nonneg_right hx hε.le
  rw [regret_equal,switches_equal]
  simp only [one_mul,neg_div,sub_neg_eq_add] at h
  linarith

theorem comparator_bound {n : ℕ} [NeZero n] (R : Fin n → ℝ) (hR : ∀ i, 0 ≤ R i)
    (ε : ℝ) (hε : 0 < ε) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) (T : ℕ) (i : Fin n) :
    (∑ t ∈ Finset.Icc 1 T, ℓ t (play (fplStar ε) R ℓ t)) - (∑ t ∈ Finset.Icc 1 T, ℓ t i) ≤
      (switches T (play (fplStar ε) R ℓ) : ℝ)+1 +
        Finset.univ.sup' Finset.univ_nonempty R / ε := by
  have h := per_epoch_bound R hR ε hε ℓ hℓ T
  have hm := ciInf_le (Finite.bddBelow_range (fun j => ∑ t ∈ Finset.Icc 1 T, ℓ t j)) i
  unfold regret at h
  linarith

def shifted_loss {n : ℕ} (st : ℕ) (ℓ : ℕ → Fin n → ℝ) (u : ℕ) (i : Fin n) : ℝ :=
  ℓ (st+u-1) i

lemma shifted_loss_sequence {n : ℕ} (st : ℕ) (hst : 1 ≤ st)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) : IsLossSeq (shifted_loss st ℓ) := by
  intro u hu i
  apply hℓ (st+u-1) (by omega) i

lemma local_action_equal {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (ε : ℝ)
    (ℓ : ℕ → Fin n → ℝ) (e st r : ℕ) :
    localAct (fplStar ε) ω ℓ e st r =
      play (fplStar ε) (ω e) (shifted_loss st ℓ) (r-st+1) := by
  unfold localAct play fplStar shifted_loss
  congr 1

lemma metrics_congr_positive {n : ℕ} (a b : ℕ → Fin n) (ℓ : ℕ → Fin n → ℝ)
    (T : ℕ) (h : ∀ t, 1 ≤ t → a t=b t) : regret T ℓ a=regret T ℓ b ∧ switches T a=switches T b := by
  constructor
  · unfold regret
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [h t (Finset.mem_Icc.mp ht).1]
  · unfold switches
    congr 1
    apply Finset.filter_congr
    intro t ht
    have hh := Finset.mem_Icc.mp ht
    rw [h t (by omega),h (t-1) (by omega)]

theorem local_epoch_bound {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (e st L : ℕ) (hst : 1 ≤ st) :
    regret L (shifted_loss st ℓ) (fun u => localAct (fplStar ε) ω ℓ e st (st+u-1)) ≤
      (switches L (fun u => localAct (fplStar ε) ω ℓ e st (st+u-1)) : ℝ)+1 +
        Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by
  have ha : ∀ u, 1 ≤ u → localAct (fplStar ε) ω ℓ e st (st+u-1) =
      play (fplStar ε) (ω e) (shifted_loss st ℓ) u := by
    intro u hu
    rw [local_action_equal]
    congr 1
    omega
  have hm := metrics_congr_positive _ _ (shifted_loss st ℓ) L ha
  rw [hm.1,hm.2]
  exact per_epoch_bound (ω e) (hω e) ε hε (shifted_loss st ℓ) (shifted_loss_sequence st hst ℓ hℓ) L

end Queelius.FPLStarEpoch

section
open LimitedSwitching.HighProb
namespace Queelius.BatchEpoch

lemma state_bounds {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (k : ℕ) :
    1 ≤ (batchRun A S ω ℓ k).start ∧ (batchRun A S ω ℓ k).start ≤ k + 1 ∧
      (batchRun A S ω ℓ k).epoch ≤ k := by
  induction k with
  | zero => simp [batchRun]
  | succ k ih =>
    simp only [batchRun]
    split_ifs <;> dsimp <;> omega

lemma state_action {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (k : ℕ) :
    (batchRun A S ω ℓ k).act = localAct A ω ℓ
      (batchRun A S ω ℓ k).epoch (batchRun A S ω ℓ k).start (k + 1) := by
  cases k with
  | zero => rfl
  | succ k => simp only [batchRun]; split_ifs <;> rfl

lemma epoch_step {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (k : ℕ) :
    (batchRun A S ω ℓ (k + 1)).epoch = (batchRun A S ω ℓ k).epoch ∨
      ((batchRun A S ω ℓ (k + 1)).epoch = (batchRun A S ω ℓ k).epoch + 1 ∧
       (batchRun A S ω ℓ (k + 1)).start = k + 2) := by
  simp only [batchRun]
  split_ifs <;> simp

lemma localAct_congr {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n)
    (ω : ℕ → Ω) (ℓ L : ℕ → Fin n → ℝ) (e st r : ℕ) (hst : 1 ≤ st) (hsr : st ≤ r)
    (h : ∀ t, 1 ≤ t → t < r → ℓ t = L t) :
    localAct A ω ℓ e st r = localAct A ω L e st r := by
  unfold localAct
  congr 1
  funext s
  apply h
  · omega
  · have hs := s.isLt
    omega

lemma run_congr {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ L : ℕ → Fin n → ℝ) (k : ℕ)
    (h : ∀ t, 1 ≤ t → t ≤ k → ℓ t = L t) :
    batchRun A S ω ℓ k = batchRun A S ω L k := by
  induction k with
  | zero =>
    have ha := localAct_congr A ω ℓ L 0 1 1 le_rfl le_rfl (by intro t ht ht1; omega)
    simpa only [batchRun] using congrArg (fun a => BState.mk 0 1 0 a) ha
  | succ k ih =>
    have hi := ih (by intro t ht hk; exact h t ht (by omega))
    have hb := state_bounds A S ω L k
    have ha := localAct_congr A ω ℓ L (batchRun A S ω L k).epoch
      (batchRun A S ω L k).start (k + 2) hb.1 (by omega)
      (by intro t ht htk; exact h t ht (by omega))
    have hf := localAct_congr A ω ℓ L ((batchRun A S ω L k).epoch + 1)
      (k + 2) (k + 2) (by omega) le_rfl
      (by intro t ht htk; exact h t ht (by omega))
    simp only [batchRun, hi, ha, hf]

lemma batch_played {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    play (batch A S) ω ℓ t = (batchRun A S ω ℓ (t - 1)).act := by
  unfold play batch
  apply congrArg BState.act
  apply run_congr
  intro r hr hrt
  unfold padPast
  rw [dif_pos ⟨hr, hrt⟩]
  change ℓ (r - 1 + 1) = ℓ r
  congr 1
  omega

lemma epoch_history {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (k : ℕ) :
    ∀ r, (batchRun A S ω ℓ k).start ≤ r → r ≤ k + 1 →
      (batchRun A S ω ℓ (r - 1)).act =
        localAct A ω ℓ (batchRun A S ω ℓ k).epoch (batchRun A S ω ℓ k).start r := by
  induction k with
  | zero =>
    intro r hr hr1
    have he : r = 1 := by simpa only [batchRun] using le_antisymm hr1 hr
    subst r
    rfl
  | succ k ih =>
    let st := batchRun A S ω ℓ k
    let c := localAct A ω ℓ st.epoch st.start (k + 2)
    let cnt := st.count + if c ≠ st.act then 1 else 0
    by_cases hc : (cnt : ℝ) ≤ S
    · have he : batchRun A S ω ℓ (k + 1) = ⟨st.epoch, st.start, cnt, c⟩ := by
        exact if_pos hc
      intro r hr hrr
      change (batchRun A S ω ℓ (r - 1)).act = _
      rw [he] at hr ⊢
      dsimp at hr ⊢
      by_cases hle : r ≤ k + 1
      · exact ih r hr hle
      · have hrr' : r = k + 2 := by omega
        subst r
        rw [show k + 2 - 1 = k + 1 by omega, he]
    · have he : batchRun A S ω ℓ (k + 1) =
          ⟨st.epoch + 1, k + 2, 0, localAct A ω ℓ (st.epoch + 1) (k + 2) (k + 2)⟩ := by
        exact if_neg hc
      intro r hr hrr
      rw [he] at hr ⊢
      dsimp at hr ⊢
      have hrr' : r = k + 2 := by omega
      subst r
      rw [show k + 2 - 1 = k + 1 by omega, he]


lemma switches_interval {n : ℕ} (a : ℕ → Fin n) (s T : ℕ) (hs : 1 ≤ s) (hT : s ≤ T) :
    switches (s - 1) a + switches (T - s + 1) (fun u => a ((s - 1) + u)) ≤ switches T a := by
  classical
  let I := (Finset.Icc 2 (s - 1)).filter (fun t => a t ≠ a (t - 1))
  let J := (Finset.Icc 2 (T - s + 1)).filter (fun u => a (s - 1 + u) ≠ a (s - 1 + (u - 1)))
  let K := J.image (fun u => s - 1 + u)
  have hd : Disjoint I K := by
    apply Finset.disjoint_left.mpr
    intro t ht hk
    have ht' := (Finset.mem_filter.mp ht).1
    rcases Finset.mem_image.mp hk with ⟨u, hu, he⟩
    have hu' := (Finset.mem_filter.mp hu).1
    simp only [Finset.mem_Icc] at ht' hu'
    omega
  have hsub : I ∪ K ⊆ (Finset.Icc 2 T).filter (fun t => a t ≠ a (t - 1)) := by
    intro t ht
    rcases Finset.mem_union.mp ht with hi | hk
    · have hi' := Finset.mem_filter.mp hi
      have hi'' := Finset.mem_Icc.mp hi'.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi''.1, by omega⟩, hi'.2⟩
    · rcases Finset.mem_image.mp hk with ⟨u, hu, rfl⟩
      have hu' := Finset.mem_filter.mp hu
      have hu'' := Finset.mem_Icc.mp hu'.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      have he : s - 1 + u - 1 = s - 1 + (u - 1) := by omega
      rw [he]
      exact hu'.2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hcard
  have hk : K.card = J.card := Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)
  rw [hk] at hcard
  exact hcard

lemma sum_shift_interval (f : ℕ → ℝ) (s T : ℕ) (hs : 1 ≤ s) (hT : s ≤ T) :
    (∑ u ∈ Finset.Icc 1 (T - s + 1), f (s - 1 + u)) = ∑ t ∈ Finset.Icc s T, f t := by
  apply Finset.sum_bij (fun u _ => s - 1 + u)
  · intro u hu
    have hu' := Finset.mem_Icc.mp hu
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro u hu v hv he
    omega
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    refine ⟨t - s + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro u hu
    rfl


lemma metrics_congr_upto {n : ℕ} (a b : ℕ → Fin n) (ℓ : ℕ → Fin n → ℝ)
    (T : ℕ) (h : ∀ t, 1 ≤ t → t ≤ T → a t = b t) :
    regret T ℓ a = regret T ℓ b ∧ switches T a = switches T b := by
  constructor
  · unfold regret
    congr 1
    exact Finset.sum_congr rfl (fun t ht => by rw [h t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2])
  · unfold switches
    congr 1
    apply Finset.filter_congr
    intro t ht
    have hh := Finset.mem_Icc.mp ht
    rw [h t (by omega) hh.2, h (t - 1) (by omega) (by omega)]

lemma prefix_sum_split (f : ℕ → ℝ) (s T : ℕ) (hs : 1 ≤ s) (hT : s ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, f t) =
      (∑ t ∈ Finset.Icc 1 (s - 1), f t) + ∑ t ∈ Finset.Icc s T, f t := by
  have he : Finset.Icc 1 T = Finset.Icc 1 (s - 1) ∪ Finset.Icc s T := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc 1 (s - 1)) (Finset.Icc s T) := by
    apply Finset.disjoint_left.mpr
    intro t ht hk
    have ht' := Finset.mem_Icc.mp ht
    have hk' := Finset.mem_Icc.mp hk
    omega
  rw [he, Finset.sum_union hd]

end Queelius.BatchEpoch

end

open LimitedSwitching.HighProb
namespace Queelius.BatchEpoch

noncomputable def runPlay {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (t : ℕ) : Fin n :=
  (batchRun A S ω ℓ (t - 1)).act

lemma epoch_comparator {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S : ℝ) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (k : ℕ) (i : Fin n) :
    let st := batchRun (fplStar ε) S ω ℓ k
    let a := runPlay (fplStar ε) S ω ℓ
    (∑ u ∈ Finset.Icc 1 (k + 1 - st.start + 1), ℓ (st.start - 1 + u) (a (st.start - 1 + u))) -
      (∑ u ∈ Finset.Icc 1 (k + 1 - st.start + 1), ℓ (st.start - 1 + u) i) ≤
      (switches (k + 1 - st.start + 1) (fun u => a (st.start - 1 + u)) : ℝ) + 1 +
        Finset.univ.sup' Finset.univ_nonempty (ω st.epoch) / ε := by
  dsimp only
  let st := batchRun (fplStar ε) S ω ℓ k
  let a := runPlay (fplStar ε) S ω ℓ
  let L := k + 1 - st.start + 1
  have hb : 1 ≤ st.start ∧ st.start ≤ k + 1 ∧ st.epoch ≤ k := state_bounds (fplStar ε) S ω ℓ k
  have ha : ∀ u, 1 ≤ u → u ≤ L →
      play (fplStar ε) (ω st.epoch) (Queelius.FPLStarEpoch.shifted_loss st.start ℓ) u =
        a (st.start - 1 + u) := by
    intro u hu huL
    have hr : st.start ≤ st.start - 1 + u := by omega
    have hrk : st.start - 1 + u ≤ k + 1 := by dsimp [L] at huL; omega
    have hh := epoch_history (fplStar ε) S ω ℓ k (st.start - 1 + u) hr hrk
    have hl := Queelius.FPLStarEpoch.local_action_equal ω ε ℓ st.epoch st.start (st.start - 1 + u)
    have he : st.start - 1 + u - st.start + 1 = u := by omega
    rw [he] at hl
    exact hl.symm.trans hh.symm
  have h := Queelius.FPLStarEpoch.comparator_bound (ω st.epoch) (hω st.epoch) ε hε
    (Queelius.FPLStarEpoch.shifted_loss st.start ℓ)
    (Queelius.FPLStarEpoch.shifted_loss_sequence st.start hb.1 ℓ hℓ) L i
  have hm := metrics_congr_upto _ (fun u => a (st.start - 1 + u))
    (Queelius.FPLStarEpoch.shifted_loss st.start ℓ) L ha
  rw [hm.2] at h
  have hsA : (∑ u ∈ Finset.Icc 1 L,
      Queelius.FPLStarEpoch.shifted_loss st.start ℓ u
        (play (fplStar ε) (ω st.epoch) (Queelius.FPLStarEpoch.shifted_loss st.start ℓ) u)) =
      ∑ u ∈ Finset.Icc 1 L, ℓ (st.start - 1 + u) (a (st.start - 1 + u)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    rw [ha u hu'.1 hu'.2]
    unfold Queelius.FPLStarEpoch.shifted_loss
    congr 1
    omega
  have hsI : (∑ u ∈ Finset.Icc 1 L, Queelius.FPLStarEpoch.shifted_loss st.start ℓ u i) =
      ∑ u ∈ Finset.Icc 1 L, ℓ (st.start - 1 + u) i := by
    apply Finset.sum_congr rfl
    intro u hu
    unfold Queelius.FPLStarEpoch.shifted_loss
    congr 1
    omega
  rw [hsA, hsI] at h
  exact h


lemma prefix_to_full {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S : ℝ) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (k : ℕ) (i : Fin n)
    (hpre : let st := batchRun (fplStar ε) S ω ℓ k
      let a := runPlay (fplStar ε) S ω ℓ
      (∑ t ∈ Finset.Icc 1 (st.start - 1), (ℓ t (a t) - ℓ t i)) ≤
        (switches (st.start - 1) a : ℝ) + st.epoch +
          ∑ e ∈ Finset.range st.epoch, Finset.univ.sup' Finset.univ_nonempty (ω e) / ε) :
    let st := batchRun (fplStar ε) S ω ℓ k
    let a := runPlay (fplStar ε) S ω ℓ
    (∑ t ∈ Finset.Icc 1 (k + 1), (ℓ t (a t) - ℓ t i)) ≤
      (switches (k + 1) a : ℝ) + (st.epoch + 1 : ℕ) +
        ∑ e ∈ Finset.range (st.epoch + 1), Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by
  let st := batchRun (fplStar ε) S ω ℓ k
  let a := runPlay (fplStar ε) S ω ℓ
  have hb : 1 ≤ st.start ∧ st.start ≤ k + 1 ∧ st.epoch ≤ k := state_bounds (fplStar ε) S ω ℓ k
  have hl := epoch_comparator ω hω ε hε S ℓ hℓ k i
  have hsw := switches_interval a st.start (k + 1) hb.1 hb.2.1
  have hsw' : (switches (st.start - 1) a : ℝ) +
      (switches (k + 1 - st.start + 1) (fun u => a (st.start - 1 + u)) : ℝ) ≤
        (switches (k + 1) a : ℝ) := by exact_mod_cast hsw
  have he : (∑ t ∈ Finset.Icc 1 (k + 1), (ℓ t (a t) - ℓ t i)) =
      (∑ t ∈ Finset.Icc 1 (st.start - 1), (ℓ t (a t) - ℓ t i)) +
      ((∑ u ∈ Finset.Icc 1 (k + 1 - st.start + 1), ℓ (st.start - 1 + u) (a (st.start - 1 + u))) -
       (∑ u ∈ Finset.Icc 1 (k + 1 - st.start + 1), ℓ (st.start - 1 + u) i)) := by
    rw [prefix_sum_split (fun t => ℓ t (a t) - ℓ t i) st.start (k + 1) hb.1 hb.2.1]
    rw [← sum_shift_interval (fun t => ℓ t (a t) - ℓ t i) st.start (k + 1) hb.1 hb.2.1,
      Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]
  change _ ≤ (switches (k + 1) a : ℝ) + (st.epoch + 1 : ℕ) + _
  rw [he, Finset.sum_range_succ]
  push_cast
  dsimp only at hpre hl
  linarith

lemma completed_prefix_bound {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S : ℝ) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (k : ℕ) (i : Fin n) :
    let st := batchRun (fplStar ε) S ω ℓ k
    let a := runPlay (fplStar ε) S ω ℓ
    (∑ t ∈ Finset.Icc 1 (st.start - 1), (ℓ t (a t) - ℓ t i)) ≤
      (switches (st.start - 1) a : ℝ) + st.epoch +
        ∑ e ∈ Finset.range st.epoch, Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by
  induction k with
  | zero => simp [batchRun, switches]
  | succ k ih =>
    let st := batchRun (fplStar ε) S ω ℓ k
    let c := localAct (fplStar ε) ω ℓ st.epoch st.start (k + 2)
    let cnt := st.count + if c ≠ st.act then 1 else 0
    by_cases hc : (cnt : ℝ) ≤ S
    · have he : batchRun (fplStar ε) S ω ℓ (k + 1) = ⟨st.epoch, st.start, cnt, c⟩ := if_pos hc
      dsimp only
      rw [he]
      exact ih
    · have he : batchRun (fplStar ε) S ω ℓ (k + 1) =
          ⟨st.epoch + 1, k + 2, 0, localAct (fplStar ε) ω ℓ (st.epoch + 1) (k + 2) (k + 2)⟩ := if_neg hc
      have hf := prefix_to_full ω hω ε hε S ℓ hℓ k i ih
      dsimp only
      rw [he]
      simpa only [show k + 2 - 1 = k + 1 by omega] using hf

lemma run_comparator {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S : ℝ) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (T : ℕ) (hT : 1 ≤ T) (i : Fin n) :
    let a := runPlay (fplStar ε) S ω ℓ
    (∑ t ∈ Finset.Icc 1 T, (ℓ t (a t) - ℓ t i)) ≤
      (switches T a : ℝ) + (numEpochs (fplStar ε) S ω ℓ T : ℝ) +
        ∑ e ∈ Finset.range (numEpochs (fplStar ε) S ω ℓ T),
          Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by
  have h := prefix_to_full ω hω ε hε S ℓ hℓ (T - 1) i
    (completed_prefix_bound ω hω ε hε S ℓ hℓ (T - 1) i)
  dsimp only at h ⊢
  rw [show T - 1 + 1 = T by omega] at h
  exact h

lemma run_regret {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S : ℝ) (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ)
    (T : ℕ) (hT : 1 ≤ T) :
    regret T ℓ (runPlay (fplStar ε) S ω ℓ) ≤
      (switches T (runPlay (fplStar ε) S ω ℓ) : ℝ) + (numEpochs (fplStar ε) S ω ℓ T : ℝ) +
        ∑ e ∈ Finset.range (numEpochs (fplStar ε) S ω ℓ T),
          Finset.univ.sup' Finset.univ_nonempty (ω e) / ε := by
  let a := runPlay (fplStar ε) S ω ℓ
  let B := (switches T a : ℝ) + (numEpochs (fplStar ε) S ω ℓ T : ℝ) +
    ∑ e ∈ Finset.range (numEpochs (fplStar ε) S ω ℓ T), Finset.univ.sup' Finset.univ_nonempty (ω e) / ε
  have h (i : Fin n) : (∑ t ∈ Finset.Icc 1 T, ℓ t (a t)) -
      (∑ t ∈ Finset.Icc 1 T, ℓ t i) ≤ B := by
    rw [← Finset.sum_sub_distrib]
    exact run_comparator ω hω ε hε S ℓ hℓ T hT i
  have hi : (∑ t ∈ Finset.Icc 1 T, ℓ t (a t)) - B ≤ ⨅ i, ∑ t ∈ Finset.Icc 1 T, ℓ t i := by
    apply le_ciInf
    intro i
    linarith [h i]
  change (∑ t ∈ Finset.Icc 1 T, ℓ t (a t)) - (⨅ i, ∑ t ∈ Finset.Icc 1 T, ℓ t i) ≤ B
  linarith

end Queelius.BatchEpoch

open LimitedSwitching.HighProb

theorem solution {n : ℕ} [NeZero n] (ω : ℕ → Fin n → ℝ) (hω : ∀ e i, 0 ≤ ω e i)
    (ε : ℝ) (hε : 0 < ε) (S' : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (ℓ : ℕ → Fin n → ℝ) (hℓ : IsLossSeq ℓ) :
    regret T ℓ (play (batch (fplStar ε) S') ω ℓ)
      ≤ (switches T (play (batch (fplStar ε) S') ω ℓ) : ℝ)
        + (numEpochs (fplStar ε) S' ω ℓ T : ℝ)
        + ∑ e ∈ Finset.range (numEpochs (fplStar ε) S' ω ℓ T),
            Finset.univ.sup' Finset.univ_nonempty (ω e) / ε  := by
  have h := Queelius.BatchEpoch.run_regret ω hω ε hε S' ℓ hℓ T hT
  have hm := Queelius.FPLStarEpoch.metrics_congr_positive
    (Queelius.BatchEpoch.runPlay (fplStar ε) S' ω ℓ) (play (batch (fplStar ε) S') ω ℓ) ℓ T
    (by intro t ht; exact (Queelius.BatchEpoch.batch_played (fplStar ε) S' ω ℓ t ht).symm)
  rw [hm.1, hm.2] at h
  exact h


namespace Queelius.BatchEpoch
lemma first_epoch_control {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) : numEpochs A S ω ℓ 1 = 1 := by
  simp [numEpochs, batchRun]

lemma negative_budget_control {Ω : Type*} {n : ℕ} (A : OnlineAlg Ω n) (S : ℝ) (hS : S < 0)
    (ω : ℕ → Ω) (ℓ : ℕ → Fin n → ℝ) (k : ℕ) :
    (batchRun A S ω ℓ k).epoch = k ∧ (batchRun A S ω ℓ k).start = k + 1 ∧
      (batchRun A S ω ℓ k).count = 0 := by
  induction k with
  | zero => simp [batchRun]
  | succ k ih =>
    let st := batchRun A S ω ℓ k
    let c := localAct A ω ℓ st.epoch st.start (k + 2)
    let cnt := st.count + if c ≠ st.act then 1 else 0
    have hc : ¬ (cnt : ℝ) ≤ S := by have := Nat.cast_nonneg (α := ℝ) cnt; linarith
    have he : batchRun A S ω ℓ (k + 1) =
        ⟨st.epoch + 1, k + 2, 0, localAct A ω ℓ (st.epoch + 1) (k + 2) (k + 2)⟩ := if_neg hc
    rw [he]
    dsimp
    exact ⟨congrArg Nat.succ ih.1, rfl, rfl⟩
end Queelius.BatchEpoch
