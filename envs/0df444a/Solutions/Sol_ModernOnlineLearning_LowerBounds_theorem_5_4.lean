-- Prove2me | solution 1 for ModernOnlineLearning.LowerBounds.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T07:54:51.862058+00:00
-- url     : https://prove2.me/submissions/06967cb0-6e66-472a-8e74-43f14991c3e1

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_phi
open scoped BigOperators
open MeasureTheory ModernOnlineLearning.LowerBounds

private lemma sum_split (f : ℕ → ℝ) {n T : ℕ} (hn : n ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, f t) =
      (∑ t ∈ Finset.Icc 1 n, f t) + ∑ t ∈ Finset.Icc (n+1) T, f t := by
  simpa only [Finset.Ico_add_one_right_eq_Icc] using
    (Finset.sum_Ico_consecutive f (by omega : 1 ≤ n+1) (by omega : n+1 ≤ T+1)).symm

private lemma triangular_sum (η : ℕ → ℝ) (a b : ℕ) :
    (∑ t ∈ Finset.Icc a b, ∑ i ∈ Finset.Ico a t, η i) =
      ∑ i ∈ Finset.Icc a b, ((b:ℝ)-i)*η i := by
  have h := (Finset.sum_Ico_Ico_comm' a (b+1) (fun i _ => η i)).symm
  simp only [Finset.Ico_add_one_right_eq_Icc] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : i ≤ b := (Finset.mem_Icc.mp hi).2
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  rw [show b+1-(i+1)=b-i by omega, Nat.cast_sub hib]

private def phase (n t : ℕ) : ℝ := if t ≤ n then -1 else 1
private noncomputable def trajectory (η : ℕ → ℝ) (n t : ℕ) : ℝ :=
  -(∑ i ∈ Finset.Ico 1 t, η i * phase n i)

private lemma trajectory_early (η : ℕ → ℝ) {n t : ℕ} (ht : t ≤ n+1) :
    trajectory η n t = ∑ i ∈ Finset.Ico 1 t, η i := by
  unfold trajectory
  have he : (∑ i ∈ Finset.Ico 1 t, η i * phase n i) =
      -∑ i ∈ Finset.Ico 1 t, η i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have : i ≤ n := by have := Finset.mem_Ico.mp hi; omega
    simp [phase,this]
  rw [he,neg_neg]

private lemma trajectory_late (η : ℕ → ℝ) {n t : ℕ} (ht : n+1 ≤ t) :
    trajectory η n t = (∑ i ∈ Finset.Icc 1 n, η i) - ∑ i ∈ Finset.Ico (n+1) t, η i := by
  unfold trajectory
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ n+1) ht]
  have he : (∑ i ∈ Finset.Ico 1 (n+1), η i * phase n i) =
      -∑ i ∈ Finset.Icc 1 n, η i := by
    rw [Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [phase,(Finset.mem_Icc.mp hi).2]
  have hl : (∑ i ∈ Finset.Ico (n+1) t, η i * phase n i) =
      ∑ i ∈ Finset.Ico (n+1) t, η i := by
    apply Finset.sum_congr rfl
    intro i hi
    have : ¬ i ≤ n := by have := Finset.mem_Ico.mp hi; omega
    simp [phase,this]
  rw [he,hl];ring

private lemma phase_regret (η : ℕ → ℝ) {n T : ℕ} (hn : n ≤ T) :
    (∑ t ∈ Finset.Icc 1 T, phase n t * trajectory η n t) =
      - (2*(n:ℝ)-T) * (∑ i ∈ Finset.Icc 1 n, η i) +
      (∑ i ∈ Finset.Icc 1 T, (i:ℝ)*η i) - (T:ℝ)*(∑ i ∈ Finset.Icc (n+1) T, η i) := by
  rw [sum_split _ hn]
  have he : (∑ t ∈ Finset.Icc 1 n, phase n t * trajectory η n t) =
      -∑ t ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 t, η i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := (Finset.mem_Icc.mp ht).2
    rw [trajectory_early η (by omega)]
    simp [phase,ht']
  have hl : (∑ t ∈ Finset.Icc (n+1) T, phase n t * trajectory η n t) =
      ((T:ℝ)-n)*(∑ i ∈ Finset.Icc 1 n, η i) -
      ∑ t ∈ Finset.Icc (n+1) T, ∑ i ∈ Finset.Ico (n+1) t, η i := by
    calc
      _ = ∑ t ∈ Finset.Icc (n+1) T,
          ((∑ i ∈ Finset.Icc 1 n, η i) - ∑ i ∈ Finset.Ico (n+1) t, η i) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht' := (Finset.mem_Icc.mp ht).1
        rw [trajectory_late η ht']
        simp [phase,show ¬t≤n by omega]
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
        rw [show T+1-(n+1)=T-n by omega,Nat.cast_sub hn]
  rw [he,hl,triangular_sum,triangular_sum,sum_split (fun i => (i:ℝ)*η i) hn]
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private lemma tail_power_sum_upper (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) :
    (∑ i ∈ Finset.Icc (n+1) T, (i:ℝ)^(q-1)) ≤
      ((T:ℝ)^q-(n:ℝ)^q)/q := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hanti : AntitoneOn (fun x : ℝ => x^(q-1)) (Set.Icc (n:ℝ) T) := by
    intro x hx y hy hxy
    apply Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy
    linarith
  have h := hanti.sum_le_integral_Ico hnT
  rw [Finset.sum_Ico_add' (fun i : ℕ => (i:ℝ)^(q-1)) n T 1,
    Finset.Ico_add_one_right_eq_Icc] at h
  rw [integral_rpow (Or.inl (by linarith : (-1:ℝ)<q-1)), sub_add_cancel] at h
  exact h

private lemma inverse_power_sum_upper (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, (i:ℝ)^(q-1)) ≤ (n:ℝ)^q/q := by
  have h := tail_power_sum_upper q hq hq1 (n:=1) (T:=n) le_rfl hn
  have hs : (∑ i ∈ Finset.Icc 1 n, (i:ℝ)^(q-1)) =
      1 + ∑ i ∈ Finset.Icc 2 n, (i:ℝ)^(q-1) := by
    have := Finset.sum_Ico_consecutive (fun i => (i:ℝ)^(q-1))
      (by omega : 1≤2) (by omega : 2≤n+1)
    simpa [Finset.Ico_add_one_right_eq_Icc] using this.symm
  rw [hs]
  norm_num at h
  have hqinv : 1 ≤ 1/q := (le_div_iff₀ hq).2 (by linarith)
  calc _ ≤ 1 + ((n:ℝ)^q-1)/q := by linarith
    _ ≤ (n:ℝ)^q/q := by rw [sub_div];linarith

private lemma power_sum_lower (q : ℝ) (hq : 0 < q) (T : ℕ) :
    (T:ℝ)^(q+1)/(q+1) ≤ ∑ i ∈ Finset.Icc 1 T, (i:ℝ)^q := by
  have hmono : MonotoneOn (fun x : ℝ => x^q) (Set.Icc (0:ℝ) T) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow hx.1 hxy hq.le
  have h := MonotoneOn.integral_le_sum_Ico (f := fun x : ℝ => x^q)
    (Nat.zero_le T) (by simpa only [Nat.cast_zero] using hmono)
  rw [Finset.sum_Ico_add' (fun i : ℕ => (i:ℝ)^q) 0 T 1,
    Finset.Ico_add_one_right_eq_Icc] at h
  rw [integral_rpow (Or.inl (by linarith : (-1:ℝ)<q))] at h
  simpa [Real.zero_rpow (by linarith : q+1 ≠ 0)] using h


private lemma scalar_regret_lower (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (T : ℕ) (hT : 1 ≤ T) :
    (1/(q+1)+((1/2:ℝ)^q-1)/q)*(T:ℝ)^(q+1) - (T:ℝ)^q/q ≤
      ∑ t ∈ Finset.Icc 1 T,
        phase ((T+1)/2) t * trajectory (fun i => (i:ℝ)^(q-1)) ((T+1)/2) t := by
  let n := (T+1)/2
  have hn : 1 ≤ n := by dsimp [n];omega
  have hnT : n ≤ T := by dsimp [n];omega
  have hpar : T ≤ 2*n ∧ 2*n ≤ T+1 := by dsimp [n];omega
  have hTpos : (0:ℝ)<T := by exact_mod_cast hT
  have hnT' : (n:ℝ)≤T := by exact_mod_cast hnT
  have hpar1 : (T:ℝ)≤2*n := by exact_mod_cast hpar.1
  have hpar2 : 2*(n:ℝ)≤T+1 := by exact_mod_cast hpar.2
  have hS0 : 0 ≤ ∑ i ∈ Finset.Icc 1 n, (i:ℝ)^(q-1) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
  have hS := inverse_power_sum_upper q hq hq1 hn
  have hnq := Real.rpow_le_rpow (Nat.cast_nonneg n) hnT' hq.le
  have hSbound : (∑ i ∈ Finset.Icc 1 n, (i:ℝ)^(q-1)) ≤ (T:ℝ)^q/q :=
    hS.trans (div_le_div_of_nonneg_right hnq hq.le)
  have hfirst : -(T:ℝ)^q/q ≤ -(2*(n:ℝ)-T)*(∑ i ∈ Finset.Icc 1 n, (i:ℝ)^(q-1)) := by
    have hm := mul_le_mul_of_nonneg_right (show 2*(n:ℝ)-T ≤ 1 by linarith) hS0
    rw [neg_div]
    nlinarith
  have hpow := power_sum_lower q hq T
  have htail := tail_power_sum_upper q hq hq1 hn hnT
  have hmTail := mul_le_mul_of_nonneg_left htail hTpos.le
  have hsum : (∑ i ∈ Finset.Icc 1 T, (i:ℝ)*(i:ℝ)^(q-1)) =
      ∑ i ∈ Finset.Icc 1 T, (i:ℝ)^q := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : (0:ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    rw [Real.rpow_sub_one hi0.ne']
    field_simp
  have hhalf : ((T:ℝ)*(1/2:ℝ))^q ≤ (n:ℝ)^q :=
    Real.rpow_le_rpow (by positivity) (by linarith) hq.le
  have hsub := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_sub_left hhalf ((T:ℝ)^q)) hq.le) hTpos.le
  change _ ≤ ∑ t ∈ Finset.Icc 1 T, phase n t * trajectory _ n t
  rw [phase_regret _ hnT,hsum]
  calc
    _ = -(T:ℝ)^q/q + (T:ℝ)^(q+1)/(q+1) -
        (T:ℝ)*(((T:ℝ)^q-((T:ℝ)*(1/2:ℝ))^q)/q) := by
      rw [Real.mul_rpow (by positivity) (by norm_num), Real.rpow_add_one hTpos.ne']
      ring
    _ ≤ -(T:ℝ)^q/q + (T:ℝ)^(q+1)/(q+1) -
        (T:ℝ)*(((T:ℝ)^q-(n:ℝ)^q)/q) := by linarith
    _ ≤ _ := by linarith

private lemma trajectory_step (η : ℕ → ℝ) (n t : ℕ) (ht : 1 ≤ t) :
    trajectory η n (t+1) = trajectory η n t - η t * phase n t := by
  simp only [trajectory, Finset.sum_Ico_succ_top ht]
  ring

theorem solution {d : ℕ} (hd : 0 < d)
    (α : ℝ) (hαpos : 0 < α) (hαlt : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) :
    ∃ (g x : ℕ → EuclideanSpace ℝ (Fin d)),
      x 1 = 0 ∧
      (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ 1) ∧
      (∀ t ∈ Finset.Icc 1 T,
        x (t + 1) = x t - ((t : ℝ) ^ (-α)) • g t) ∧
      (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
        ∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (x t) := by
  by_cases hφ : 0 < phi α
  · have hq : 0 < 1-α := by linarith
    have hTpos : (0:ℝ)<T := (div_pos (by norm_num) (mul_pos hq hφ)).trans_le hT
    have hTnat : 1 ≤ T := by
      have : 0 < T := by exact_mod_cast hTpos
      omega
    let n := (T+1)/2
    let η : ℕ → ℝ := fun i => (i:ℝ)^(-α)
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0,hd⟩ 1
    have he : ‖e‖ = 1 := by simp [e]
    have hei : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq,he];norm_num
    refine ⟨fun t => phase n t • e, fun t => trajectory η n t • e, ?_, ?_, ?_, ?_⟩
    · simp [trajectory]
    · intro t ht
      rw [norm_smul,he,mul_one,Real.norm_eq_abs]
      unfold phase
      split_ifs <;> norm_num
    · intro t ht
      change trajectory η n (t+1) • e = trajectory η n t • e -
        ((t:ℝ)^(-α)) • (phase n t • e)
      rw [trajectory_step η n t (Finset.mem_Icc.mp ht).1]
      simp only [sub_smul,mul_smul]
      rfl
    · have hsum : (∑ t ∈ Finset.Icc 1 T, inner ℝ (phase n t • e) (trajectory η n t • e)) =
          ∑ t ∈ Finset.Icc 1 T, phase n t * trajectory η n t := by
        simp only [real_inner_smul_left,real_inner_smul_right,hei,mul_one,mul_comm]
      rw [hsum]
      have hb := scalar_regret_lower (1-α) hq (by linarith) T hTnat
      have hqm : 1-α-1 = -α := by ring
      have hqp : 1-α+1 = 2-α := by ring
      simp only [hqm,hqp] at hb
      change phi α * (T:ℝ)^(2-α) - (T:ℝ)^(1-α)/(1-α) ≤
        ∑ t ∈ Finset.Icc 1 T, phase n t * trajectory η n t at hb
      have hprod : 2 ≤ (T:ℝ)*((1-α)*phi α) := (div_le_iff₀ (mul_pos hq hφ)).mp hT
      have hp : (T:ℝ)^(2-α) = (T:ℝ)^(1-α)*(T:ℝ) := by
        rw [← hqp,Real.rpow_add_one hTpos.ne']
      have herr : (T:ℝ)^(1-α)/(1-α) ≤ (1/2:ℝ)*phi α*(T:ℝ)^(2-α) := by
        rw [div_le_iff₀ hq,hp]
        have hm := mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hTpos.le (1-α))
        nlinarith
      linarith
  · refine ⟨fun _ => 0,fun _ => 0,rfl,?_,?_,?_⟩
    · intro t ht;simp
    · intro t ht;simp
    · simp only [inner_zero_left, Finset.sum_const_zero]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hφ))
        (Real.rpow_nonneg (Nat.cast_nonneg T) _)

