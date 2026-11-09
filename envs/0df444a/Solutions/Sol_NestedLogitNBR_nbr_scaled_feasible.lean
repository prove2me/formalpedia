-- Prove2me | solution 1 for NestedLogitNBR.nbr_scaled_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T06:36:54.652711+00:00
-- url     : https://prove2.me/submissions/1ff26a4c-56d9-4386-8974-e5f3eb76be94

import Mathlib
import Definitions.Def_NestedLogitNBR_IsOptimalNBR
import Definitions.Def_NestedLogitNBR_FeasibleFull
import Definitions.Def_NestedLogitNBR_factor6

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NLNBRAux

lemma conv {γ x V P : ℝ} (hV : 0 < V) : V ^ γ * (P / V - x) = V ^ (γ - 1) * (P - x * V) := by
  rw [Real.rpow_sub_one hV.ne']
  field_simp

lemma pick {L A B β : ℝ} (h : L ≤ β * max 0 (max A B)) :
    L ≤ β * 0 ∨ L ≤ β * A ∨ L ≤ β * B := by
  rcases le_total 0 (max A B) with h1 | h1
  · rw [max_eq_right h1] at h
    rcases le_total A B with h2 | h2
    · right; right; rwa [max_eq_right h2] at h
    · right; left; rwa [max_eq_left h2] at h
  · left; rwa [max_eq_left h1] at h

/-- Arm one of factor (6): the revenue ratio. -/
lemma arm1 {γ x β V Vb P Ra Rb : ℝ} (hγ : 0 ≤ γ) (hx : 0 ≤ x) (hβ : 1 ≤ β) (hV : 0 < V)
    (hV2 : V ≤ Vb) (hPV : P / V ≤ Ra) (hab : Ra ≤ β * Rb) :
    V ^ γ * (P / V - β * x) ≤ β * max 0 (Vb ^ γ * (Rb - x)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hVg : 0 ≤ V ^ γ := Real.rpow_nonneg hV.le γ
  have hR : 0 ≤ β * max 0 (Vb ^ γ * (Rb - x)) := mul_nonneg hβ0 (le_max_left _ _)
  rcases le_or_gt (P / V - β * x) 0 with hn | hp
  · have := mul_nonpos_of_nonneg_of_nonpos hVg hn
    linarith
  · have hle : V ^ γ ≤ Vb ^ γ := Real.rpow_le_rpow hV.le hV2 hγ
    have h1 : V ^ γ * (P / V - β * x) ≤ Vb ^ γ * (P / V - β * x) :=
      mul_le_mul_of_nonneg_right hle hp.le
    have hVbg : 0 ≤ Vb ^ γ := le_trans hVg hle
    have h2 : Vb ^ γ * (P / V - β * x) ≤ Vb ^ γ * (β * (Rb - x)) := by
      apply mul_le_mul_of_nonneg_left _ hVbg
      have : β * (Rb - x) = β * Rb - β * x := by ring
      rw [this]; linarith
    have h3 : Vb ^ γ * (β * (Rb - x)) = β * (Vb ^ γ * (Rb - x)) := by ring
    have h4 : β * (Vb ^ γ * (Rb - x)) ≤ β * max 0 (Vb ^ γ * (Rb - x)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hβ0
    linarith

/-- Endpoint comparison. -/
lemma endpt {E β x V P : ℝ} (hE : 0 ≤ E) (hβ : 1 ≤ β) (hP : 0 ≤ P) :
    E * (P - β * x * V) ≤ β * max 0 (E * (P - x * V)) := by
  have h1 : E * (P - β * x * V) ≤ β * (E * (P - x * V)) := by
    have : β * (E * (P - x * V)) - E * (P - β * x * V) = E * ((β - 1) * P) := by ring
    have : 0 ≤ E * ((β - 1) * P) := mul_nonneg hE (mul_nonneg (by linarith) hP)
    linarith
  exact le_trans h1 (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))

/-- Segment bound for `γ ≤ 1`: concavity of `t ↦ t ^ (1 - γ)`. -/
lemma le1 {γ x' Va Vb V Pa ρ L : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hVa : 0 < Va)
    (hV1 : Va ≤ V) (hV2 : V ≤ Vb) (hL : 0 ≤ L)
    (ha : Va ^ (γ - 1) * (Pa - x' * Va) ≤ L)
    (hb : Vb ^ (γ - 1) * (Pa + (Vb - Va) * ρ - x' * Vb) ≤ L) :
    V ^ (γ - 1) * (Pa + (V - Va) * ρ - x' * V) ≤ L := by
  have hV : 0 < V := lt_of_lt_of_le hVa hV1
  have hVb : 0 < Vb := lt_of_lt_of_le hV hV2
  have one : ∀ t : ℝ, 0 < t → t ^ (γ - 1) * t ^ (1 - γ) = 1 := by
    intro t ht
    rw [← Real.rpow_add ht]
    norm_num
  have qa : Pa - x' * Va ≤ L * Va ^ (1 - γ) := by
    have h := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hVa.le (1 - γ))
    have e : Va ^ (γ - 1) * (Pa - x' * Va) * Va ^ (1 - γ) = Pa - x' * Va := by
      rw [mul_comm (Va ^ (γ - 1)) _, mul_assoc, one Va hVa, mul_one]
    linarith
  have qb : Pa + (Vb - Va) * ρ - x' * Vb ≤ L * Vb ^ (1 - γ) := by
    have h := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hVb.le (1 - γ))
    have e : Vb ^ (γ - 1) * (Pa + (Vb - Va) * ρ - x' * Vb) * Vb ^ (1 - γ) =
        Pa + (Vb - Va) * ρ - x' * Vb := by
      rw [mul_comm (Vb ^ (γ - 1)) _, mul_assoc, one Vb hVb, mul_one]
    linarith
  have qv : Pa + (V - Va) * ρ - x' * V ≤ L * V ^ (1 - γ) := by
    rcases eq_or_lt_of_le (le_trans hV1 hV2) with hab | hab
    · have hVe : V = Va := le_antisymm (hab ▸ hV2) hV1
      rw [hVe, sub_self, zero_mul, add_zero]
      exact qa
    · have hw : 0 < Vb - Va := by linarith
      set lam := (Vb - V) / (Vb - Va) with hlam
      set μ := (V - Va) / (Vb - Va) with hμ
      have hl0 : 0 ≤ lam := div_nonneg (by linarith) hw.le
      have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hw.le
      have hsum : lam + μ = 1 := by
        rw [hlam, hμ, ← add_div, div_eq_one_iff_eq hw.ne']; ring
      have hVcomb : lam * Va + μ * Vb = V := by
        rw [hlam, hμ, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hw.ne']
        ring
      have hconc : lam * Va ^ (1 - γ) + μ * Vb ^ (1 - γ) ≤ V ^ (1 - γ) := by
        have := (Real.concaveOn_rpow (by linarith : (0:ℝ) ≤ 1 - γ) (by linarith)).2
          (Set.mem_Ici.2 hVa.le) (Set.mem_Ici.2 hVb.le) hl0 hμ0 hsum
        simpa [smul_eq_mul, hVcomb] using this
      have hlin : Pa + (V - Va) * ρ - x' * V =
          lam * (Pa - x' * Va) + μ * (Pa + (Vb - Va) * ρ - x' * Vb) := by
        rw [hlam, hμ]
        field_simp
        ring
      rw [hlin]
      calc lam * (Pa - x' * Va) + μ * (Pa + (Vb - Va) * ρ - x' * Vb)
          ≤ lam * (L * Va ^ (1 - γ)) + μ * (L * Vb ^ (1 - γ)) :=
            add_le_add (mul_le_mul_of_nonneg_left qa hl0) (mul_le_mul_of_nonneg_left qb hμ0)
        _ = L * (lam * Va ^ (1 - γ) + μ * Vb ^ (1 - γ)) := by ring
        _ ≤ L * V ^ (1 - γ) := mul_le_mul_of_nonneg_left hconc hL
  calc V ^ (γ - 1) * (Pa + (V - Va) * ρ - x' * V)
      ≤ V ^ (γ - 1) * (L * V ^ (1 - γ)) :=
        mul_le_mul_of_nonneg_left qv (Real.rpow_nonneg hV.le _)
    _ = L * (V ^ (γ - 1) * V ^ (1 - γ)) := by ring
    _ = L := by rw [one V hV, mul_one]

/-- Segment bound for `1 ≤ γ` under arm two of factor (6). -/
lemma ge1 {γ x β Va Vb V Pa Pb P ρ : ℝ} (hγ : 1 ≤ γ) (hx : 0 ≤ x) (hβ : 1 ≤ β)
    (hVa : 0 < Va) (hV1 : Va ≤ V) (hV2 : V ≤ Vb) (hPa : 0 < Pa) (hPab : Pa ≤ Pb)
    (hP : P ≤ Pa + (V - Va) * ρ) (hPb : Pb = Pa + (Vb - Va) * ρ)
    (harm : Pb * Vb ^ (γ - 1) ≤ β * (Pa * Va ^ (γ - 1))) :
    V ^ (γ - 1) * (P - β * x * V) ≤
      β * max 0 (max (Va ^ (γ - 1) * (Pa - x * Va)) (Vb ^ (γ - 1) * (Pb - x * Vb))) := by
  have hV : 0 < V := lt_of_lt_of_le hVa hV1
  have hβ0 : 0 ≤ β := by linarith
  have hF0 : 0 ≤ Va ^ (γ - 1) := Real.rpow_nonneg hVa.le _
  have hVg : 0 ≤ V ^ (γ - 1) := Real.rpow_nonneg hV.le _
  have hEV : V ^ (γ - 1) ≤ Vb ^ (γ - 1) := Real.rpow_le_rpow hV.le hV2 (by linarith)
  have hE0 : 0 ≤ Vb ^ (γ - 1) := le_trans hVg hEV
  have hM0 : 0 ≤ β * max 0 (max (Va ^ (γ - 1) * (Pa - x * Va)) (Vb ^ (γ - 1) * (Pb - x * Vb))) :=
    mul_nonneg hβ0 (le_max_left _ _)
  rcases le_or_gt (P - β * x * V) 0 with hn | hp
  · have := mul_nonpos_of_nonneg_of_nonpos hVg hn
    linarith
  have h1 : V ^ (γ - 1) * (P - β * x * V) ≤ Vb ^ (γ - 1) * (P - β * x * V) :=
    mul_le_mul_of_nonneg_right hEV hp.le
  have hβx : 0 ≤ (β - 1) * x := mul_nonneg (by linarith) hx
  rcases le_total 0 (ρ - β * x) with hc | hc
  · have hQ : P - β * x * V ≤ Pb - β * x * Vb := by
      have : 0 ≤ (Vb - V) * (ρ - β * x) := mul_nonneg (by linarith) hc
      rw [hPb]; nlinarith
    have hPb0 : 0 ≤ Pb := by linarith
    have h2 : Pb - β * x * Vb ≤ β * (Pb - x * Vb) := by
      have : 0 ≤ (β - 1) * Pb := mul_nonneg (by linarith) hPb0
      nlinarith
    calc V ^ (γ - 1) * (P - β * x * V) ≤ Vb ^ (γ - 1) * (Pb - β * x * Vb) :=
          le_trans h1 (mul_le_mul_of_nonneg_left hQ hE0)
      _ ≤ Vb ^ (γ - 1) * (β * (Pb - x * Vb)) := mul_le_mul_of_nonneg_left h2 hE0
      _ = β * (Vb ^ (γ - 1) * (Pb - x * Vb)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_trans (le_max_right _ _) (le_max_right _ _)) hβ0
  · have hQ : P - β * x * V ≤ Pa - β * x * Va := by
      have : (V - Va) * (ρ - β * x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
      nlinarith
    set c := Pa - β * x * Va with hcdef
    have hc0 : 0 < c := by linarith
    have hPb : 0 < Pb := by linarith
    have k1 : Pb * Vb ^ (γ - 1) * c ≤ β * (Pa * Va ^ (γ - 1)) * c :=
      mul_le_mul_of_nonneg_right harm hc0.le
    have k2 : β * (Pa * Va ^ (γ - 1)) * c ≤ β * (Pb * Va ^ (γ - 1)) * c := by
      have := mul_nonneg (mul_nonneg hβ0 hF0) hc0.le
      have h := mul_le_mul_of_nonneg_right hPab this
      nlinarith
    have k3 : Vb ^ (γ - 1) * c ≤ β * Va ^ (γ - 1) * c := by
      have : Pb * (Vb ^ (γ - 1) * c) ≤ Pb * (β * Va ^ (γ - 1) * c) := by
        have e1 : Pb * (Vb ^ (γ - 1) * c) = Pb * Vb ^ (γ - 1) * c := by ring
        have e2 : Pb * (β * Va ^ (γ - 1) * c) = β * (Pb * Va ^ (γ - 1)) * c := by ring
        rw [e1, e2]; linarith
      exact le_of_mul_le_mul_left this hPb
    have k4 : c ≤ Pa - x * Va := by
      have : 0 ≤ (β - 1) * x * Va := mul_nonneg hβx hVa.le
      rw [hcdef]; nlinarith
    have k5 : β * Va ^ (γ - 1) * c ≤ β * (Va ^ (γ - 1) * (Pa - x * Va)) := by
      have := mul_le_mul_of_nonneg_left k4 (mul_nonneg hβ0 hF0)
      nlinarith
    calc V ^ (γ - 1) * (P - β * x * V) ≤ Vb ^ (γ - 1) * c :=
          le_trans h1 (mul_le_mul_of_nonneg_left hQ hE0)
      _ ≤ β * (Va ^ (γ - 1) * (Pa - x * Va)) := le_trans k3 k5
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_trans (le_max_left _ _) (le_max_right _ _)) hβ0

open NestedLogitNBR

lemma mem_nbr {n k : ℕ} (j : Fin n) : j ∈ (nbr k : Finset (Fin n)) ↔ j.val < k := by
  simp [nbr]

lemma nbr_succ {n : ℕ} (a : Fin n) :
    (nbr (a.val + 1) : Finset (Fin n)) = insert a (nbr a.val) := by
  ext j; simp only [Finset.mem_insert, mem_nbr, Fin.ext_iff]; omega

lemma nbr_zero (n : ℕ) : (nbr 0 : Finset (Fin n)) = ∅ := by
  ext j; simp [mem_nbr]

lemma nbr_n (n : ℕ) : (nbr n : Finset (Fin n)) = Finset.univ := by
  ext j; simp [mem_nbr, j.isLt]

lemma exch {n : ℕ} (r v : Fin n → ℝ) (hr : Antitone r) (hv : ∀ j, 0 ≤ v j) (a : Fin n)
    (S : Finset (Fin n)) :
    ∑ j ∈ S, r j * v j ≤
      ∑ j ∈ (nbr a.val : Finset (Fin n)), r j * v j +
        (∑ j ∈ S, v j - ∑ j ∈ (nbr a.val : Finset (Fin n)), v j) * r a := by
  have key : ∑ j ∈ S, (r j - r a) * v j ≤
      ∑ j ∈ (nbr a.val : Finset (Fin n)), (r j - r a) * v j := by
    rw [← Finset.sum_inter_add_sum_sdiff S (nbr a.val)]
    have h1 : ∑ j ∈ S \ nbr a.val, (r j - r a) * v j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      rw [Finset.mem_sdiff, mem_nbr] at hj
      have : a ≤ j := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hr this]) (hv j)
    have h2 : ∑ j ∈ S ∩ nbr a.val, (r j - r a) * v j ≤
        ∑ j ∈ (nbr a.val : Finset (Fin n)), (r j - r a) * v j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro j hj _
      rw [mem_nbr] at hj
      have : j ≤ a := by rw [Fin.le_iff_val_le_val]; omega
      exact mul_nonneg (by linarith [hr this]) (hv j)
    linarith
  have e1 : ∑ j ∈ S, (r j - r a) * v j = ∑ j ∈ S, r j * v j - (∑ j ∈ S, v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  have e2 : ∑ j ∈ (nbr a.val : Finset (Fin n)), (r j - r a) * v j =
      ∑ j ∈ (nbr a.val : Finset (Fin n)), r j * v j -
        (∑ j ∈ (nbr a.val : Finset (Fin n)), v j) * r a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  rw [e1, e2] at key
  linarith

lemma pw_nonneg {m n : ℕ} (v : Fin m → Fin n → ℝ) (i : Fin m) (hv : ∀ j, 0 ≤ v i j)
    (S : Finset (Fin n)) : 0 ≤ prefWeight v i S :=
  Finset.sum_nonneg (fun j _ => hv j)

lemma att_nonneg {m n : ℕ} (v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (S : Finset (Fin n)) : 0 ≤ nestAttraction v γ i S := by
  unfold nestAttraction
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (pw_nonneg v i hv S) _

lemma rev_nonneg {m n : ℕ} (r v : Fin m → Fin n → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (S : Finset (Fin n)) :
    0 ≤ nestRevenue r v i S :=
  div_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j))) (pw_nonneg v i hv S)

lemma att_pos_eq {m n : ℕ} (v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (S : Finset (Fin n)) (h : 0 < prefWeight v i S) :
    nestAttraction v γ i S = prefWeight v i S ^ γ i := by
  unfold nestAttraction; rw [if_neg h.ne']

lemma T_zero {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m) (x : ℝ) :
    nestAttraction v γ i (nbr 0 : Finset (Fin n)) * (nestRevenue r v i (nbr 0) - x) = 0 := by
  have : prefWeight v i (nbr 0 : Finset (Fin n)) = 0 := by
    simp [prefWeight, nbr_zero]
  unfold nestAttraction; rw [if_pos this, zero_mul]

set_option maxHeartbeats 1000000 in
/-- Per-nest bound: every assortment, at `β x`, is dominated by `β` times a revenue prefix at `x`. -/
theorem per_nest {m n : ℕ} (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ) (i : Fin m)
    (hv : ∀ j, 0 ≤ v i j) (hr : ∀ j, 0 ≤ r i j) (hanti : Antitone (r i)) (hγ : 0 ≤ γ i)
    (x β : ℝ) (hx : 0 ≤ x) (hβ1 : 1 ≤ β)
    (hfac : ∀ j, 2 ≤ j → j ≤ n → factor6Term r v γ i j ≤ β) (S : Finset (Fin n)) :
    ∃ j ≤ n, nestAttraction v γ i S * (nestRevenue r v i S - β * x) ≤
      β * (nestAttraction v γ i (nbr j) * (nestRevenue r v i (nbr j) - x)) := by
  have hβ0 : 0 ≤ β := by linarith
  rcases (pw_nonneg v i hv S).eq_or_lt with hS0 | hSpos
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [T_zero]
    unfold nestAttraction
    rw [if_pos hS0.symm]
    simp
  have hn : 0 < n := by
    by_contra h0
    have h0 : n = 0 := by omega
    subst h0
    have hS : S = ∅ := by ext j; exact j.elim0
    rw [hS] at hSpos
    simp [prefWeight] at hSpos
  set W : ℕ → ℝ := fun k => prefWeight v i (nbr k : Finset (Fin n)) with hW
  set WS := prefWeight v i S with hWS
  have hWn : WS ≤ W n := by
    simp only [hW, hWS, prefWeight, nbr_n]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hv j)
  have hex : ∃ k, WS ≤ W (k + 1) := ⟨n - 1, by rw [show n - 1 + 1 = n by omega]; exact hWn⟩
  classical
  set a := Nat.find hex with ha
  have ha_spec : WS ≤ W (a + 1) := Nat.find_spec hex
  have ha_lt : a < n := by
    have := Nat.find_min' hex (show WS ≤ W (n - 1 + 1) by
      rw [show n - 1 + 1 = n by omega]; exact hWn)
    omega
  have ha_lo : W a ≤ WS := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · simp only [hW, h0, prefWeight, nbr_zero, Finset.sum_empty]
      exact pw_nonneg v i hv S
    · have := Nat.find_min hex (show a - 1 < a by omega)
      have e : a - 1 + 1 = a := by omega
      rw [e] at this; exact (not_le.1 this).le
  set a' : Fin n := ⟨a, ha_lt⟩ with ha'
  have hsucc : (nbr (a + 1) : Finset (Fin n)) = insert a' (nbr a) := nbr_succ a'
  have hnot : a' ∉ (nbr a : Finset (Fin n)) := by rw [mem_nbr]; simp [ha']
  set Va := prefWeight v i (nbr a : Finset (Fin n)) with hVa_def
  set Vb := prefWeight v i (nbr (a + 1) : Finset (Fin n)) with hVb_def
  set Pa := ∑ j ∈ (nbr a : Finset (Fin n)), r i j * v i j with hPa_def
  set Pb := ∑ j ∈ (nbr (a + 1) : Finset (Fin n)), r i j * v i j with hPb_def
  set PS := ∑ j ∈ S, r i j * v i j with hPS_def
  set ρ := r i a' with hρ_def
  have hVb : Vb = Va + v i a' := by
    simp only [hVb_def, hVa_def, prefWeight, hsucc, Finset.sum_insert hnot]; ring
  have hPb : Pb = Pa + v i a' * ρ := by
    simp only [hPb_def, hPa_def, hsucc, Finset.sum_insert hnot, hρ_def]; ring
  have hV1 : Va ≤ WS := ha_lo
  have hV2 : WS ≤ Vb := ha_spec
  have hexch := exch (r i) (v i) hanti hv a' S
  have hP : PS ≤ Pa + (WS - Va) * ρ := hexch
  have hexch0 := exch (r i) (v i) hanti hv a' ∅
  have hρVa : ρ * Va ≤ Pa := by
    simp only [Finset.sum_empty] at hexch0
    have : Pa + (0 - Va) * ρ = Pa - ρ * Va := by ring
    change 0 ≤ Pa + (0 - Va) * ρ at hexch0
    linarith
  have hPa0 : 0 ≤ Pa := Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j))
  have hρ0 : 0 ≤ ρ := hr a'
  have hVa0 : 0 ≤ Va := pw_nonneg v i hv _
  have hVbpos : 0 < Vb := lt_of_lt_of_le hSpos hV2
  have eS : nestAttraction v γ i S * (nestRevenue r v i S - β * x) =
      WS ^ γ i * (PS / WS - β * x) := by
    rw [att_pos_eq v γ i S hSpos]; rfl
  have eB : nestAttraction v γ i (nbr (a + 1)) * (nestRevenue r v i (nbr (a + 1)) - x) =
      Vb ^ γ i * (Pb / Vb - x) := by
    rw [att_pos_eq v γ i _ hVbpos]; rfl
  have hmain : WS ^ γ i * (PS / WS - β * x) ≤
      β * max 0 (max (Va ^ γ i * (Pa / Va - x)) (Vb ^ γ i * (Pb / Vb - x))) := by
    rcases (hv a').eq_or_lt with hw | hw
    · -- zero weight on the next product: flat segment
      have hVbeq : Vb = Va := by rw [hVb, ← hw]; ring
      have hVSeq : WS = Va := le_antisymm (hVbeq ▸ hV2) hV1
      have hPS : PS ≤ Pa := by rw [hVSeq, sub_self, zero_mul, add_zero] at hP; exact hP
      have hVapos : 0 < Va := hVSeq ▸ hSpos
      have hRa0 : 0 ≤ Pa / Va := div_nonneg hPa0 hVa0
      have h := arm1 (γ := γ i) (x := x) (β := β) (P := PS) (Ra := Pa / Va) (Rb := Pa / Va)
        hγ hx hβ1 hSpos hVSeq.le
        (by rw [hVSeq]; exact div_le_div_of_nonneg_right hPS hVa0) (by nlinarith)
      exact le_trans h (mul_le_mul_of_nonneg_left
        (max_le_max le_rfl (le_max_left _ _)) hβ0)
    rcases hVa0.eq_or_lt with hVa00 | hVapos
    · -- empty-weight prefix
      have hz : ∀ j ∈ (nbr a : Finset (Fin n)), v i j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hVa00.symm
      have hPa00 : Pa = 0 := Finset.sum_eq_zero (fun j hj => by rw [hz j hj, mul_zero])
      have hRb : Pb / Vb = ρ := by
        rw [hPb, hVb, hPa00, ← hVa00, zero_add, zero_add]
        exact mul_div_cancel_left₀ ρ hw.ne'
      have hPV : PS / WS ≤ ρ := by
        rw [div_le_iff₀ hSpos]; rw [hPa00, ← hVa00] at hP; linarith
      have h := arm1 (γ := γ i) (x := x) (β := β) (P := PS) (Ra := ρ) (Rb := Pb / Vb)
        hγ hx hβ1 hSpos hV2 hPV (by rw [hRb]; nlinarith)
      exact le_trans h (mul_le_mul_of_nonneg_left
        (max_le_max le_rfl (le_max_right _ _)) hβ0)
    -- Va > 0 and a positive next weight
    have ha1 : 1 ≤ a := by
      by_contra h0
      have h0 : a = 0 := by omega
      have : Va = 0 := by simp [hVa_def, h0, prefWeight, nbr_zero]
      linarith
    rw [conv hSpos, conv hVapos, conv hVbpos]
    have hPbVb : Pb = Pa + (Vb - Va) * ρ := by rw [hPb, hVb]; ring
    rcases le_total (γ i) 1 with hle | hge
    · have hL : 0 ≤ β * max 0 (max (Va ^ (γ i - 1) * (Pa - x * Va))
          (Vb ^ (γ i - 1) * (Pb - x * Vb))) := mul_nonneg hβ0 (le_max_left _ _)
      have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
      have ha := endpt (E := Va ^ (γ i - 1)) (x := x) (V := Va) (Real.rpow_nonneg hVa0 _) hβ1 hPa0
      have hb := endpt (E := Vb ^ (γ i - 1)) (x := x) (V := Vb)
        (Real.rpow_nonneg hVbpos.le _) hβ1 hPb0
      have key := le1 (x' := β * x) (ρ := ρ) hγ hle hVapos hV1 hV2 hL
        (le_trans ha (mul_le_mul_of_nonneg_left (max_le_max le_rfl (le_max_left _ _)) hβ0))
        (by rw [← hPbVb]; exact le_trans hb
              (mul_le_mul_of_nonneg_left (max_le_max le_rfl (le_max_right _ _)) hβ0))
      have hle2 : WS ^ (γ i - 1) * (PS - β * x * WS) ≤
          WS ^ (γ i - 1) * (Pa + (WS - Va) * ρ - β * x * WS) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hSpos.le _)
      exact le_trans hle2 key
    · rcases hPa0.eq_or_lt with hPa00 | hPapos
      · have hρ00 : ρ ≤ 0 := by
          by_contra h
          have := mul_pos (not_le.1 h) hVapos
          linarith
        have hPS0 : PS ≤ 0 := by
          have := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ WS - Va) hρ00
          linarith
        have h1 : WS ^ (γ i - 1) * (PS - β * x * WS) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hSpos.le _)
          have := mul_nonneg (mul_nonneg hβ0 hx) hSpos.le
          linarith
        exact le_trans h1 (mul_nonneg hβ0 (le_max_left _ _))
      have hPab : Pa ≤ Pb := by rw [hPb]; nlinarith [mul_nonneg hw.le hρ0]
      have hPbpos : 0 < Pb := lt_of_lt_of_le hPapos hPab
      have hf := hfac (a + 1) (by omega) (by omega)
      unfold factor6Term at hf
      simp only [Nat.add_sub_cancel] at hf
      have eRa : nestRevenue r v i (nbr a : Finset (Fin n)) = Pa / Va := rfl
      have eRb : nestRevenue r v i (nbr (a + 1) : Finset (Fin n)) = Pb / Vb := rfl
      rw [eRa, eRb] at hf
      rcases min_le_iff.1 hf with h1 | h2
      · -- arm one
        have hRbpos : 0 < Pb / Vb := div_pos hPbpos hVbpos
        have hab : Pa / Va ≤ β * (Pb / Vb) := by rwa [div_le_iff₀ hRbpos] at h1
        have hPV : PS / WS ≤ Pa / Va := by
          rw [div_le_div_iff₀ hSpos hVapos]
          have h3 := mul_le_mul_of_nonneg_right hP hVapos.le
          have h4 := mul_le_mul_of_nonneg_left hρVa (by linarith : 0 ≤ WS - Va)
          have e1 : (Pa + (WS - Va) * ρ) * Va = Pa * Va + (WS - Va) * (ρ * Va) := by ring
          have e2 : Pa * WS = Pa * Va + (WS - Va) * Pa := by ring
          rw [e1] at h3; rw [e2]; linarith
        have h := arm1 (γ := γ i) (x := x) (β := β) (P := PS) hγ hx hβ1 hSpos hV2 hPV hab
        rw [conv hSpos, conv hVbpos] at h
        exact le_trans h (mul_le_mul_of_nonneg_left
          (max_le_max le_rfl (le_max_right _ _)) hβ0)
      · -- arm two
        have e : Pb / Vb / (Pa / Va) * (Vb ^ γ i / Va ^ γ i) =
            (Pb * Vb ^ (γ i - 1)) / (Pa * Va ^ (γ i - 1)) := by
          rw [Real.rpow_sub_one hVbpos.ne', Real.rpow_sub_one hVapos.ne']
          have : 0 < Va ^ γ i := Real.rpow_pos_of_pos hVapos _
          have : 0 < Vb ^ γ i := Real.rpow_pos_of_pos hVbpos _
          field_simp
        rw [e, div_le_iff₀ (mul_pos hPapos (Real.rpow_pos_of_pos hVapos _))] at h2
        exact ge1 hge hx hβ1 hVapos hV1 hV2 hPapos hPab hP hPbVb h2
  rcases pick hmain with h | h | h
  · exact ⟨0, Nat.zero_le _, by rw [eS, T_zero]; exact h⟩
  · rcases hVa0.eq_or_lt with hVa00 | hVapos
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [eS, T_zero]
      have : Va ^ γ i * (Pa / Va - x) ≤ 0 := by
        rw [← hVa00, div_zero, zero_sub]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg le_rfl _) (by linarith)
      have := mul_le_mul_of_nonneg_left this hβ0
      linarith
    · refine ⟨a, ha_lt.le, ?_⟩
      rw [eS, att_pos_eq v γ i _ hVapos]
      exact h
  · exact ⟨a + 1, ha_lt, by rw [eS, eB]; exact h⟩

theorem main {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y) :
    FeasibleFull v0 r v γ (factor6 r v γ * x) (fun i => factor6 r v γ * y i) := by
  obtain ⟨⟨hsum, hcand⟩, hmin⟩ := hopt
  have hβ1 : 1 ≤ factor6 r v γ := by
    unfold factor6
    exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  have hβ0 : 0 ≤ factor6 r v γ := by linarith
  have hfac : ∀ i j, 2 ≤ j → j ≤ n → factor6Term r v γ i j ≤ factor6 r v γ := by
    intro i j h2 hjn
    unfold factor6
    exact (Finset.le_fold_max _).2 (Or.inr ⟨(i, j),
      Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_Icc.2 ⟨h2, hjn⟩⟩, le_rfl⟩)
  have hx : 0 ≤ x := by
    by_contra hneg
    have hneg : x < 0 := not_le.1 hneg
    have hT0 : ∀ i (S : Finset (Fin n)),
        0 ≤ nestAttraction v γ i S * (nestRevenue r v i S - x) := fun i S =>
      mul_nonneg (att_nonneg v γ i (hv i) S) (by linarith [rev_nonneg r v i (hv i) (hr i) S])
    have hy0 : ∀ i, 0 ≤ y i := fun i =>
      le_trans (hT0 i (nbr 0)) (hcand i 0 (Nat.zero_le _))
    have hs0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy0 i)
    have hv0x : v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hneg.le
    have hsumeq : ∑ i, y i = 0 := by linarith
    have hyz : ∀ i, y i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hsumeq i (Finset.mem_univ _)
    have hv0z : v0 = 0 := by
      have : v0 * x = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hneg.ne
    have hfeas : FeasibleNBR v0 r v γ (x - 1) y := by
      refine ⟨?_, ?_⟩
      · rw [hsumeq, hv0z, zero_mul]
      · intro i j hj
        have hTS := hcand i j hj
        rw [hyz i] at hTS ⊢
        have hTS0 := le_antisymm hTS (hT0 i (nbr j))
        have hRx : 0 < nestRevenue r v i (nbr j) - x := by
          linarith [rev_nonneg r v i (hv i) (hr i) (nbr j)]
        have hA : nestAttraction v γ i (nbr j) = 0 :=
          (mul_eq_zero.1 hTS0).resolve_right hRx.ne'
        rw [hA, zero_mul]
    have := hmin _ _ hfeas
    linarith
  refine ⟨?_, ?_⟩
  · rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hsum hβ0
    calc factor6 r v γ * ∑ i, y i ≤ factor6 r v γ * (v0 * x) := this
      _ = v0 * (factor6 r v γ * x) := by ring
  · intro i S
    obtain ⟨j, hj, hb⟩ := per_nest r v γ i (hv i) (hr i) (hord i) (hγ i) x (factor6 r v γ)
      hx hβ1 (hfac i) S
    exact le_trans hb (mul_le_mul_of_nonneg_left (hcand i j hj) hβ0)

end NLNBRAux

open NestedLogitNBR in
theorem solution {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (hv0 : 0 ≤ v0) (hv : ∀ i j, 0 ≤ v i j) (hr : ∀ i j, 0 ≤ r i j)
    (hord : ∀ i, Antitone (r i)) (hγ : ∀ i, 0 ≤ γ i)
    (x : ℝ) (y : Fin m → ℝ) (hopt : IsOptimalNBR v0 r v γ x y) :
    FeasibleFull v0 r v γ (factor6 r v γ * x) (fun i => factor6 r v γ * y i) := by
  exact NLNBRAux.main v0 r v γ hv0 hv hr hord hγ x y hopt
