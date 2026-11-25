-- Prove2me | solution 1 for GlobalTheory.sum_over_dyadic_shells
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:51.650945+00:00
-- url     : https://prove2.me/submissions/58c8c223-60a7-4ea9-bf91-48e75ab9fb8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ShellSumElementaryInequalities
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDyadicShellIndex
import Theorems.Thm_GlobalTheory_exists_dyadic_shell_index
import Theorems.Thm_GlobalTheory_sum_prod_box_erase_zero
import Theorems.Thm_GlobalTheory_exp_neg_mul_two_pow_le_geometric
import Theorems.Thm_GlobalTheory_shell_sum_elementary_inequalities


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ ι : Type) [Fintype ι] (d : Γ → ι → ℝ) (w : Γ → ℝ) (A κ h ep c : ℝ), 0 ≤ A → 0 ≤ κ → 0 < ep → 0 < c → ep ≤ 1 / c → κ * ep ≤ Real.log 2 → 32 * κ ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → (∀ γ v, 0 ≤ d γ v) → (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | ∀ v, d γ v ≤ r v}.Finite ∧ (({γ | ∀ v, d γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (κ * ∑ v, r v)) → (∀ γ, ∃ v, ep < d γ v) → (∀ γ, 0 ≤ w γ ∧ w γ ≤ ∏ v, Real.exp (-(h / 8) * min (d γ v ^ 2) (d γ v / c))) → Summable w ∧ ∑' γ, w γ ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
  intro Γ ι _ d w A κ h ep c hA hκ hep hc hepc hκep hh hT hd hcount hfar hw
  classical
  obtain ⟨sh, hsh1, hsh2⟩ := exists_dyadic_shell_index ep hep
  obtain ⟨hineq, -, hpow⟩ := shell_sum_elementary_inequalities
  set T : ℝ := h * ep ^ 2 / 16 with hTdef
  have hhpos : 0 < h := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have h1 : h * ep ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg ep)
    linarith
  have hκT : κ * ep ≤ T / 2 := by
    have h1 : 32 * κ * ep ≤ h * ep * ep := mul_le_mul_of_nonneg_right hh hep.le
    rw [hTdef]
    nlinarith

  let F : ℕ → ℝ := fun j => if j = 0 then 1 else Real.exp (-T * 2 ^ j)
  let W : ℕ → ℝ := fun j => Real.exp (κ * (2 ^ j * ep)) * F j
  let K : Γ → ι → ℕ := fun γ v => sh (d γ v)
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    simp only [F]
    split_ifs
    · exact zero_le_one
    · exact (Real.exp_pos _).le
  have hW0 : ∀ j, 0 ≤ W j := fun j => mul_nonneg (Real.exp_pos _).le (hF0 j)

  have hwF : ∀ γ, w γ ≤ ∏ v, F (K γ v) := by
    intro γ
    refine (hw γ).2.trans (Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => ?_))
    have hmin0 : 0 ≤ min (d γ v ^ 2) (d γ v / c) := le_min (sq_nonneg _) (div_nonneg (hd γ v) hc.le)
    simp only [F, K]
    split_ifs with hk
    · rw [Real.exp_le_one_iff]
      nlinarith
    · rw [Real.exp_le_exp]
      have hlt : sh (d γ v) - 1 < sh (d γ v) := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
      have hbig := hsh2 (d γ v) _ hlt
      have hp1 : (1 : ℝ) ≤ 2 ^ (sh (d γ v) - 1) := one_le_pow₀ (by norm_num)
      have hge : ep ≤ d γ v := by nlinarith
      have hm := hineq (d γ v) ep c hep hge hc hepc
      have h2 : (2 : ℝ) ^ sh (d γ v) = 2 * 2 ^ (sh (d γ v) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hm2 : ep ^ 2 * 2 ^ (sh (d γ v) - 1) ≤ min (d γ v ^ 2) (d γ v / c) := by
        have : ep * (2 ^ (sh (d γ v) - 1) * ep) ≤ ep * d γ v :=
          mul_le_mul_of_nonneg_left hbig.le hep.le
        nlinarith
      have hm3 := mul_le_mul_of_nonneg_left hm2 hhpos.le
      rw [h2, hTdef]
      nlinarith

  have hfib : ∀ (u : Finset Γ) (k : ι → ℕ),
      ((u.filter fun γ => K γ = k).card : ℝ) ≤ A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
    intro u k
    have hr : ∀ v, 0 ≤ (2 : ℝ) ^ k v * ep := fun v => mul_nonneg (pow_nonneg (by norm_num) _) hep.le
    obtain ⟨hfin, hcard⟩ := hcount (fun v => 2 ^ k v * ep) hr
    have hsub : ((u.filter fun γ => K γ = k : Finset Γ) : Set Γ) ⊆ {γ | ∀ v, d γ v ≤ 2 ^ k v * ep} := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp (Finset.mem_coe.mp hγ)
      intro v
      have := hsh1 (d γ v)
      rw [← hγ'.2]
      exact this
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hle
    calc ((u.filter fun γ => K γ = k).card : ℝ)
        ≤ (({γ | ∀ v, d γ v ≤ 2 ^ k v * ep}.ncard : ℕ) : ℝ) := by exact_mod_cast hle
      _ ≤ A * Real.exp (κ * ∑ v, 2 ^ k v * ep) := hcard
      _ = A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
        rw [Finset.mul_sum, Real.exp_sum]

  have hpart : ∀ u : Finset Γ, ∑ γ ∈ u, w γ
      ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
    intro u
    set N : ℕ := u.sup fun γ => Finset.univ.sup (K γ) with hN
    set B := (Fintype.piFinset fun _ : ι => range (N + 1)).erase (fun _ => 0) with hB
    have hmaps : ∀ γ ∈ u, K γ ∈ B := by
      intro γ hγ
      rw [hB, Finset.mem_erase, Fintype.mem_piFinset]
      refine ⟨?_, fun v => ?_⟩
      · intro h0
        obtain ⟨v, hv⟩ := hfar γ
        have h1 : K γ v = 0 := congrFun h0 v
        have h2 := hsh1 (d γ v)
        simp only [K] at h1
        rw [h1, pow_zero, one_mul] at h2
        linarith
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Finset.le_sup (f := K γ) (Finset.mem_univ v)).trans
          (Finset.le_sup (f := fun γ => Finset.univ.sup (K γ)) hγ)
    have hal0 : 0 ≤ W 0 := hW0 0
    have hal2 : W 0 ≤ 2 := by
      show Real.exp (κ * (2 ^ 0 * ep)) * (if (0 : ℕ) = 0 then 1 else Real.exp (-T * 2 ^ 0)) ≤ 2
      rw [if_pos rfl, pow_zero, one_mul, mul_one]
      calc Real.exp (κ * ep) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hκep
        _ = 2 := Real.exp_log (by norm_num)
    have hT1 : 1 ≤ T := hT
    have hWs : ∀ i, W (i + 1) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
      intro i
      refine le_trans ?_ (exp_neg_mul_two_pow_le_geometric T hT1 i)
      simp only [W, F, if_neg (Nat.succ_ne_zero i)]
      rw [← Real.exp_add, Real.exp_le_exp, pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ i := pow_nonneg (by norm_num) _
      nlinarith
    have hexpT : Real.exp (-T) ≤ 1 / 2 := by
      have h1 : Real.exp (-T) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-1) := Real.exp_pos _
      nlinarith
    have hbe : ∑ i ∈ range N, W (i + 1) ≤ 2 * Real.exp (-T) := by
      calc ∑ i ∈ range N, W (i + 1) ≤ ∑ i ∈ range N, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
            Finset.sum_le_sum fun i _ => hWs i
        _ = Real.exp (-T) * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
        _ ≤ Real.exp (-T) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (Real.exp_pos _).le
        _ = 2 * Real.exp (-T) := mul_comm _ _
    have hbe0 : 0 ≤ ∑ i ∈ range N, W (i + 1) := Finset.sum_nonneg fun i _ => hW0 _
    have hbe1 : ∑ i ∈ range N, W (i + 1) ≤ 1 := by linarith
    have hbox := sum_prod_box_erase_zero ι W N
    have key := hpow (W 0) (∑ i ∈ range N, W (i + 1)) (Fintype.card ι) hal0 hal2 hbe0 hbe1
    calc ∑ γ ∈ u, w γ ≤ ∑ γ ∈ u, ∏ v, F (K γ v) := Finset.sum_le_sum fun γ _ => hwF γ
      _ = ∑ k ∈ B, ∑ γ ∈ u with K γ = k, ∏ v, F (k v) :=
          (Finset.sum_fiberwise_of_maps_to' hmaps (fun k => ∏ v, F (k v))).symm
      _ = ∑ k ∈ B, ((u.filter fun γ => K γ = k).card : ℝ) * ∏ v, F (k v) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, (A * ∏ v, Real.exp (κ * (2 ^ k v * ep))) * ∏ v, F (k v) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hfib u k) (Finset.prod_nonneg fun v _ => hF0 _)
      _ = A * ∑ k ∈ B, ∏ v, W (k v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
      _ = A * ((W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι) := by
          rw [hB, hbox]
      _ ≤ A * (Fintype.card ι * (2 * Real.exp (-T)) * 3 ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left (key.trans ?_) hA
          have h3 : (0 : ℝ) ≤ 3 ^ Fintype.card ι := pow_nonneg (by norm_num) _
          have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbe hn) h3
      _ = A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
          rw [hTdef]
          ring
  have hw0 : 0 ≤ w := fun γ => (hw γ).1
  exact ⟨summable_of_sum_le hw0 hpart, Real.tsum_le_of_sum_le hw0 hpart⟩
end GlobalTheory
