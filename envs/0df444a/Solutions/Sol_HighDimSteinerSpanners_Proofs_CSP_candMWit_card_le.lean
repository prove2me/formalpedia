-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.candMWit_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:14.839394+00:00
-- url     : https://prove2.me/submissions/b895f9f1-a81f-4bda-bf1c-ff7e2fe155d9

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_choose_bound_exp4
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_lam0_ge_1000_C1


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by
  intro M
  let K_max := cspKMax C₁
  let W_ab := disagreeSet x a ∪ disagreeSet x b
  have hW_card : W_ab.card ≤ 2 * C₁ * r_star := by
    have h1 := Finset.card_union_le (disagreeSet x a) (disagreeSet x b)
    have h2 : (disagreeSet x a).card ≤ C₁ * r_star := hd_xa
    have h3 : (disagreeSet x b).card ≤ C₁ * r_star := hd_xb
    calc
      W_ab.card ≤ C₁ * r_star + C₁ * r_star := le_trans h1 (Nat.add_le_add h2 h3)
      _ = 2 * C₁ * r_star := by ring
  let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
    (Fintype.piFinset (fun u : Fin N =>
      if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
      Fintype.piFinset (fun _ : Fin K_max => M.powerset))
  let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
    if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
  have hcard_le1 : (candMWit C₁ r_star a b m z_prev x).card ≤
      ∑ ktB ∈ base, (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
        (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) := by
    have h1 : (candMWit C₁ r_star a b m z_prev x).card ≤
        (base.biUnion (fun ktB =>
          (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
            (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).card :=
      Finset.card_filter_le _ _
    refine le_trans h1 (le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun ktB _ => ?_)))
    exact le_trans Finset.card_image_le (le_of_eq (Finset.card_powersetCard _ _))
  have hU_card : ((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card ≤ 16 * C₁ ^ 2 * r_star := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    calc
      K_max * W_ab.card ≤ (8 * C₁) * (2 * C₁ * r_star) :=
        Nat.mul_le_mul_left K_max hW_card
      _ = 16 * C₁ ^ 2 * r_star := by ring
  have hS_le : ∀ ktB : Fin (K_max + 1) × (Fin N → Fin (K_max + 1)) × (Fin K_max → Finset (Fin N)),
      ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤ M.card := by
    intro ktB
    have hle1 : ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤
        ∑ r : Fin K_max, (M.filter (fun u => ktB.2.1 u = r.succ)).card := by
      refine Finset.sum_le_sum (fun r _ => ?_)
      dsimp [s_hat]
      split_ifs
      · exact Nat.sub_le _ _
      · exact Nat.zero_le _
    have hdisj : ((Finset.univ : Finset (Fin K_max)) : Set (Fin K_max)).PairwiseDisjoint
        (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) := by
      intro r₁ _ r₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro u hu₁ hu₂
      simp only [Finset.mem_filter] at hu₁ hu₂
      exact hne (Fin.succ_injective _ (hu₁.2.symm.trans hu₂.2))
    have hsub : (Finset.univ : Finset (Fin K_max)).biUnion
        (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) ⊆ M := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨_, _, huM⟩
      exact (Finset.mem_filter.mp huM).1
    rw [← Finset.card_biUnion hdisj] at hle1
    exact le_trans hle1 (Finset.card_le_card hsub)
  have hbase_card : base.card =
      (K_max + 1) * ((K_max + 1) ^ M.card * (2 ^ M.card) ^ K_max) := by
    dsimp [base]
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Fintype.card_piFinset, Fintype.card_piFinset]
    have htau : ∀ u : Fin N,
        (if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))).card =
          if u ∈ M then K_max + 1 else 1 := by
      intro u
      split_ifs
      · rw [Finset.card_univ, Fintype.card_fin]
      · exact Finset.card_singleton 0
    simp_rw [htau, Finset.card_powerset]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum_r : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
    have hc : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
        ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
          (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := by
      exact_mod_cast hcard_le1
    calc
      ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
        ≤ ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := hc
      _ ≤ ∑ _ktB ∈ base, ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
          refine Finset.sum_le_sum (fun ktB _ => ?_)
          have hch := choose_bound_exp4 (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card)
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) M.card r_star (16 * C₁ ^ 2)
            (by nlinarith) hU_card (hS_le ktB)
          simpa using hch
      _ = (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hconst_r : ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
    have hk_r : K_max + 1 ≤ 2 ^ r_star := by
      have hk1 : K_max + 1 ≤ r_star := by dsimp [K_max, cspKMax]; omega
      exact le_trans hk1 (le_of_lt Nat.lt_two_pow_self)
    have hk_real : ((K_max + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
      have hc : ((K_max + 1 : ℕ) : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by exact_mod_cast hk_r
      rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hc
    have h4_eq : (4 : ℝ) ^ r_star = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
      push_cast; rfl
    calc
      ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star
        ≤ (2 : ℝ) ^ (r_star : ℝ) * (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
          rw [h4_eq]; exact mul_le_mul_of_nonneg_right hk_real (by positivity)
      _ = (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
  have hper_s : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
      (2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ)) := by
    have hk_pow : K_max + 1 ≤ 2 ^ K_max := Nat.lt_two_pow_self
    have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
    have hnat : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
        2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) := by
      have h1 : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
          2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) := by
        have hC2 : C₁ ^ 2 ≤ (2 ^ Nat.clog 2 C₁) ^ 2 := Nat.pow_le_pow_left hC_pow 2
        have h16 : 16 * C₁ ^ 2 ≤ 2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2 := by
          simpa using Nat.mul_le_mul_left 16 hC2
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hk_pow) h16
      have h2 : 2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) =
          2 ^ (2 * K_max + 4 + 2 * Nat.clog 2 C₁) := by
        rw [← pow_mul (2 : ℕ) (Nat.clog 2 C₁) 2,
          show Nat.clog 2 C₁ * 2 = 2 * Nat.clog 2 C₁ by ring,
          ← pow_add, ← pow_add, ← pow_add]
        congr 1; omega
      have hclog_ge2 := (lam0_ge_1000_C1 C₁ hC₁).1
      have hexp : 2 * K_max + 4 + 2 * Nat.clog 2 C₁ ≤ 10 * C₁ * (2 * Nat.clog 2 C₁ + 6) := by
        dsimp [K_max, cspKMax]
        have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
        nlinarith
      rw [h2] at h1
      exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) hexp)
    have hcast : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
        ((2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine le_trans hcast (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    congr 1
    dsimp [cspLam0]
    push_cast
    ring
  have hrew_base : (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) =
      (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
        (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
    rw [hbase_card]
    push_cast
    rw [pow_right_comm (2 : ℝ) M.card K_max]
    repeat rw [mul_pow]
    ring
  calc
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
      ≤ (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
          (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
        rwa [hrew_base] at hsum_r
    _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) *
          ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ))) ^ M.card :=
        mul_le_mul hconst_r (pow_le_pow_left₀ (by positivity) hper_s M.card)
          (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _) M.card,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
end HighDimSteinerSpanners.Proofs.CSP
