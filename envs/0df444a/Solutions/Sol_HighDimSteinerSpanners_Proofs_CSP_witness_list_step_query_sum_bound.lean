-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.witness_list_step_query_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:53.871777+00:00
-- url     : https://prove2.me/submissions/022537d0-6202-4640-ac07-6bf35c5fa139

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_incidentQueryCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candidateQueriesFreshAndSupported
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_freshCoordinateFiberCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_candMWit_card_and_quad
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_lam0_ge_1000_C1

section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
private lemma calibration_range_bound (C₁ r_star : ℕ) (hC₁ : 3 ≤ C₁)
    (hr : 1000 * C₁ < r_star) :
    ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
  have hcr_le : C₁ * r_star + 1 ≤ r_star * r_star := by
    have hC1_le : C₁ + 1 ≤ r_star := by omega
    calc
      C₁ * r_star + 1 ≤ C₁ * r_star + r_star := by omega
      _ = (C₁ + 1) * r_star := (Nat.succ_mul C₁ r_star).symm
      _ ≤ r_star * r_star := Nat.mul_le_mul_right r_star hC1_le
  have hr_pow : r_star ≤ 2 ^ r_star := Nat.le_of_lt Nat.lt_two_pow_self
  have hsq_pow : r_star * r_star ≤ 2 ^ (2 * r_star) := by
    calc
      r_star * r_star ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
      _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
      _ = 2 ^ (2 * r_star) := by rw [two_mul]
  have hnat := le_trans hcr_le hsq_pow
  have hcast : ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ ((2 ^ (2 * r_star) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] at hcast
open Classical in
private lemma witnessMoments_h_xw_bound :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            ∀ (N q : ℕ) (σ p_keep : ℝ),
              (0 : ℝ) < σ →
                σ * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) * (↑(cspBeta0 C₁) : ℝ) →
                  (0 : ℝ) < p_keep →
                    ∀ (a₀ b₀ : Fin N → Fin q),
                      ∀ (m : ℕ),
                        ∀ (z_prev : Fin m → Fin N → Fin q),
                          (3000 : ℕ) ≤ cspLam0 C₁ →
                            (↑(cspBeta0 C₁) : ℝ) = (6 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                              let p_edge : ℝ := (2 : ℝ) ^ (-σ);
                              let P_rem : Finset (Fin N → Fin q) :=
                                cspPoolCand C₁ r_star a₀ b₀ \ Finset.image z_prev Finset.univ;
                              ∀ x ∈ P_rem,
                                ∀ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
                                  ∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
                                      Sum.elim (fun (_ : Fin N × Fin N × Fin q × Fin q) => p_edge)
                                        (fun (_ : Fin N → Fin q) => p_keep) i ≤
                                    p_keep * p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N -
                                        (1 : ℕ))) *
                                      (2 : ℝ) ^
                                        ((346 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑(candMFresh
                                            a₀ b₀ m z_prev x).card : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr N q σ p_keep hσ_pos_loc hσ_up_loc hp_keep_pos_loc a₀ b₀ m z_prev
      hlam_ge hbeta_eq p_edge P_rem x hx w hw
  have hx_pool := (Finset.mem_sdiff.mp hx).1
  simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
  rcases hx_pool with ⟨_, _, hd_xa, hd_xb⟩
  obtain ⟨_, _, _, h_prod_eq⟩ := candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a₀ b₀
      z_prev x hx
  rw [h_prod_eq w p_edge p_keep]
  let S := candMFresh a₀ b₀ m z_prev x
  let s := S.card
  let a1 := (candA1 S).card
  let a2 := (candA2 C₁ a₀ b₀ x S w).card
  let N1 := N - 1
  have hs1_z : 2 * ((s : ℤ) * (N1 : ℤ) - (a1 : ℤ)) ≤ (s : ℤ) ^ 2 := incidentQueryCardinality S
  have hs2_z : 40 * ((s : ℤ) ^ 2 - 2 * (a2 : ℤ)) ≤ 23 * (r_star : ℤ) * (s : ℤ) :=
    ((candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hd_xa hd_xb).2 w hw).2
  have hdef_z : 80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ)) ≤
      23 * (r_star : ℤ) * (s : ℤ) := by
    push_cast
    linarith only [hs1_z, hs2_z]
  have hdef_r : 80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
      23 * (r_star : ℝ) * (s : ℝ) := by
    have hcast : ((80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ))) : ℝ) ≤
        ((23 * (r_star : ℤ) * (s : ℤ)) : ℝ) := by exact_mod_cast hdef_z
    push_cast at hcast ⊢
    linarith only [hcast]
  have hσ_def : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
      (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ) := by
    have h1 : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
        (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left hdef_r (le_of_lt hσ_pos_loc)
      linarith [hm,
        show σ * (23 * (r_star : ℝ) * (s : ℝ)) =
          80 * ((σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ))) by ring,
        show σ * (80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) =
          80 * (σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) by ring]
    have h2 : (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) ≤
        ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * ((23 / 40 : ℝ) * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_up_loc, hbeta_eq]) (by positivity)
    have hprod_nn : (0 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
    linarith [h1, h2, hprod_nn]
  have hp_pow : p_edge ^ (a1 + a2) ≤ p_edge ^ (s * N1) *
      (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
    have h_eq1 : p_edge ^ (a1 + a2) = (2 : ℝ) ^ (- σ * ((a1 + a2 : ℕ) : ℝ)) := by
      dsimp [p_edge]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h_eq2 : p_edge ^ (s * N1) *
        (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) =
        (2 : ℝ) ^ (- σ * ((s * N1 : ℕ) : ℝ) +
          (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
      dsimp [p_edge]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [h_eq1, h_eq2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hσ_def]
  calc
    p_keep * p_edge ^ (a1 + a2)
      ≤ p_keep * (p_edge ^ (s * N1) *
          (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
        mul_le_mul_of_nonneg_left hp_pow (le_of_lt hp_keep_pos_loc)
    _ = p_keep * p_edge ^ (s * N1) *
          (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
        (mul_assoc _ _ _).symm
open Classical in
private lemma witnessMoments_h_s_term :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star N q : ℕ) (σ p_keep : ℝ),
          (∀ (s : ℕ),
              (↑(N.choose s) : ℝ) * (↑(q - (1 : ℕ)) : ℝ) ^ s * ((2 : ℝ) ^ (-σ)) ^ (s * (N - (1 :
                  ℕ))) ≤
                (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
            (0 : ℝ) < p_keep →
              ∀ (a₀ b₀ : Fin N → Fin q),
                dHam a₀ b₀ ≤ C₁ * r_star →
                  ∀ m < cspKMom C₁,
                    ∀ (z_prev : Fin m → Fin N → Fin q),
                      (3000 : ℕ) ≤ cspLam0 C₁ →
                        (↑(cspGamma0 C₁) : ℝ) = (5 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                          let p_edge : ℝ := (2 : ℝ) ^ (-σ);
                          let P_rem : Finset (Fin N → Fin q) :=
                            cspPoolCand C₁ r_star a₀ b₀ \ Finset.image z_prev Finset.univ;
                          let C_fixed : ℝ := (2 : ℝ) ^ ((3 : ℝ) * (↑r_star : ℝ)) * p_keep;
                          (0 : ℝ) ≤ C_fixed →
                            let R_s : Finset ℕ := Finset.range (C₁ * r_star + (1 : ℕ));
                            (∀ (t : Fin m), dHam (z_prev t) a₀ ≤ C₁ * r_star) →
                              (↑(C₁ * r_star + (1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) →
                                ∀ s ∈ R_s,
                                  ∑ x ∈ P_rem with (candMFresh a₀ b₀ m z_prev x).card = s,
                                      p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - (1 :
                                          ℕ))) *
                                          (2 : ℝ) ^
                                            ((356 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                              (↑(candMFresh a₀ b₀ m z_prev x).card : ℝ)) *
                                        C_fixed ≤
                                    (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) *
                                          (2 : ℝ) ^ ((1 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                              (↑r_star : ℝ)) *
                                        (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ)) *
                                      C_fixed := by
  classical
  intro C₁ hC₁ r_star N q σ p_keep h_bin_loc hp_keep_pos_loc a₀ b₀ hd_ab_loc m hm z_prev hlam_ge
      hgamma_eq p_edge P_rem C_fixed hC_nn R_s hz_da h_range_r s _
  have h_congr : ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
      ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
        (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
          ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) =
    ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
      ((p_edge ^ (s * (N - 1)) *
        (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) := by
    have h1 : ∀ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
        (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
            ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed =
          (p_edge ^ (s * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  rw [h_congr]
  have hfib_sub : P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s) ⊆
      Finset.univ.filter (fun x =>
        (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxP, hxs⟩
    have hx_pool := (Finset.mem_sdiff.mp hxP).1
    simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxs, hx_pool.2.2.1⟩
  have hfib_le1 : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
      ((Finset.univ.filter (fun x =>
        (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hfib_sub
  have hfib_r : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    have hs4 := le_trans hfib_le1 (freshCoordinateFiberCardinality C₁ r_star m hC₁ hm a₀ b₀
        z_prev hd_ab_loc hz_da s)
    exact le_trans hs4 (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h_range_r (by positivity)) (by positivity))
  have hs_bin : ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
      (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    calc
      ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))
        ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
          mul_le_mul_of_nonneg_right (h_bin_loc s) (by positivity)
      _ = (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
            (356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hls_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
          rw [hgamma_eq]
          linarith only [hls_nn]
  calc
    ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
        ((p_edge ^ (s * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed)
      ≤ ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s)) *
          ((p_edge ^ (s * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) :=
        mul_le_mul_of_nonneg_right hfib_r (by positivity)
    _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
        ring
    _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs_bin (by positivity)) hC_nn
end Helpers
end HighDimSteinerSpanners.Proofs.CSP
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ <
    r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (a b : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
    (hd_ab : dHam a b ≤ C₁ * r_star) :
    ∃ (M_wit : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        Finset (candWitType (2 ^ cspL C₁ * r_star) C₁))
      (Q_cand : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        candWitType (2 ^ cspL C₁ * r_star) C₁ →
        Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))),
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
        ∀ w ∈ M_wit m z_prev x,
          Q_cand m z_prev x w ⊆
            cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
      (∀ (ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (m : ℕ), m < cspKMom C₁ →
        ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ω (Sum.inr x) = true →
          x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
          ∃ w ∈ M_wit m z_prev x, ∀ i ∈ Q_cand m z_prev x w, ω i = true) ∧
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∑ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ∑ w ∈ M_wit m z_prev x, (∏ i ∈ Q_cand m z_prev x w, cspPIota C₁ r_star i) ≤
            (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  have h_s5_poly : ∀ (N q : ℕ) (σ p_keep : ℝ),
      0 < σ →
      σ * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) →
      (∀ s : ℕ,
        (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * ((2 : ℝ) ^ (- σ)) ^ (s * (N - 1)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) →
      0 < p_keep →
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) →
      ∀ (a₀ b₀ : Fin N → Fin q), dHam a₀ b₀ ≤ C₁ * r_star →
      ∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin N → Fin q),
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a₀ b₀) →
        ∑ x ∈ cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev,
          ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
            (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
              Sum.elim (fun _ => (2 : ℝ) ^ (- σ)) (fun _ => p_keep) i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    clear hσ_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up hd_ab a b
    intro N q σ p_keep hσ_pos_loc hσ_up_loc h_bin_loc hp_keep_pos_loc hp_keep_up_loc
      a₀ b₀ hd_ab_loc m hm z_prev hz_pool
    have hlam_ge : 3000 ≤ cspLam0 C₁ := by
      have h := (lam0_ge_1000_C1 C₁ hC₁).2.1
      omega
    have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
      unfold cspBeta0; push_cast; ring
    have hgamma_eq : (cspGamma0 C₁ : ℝ) = 5 * (cspLam0 C₁ : ℝ) := by
      unfold cspGamma0; push_cast; ring
    let p_edge : ℝ := (2 : ℝ) ^ (- σ)
    let P_rem := cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev
    have h_xw_bound :=
      @witnessMoments_h_xw_bound C₁ hC₁ r_star hr N q σ p_keep hσ_pos_loc hσ_up_loc
          hp_keep_pos_loc a₀ b₀ m z_prev hlam_ge hbeta_eq
    let C_fixed : ℝ := (2 : ℝ) ^ (3 * (r_star : ℝ)) * p_keep
    have hC_nn : 0 ≤ C_fixed := by positivity
    have h_x_bound : ∀ x ∈ P_rem,
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
          (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
            Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
            ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed := by
      intro x hx
      have hx_pool := (Finset.mem_sdiff.mp hx).1
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
      have h_wcard_r :=
        (candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx_pool.2.2.1 hx_pool.2.2.2).1
      let s := (candMFresh a₀ b₀ m z_prev x).card
      calc
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ _w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            Finset.sum_le_sum (fun w hw => h_xw_bound x hx w hw)
        _ = ((candMWit C₁ r_star a₀ b₀ m z_prev x).card : ℝ) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            mul_le_mul_of_nonneg_right h_wcard_r (by positivity)
        _ = (p_edge ^ (s * (N - 1)) *
              ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)))) * C_fixed := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            dsimp [C_fixed]
            ring
        _ = (p_edge ^ (s * (N - 1)) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 3
            ring
    let R_s := Finset.range (C₁ * r_star + 1)
    have hP_bi : P_rem = R_s.biUnion
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      ext x
      simp only [R_s, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · intro hx
        have hS_sub := (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx).1
        have hx_pool := (Finset.mem_sdiff.mp hx).1
        simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
        have hs_le : (candMFresh a₀ b₀ m z_prev x).card ≤ C₁ * r_star :=
          le_trans (Finset.card_le_card (hS_sub.trans Finset.inter_subset_left)) hx_pool.2.2.1
        exact ⟨(candMFresh a₀ b₀ m z_prev x).card, Nat.lt_succ_of_le hs_le, hx, rfl⟩
      · rintro ⟨_, _, hx, _⟩
        exact hx
    have hP_disj : (R_s : Set ℕ).PairwiseDisjoint
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      intro s₁ _ s₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      intro x hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
    have hz_da : ∀ t : Fin m, dHam (z_prev t) a₀ ≤ C₁ * r_star := by
      intro t
      have ht := hz_pool t
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht.2.2.1
    have h_range_r := calibration_range_bound C₁ r_star hC₁ hr
    have h_s_term :=
      @witnessMoments_h_s_term C₁ hC₁ r_star N q σ p_keep h_bin_loc hp_keep_pos_loc a₀ b₀
          hd_ab_loc m hm z_prev hlam_ge hgamma_eq hC_nn hz_da h_range_r
    have hRs_card : (R_s.card : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      simpa [R_s] using h_range_r
    have h_tot_1 : ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
        (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
          Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
      calc
        ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ x ∈ P_rem,
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) :=
            Finset.sum_le_sum h_x_bound
        _ = ∑ s ∈ R_s, ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) := by
            conv_lhs => rw [hP_bi]
            exact Finset.sum_biUnion hP_disj
        _ ≤ ∑ _s ∈ R_s,
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            Finset.sum_le_sum h_s_term
        _ = (R_s.card : ℝ) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            mul_le_mul_of_nonneg_right hRs_card (by positivity)
    have hC_up : C_fixed ≤
        (2 : ℝ) ^ (3 * (r_star : ℝ)) *
          (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
      dsimp [C_fixed]
      exact mul_le_mul_of_nonneg_left hp_keep_up_loc (by positivity)
    have h_tot_2 : (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
          (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
          3 * (r_star : ℝ) +
          (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
      calc
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
            ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed)
          ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) *
                ((2 : ℝ) ^ (3 * (r_star : ℝ)) *
                  (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hC_up (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (3 * (r_star : ℝ)) *
              (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by ring
        _ = _ := by
            repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h_exp_le : 2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
        (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
        3 * (r_star : ℝ) +
        (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        - (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      have hlam_r : (3000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam_ge
      have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
      nlinarith only [hlam_r, hr_nn]
    exact le_trans h_tot_1
      (le_trans h_tot_2 (Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp_le))
  refine ⟨fun m z_prev x => candMWit C₁ r_star a b m z_prev x,
    fun m z_prev x w => candQCand C₁ a b m z_prev x w, ?_, ?_, ?_⟩
  · intro m _ z_prev _ x hx w hw
    exact (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a b z_prev x hx).2.1 w hw
  · intro ω m _ z_prev _ x hx hω hClean
    exact (candidateQueriesFreshAndSupported C₁ r_star m hC₁ hr a b z_prev x hx).2.2.1 ω hω hClean
  · unfold cspPEdge at h_binom_edge
    unfold cspPIota cspPEdge
    exact h_s5_poly (2 ^ cspL C₁ * r_star) (cspQ C₁)
      (cspSigmaEdge C₁ r_star) (cspPKeep C₁ r_star)
      hσ_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up a b hd_ab
end HighDimSteinerSpanners.Proofs.CSP
