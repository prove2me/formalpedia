-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:36:44.910939+00:00
-- url     : https://prove2.me/submissions/131bbe18-d68c-4664-b775-82232040c5a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_det_en
import Theorems.Thm_GlobalTheory_BruhatRep_en_mul
import Theorems.Thm_GlobalTheory_BruhatRep_en_wS
import Theorems.Thm_GlobalTheory_BruhatRep_a_ne
import Theorems.Thm_GlobalTheory_BruhatRep_d_ne
import Theorems.Thm_GlobalTheory_BruhatRep_mx_mulh
import Theorems.Thm_GlobalTheory_BruhatRep_mx_n
import Theorems.Thm_GlobalTheory_BruhatRep_mx_nh
import Theorems.Thm_GlobalTheory_BruhatRep_t_th
import Theorems.Thm_GlobalTheory_BruhatRep_t_n_th
import Theorems.Thm_GlobalTheory_BruhatRep_four_eq
import Theorems.Thm_GlobalTheory_BruhatRep_two_eq
import Theorems.Thm_GlobalTheory_BruhatRep_three_eq
import Theorems.Thm_GlobalTheory_BruhatRep_rho_pos
import Theorems.Thm_GlobalTheory_BruhatRep_rho_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution (hn0 : n 0 = 1) (hn : ∀ a b, n (a + b) = n a * n b) (hm : ∀ a b, m (a * b) = m a * m b)
    (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) (htt : t * t = m (-1))
    (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    (g : SpecialLinearGroup (Fin 2) K) :
    rho n m t (g * wS K) = rho n m t g * t := by
  obtain ⟨a0, a1, a2, a3⟩ := en_wS (K := K)
  have hdet := det_en g
  have e0 : en (g * wS K) 0 0 = -en g 0 1 := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * wS K) 0 1 = en g 0 0 := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * wS K) 1 0 = -en g 1 1 := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * wS K) 1 1 = en g 1 0 := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · have hd := d_ne g hc
    have ha := a_ne g hc
    rw [rho_neg n m t (by rw [e2]; exact neg_ne_zero.2 hd), rho_pos n m t hc, e0, e2, e3, hc, zero_div,
      hn0, mul_one, mx_n n m hmn ha]
    rw [hc] at hdet
    apply three_eq n m t
    · field_simp; linear_combination (-en g 0 1) * hdet
    · field_simp; linear_combination -hdet
  · by_cases hd : en g 1 1 = 0
    · rw [rho_pos n m t (by rw [e2, hd, neg_zero]), rho_neg n m t hc, e0, e1, hd, zero_div, hn0, mul_one,
        t_th m t htt]
      rw [hd] at hdet
      have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
      have h01 : -en g 0 1 ≠ 0 := by intro h; rw [neg_eq_zero] at h; rw [h] at hdet; simp at hdet
      rw [mx_mulh m hm hb (by norm_num), mx_n n m hmn h01]
      apply two_eq n m
      · field_simp; linear_combination (en g 0 0) * hdet
      · field_simp; linear_combination hdet
    · rw [rho_neg n m t (by rw [e2]; exact neg_ne_zero.2 hd), rho_neg n m t hc, e0, e2, e3]
      have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
      have hu : -(en g 1 1 / en g 1 0)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (div_ne_zero hd hc))
      rw [t_n_th n m t htnt (div_ne_zero hd hc), mx_nh n m hmn hb, ← hn, mx_mulh m hm hb hu]
      apply four_eq n m t
      · field_simp; linear_combination -hdet
      · field_simp
      · field_simp
end GlobalTheory.BruhatRep
