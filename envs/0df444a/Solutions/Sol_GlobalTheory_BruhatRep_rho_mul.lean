-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:52:42.535911+00:00
-- url     : https://prove2.me/submissions/2872c550-6158-4924-8b6b-0c553ccd918a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_det_en
import Theorems.Thm_GlobalTheory_BruhatRep_en_mul
import Theorems.Thm_GlobalTheory_BruhatRep_en_nS
import Theorems.Thm_GlobalTheory_BruhatRep_en_mS
import Theorems.Thm_GlobalTheory_BruhatRep_en_wS
import Theorems.Thm_GlobalTheory_BruhatRep_mx_ne
import Theorems.Thm_GlobalTheory_BruhatRep_a_ne
import Theorems.Thm_GlobalTheory_BruhatRep_rho_pos
import Theorems.Thm_GlobalTheory_BruhatRep_rho_neg
import Theorems.Thm_GlobalTheory_BruhatRep_rho_n
import Theorems.Thm_GlobalTheory_BruhatRep_rho_m
import Theorems.Thm_GlobalTheory_BruhatRep_rho_w

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
    (htm : ∀ s, t * m s = m s⁻¹ * t)
    (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    (g h : SpecialLinearGroup (Fin 2) K) : rho n m t (g * h) = rho n m t g * rho n m t h := by
  have hdet := det_en h
  by_cases hc : en h 1 0 = 0
  · have ha := a_ne h hc
    have hh : h = mS (Units.mk0 (en h 0 0) ha) * nS (en h 0 1 / en h 0 0) := by
      obtain ⟨a0, a1, a2, a3⟩ := en_mS (Units.mk0 (en h 0 0) ha)
      obtain ⟨b0, b1, b2, b3⟩ := en_nS (en h 0 1 / en h 0 0)
      rw [hc] at hdet
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change en h i j = en _ i j
      rw [en_mul]
      fin_cases i <;> fin_cases j <;>
        simp only [a0, a1, a2, a3, b0, b1, b2, b3, Units.val_mk0, Fin.zero_eta, Fin.mk_one, hc] <;> first | ring1 | (field_simp; done) | (field_simp; ring1) | (field_simp; linear_combination hdet) | (field_simp; linear_combination -hdet) | (field_simp; linear_combination (en h 1 0) * hdet) | (field_simp; linear_combination (-en h 1 0) * hdet)
    rw [show g * h = g * mS (Units.mk0 (en h 0 0) ha) * nS (en h 0 1 / en h 0 0) from by
      conv_lhs => rw [hh]
      rw [mul_assoc]]
    rw [rho_n n m t hn, rho_m n m t hm hmn htm, mul_assoc, rho_pos n m t hc, mx_ne m ha]
  · have hb : -1 / en h 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
    have hh : h = nS (en h 0 0 / en h 1 0) * mS (Units.mk0 (-1 / en h 1 0) hb) * wS K *
        nS (en h 1 1 / en h 1 0) := by
      obtain ⟨a0, a1, a2, a3⟩ := en_mS (Units.mk0 (-1 / en h 1 0) hb)
      obtain ⟨b0, b1, b2, b3⟩ := en_nS (en h 0 0 / en h 1 0)
      obtain ⟨c0, c1, c2, c3⟩ := en_nS (en h 1 1 / en h 1 0)
      obtain ⟨d0, d1, d2, d3⟩ := en_wS (K := K)
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change en h i j = en _ i j
      simp only [en_mul]
      fin_cases i <;> fin_cases j <;>
        simp only [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3, Units.val_mk0,
          Fin.zero_eta, Fin.mk_one] <;> first | ring1 | (field_simp; done) | (field_simp; ring1) | (field_simp; linear_combination hdet) | (field_simp; linear_combination -hdet) | (field_simp; linear_combination (en h 1 0) * hdet) | (field_simp; linear_combination (-en h 1 0) * hdet)
    rw [show g * h = g * nS (en h 0 0 / en h 1 0) * mS (Units.mk0 (-1 / en h 1 0) hb) * wS K *
        nS (en h 1 1 / en h 1 0) from by
      conv_lhs => rw [hh]
      simp only [mul_assoc]]
    rw [rho_n n m t hn, rho_w n m t hn0 hn hm hmn htt htnt, rho_m n m t hm hmn htm, rho_n n m t hn,
      rho_neg n m t hc, mx_ne m hb]
    simp only [mul_assoc]
end GlobalTheory.BruhatRep
