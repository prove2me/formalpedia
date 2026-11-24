-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:34:32.111575+00:00
-- url     : https://prove2.me/submissions/ac4751c6-e4ac-469a-aa49-8ae8fbcca1fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_en_mul
import Theorems.Thm_GlobalTheory_BruhatRep_en_mS
import Theorems.Thm_GlobalTheory_BruhatRep_mx_unit
import Theorems.Thm_GlobalTheory_BruhatRep_a_ne
import Theorems.Thm_GlobalTheory_BruhatRep_mx_mul
import Theorems.Thm_GlobalTheory_BruhatRep_mx_mulh
import Theorems.Thm_GlobalTheory_BruhatRep_n_mxh
import Theorems.Thm_GlobalTheory_BruhatRep_t_mxh
import Theorems.Thm_GlobalTheory_BruhatRep_four_eq
import Theorems.Thm_P2M_GlobalTheory_BruhatRep_two_eq__9038439e0117
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
theorem _root_.solution (hm : ∀ a b, m (a * b) = m a * m b) (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s)
    (htm : ∀ s, t * m s = m s⁻¹ * t) (g : SpecialLinearGroup (Fin 2) K) (s : Kˣ) :
    rho n m t (g * mS s) = rho n m t g * m s := by
  obtain ⟨a0, a1, a2, a3⟩ := en_mS s
  have hs := s.ne_zero
  have e0 : en (g * mS s) 0 0 = en g 0 0 * s := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * mS s) 0 1 = en g 0 1 * (s : K)⁻¹ := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * mS s) 1 0 = en g 1 0 * s := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * mS s) 1 1 = en g 1 1 * (s : K)⁻¹ := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · have ha := a_ne g hc
    rw [rho_pos n m t (by rw [e2, hc, zero_mul]), rho_pos n m t hc, e0, e1]
    rw [← mx_unit m s, n_mxh n m hmn hs, mx_mul m hm ha hs]
    apply two_eq' n m rfl; field_simp
  · have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
    rw [rho_neg n m t (by rw [e2]; exact mul_ne_zero hc hs), rho_neg n m t hc, e0, e2, e3]
    rw [← mx_unit m s, n_mxh n m hmn hs, t_mxh m t htm hs, mx_mulh m hm hb (inv_ne_zero hs)]
    apply four_eq n m t <;> field_simp
end GlobalTheory.BruhatRep
