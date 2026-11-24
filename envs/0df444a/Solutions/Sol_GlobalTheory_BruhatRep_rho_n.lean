-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:30.427279+00:00
-- url     : https://prove2.me/submissions/f13dea12-8ec2-4319-ba8d-e11d46eb82b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_en_mul
import Theorems.Thm_GlobalTheory_BruhatRep_en_nS
import Theorems.Thm_GlobalTheory_BruhatRep_a_ne
import Theorems.Thm_GlobalTheory_BruhatRep_nn
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
theorem _root_.solution (hn : ∀ a b, n (a + b) = n a * n b) (g : SpecialLinearGroup (Fin 2) K) (z : K) :
    rho n m t (g * nS z) = rho n m t g * n z := by
  obtain ⟨a0, a1, a2, a3⟩ := en_nS z
  have e0 : en (g * nS z) 0 0 = en g 0 0 := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * nS z) 0 1 = en g 0 0 * z + en g 0 1 := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * nS z) 1 0 = en g 1 0 := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * nS z) 1 1 = en g 1 0 * z + en g 1 1 := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · rw [rho_pos n m t (e2 ▸ hc), rho_pos n m t hc, e0, e1, nn n hn]
    apply two_eq' n m rfl; have := a_ne g hc; field_simp; ring
  · rw [rho_neg n m t (e2 ▸ hc), rho_neg n m t hc, e0, e2, e3, nn n hn]
    apply four_eq n m t rfl rfl; field_simp; ring
end GlobalTheory.BruhatRep
