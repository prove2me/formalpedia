-- Prove2me | solution 1 for GlobalTheory.CapelliTop.qdet_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:23:01.221168+00:00
-- url     : https://prove2.me/submissions/5ce0cf0f-d69d-4b56-af91-516a6ff5c431

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
import Theorems.Thm_GlobalTheory_CapelliTop_prod_add_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.CapelliTop
theorem _root_.solution [Algebra ℂ A] (E : Fin n → Fin n → A) (u : ℂ) :
    Formalism.REAL.qdet E u = ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (u - (k : ℂ))) • subdet E S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  have h : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ S : Finset (Fin n), (∏ k ∈ Sᶜ, (if σ k = k then u - (k : ℂ) else 0)) •
        oprod S (fun k => E (σ k) k) := by
    intro σ
    rw [← prod_add_expand]
    congr 2
    funext k
    by_cases hk : σ k = k <;> simp [Formalism.REAL.Tm, hk, Algebra.algebraMap_eq_smul_one]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [subdet, Finset.smul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]
  split_ifs with hσ
  · congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [if_pos (hσ k (Finset.mem_compl.1 hk))]
  · push Not at hσ
    obtain ⟨k, hk, hk'⟩ := hσ
    rw [Finset.prod_eq_zero (Finset.mem_compl.2 hk) (if_neg hk'), zero_smul]
end GlobalTheory.CapelliTop
