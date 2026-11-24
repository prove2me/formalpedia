-- Prove2me | solution 1 for GlobalTheory.RegBound.hom_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:19.253838+00:00
-- url     : https://prove2.me/submissions/83238373-4232-4159-9e9b-39484e697c2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_comp_succ_mul
import Theorems.Thm_GlobalTheory_RegBound_comp_zero_mul
import Theorems.Thm_GlobalTheory_RegBound_mem_sup_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) :
    ∀ F ∈ I ⊔ Ideal.span {h}, ∀ e, homogeneousComponent e F ∈ I ⊔ Ideal.span {h} := by
  intro F hF e
  obtain ⟨A, hA, B, rfl⟩ := mem_sup_span.1 hF
  rw [map_add]
  cases e with
  | zero => exact mem_sup_span.2 ⟨_, hI A hA 0, 0, by rw [comp_zero_mul hh, mul_zero]⟩
  | succ e => exact mem_sup_span.2 ⟨_, hI A hA _, _, by rw [comp_succ_mul hh]⟩
end GlobalTheory.RegBound
