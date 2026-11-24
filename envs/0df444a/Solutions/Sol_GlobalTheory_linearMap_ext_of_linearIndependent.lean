-- Prove2me | solution 1 for GlobalTheory.linearMap_ext_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:19:01.675814+00:00
-- url     : https://prove2.me/submissions/f588b600-d32b-4a08-90c2-41a323e363a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
import Theorems.Thm_GlobalTheory_exists_zsmul_mem_span_of_linearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open MeasureTheory Metric
namespace GlobalTheory
theorem _root_.solution {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module.Finite ℤ A] [Module.IsTorsionFree ℤ B] {n : ℕ} (hn : finrank ℤ A = n) {v : Fin n → A}
    (hv : LinearIndependent ℤ v) {f g : A →ₗ[ℤ] B} (h : ∀ i, f (v i) = g (v i)) : f = g := by
  ext x
  obtain ⟨k, hk, hx⟩ := exists_zsmul_mem_span_of_linearIndependent hn hv x
  have h1 : f (k • x) = g (k • x) :=
    LinearMap.eqOn_span' (by rintro _ ⟨i, rfl⟩; exact h i) hx
  rw [map_smul, map_smul] at h1
  exact smul_right_injective B hk h1
end GlobalTheory
