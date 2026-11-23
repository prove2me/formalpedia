-- Prove2me | solution 1 for GlobalTheory.exists_zsmul_mem_span_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:42.149869+00:00
-- url     : https://prove2.me/submissions/0d7890e1-191a-47ce-959e-82c81fe930da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

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
theorem _root_.solution {A : Type*} [AddCommGroup A]
    [Module.Finite ℤ A] {n : ℕ} (hn : finrank ℤ A = n) {v : Fin n → A}
    (hv : LinearIndependent ℤ v) (x : A) :
    ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ Submodule.span ℤ (Set.range v) := by
  have h1 := Submodule.finrank_quotient_add_finrank (Submodule.span ℤ (Set.range v))
  rw [finrank_span_eq_card hv, Fintype.card_fin, hn] at h1
  have h2 : finrank ℤ (A ⧸ Submodule.span ℤ (Set.range v)) = 0 := by omega
  obtain ⟨k, hk, hx⟩ := (Module.finrank_eq_zero_iff.1 h2) (Submodule.Quotient.mk x)
  exact ⟨k, hk, by rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx⟩
end GlobalTheory
