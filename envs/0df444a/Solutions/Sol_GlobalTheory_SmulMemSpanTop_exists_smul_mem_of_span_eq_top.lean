-- Prove2me | solution 1 for GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:47.976805+00:00
-- url     : https://prove2.me/submissions/df20627e-ceb1-4a18-877f-b5e7b2413f5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfSpanEqTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemSpanTop
open NumberField
namespace GlobalTheory.SmulMemSpanTop
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ hax
    · rw [mul_smul, smul_comm]
      rw [smul_comm]; exact Λ.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) c
    refine ⟨a * s, mul_ne_zero ha (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have h1 : (s : 𝓞 E) • c • x = r • x := by
      rw [← algebraMap_smul E (s : 𝓞 E), ← algebraMap_smul E r, smul_smul, mul_comm]
      exact congrArg (· • x) hrs
    rw [mul_smul, h1, smul_comm]
    exact Λ.smul_mem _ hax
end GlobalTheory.SmulMemSpanTop
