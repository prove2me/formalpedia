-- Prove2me | solution 1 for GlobalTheory.LaurentFlagBasis.adapted_integral_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:56:44.590557+00:00
-- url     : https://prove2.me/submissions/f5ff999e-9fdf-4f69-bd78-c444c6f26252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
import Theorems.Thm_GlobalTheory_LaurentFlagBasis_greedy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory.LaurentFlagBasis
namespace GlobalTheory.LaurentFlagBasis
theorem _root_.solution : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by
  intro F _ n R W hW
  let V : ℕ → Submodule (LaurentSeries F) (Fin n → LaurentSeries F) := fun j =>
    ⨅ (k : Fin (R + 1)) (_ : j < Module.finrank (LaurentSeries F) (W k)), W k
  have hV : ∀ j, j < n → j < Module.finrank (LaurentSeries F) (V j) := by
    intro j hj
    by_cases h : ∃ k, j < Module.finrank (LaurentSeries F) (W k)
    · obtain ⟨k, hk⟩ := h
      obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun k => j < Module.finrank (LaurentSeries F) (W k)) id
        ⟨k, by simp [hk]⟩
      have hle : W k0 ≤ V j := le_iInf₂ fun k hk => hW (hmin k (by simp [hk]))
      have := Submodule.finrank_mono hle
      simp at hk0
      omega
    · push_neg at h
      have hle : ⊤ ≤ V j := le_iInf₂ fun k hk => absurd hk (not_lt.mpr (h k))
      have := Submodule.finrank_mono hle
      rw [finrank_top, Module.finrank_fin_fun] at this
      omega
  obtain ⟨c, hcV, hci⟩ := greedy V hV n le_rfl
  let g : Matrix (Fin n) (Fin n) (PowerSeries F) := Matrix.of fun a j => c j a
  have hunit : IsUnit g := by
    rw [Matrix.isUnit_iff_isUnit_det, PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    convert hci using 1
    funext j a
    simp [g, red, Matrix.col]
  refine ⟨hunit.unit, fun k j hj => ?_⟩
  have hmem := hcV j
  have hVk : V j ≤ W k := iInf₂_le k hj
  exact hVk hmem
end GlobalTheory.LaurentFlagBasis
