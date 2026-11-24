-- Prove2me | solution 1 for GlobalTheory.exists_section_of_fractionalIdeal_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:00.741967+00:00
-- url     : https://prove2.me/submissions/3e2da931-c3ad-448e-a84e-fce41b8ed2a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeVectorPairingOneIdealMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) {v : V} (K : FractionalIdeal (𝓞 F)⁰ F)
    (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  have hmul : K * K⁻¹ = 1 := mul_inv_cancel₀ hK
  have key : ∀ s ∈ K * K⁻¹, ∃ w : V, B w v = s ∧ ∀ t ∈ K, t • w ∈ L := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro k hk k' hk'
      obtain ⟨z, hz, rfl⟩ := (hKL k).1 hk
      refine ⟨k' • z, by simp [mul_comm], fun t ht => ?_⟩
      have h1 : t * k' ∈ K * K⁻¹ := FractionalIdeal.mul_mem_mul ht hk'
      rw [hmul, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨r, hr⟩ := h1
      rw [smul_smul, ← hr]
      exact hLsmul r z hz
    · rintro x y ⟨w, hw, hw'⟩ ⟨u, hu, hu'⟩
      refine ⟨w + u, by simp [hw, hu], fun t ht => ?_⟩
      rw [smul_add]
      exact hLadd _ (hw' t ht) _ (hu' t ht)
  refine key 1 ?_
  rw [hmul]
  exact FractionalIdeal.one_mem_one _
end GlobalTheory
