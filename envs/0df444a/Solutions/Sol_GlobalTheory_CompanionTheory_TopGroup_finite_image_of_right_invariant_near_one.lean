-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:34.467356+00:00
-- url     : https://prove2.me/submissions/a0f1c863-537b-420f-9985-56637d7332ba

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteImageCompactRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TopGroup
namespace GlobalTheory.CompanionTheory.TopGroup
theorem _root_.solution :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by
  intro Γ X _ _ _ K hK Gf hS
  have hU : ∀ k ∈ K, {y : Γ | k⁻¹ * y ∈ {s : Γ | ∀ x, Gf (x * s) = Gf x}} ∈ nhds k := by
    intro k _
    have hc : Continuous fun y : Γ => k⁻¹ * y := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds ?_
    show _ ∈ nhds (k⁻¹ * k)
    rw [inv_mul_cancel]
    exact hS
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image Gf).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hcover hy)
  refine ⟨k, hk, ?_⟩
  have h := hyk k
  rw [mul_inv_cancel_left] at h
  exact h.symm
end GlobalTheory.CompanionTheory.TopGroup
