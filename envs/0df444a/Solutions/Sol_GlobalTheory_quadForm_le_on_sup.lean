-- Prove2me | solution 1 for GlobalTheory.quadForm_le_on_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:26.069064+00:00
-- url     : https://prove2.me/submissions/d02c4d6f-bea3-4b09-9cad-6d595ec9bf6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CompactCasimirLeSubspaceMonotone
import Theorems.Thm_P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (B : M →ₗ[ℂ] M)
    (hB : B.IsSymmetric) (C : ℝ) (S₁ S₂ : Submodule ℂ M) [FiniteDimensional ℂ S₁] [FiniteDimensional ℂ S₂]
    (h₁ : ∀ x ∈ S₁, B x ∈ S₁) (h₂ : ∀ x ∈ S₂, B x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) (b₂ : ∀ x ∈ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ S₁ ⊔ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2 := by
  let e := WithLp.linearEquiv 2 ℂ (S₁ × S₂)
  let Φ : WithLp 2 (S₁ × S₂) →ₗ[ℂ] M := (S₁.subtype.coprod S₂.subtype) ∘ₗ e.toLinearMap
  let A : WithLp 2 (S₁ × S₂) →ₗ[ℂ] WithLp 2 (S₁ × S₂) :=
    e.symm.toLinearMap ∘ₗ ((B.restrict h₁).prodMap (B.restrict h₂)) ∘ₗ e.toLinearMap
  have hA1 : ∀ z, ((A z).fst : M) = B z.fst := fun z => rfl
  have hA2 : ∀ z, ((A z).snd : M) = B z.snd := fun z => rfl
  have hΦ : ∀ z, Φ z = (z.fst : M) + (z.snd : M) := fun z => rfl
  have key := GlobalTheory.T.re_inner_le_on_image_of_intertwining' (WithLp 2 (S₁ × S₂)) M Φ A B C
    (by
      intro z w
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change ⟪((A z).fst : M), (w.fst : M)⟫_ℂ + ⟪((A z).snd : M), (w.snd : M)⟫_ℂ =
        ⟪(z.fst : M), ((A w).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A w).snd : M)⟫_ℂ
      rw [hA1, hA2, hA1, hA2, hB, hB])
    hB
    (by
      intro z
      rw [hΦ, hΦ, hA1, hA2, map_add])
    (by
      intro z
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change (⟪(z.fst : M), ((A z).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A z).snd : M)⟫_ℂ).re ≤
        C * (‖(z.fst : M)‖ ^ 2 + ‖(z.snd : M)‖ ^ 2)
      rw [hA1, hA2, Complex.add_re, mul_add]
      exact add_le_add (b₁ _ z.fst.2) (b₂ _ z.snd.2))
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  exact key (WithLp.toLp 2 (⟨y, hy⟩, ⟨z, hz⟩))
end GlobalTheory
