-- Prove2me | solution 1 for GlobalTheory.BCT.DimFac.hasComp_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:28:44.45119+00:00
-- url     : https://prove2.me/submissions/02db071a-d3b4-4dc3-9363-088c89a85dde

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompOfSurjective
import Theorems.Thm_GlobalTheory_BCT_DimFac_mem_fix
import Theorems.Thm_GlobalTheory_BCT_DimFac_schur_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GroundTheory.Automorphic.RestrictedTensor Module
open scoped TensorProduct
open GlobalTheory GlobalTheory.BCT GlobalTheory.BCT.DimFac
variable {Γ V W M : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.BCT.DimFac
theorem _root_.solution {H : Type} [Group H] (ρ : Representation ℂ Γ V) (e : Γ →* Γ) (L : Subgroup Γ)
    (q : Γ →* H) (hq : Function.Surjective q) (hqe : ∀ g, q (e g) = q g) (σ : Representation ℂ H W)
    (hσ : σ.IsIrreducible) (U : Subgroup H) (hU : fixed σ U ≠ ⊥) [FiniteDimensional ℂ (fixed σ U)]
    (f : W →ₗ[ℂ] V) (hf0 : f ≠ 0) (hf : ∀ g x, f (σ (q g) x) = ρ (e g) (f x)) (K : Subgroup H)
    (h1 : ∀ g ∈ L, q g ∈ K) (h2 : ∀ k ∈ K, ∃ g ∈ L, q g = k) : HasComp ρ e L (finrank ℂ (fixed σ K)) := by
  obtain ⟨h0, h3⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ
  refine ⟨W, _, _, σ.comp q, (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun N hN => h3 N fun k v hv => ?_⟩,
    fun T hT => schur_of_fixed hσ U hU T fun k => ?_, fun g => congrArg σ (hqe g), ⟨f, hf0, hf⟩, ?_⟩
  · obtain ⟨g, rfl⟩ := hq k
    exact hN g v hv
  · obtain ⟨g, rfl⟩ := hq k
    exact hT g
  · have : fixed (σ.comp q) L = fixed σ K := by
      ext x
      rw [mem_fix, mem_fix]
      refine ⟨fun h k hk => ?_, fun h g hg => h _ (h1 g hg)⟩
      obtain ⟨g, hg, rfl⟩ := h2 k hk
      exact h g hg
    rw [this]
end GlobalTheory.BCT.DimFac
