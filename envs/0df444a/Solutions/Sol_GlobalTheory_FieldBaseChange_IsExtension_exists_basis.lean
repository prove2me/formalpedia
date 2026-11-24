-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.IsExtension.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:53:51.64043+00:00
-- url     : https://prove2.me/submissions/3ad05c12-c086-45f0-b3ce-b9727375f693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W V' W' : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']
namespace GlobalTheory.FieldBaseChange
namespace IsExtension
theorem _root_.solution {a : V →ₛₗ[algebraMap K F] V'} (h : IsExtension a) {ι : Type}
    (v : Module.Basis ι K V) : ∃ v' : Module.Basis ι F V', ∀ i, v' i = a (v i) := by
  have li : LinearIndependent F (fun i => a (v i)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    refine (Module.forall_dual_apply_eq_zero_iff K (g i)).1 fun ℓ => ?_
    obtain ⟨Λ, hΛ⟩ := h.coord ℓ
    have := congrArg Λ hg
    rw [map_sum, map_zero] at this
    simp only [hΛ _ _] at this
    exact linearIndependent_iff'.1 v.linearIndependent s (fun j => ℓ (g j)) this i hi
  have sp : ⊤ ≤ Submodule.span F (Set.range fun i => a (v i)) := by
    rw [← h.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span K (Set.range v) := v.span_eq ▸ Submodule.mem_top
    show a x ∈ Submodule.span F _
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  exact ⟨Module.Basis.mk li sp, fun i => by simp⟩
end IsExtension
end GlobalTheory.FieldBaseChange
