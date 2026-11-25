-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_app_iff_surjective_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:28.120656+00:00
-- url     : https://prove2.me/submissions/e173b3b8-76de-4a8e-aa5a-dd098398098b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (S : ShortComplex X.Modules) (U : X.Opens) :
    Function.Exact (S.f.app U) (S.g.app U) ↔
      Function.Surjective ((kernel.lift S.g S.f S.zero).app U) := by
  refine ⟨fun h t ↦ ?_, fun h t ↦ ⟨fun ht ↦ ?_, ?_⟩⟩
  · obtain ⟨s, hs⟩ := (h _).mp ((exact_kernel_ι_app S.g U).apply_apply_eq_zero t)
    exact ⟨s, injective_kernel_ι_app S.g U (by rw [app_app, kernel.lift_ι, hs])⟩
  · obtain ⟨t, rfl⟩ := (exact_kernel_ι_app S.g U t).mp ht
    obtain ⟨s, rfl⟩ := h t
    exact ⟨s, by rw [app_app, kernel.lift_ι]⟩
  · rintro ⟨s, rfl⟩
    rw [app_app, S.zero]
    rfl
end GlobalTheory.QCoh
