-- Prove2me | solution 1 for GlobalTheory.UnitarySemisimple.exists_orth_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:17.343074+00:00
-- url     : https://prove2.me/submissions/540051d2-d1a5-4c08-a1d2-d97ad1c09839

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIrreducibleSubrepFixedOfUnitary
import Theorems.Thm_GlobalTheory_OrthogonalProjection_exists_orth_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitarySemisimple
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.UnitarySemisimple
theorem _root_.solution (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hdef : ∀ v, B v v = 0 → v = 0)
    (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | (apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj ..)
end GlobalTheory.UnitarySemisimple
