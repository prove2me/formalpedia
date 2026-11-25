-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckDecTens.hom_cas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:58.813873+00:00
-- url     : https://prove2.me/submissions/ac4240cd-e767-4f1f-88f4-b107d19dff41

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfTensorFromHomLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckDecTens
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckDecTens
theorem _root_.solution (hL : HomLie) {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hX : X.1.OK) (hY : Y.1.OK) (hf : IsHom X Y f) :
    cas Y ∘ₗ f = f ∘ₗ cas X := by
  refine LinearMap.ext fun x => ?_
  have h := fun Z y => LinearMap.congr_fun (hL k r X Y f hX hY hf Z) y
  simp only [LinearMap.comp_apply] at h
  simp only [cas, LinearMap.comp_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h]
end GlobalTheory.CompanionTheory.ZuckDecTens
