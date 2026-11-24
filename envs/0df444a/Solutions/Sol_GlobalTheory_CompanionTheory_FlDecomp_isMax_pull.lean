-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.isMax_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:30.478987+00:00
-- url     : https://prove2.me/submissions/43f7586d-65cb-4bba-8a48-a858b91141fb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_mem_pull
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isIso_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_isLat_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution {h : V → V → L} {Λ : AddSubgroup V} (hM : IsMax h Λ)
    {g : V ≃ₗ[L] V} (hg : IsIso h g) : IsMax h (pull g⁻¹ Λ) := by
  have hgi := isIso_inv hg
  have h1 : ∀ z, g (g⁻¹ z) = z := fun z => by
    change (g * g⁻¹) z = z
    simp
  have h2 : ∀ z, g⁻¹ (g z) = z := fun z => by
    change (g⁻¹ * g) z = z
    simp
  refine ⟨isLat_pull _ hM.1, fun x hx => ?_, fun Λ' hl hi hle => ?_⟩
  · rw [← hgi x x]
    exact hM.2.1 _ hx
  · have key : pull g Λ' = Λ := hM.2.2 _ (isLat_pull _ hl) (fun x hx => by
      have : ‖h (g x) (g x)‖ ≤ 1 := hi _ hx
      rwa [hg] at this) (fun x hx => by
      apply hle
      show g⁻¹ (g x) ∈ Λ
      rw [h2]
      exact hx)
    ext x
    rw [mem_pull, ← key, mem_pull, h1]
end GlobalTheory.CompanionTheory.FlDecomp
