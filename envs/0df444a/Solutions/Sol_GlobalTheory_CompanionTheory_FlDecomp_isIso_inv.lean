-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.isIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:41.378567+00:00
-- url     : https://prove2.me/submissions/e94da9c1-3a1d-47d6-b242-c24f6cec45d1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus

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
theorem _root_.solution {h : V → V → L} {a : V ≃ₗ[L] V} (ha : IsIso h a) : IsIso h a⁻¹ := fun x y => by
  have := ha (a⁻¹ x) (a⁻¹ y)
  have h1 : ∀ z, a (a⁻¹ z) = z := fun z => by
    change (a * a⁻¹) z = z
    simp
  rw [h1, h1] at this
  exact this.symm
end GlobalTheory.CompanionTheory.FlDecomp
