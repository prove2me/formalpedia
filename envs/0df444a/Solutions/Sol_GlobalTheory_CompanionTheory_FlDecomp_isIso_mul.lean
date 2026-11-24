-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.isIso_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:30.11214+00:00
-- url     : https://prove2.me/submissions/38057c04-b64f-4dc7-9a7a-c52adf2a2e16

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
theorem _root_.solution {h : V → V → L} {a b : V ≃ₗ[L] V} (ha : IsIso h a) (hb : IsIso h b) : IsIso h (a * b) :=
  fun x y => by simpa [LinearEquiv.mul_apply] using (ha (b x) (b y)).trans (hb x y)
end GlobalTheory.CompanionTheory.FlDecomp
