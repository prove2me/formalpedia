-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Red.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:36.874583+00:00
-- url     : https://prove2.me/submissions/c62ce8bc-e062-4151-bead-9bd1c777978c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Red
theorem _root_.solution {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a)
    (he : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ev E a' = ev E a) : Red a' := by
  obtain ⟨u, hu, h⟩ := h
  exact ⟨u, hu, fun V _ _ E hE => he V E hE ▸ h V E hE⟩
end Red
end GlobalTheory.CompanionTheory.HCdecomp
