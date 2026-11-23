-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.mem_NV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:40.657323+00:00
-- url     : https://prove2.me/submissions/a2223fad-3104-442f-aa0b-c6c0063594c4

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n} (h : a < b) (w : V) :
    E a b w ∈ NV E :=
  Submodule.mem_iSup_of_mem (⟨(a, b), h⟩ : Pos n) ⟨w, rfl⟩
end GlobalTheory.CompanionTheory.HCdecomp
