-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Low.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:02.878359+00:00
-- url     : https://prove2.me/submissions/5fc72e3d-6121-4820-811e-07c4e2233b0a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Low
theorem _root_.solution : Low (0 : FreeAlgebra ℂ (Fin n × Fin n)) := by
  simpa using Low.smul (0 : ℂ) (1 : FreeAlgebra ℂ (Fin n × Fin n)) Low.one
end Low
end GlobalTheory.CompanionTheory.HCdecomp
