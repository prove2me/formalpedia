-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.mem_filt_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:21.68741+00:00
-- url     : https://prove2.me/submissions/ad68a693-82e9-4136-9294-a378e80f6db4

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {ι : Type*}
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (d : ι → Module.End ℂ Z) (m : ℕ) (z : Z) :
    z ∈ filt d (m + 1) ↔ ∀ i, d i z ∈ filt d m := by
  show z ∈ (⨅ i, (filt d m).comap (d i)) ↔ _
  simp [Submodule.mem_iInf]
end GlobalTheory.CompanionTheory.DSICKoszul
