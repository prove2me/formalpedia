-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.pres_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:28.401534+00:00
-- url     : https://prove2.me/submissions/1853121d-79c3-417f-9d90-c388b35df4d5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution {R : Submodule ℂ (V × W)} {S S' : Module.End ℂ V} {T T' : Module.End ℂ W}
    (h : Pres R S T) (h' : Pres R S' T') : Pres R (S * S') (T * T') :=
  fun x y hxy => h _ _ (h' x y hxy)
end GlobalTheory.CompanionTheory.CasselmanOsborne
