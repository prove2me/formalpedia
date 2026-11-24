-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.bd_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:46.821528+00:00
-- url     : https://prove2.me/submissions/35cc8088-3118-4457-95d3-0526c47be801

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_zeta
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_graph

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
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (hB : BdFacts) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (u : ℂ) (x : Ch ε V) :
    bd ε E (zeta ε (Fop ε E) u x) = zeta ε (Fop ε E) u (bd ε E x) :=
  (pres_graph (bd ε E) _ _).1 (pres_zeta ε _ _ (fun c d hcd => (pres_graph _ _ _).2 fun x =>
    (LinearMap.congr_fun ((hB n ε V E hE).2 c d hcd).1.eq x).symm) u) x
end GlobalTheory.CompanionTheory.CasselmanOsborne
