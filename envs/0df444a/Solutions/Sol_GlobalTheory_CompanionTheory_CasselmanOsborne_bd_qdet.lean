-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.bd_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:32.176004+00:00
-- url     : https://prove2.me/submissions/ba0d6f65-9c18-432e-af4d-dc1a2b2e4143

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_lift_bd
import Theorems.Thm_Formalism_REAL_qDetCentral


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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (u : ℂ) (x : Ch ε V) :
    bd ε E (lift ε (qdet E u) x) = lift ε (qdet E u) (bd ε E x) :=
  (lift_bd (qdet E u) E E (fun a b v => LinearMap.congr_fun (Formalism.REAL.qDetCentral _ n E hE u a b) v) x).symm
end GlobalTheory.CompanionTheory.CasselmanOsborne
