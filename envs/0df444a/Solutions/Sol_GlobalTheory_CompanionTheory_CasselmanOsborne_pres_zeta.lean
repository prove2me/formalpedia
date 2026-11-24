-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.pres_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:55:28.04198+00:00
-- url     : https://prove2.me/submissions/e75dcf40-27ab-48f4-be52-25ae8f998926

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_qminor
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_blk_eq

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
theorem _root_.solution {n : ℕ} {R : Submodule ℂ (V × W)} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ c d, ε c = ε d → Pres R (E c d) (F c d)) (u : ℂ) :
    Pres R (zeta ε E u) (zeta ε F u) :=
  pres_mul (pres_qminor E F _ _ (fun _ _ => h _ _ ((blk_eq ε _ _).trans (blk_eq ε _ _).symm)) _)
    (pres_qminor E F _ _ (fun _ _ => h _ _ ((blk_eq ε _ _).trans (blk_eq ε _ _).symm)) _)
end GlobalTheory.CompanionTheory.CasselmanOsborne
