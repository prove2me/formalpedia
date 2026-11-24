-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.blk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:01.77483+00:00
-- url     : https://prove2.me/submissions/985a89fe-aa14-4cbc-84b4-76d5d0a494a6

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 this).2
end GlobalTheory.CompanionTheory.CasselmanOsborne
