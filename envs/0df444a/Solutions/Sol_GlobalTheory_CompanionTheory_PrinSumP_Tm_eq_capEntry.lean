-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrinSumP.Tm_eq_capEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:08.078587+00:00
-- url     : https://prove2.me/submissions/3726b4b1-df2d-4192-baae-e47d87146fb1

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrinSumP
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.PrinSumP
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    Tm E u a b = capEntry E u a b := add_comm _ _
end GlobalTheory.CompanionTheory.PrinSumP
