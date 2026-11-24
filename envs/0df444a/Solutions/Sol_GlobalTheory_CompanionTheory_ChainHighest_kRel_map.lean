-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ChainHighest.kRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:23:02.444817+00:00
-- url     : https://prove2.me/submissions/7a81c89c-a4c5-45c4-9389-c12a10f4d477

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
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
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ChainHighest
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)
namespace GlobalTheory.CompanionTheory.ChainHighest
theorem _root_.solution {n : ℕ} {A B : Type} [Ring A] [Ring B] (ε : Fin n → Bool) (f : A →+* B)
    (F : Fin n → Fin n → A) (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul] at this
  rw [this]
  congr 1 <;> split_ifs <;> simp
end GlobalTheory.CompanionTheory.ChainHighest
