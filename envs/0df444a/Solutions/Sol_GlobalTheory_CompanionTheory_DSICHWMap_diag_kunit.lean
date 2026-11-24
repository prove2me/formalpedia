-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICHWMap.diag_kunit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:54.024967+00:00
-- url     : https://prove2.me/submissions/9f4d263b-3998-46f8-b776-a00c78bf862b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_diagOp_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_diagOp_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICHWMap
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
variable {T V : Type} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.CompanionTheory.DSICHWMap
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {ET : Fin n → Fin n → Module.End ℂ T}
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KUnit ε ET) (h2 : KUnit ε E) :
    KUnit ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b hab x y
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply, diagOp_fst, diagOp_snd, diagOp_fst, diagOp_snd,
    h1 a b hab, h2 a b hab]
end GlobalTheory.CompanionTheory.DSICHWMap
