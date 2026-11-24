-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICHWMap.diag_krel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:26.498647+00:00
-- url     : https://prove2.me/submissions/6368391e-a1ca-4c1f-873c-26f4168396d1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HwMapOfLowSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICHWMap_sum_ext

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
    {E : Fin n → Fin n → Module.End ℂ V} (h1 : KRel ε ET) (h2 : KRel ε E) :
    KRel ε (fun a b => diagOp (ET a b) (E a b)) := by
  intro a b c d hab hcd
  have e1 := LinearMap.congr_fun (h1 a b c d hab hcd)
  have e2 := LinearMap.congr_fun (h2 a b c d hab hcd)
  refine LinearMap.ext fun x => ?_
  apply sum_ext
  · have := e1 (WithLp.ofLp x).1
    split_ifs at this ⊢ <;> exact this
  · have := e2 (WithLp.ofLp x).2
    split_ifs at this ⊢ <;> exact this
end GlobalTheory.CompanionTheory.DSICHWMap
