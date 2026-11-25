-- Prove2me | solution 1 for GlobalTheory.FlagEich.X_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:32.898786+00:00
-- url     : https://prove2.me/submissions/f7f57f3d-bdca-4413-9379-51cb0ffcde3c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_pairL
import Theorems.Thm_GlobalTheory_FlagEich_pairR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) :
    S.spanTo g r ≤ perp L S.Hm (S.spanTo g r) := by
  intro x hx
  show ∀ y ∈ S.spanTo g r, hf L S.Hm x y = 0
  intro y hy
  exact pairL S le_rfl y (fun c _ => pairR S le_rfl (g c.castSucc) (fun d _ => H0 c d) y hy) x hx
end GlobalTheory.FlagEich
