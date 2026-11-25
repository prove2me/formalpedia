-- Prove2me | solution 1 for GlobalTheory.HL.SAN.IntParam.prod_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:21.129408+00:00
-- url     : https://prove2.me/submissions/ba6067f5-5d58-4a36-b95c-3fad794a67fe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductParamsIntegral
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SAN GlobalTheory.HL.SAN.IntParam
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SAN.IntParam
theorem _root_.solution {N : ℕ} (y : Fin N → E) :
    ∀ l : List ((Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ g ∈ l, g y = y) → l.prod y = y := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons g l ih =>
    intro h
    rw [List.prod_cons, LinearEquiv.mul_apply, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]
end GlobalTheory.HL.SAN.IntParam
