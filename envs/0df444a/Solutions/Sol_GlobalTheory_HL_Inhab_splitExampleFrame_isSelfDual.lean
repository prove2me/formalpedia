-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.splitExampleFrame_isSelfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:26.517667+00:00
-- url     : https://prove2.me/submissions/42964d36-7277-4ce0-9f4a-01bc77338fb8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_isSD_stdLat
import Theorems.Thm_GlobalTheory_HL_Inhab_big_int
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
end General
section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)
end Blocks
private theorem isIntM_H6 (L : LocE F E) : IsIntM L (H6 : Matrix (Fin 6) (Fin 6) E) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [H6]
end GlobalTheory.HL.Inhab
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    IsSD L (toyG L hE ϖ hϖ m).Hm (stdLat L _) := by
  exact isSD_stdLat L (big (e6 m) H6) (big (e6 m) H6) (big_int _ L _ (isIntM_H6 L))
    (big_int _ L _ (isIntM_H6 L)) (big_mul _ _ _ hermitian_six_mul_self)
end GlobalTheory.HL.Inhab
