-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.baer_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:09.381803+00:00
-- url     : https://prove2.me/submissions/6b687778-08e1-4c4d-b42d-7d7f5448902c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory.HL.LocDict
theorem _root_.solution : Module.Baer R K := by
  intro I g
  by_cases hI : I = ⊥
  · subst hI
    refine ⟨0, fun x hx => ?_⟩
    have h0 : x = 0 := by simpa using hx
    subst h0
    have : (⟨0, hx⟩ : (⊥ : Ideal R)) = 0 := rfl
    rw [this, map_zero, map_zero]
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have ha' : algebraMap R K a ≠ 0 := by
      simpa using ha0
    refine ⟨LinearMap.toSpanSingleton R K (g ⟨a, ha⟩ / algebraMap R K a), fun x hx => ?_⟩
    have h1 : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp [mul_comm]
    rw [Algebra.smul_def, Algebra.smul_def] at h1
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    field_simp
    rw [← h1]
end GlobalTheory.HL.LocDict
