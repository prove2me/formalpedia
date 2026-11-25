-- Prove2me | solution 1 for GlobalTheory.HL.LocDict.exists_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:07.207819+00:00
-- url     : https://prove2.me/submissions/d7144ab3-2f9b-430e-b3bb-92ffc73cf0b7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Theorems.Thm_GlobalTheory_HL_LocDict_baer_fractionRing

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocDict
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.HL.LocDict
theorem _root_.solution (L : Submodule R V) (φ : L →ₗ[R] K) :
    ∃ Φ : V →ₗ[K] K, ∀ y : L, Φ (y : V) = φ y := by
  obtain ⟨h, hh⟩ := (baer_fractionRing (R := R) (K := K)).extension_property L.subtype
    L.injective_subtype φ
  exact ⟨LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors R) K h, fun y => congr($hh y)⟩
end GlobalTheory.HL.LocDict
