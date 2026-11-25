-- Prove2me | solution 1 for GlobalTheory.HL.PatternApprox.det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:16.291538+00:00
-- url     : https://prove2.me/submissions/14a9e121-be32-472d-8a0a-b8ac4f394e23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PatternUnitriangularStrongApproximation
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PatternApprox
variable {R : Type} [CommRing R]
namespace GlobalTheory.HL.PatternApprox
theorem _root_.solution {m : ℕ} (I : Fin m → Fin m → Prop) (hI : ∀ i j, I i j → i < j)
    (s : Matrix (Fin m) (Fin m) R) (hs : ∀ i j, ¬ I i j → s i j = if i = j then 1 else 0) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [hs i i (fun h => lt_irrefl i (hI i i h))]
    simp
  · intro i j hji
    rw [hs i j (fun h => lt_asymm (hI i j h) hji)]
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    simp [hne]
end GlobalTheory.HL.PatternApprox
