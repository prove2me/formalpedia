-- Prove2me | solution 1 for GlobalTheory.HL.OverBasis.linearIndependent_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:39.26484+00:00
-- url     : https://prove2.me/submissions/95eade2b-bc78-4dcb-b0b1-283fd8e1d6e0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LinearIndependentOfGram
import Theorems.Thm_GlobalTheory_HL_OverBasis_hf_comb
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OverBasis
open Matrix GlobalTheory.HL.SelfDual
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.OverBasis
theorem _root_.solution (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin m → Fin n → E) (h : IsUnit (gramT L Hm y).det) : LinearIndependent E y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 := hf_comb L Hm y c
  rw [hc] at h1
  have h2 : gramT L Hm y *ᵥ c = 0 := by
    rw [← h1]; funext a; simp [hf]
  have h3 : (gramT L Hm y)⁻¹ *ᵥ (gramT L Hm y *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_zero] at h3
  exact fun i => congrFun h3.symm i
end GlobalTheory.HL.OverBasis
