-- Prove2me | solution 1 for GlobalTheory.HL.LatCard.hf_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:07.722866+00:00
-- url     : https://prove2.me/submissions/b58d576f-02f8-4ab6-8131-2f2645012406

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.LatCard
theorem _root_.solution (L : LocE F E) {n k : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (c : Fin k → E) (b : Fin k → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • b i) y = ∑ i, c i * hf L Hm (b i) y := by
  have key : ∀ x : Fin n → E, hf L Hm x y = ∑ i, x i * ∑ j, Hm i j * L.cj (y j) := by
    intro x
    simp only [hf, Finset.mul_sum, mul_assoc]
  obtain ⟨v, hv⟩ : ∃ v : Fin n → E, ∀ x, hf L Hm x y = ∑ i, x i * v i := ⟨_, key⟩
  simp only [hv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm
end GlobalTheory.HL.LatCard
