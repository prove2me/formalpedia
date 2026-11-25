-- Prove2me | solution 1 for GlobalTheory.IntClsCount.pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:42:56.038695+00:00
-- url     : https://prove2.me/submissions/20787051-6646-4eca-876b-a825c7c761ff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardUniCosetsLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
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
open GlobalTheory GlobalTheory.IntClsCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IntClsCount
theorem _root_.solution (L : LocE F E) {r k : ℕ} (S : Frames L r k)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    (cT L u * S.Zh * u') a b = S.h (∑ i, u' i b • S.f' i) (∑ i, u i a • S.f i) := by
  have h1 : ∀ (y : S.V) (c : Fin (r + 1) → E) (x : Fin (r + 1) → S.V),
      S.h (∑ i, c i • x i) y = ∑ i, c i * S.h (x i) y := by
    intro y c x
    simp only [Frames.h, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    simp only [mul_assoc]
  have h2 : ∀ (y : S.V) (c : Fin (r + 1) → E) (x : Fin (r + 1) → S.V),
      S.h y (∑ i, c i • x i) = ∑ i, L.cj (c i) * S.h y (x i) := by
    intro y c x
    simp only [Frames.h, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [h1]
  simp only [h2, Matrix.mul_apply, cT, Frames.Zh, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end GlobalTheory.IntClsCount
