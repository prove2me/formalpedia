-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.pair_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:56.066392+00:00
-- url     : https://prove2.me/submissions/1107fc41-84ef-4b2a-a846-e3fc17eae667

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    S.h (∑ i, A' i b • S.f' i) (∑ i, A i a • S.f i) = (cT L A * S.Zh * A') a b := by
  have key : ∀ (α : Fin (r + 1) → E) (g : Fin (r + 1) → S.V) (y : S.V),
      hf L S.Hm (∑ i, α i • g i) y = ∑ i, α i * hf L S.Hm (g i) y := fun α g y => by
    change GlobalTheory.FrameBasic.hfL L S.Hm y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  simp only [Frames.h, Matrix.mul_apply, Frames.Zh, Matrix.of_apply, cT]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, key, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L S.herm.1]
end GlobalTheory.HL.GoodClass
