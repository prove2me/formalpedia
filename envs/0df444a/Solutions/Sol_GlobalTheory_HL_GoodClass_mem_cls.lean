-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:39:53.957919+00:00
-- url     : https://prove2.me/submissions/92d43062-c63f-47a7-9ef0-4421f2007ed6

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
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hg : S.gg = false)
    (g g' : Fin (r + 1) → S.V) (p : S.FrP) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hA : UpU A) (hA' : UpU A') (iA : IsIntM L A) (iA' : IsIntM L A')
    (h : ∀ j, p.1 j = ∑ i, A i j • g i) (h' : ∀ j, p.2 j = ∑ i, A' i j • g' i) :
    p ∈ S.frameCls g g' :=
  ⟨A, A', iA, iA', fun i j hij => ⟨hA.1 i j hij, hA'.1 i j hij⟩, fun i => ⟨hA.2 i, hA'.2 i⟩,
    fun i j => ⟨_, L.O.sub_mem (iA' i j) (iA i j), by simp [Frames.th, hg]⟩, h, h'⟩
end GlobalTheory.HL.GoodClass
