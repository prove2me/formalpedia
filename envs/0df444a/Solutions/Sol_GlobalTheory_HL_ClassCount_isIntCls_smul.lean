-- Prove2me | solution 1 for GlobalTheory.HL.ClassCount.isIntCls_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:15.615633+00:00
-- url     : https://prove2.me/submissions/39ca9c56-ef0e-4c86-91bd-c6965d56e84a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
import Theorems.Thm_GlobalTheory_T_hermitianDoubleCosetFrameClass_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ClassCount
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.ClassCount
theorem _root_.solution {h : S.GLV} (hh : h ∈ S.St) {C : Set S.FrP} (hC : S.IsIntCls C) :
    S.IsIntCls (h • C) := by
  obtain ⟨⟨n, hn, n', hn', rfl⟩, hI⟩ := hC
  refine ⟨⟨h * n, mul_mem hh.1 hn, h * n', mul_mem hh.2 hn', ?_⟩, ?_⟩
  · rw [(GlobalTheory.T.hermitianDoubleCosetFrameClass_properties L r k S _ _).2.2 h]
    rfl
  · rintro _ ⟨p, hp, rfl⟩ a b
    have := hh.1.1.1 (p.2 b) (p.1 a)
    have h2 := hI p hp a b
    rw [Frames.h, ← this] at h2
    exact h2
end GlobalTheory.HL.ClassCount
