-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.smul_span_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:50.829022+00:00
-- url     : https://prove2.me/submissions/ac59eed8-8c5a-42cb-85b7-8e02349f55a7

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
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) (h : S.GLV)
    {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (iA : IsIntM L A) (hA : ∀ j, h (g j) = ∑ i, A i j • g i) :
    h • Submodule.span L.O (Set.range g) ≤ Submodule.span L.O (Set.range g) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  change h (g j) ∈ Submodule.span L.O (Set.range g)
  rw [hA]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (⟨A i j, iA i j⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.HL.GoodClass
