-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.int_of_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:36:52.437838+00:00
-- url     : https://prove2.me/submissions/1707149d-a512-4b16-b088-dfe7381c05fe

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
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : LinearIndependent E g) (h : S.GLV)
    (hh : h • Submodule.span L.O (Set.range g) = Submodule.span L.O (Set.range g))
    {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hA : ∀ j, h (g j) = ∑ i, A i j • g i) : IsIntM L A := by
  intro i j
  have h1 : h • g j ∈ Submodule.span L.O (Set.range g) := by
    rw [← hh]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
  have h2 : ∑ i, (c i : E) • g i = ∑ i, A i j • g i := by rw [← hA]; exact hc
  rw [← Fintype.linearIndependent_iffₛ.1 hg _ _ h2 i]
  exact (c i).2
end GlobalTheory.HL.GoodClass
