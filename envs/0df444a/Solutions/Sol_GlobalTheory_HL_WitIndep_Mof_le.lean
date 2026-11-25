-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.Mof_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:40:59.57784+00:00
-- url     : https://prove2.me/submissions/bfd03723-6a16-444f-857f-c15b9a1605f9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_GlobalTheory_HL_WitIndep_th_mul
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution {g g' h h' : Fin (r + 1) → S.V} (H : (h, h') ∈ S.frameCls g g') :
    S.Mof h h' ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', -, -, hc, e, e'⟩ := H
  simp only at e e'
  choose c hcO hc using hc
  have m1 : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (.inl ⟨i, rfl⟩)
  have m2 : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (.inr ⟨i, rfl⟩)
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (⟨_, hA i j⟩ : L.O) (m1 i)
  · have : algebraMap F E S.th⁻¹ • (h' j - h j) =
        ∑ i, (A' i j • algebraMap F E S.th⁻¹ • (g' i - g i) + c i j • g i) := by
      rw [e, e', ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h3 : c i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hc, ← mul_assoc, th_mul, one_mul]
      rw [h3]
      module
    simp only [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun i _ => Submodule.add_mem _
      (Submodule.smul_mem _ (⟨_, hA' i j⟩ : L.O) (m2 i))
      (Submodule.smul_mem _ (⟨_, hcO i j⟩ : L.O) (m1 i))
end GlobalTheory.HL.WitIndep
