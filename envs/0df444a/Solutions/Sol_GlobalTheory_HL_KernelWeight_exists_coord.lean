-- Prove2me | solution 1 for GlobalTheory.HL.KernelWeight.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:02.480926+00:00
-- url     : https://prove2.me/submissions/eecee15b-edc2-40b4-9744-201636b5446d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetInFamilyMovedOfNotLeakStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMoveTermWeightCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermDoubleCosetMovesFiniteTargetsSplitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetKernelBoundByWeight
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.KernelWeight
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.KernelWeight
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1)) :
    ∃ al : Fin (r + 1) → E, x = ∑ i, al i • n (g i) ∧ al j.castSucc = S.h x (gs j) := by
  have hu : n⁻¹ ∈ unipOn (S.spanTo g (j + 1)) (S.spanTo g j) := by
    apply Subgroup.inv_mem
    exact Subgroup.mem_iInf.1 hn.1.2 j
  have h1 : n⁻¹ x ∈ S.spanTo g (j + 1) := (hu.1 x).2 hx
  have h2 : n⁻¹ x - x ∈ S.spanTo g j := hu.2 x hx
  have h3 : n⁻¹ x ∈ Submodule.span E (Set.range g) :=
    Submodule.span_mono (Set.image_subset_range _ _) h1
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 h3
  have h4 : S.spanTo g j ≤ LinearMap.ker (hfLin L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < j := hi
    have : i ≠ j.castSucc := by
      rintro rfl
      simp at hi'
    show hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg this]
  have h5 : hfLin L S.Hm (gs j) (n⁻¹ x) = hfLin L S.Hm (gs j) x := by
    have := h4 h2
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  refine ⟨c, ?_, ?_⟩
  · have : x = n (n⁻¹ x) := (n.apply_symm_apply x).symm
    rw [this, ← hc, map_sum]
    simp
  · show _ = hfLin L S.Hm (gs j) x
    rw [← h5, ← hc, map_sum]
    have : ∀ i, hfLin L S.Hm (gs j) (c i • g i) = if i = j.castSucc then c i else 0 := by
      intro i
      rw [map_smul]
      show c i * hf L S.Hm (g i) (gs j) = _
      rw [hd]; split_ifs <;> simp
    simp [this]
end GlobalTheory.HL.KernelWeight
