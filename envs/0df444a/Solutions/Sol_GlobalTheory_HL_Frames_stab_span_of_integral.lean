-- Prove2me | solution 1 for GlobalTheory.HL.Frames.stab_span_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:45.836416+00:00
-- url     : https://prove2.me/submissions/faff13bf-cc42-429e-8e1d-4485bdb0471e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemMaximalCompactOfIntegral
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Frames
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Frames
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : S.GLV)
    (g : Fin (r + 1) → S.V) (s si : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ i j, s i j ∈ L.O) (hsi : ∀ i j, si i j ∈ L.O) (hm : s * si = 1)
    (hg : ∀ j, h (g j) = ∑ i, s i j • g i) :
    h ∈ MulAction.stabilizer S.GLV (Submodule.span L.O (Set.range g)) := by
  rw [MulAction.mem_stabilizer_iff]
  set N := Submodule.span L.O (Set.range g) with hN
  have mem : ∀ (c : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ i j, c i j ∈ L.O) →
      ∀ j, ∑ i, c i j • g i ∈ N := by
    intro c hc j
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i j • g i = (⟨c i j, hc i j⟩ : L.O) • g i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · rw [Submodule.pointwise_smul_def, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    show h (g j) ∈ N
    rw [hg j]
    exact mem s hs j
  · rw [hN, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have key : g j = h (∑ i, si i j • g i) := by
      rw [map_sum]
      simp_rw [map_smul, hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ x, ∑ i, si i j * s x i = (s * si) x j := fun x => by
        rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [key]
    exact Submodule.smul_mem_pointwise_smul _ h _ (mem si hsi j)
end GlobalTheory.HL.Frames
