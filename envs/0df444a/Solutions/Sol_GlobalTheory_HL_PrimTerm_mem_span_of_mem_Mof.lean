-- Prove2me | solution 1 for GlobalTheory.HL.PrimTerm.mem_span_of_mem_Mof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:40:30.919543+00:00
-- url     : https://prove2.me/submissions/af72235f-b511-4fc0-9bc4-4be871e1bdb0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanOfMemMof
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.PrimTerm
theorem _root_.solution (P P' : Submodule E S.V) (hd : Disjoint P P')
    (g g' : Fin (r + 1) → S.V) (hg : ∀ b, g b ∈ P) (hg' : ∀ b, g' b ∈ P')
    (hi : LinearIndependent E g') (x : S.V) (hx : x ∈ S.Mof g g') (hP : x ∈ P) :
    x ∈ Submodule.span L.O (Set.range g) := by
  unfold Frames.Mof at hx
  rw [Submodule.span_union] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hz
  have hyP : y ∈ P := by
    have : Submodule.span L.O (Set.range g) ≤ P.restrictScalars L.O := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      exact hg b
    exact this hy
  set e : Fin (r + 1) → E := fun b => (c b : E) * algebraMap F E S.th⁻¹ with he
  have hs : ∑ b, c b • algebraMap F E S.th⁻¹ • (g' b - g b) = ∑ b, e b • g' b - ∑ b, e b • g b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_sub, he, mul_smul]
    rfl
  rw [hs] at hP ⊢
  have h1 : ∑ b, e b • g b ∈ P := P.sum_mem fun b _ => P.smul_mem _ (hg b)
  have h2 : ∑ b, e b • g' b ∈ P' := P'.sum_mem fun b _ => P'.smul_mem _ (hg' b)
  have h3 : ∑ b, e b • g' b ∈ P := by
    have := P.add_mem (P.sub_mem hP hyP) h1
    rwa [add_sub_cancel_left, sub_add_cancel] at this
  have h4 : ∑ b, e b • g' b = 0 := (Submodule.disjoint_def.1 hd) _ h3 h2
  have h5 : ∀ b, e b = 0 := Fintype.linearIndependent_iff.1 hi e h4
  simpa [h5] using hy
end GlobalTheory.HL.PrimTerm
