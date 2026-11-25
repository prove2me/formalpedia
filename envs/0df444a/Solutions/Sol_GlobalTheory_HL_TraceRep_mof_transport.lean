-- Prove2me | solution 1 for GlobalTheory.HL.TraceRep.mof_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:28:47.539087+00:00
-- url     : https://prove2.me/submissions/1204644d-062f-41a5-9add-7e83112ededf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDefectClassMemTraceFirstFrameSpan
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_add
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_sub
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_smul
import Theorems.Thm_GlobalTheory_HL_TraceRep_hf_zero
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TraceRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}
variable {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TraceRep
theorem _root_.solution (Λ : Submodule L.O S.V) (Y : Submodule E S.V) (g g' g₁ g₁' : Fin (r + 1) → S.V)
    (x x' u : S.V) (h1 : ∀ b, g₁ b = g b - S.h (g b) u • x) (h1' : ∀ b, g₁' b = g' b + S.h (g' b) u • x')
    (hO : ∀ b, S.h (g' b) u ∈ L.O) (hΛ : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ) (hY : x + x' ∈ Y)
    (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ y₁ ∈ Λ, y₁ ∈ Y ∧ m - S.h m u • x + y₁ ∈ S.Mof g₁ g₁' := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
      rw [add_zero, ← h1]
      exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · refine ⟨S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')), Λ.smul_mem ⟨_, hO b⟩ hΛ,
        Y.smul_mem _ (Y.smul_mem _ hY), ?_⟩
      have : algebraMap F E S.th⁻¹ • (g' b - g b) - S.h (algebraMap F E S.th⁻¹ • (g' b - g b)) u • x +
          S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')) = algebraMap F E S.th⁻¹ • (g₁' b - g₁ b) := by
        rw [h1, h1']
        simp only [Frames.h, hf_smul, hf_sub]
        module
      simp only []
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  | zero =>
    refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
    simp [Frames.h, hf_zero]
  | add a c _ _ ha hc =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    obtain ⟨z, hz, hz', hc⟩ := hc
    refine ⟨y + z, Λ.add_mem hy hz, Y.add_mem hy' hz', ?_⟩
    have : a + c - S.h (a + c) u • x + (y + z) = (a - S.h a u • x + y) + (c - S.h c u • x + z) := by
      simp only [Frames.h, hf_add]
      module
    rw [this]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    refine ⟨(c : E) • y, Λ.smul_mem c hy, Y.smul_mem _ hy', ?_⟩
    have : c • a - S.h (c • a) u • x + (c : E) • y = (c : E) • (a - S.h a u • x + y) := by
      change (c : E) • a - S.h ((c : E) • a) u • x + (c : E) • y = _
      simp only [Frames.h, hf_smul]
      module
    rw [this]
    exact Submodule.smul_mem _ c ha
end GlobalTheory.HL.TraceRep
