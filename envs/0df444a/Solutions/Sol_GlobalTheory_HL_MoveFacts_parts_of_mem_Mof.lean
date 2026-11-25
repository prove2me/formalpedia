-- Prove2me | solution 1 for GlobalTheory.HL.MoveFacts.parts_of_mem_Mof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:12.468309+00:00
-- url     : https://prove2.me/submissions/a132f86c-1cfd-4441-93ab-6dcc83d07860

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMoveProperties
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveFacts
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveFacts
theorem _root_.solution (hth : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O)
    (g g' : Fin (r + 1) → S.V) (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ ξ ∈ Submodule.span L.O (Set.range g), ∃ ξ' ∈ Submodule.span L.O (Set.range g'),
      algebraMap F E S.th • m = ξ + ξ' := by
  have hinv : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨algebraMap F E S.th • g b, ?_, 0, zero_mem _, by rw [add_zero]⟩
      exact Submodule.smul_mem _ (⟨algebraMap F E S.th, hO⟩ : L.O) (Submodule.subset_span ⟨b, rfl⟩)
    · refine ⟨-g b, neg_mem (Submodule.subset_span ⟨b, rfl⟩), g' b, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
      show algebraMap F E S.th • algebraMap F E S.th⁻¹ • (g' b - g b) = -g b + g' b
      rw [smul_smul, hinv, one_smul, sub_eq_neg_add]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    obtain ⟨b, hb, b', hb', e'⟩ := hv
    exact ⟨a + b, add_mem ha hb, a' + b', add_mem ha' hb', by rw [smul_add, e, e']; abel⟩
  | smul c u _ hu =>
    obtain ⟨a, ha, a', ha', e⟩ := hu
    refine ⟨c • a, Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', ?_⟩
    show algebraMap F E S.th • ((c : E) • u) = (c : E) • a + (c : E) • a'
    rw [smul_smul, mul_comm (algebraMap F E S.th) (c : E), ← smul_smul, e, smul_add]
end GlobalTheory.HL.MoveFacts
