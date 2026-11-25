-- Prove2me | solution 1 for GlobalTheory.HL.TypeRep.frame_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:27:42.350104+00:00
-- url     : https://prove2.me/submissions/ee635b72-01c3-4386-9430-b4408b71f474

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermLevelZeroAndBoundedRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingSecondTypeTestOnRepresentatives
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_LevelRep_Good_add
import Theorems.Thm_GlobalTheory_HL_LevelRep_Good_smul
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TypeRep
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.TypeRep
theorem _root_.solution (Λ : Submodule L.O S.V) (g g' : Fin (r + 1) → S.V) (h0 : S.th ≠ 0)
    (hg : ∀ b, g b ∈ S.spanTo S.f (r + 1))
    (hg' : ∀ b, g' b ∈ Λ ∧ g' b ∈ S.spanTo S.f' (r + 1)) {m : S.V} (hm : m ∈ S.Mof g g') :
    ∃ a ∈ S.spanTo S.f (r + 1), ∃ a' ∈ S.spanTo S.f' (r + 1), a' ∈ Λ ∧
      algebraMap F E S.th • m = a + a' := by
  have hinv : ∀ v : S.V, algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
    intro v
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨algebraMap F E S.th • g b, Submodule.smul_mem _ _ (hg b), 0, Submodule.zero_mem _,
        Submodule.zero_mem _, by rw [add_zero]⟩
    · refine ⟨-g b, Submodule.neg_mem _ (hg b), g' b, (hg' b).2, (hg' b).1, ?_⟩
      dsimp only
      rw [hinv]
      abel
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    obtain ⟨b, hb, b', hb', hΛ', he'⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb',
      Submodule.add_mem _ hΛ hΛ', by rw [smul_add, he, he']; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    refine ⟨(c : E) • a, Submodule.smul_mem _ _ ha, (c : E) • a', Submodule.smul_mem _ _ ha',
      Λ.smul_mem c hΛ, ?_⟩
    rw [Subring.smul_def, smul_comm, he, smul_add]
end GlobalTheory.HL.TypeRep
