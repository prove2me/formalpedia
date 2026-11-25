-- Prove2me | solution 1 for GlobalTheory.HL.Unimod.qrefl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:33.613619+00:00
-- url     : https://prove2.me/submissions/2064fede-5a8c-41e2-9ef9-636848710857

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HaarInvVolumeConjModularCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryGroupOrthogonalComplementUnimodular
import Theorems.Thm_GlobalTheory_HL_Unimod_hf_swap
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Unimod
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Unimod
theorem _root_.solution (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) {a : Fin n → E} (ha : a ∈ perp L Hm Y)
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) : g ∈ fixG L Hm Y := by
  obtain ⟨_, hi, c, hc⟩ := hg
  have hfix : ∀ v ∈ Y, g v = v := fun v hv => by
    have h0 : hf L Hm a v = 0 := ha v hv
    rw [hc, hf_swap L hH v a, h0]; simp
  refine ⟨hi, fun v => ⟨fun hv => ?_, fun hv => by rw [hfix v hv]; exact hv⟩, fun v hv => ?_⟩
  · have : g v = v := g.injective (hfix _ hv)
    rwa [this] at hv
  · rw [hfix v hv]; simp
end GlobalTheory.HL.Unimod
