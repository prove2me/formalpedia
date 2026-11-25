-- Prove2me | solution 1 for GlobalTheory.InvH.conj_Nof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:17.906808+00:00
-- url     : https://prove2.me/submissions/910235bf-b17d-48e1-9a20-e046d033333c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumOrbitNormaliser
import Theorems.Thm_GlobalTheory_InvH_conj_unipOn
import Theorems.Thm_GlobalTheory_InvH_mem_iff_of_fix
import Theorems.Thm_GlobalTheory_InvH_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_ComplAct_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.InvH
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.InvH
theorem _root_.solution (g : Fin (r + 1) → S.V) {h s : S.GLV} (hi : h ∈ isomG L S.Hm)
    (hg : ∀ v ∈ S.spanTo g (r + 1), h v = v) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  have hfix : ∀ j ≤ r + 1, ∀ v, h v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := fun j hj =>
    mem_iff_of_fix fun v hv => hg v (spanTo_mono S g hj hv)
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hi s1) ((isomG L S.Hm).inv_mem hi), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun j => ?_
    exact conj_unipOn (hfix _ (by omega)) (hfix _ (by omega)) (Subgroup.mem_iInf.1 s2 j)
  · refine conj_unipOn (fun v => ?_) (hfix _ (by omega)) s3
    refine forall₂_congr fun y hy => ?_
    have := hi v y
    rw [hg y (spanTo_mono S g (by omega) hy)] at this
    rw [this]
end GlobalTheory.InvH
