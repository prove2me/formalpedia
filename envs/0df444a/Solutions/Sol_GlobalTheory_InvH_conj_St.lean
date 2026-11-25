-- Prove2me | solution 1 for GlobalTheory.InvH.conj_St
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:25:40.123802+00:00
-- url     : https://prove2.me/submissions/92690928-3cd5-4ac4-b90c-0229c3eaf575

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumOrbitNormaliser
import Theorems.Thm_GlobalTheory_InvH_conj_Nof

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
theorem _root_.solution {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : h * s * h⁻¹ ∈ S.St := by
  have hfix : ∀ v ∈ S.ME, h v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 v hv))
  exact ⟨conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_left hv)) hs.1,
    conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_right hv)) hs.2⟩
end GlobalTheory.InvH
