-- Prove2me | solution 1 for GlobalTheory.Cyc.trace_almost_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:30:08.284071+00:00
-- url     : https://prove2.me/submissions/922b924f-0389-43aa-a452-c6d00ef64e2b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjective
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_trace_almost_onto_of_levels
import Theorems.Thm_GlobalTheory_Cyc_exists_trace_norm_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
namespace GlobalTheory.Cyc
theorem _root_.solution (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)) (hKL : Kinf K ≤ L)
    (_hL : ∀ h ∈ Hinf K, ∀ x ∈ L, h x ∈ L) (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup)
    (a : Om l) (ha : a ∈ Kinf K) (ha1 : ‖a‖ < 1) :
    ∃ b : Om l, b ∈ L ∧ ‖b‖ ≤ 1 ∧ ∑ s ∈ S, s b = a :=
  AlmostTrace.trace_almost_onto_of_levels (GlobalTheory.Cyc.exists_trace_norm_ge l) K L S hKL hS hrep a ha ha1
end GlobalTheory.Cyc
