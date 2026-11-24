-- Prove2me | solution 1 for GlobalTheory.StepData.det_of_mem_KOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:47.775079+00:00
-- url     : https://prove2.me/submissions/a6fcfe93-5eb2-4e60-8b3a-979fca414997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_residue_eq_iff_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.StepData
theorem _root_.solution {g : GL n k} (h : g ∈ KOne k n) :
    valuation k (((Matrix.GeneralLinearGroup.det g : kˣ) : k) - 1) < 1 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : IsLocalRing.residue 𝒪[k] u.val.det = IsLocalRing.residue 𝒪[k] 1 := by
    rw [RingHom.map_det, map_one]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 := congrArg Units.val hu
    rw [this, det_one]
  convert (residue_eq_iff_lt _ _).1 h1 using 3
  · exact ((algebraMap 𝒪[k] k).map_det u.val).symm
  · rfl
end GlobalTheory.StepData
