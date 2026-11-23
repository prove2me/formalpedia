-- Prove2me | solution 1 for GlobalTheory.StepData.mem_KOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:52.207013+00:00
-- url     : https://prove2.me/submissions/10ea7cac-e277-404d-a2d3-c379f9f9013c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_residue_eq_iff_lt
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KOne

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
theorem _root_.solution {g : GL n k} : g ∈ KOne k n ↔ MaxM (g.val - 1) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ i j
    have h1 : IsLocalRing.residue 𝒪[k] (u.val i j) = IsLocalRing.residue 𝒪[k] ((1 : Matrix n n 𝒪[k]) i j) := by
      have h0 : (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 := congrArg Units.val hu
      refine (congrFun (congrFun h0 i) j).trans ?_
      simp only [Matrix.one_apply]; split_ifs <;> simp
    convert (residue_eq_iff_lt _ _).1 h1 using 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  · intro h
    obtain ⟨g', h1, h2⟩ := exists_mem_KOne h
    rwa [← Units.ext h2]
end GlobalTheory.StepData
