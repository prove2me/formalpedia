-- Prove2me | solution 1 for GlobalTheory.StepData.exists_mem_KOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:19.652245+00:00
-- url     : https://prove2.me/submissions/8348ac25-4446-49b2-a80c-4f9b1c1ca08a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_MaxM_intM
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
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
theorem _root_.solution {M : Matrix n n k} (h : MaxM (M - 1)) : ∃ g ∈ KOne k n, g.val = M := by
  have hM : IntM M := by simpa using h.intM.add (intM_one (k := k) (n := n))
  let A : Matrix n n 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have hA : (IsLocalRing.residue 𝒪[k]).mapMatrix A = 1 := by
    ext i j
    have : (1 : Matrix n n (IsLocalRing.ResidueField 𝒪[k])) i j =
        IsLocalRing.residue 𝒪[k] ((1 : Matrix n n 𝒪[k]) i j) := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [this]
    refine (residue_eq_iff_lt _ _).2 ?_
    convert h i j using 2
    simp only [Matrix.sub_apply, Matrix.one_apply, A]; split_ifs <;> simp
  have hd : IsUnit A.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hA]; simp
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hd
  refine ⟨_, ⟨u, ?_, rfl⟩, ?_⟩
  · exact Units.ext (show (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = 1 by rw [hu, hA])
  · change (algebraMap 𝒪[k] k).mapMatrix u.val = M
    rw [hu]; rfl
end GlobalTheory.StepData
