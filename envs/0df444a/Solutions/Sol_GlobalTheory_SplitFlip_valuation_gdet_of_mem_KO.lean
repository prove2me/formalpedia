-- Prove2me | solution 1 for GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:27.323327+00:00
-- url     : https://prove2.me/submissions/c2f63dee-c3ba-4b3e-9cab-82b49291ec0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {g : GL D k} (hg : g ∈ KO k D) : valuation k (gdet g : k) = 1 := by
  obtain ⟨u, rfl⟩ := hg
  have h : ((gdet (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
end GlobalTheory.SplitFlip
