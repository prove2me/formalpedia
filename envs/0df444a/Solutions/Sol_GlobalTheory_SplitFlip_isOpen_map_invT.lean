-- Prove2me | solution 1 for GlobalTheory.SplitFlip.isOpen_map_invT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:15.738053+00:00
-- url     : https://prove2.me/submissions/e08dbec6-0f0c-475c-933c-633e2169cff1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invT_mem_KO

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    IsOpen (J.map invT : Set (GL n k)) ∧ J.map invT ≤ KO k n := by
  refine ⟨?_, by rintro _ ⟨g, hg, rfl⟩; exact invT_mem_KO (hK hg)⟩
  have hc : Continuous (invT : GL n k → GL n k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  convert ho.preimage hc using 1
  ext g
  exact ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hg => ⟨invT g, hg, invT_invT g⟩⟩
end GlobalTheory.SplitFlip
