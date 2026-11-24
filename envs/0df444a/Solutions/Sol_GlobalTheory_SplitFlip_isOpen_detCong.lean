-- Prove2me | solution 1 for GlobalTheory.SplitFlip.isOpen_detCong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:50.981803+00:00
-- url     : https://prove2.me/submissions/f87a3177-6736-4aec-bd49-ec3e11fdda5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int


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
theorem _root_.solution (c : kˣ) (n : Type*) [Fintype n] [DecidableEq n] : IsOpen (detCong c n : Set (GL n k)) := by
  have hc : Continuous fun g : GL n k => (g.val.det - 1) / (c : k) :=
    (Units.continuous_val.matrix_det.sub continuous_const).div_const _
  convert isOpen_KO.inter (isOpen_int.preimage hc) using 1
  ext g
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  have h : (g.val.det - 1) / (c : k) ∈ 𝒪[k] ↔ valuation k (g.val.det - 1) ≤ valuation k (c : k) := by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]
  exact ⟨fun hg => ⟨hg.1, h.2 hg.2.2⟩, fun hg => ⟨hg.1, valuation_gdet_of_mem_KO hg.1, h.1 hg.2⟩⟩
end GlobalTheory.SplitFlip
