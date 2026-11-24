-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isHaarMeasure_volGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:21.760069+00:00
-- url     : https://prove2.me/submissions/d52a256f-a96f-423d-a926-b524a865e285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_isMulLeftInvariant_volGL
import Theorems.Thm_GlobalTheory_SplitWeil_volGL_KO
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : (volGL ν n).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI := isMulLeftInvariant_volGL (n := n) ν
  have ho := SplitFlip.isOpen_KO (k := k) (n := n)
  have hc := SplitFlip.isCompact_KO (k := k) (n := n)
  have hoe : Topology.IsOpenEmbedding (fun g : GL n k => g.val) := by
    refine ⟨SplitFlip.isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ _ hc
    (by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩) ?_ ?_
  · rw [volGL_KO]
    exact ((hoe.isOpenMap _ ho).measure_pos _ ⟨_, 1, one_mem _, rfl⟩).ne'
  · rw [volGL_KO]
    exact (hc.image hoe.continuous).measure_lt_top.ne
end GlobalTheory.SplitWeil
