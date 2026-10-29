-- Prove2me | solution 1 for MIPStarRE.QPBT.dLinePointDist_zero_direction_mass_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:59:22.391787+00:00
-- url     : https://prove2.me/submissions/44d0e846-41ca-45a1-a208-1a89470cb0b8

-- Generated proof for MIPStarRE.QPBT.dLinePointDist_zero_direction_mass_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_dLineDescOf_ldDLineCL

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Discarded zero-direction mass

## References

Paper `lem:qld-xz-lines`, lines 950--963.
-/



open MIPStarRE.QPBT
open LIDT.MIPStarRE.LDT

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) ≤
      1 / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) := by
  classical
  let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
  let coord : _root_.MIPStarRE.QPBT.LdIndex L := .inr last
  have hmap : (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map (fun raw => raw coord) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L) := by
    change (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L)).map
      (fun raw => (Equiv.funSplitAt coord (_root_.MIPStarRE.QPBT.ScalarQ L) raw).1) = _
    rw [← _root_.MIPStarRE.QPBT.Distribution.map_map, _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv,
      _root_.MIPStarRE.QPBT.uniformDistribution_map_fst]
  have hzero : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
      1 / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) := by
    rw [← _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.LdSpace L))
      (fun raw => raw coord) (fun value => if value = 0 then (1 : ℝ) else 0), hmap]
    simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply, mul_ite]
  unfold _root_.MIPStarRE.QPBT.dLinePointDist _root_.MIPStarRE.QPBT.clDistribution
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]
  refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ ?_) hzero.le
  intro raw
  dsimp only
  rw [_root_.MIPStarRE.QPBT.dLineDescOf_ldDLineCL]
  split_ifs with hdir hcoord hcoord
  · exact le_rfl
  · exfalso
    apply hcoord
    have hlast := congrFun hdir last
    change _root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed raw))
      (_root_.MIPStarRE.QPBT.LdSpace.direction raw) last = 0 at hlast
    have hindex : ¬ last.val < (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed raw)).val := by
      have := (_root_.MIPStarRE.QPBT.chiIndex L (_root_.MIPStarRE.QPBT.LdSpace.seed raw)).isLt
      dsimp [last]
      omega
    simpa [_root_.MIPStarRE.QPBT.prefixProjection, hindex, _root_.MIPStarRE.QPBT.LdSpace.direction, coord] using hlast
  · norm_num
  · exact le_rfl
