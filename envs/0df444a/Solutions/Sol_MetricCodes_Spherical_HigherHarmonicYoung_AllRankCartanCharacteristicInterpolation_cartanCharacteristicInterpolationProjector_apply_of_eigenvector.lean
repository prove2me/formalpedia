-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation.cartanCharacteristicInterpolationProjector_apply_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/41ee83c4-04fc-4004-94f6-51614649e170

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (nodes : ι → ℝ) (T : Module.End ℝ V)
    (hnode : Function.Injective nodes)
    (i j : ι) (x : V) (hx : T x = nodes j • x) :
    cartanCharacteristicInterpolationProjector nodes T i x =
      if i = j then x else 0 := by
  unfold cartanCharacteristicInterpolationProjector
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hx]
  by_cases hij : i = j
  · subst j
    rw [Lagrange.eval_basis_self hnode.injOn (Finset.mem_univ i)]
    simp
  · rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
    simp [hij]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
