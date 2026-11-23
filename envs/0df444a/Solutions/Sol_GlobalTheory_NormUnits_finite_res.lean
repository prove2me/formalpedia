-- Prove2me | solution 1 for GlobalTheory.NormUnits.finite_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:59.825487+00:00
-- url     : https://prove2.me/submissions/40299cc5-4479-4897-b2ac-ca42d1107c1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GlobalTheory.NormUnits
theorem _root_.solution [LocallyCompactSpace K] : Finite (intRing K ⧸ maxIdeal K) := by
  haveI : ProperSpace K := ProperSpace.of_locallyCompactSpace K
  haveI : CompactSpace (intRing K) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : K) 1)
  have hopen : IsOpen ((maxIdeal K : Set (intRing K))) := by
    have e : ((maxIdeal K : Set (intRing K))) = Subtype.val ⁻¹' Metric.ball (0 : K) 1 := by
      ext x; simp [mem_maxIdeal]
    rw [e]; exact Metric.isOpen_ball.preimage continuous_subtype_val
  exact AddSubgroup.quotient_finite_of_isOpen (maxIdeal K).toAddSubgroup hopen
end GlobalTheory.NormUnits
