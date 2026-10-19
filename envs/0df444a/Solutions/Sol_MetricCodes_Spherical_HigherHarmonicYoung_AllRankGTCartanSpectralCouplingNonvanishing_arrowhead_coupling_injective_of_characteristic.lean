-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.arrowhead_coupling_injective_of_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/8d52313e-f62b-44cd-b0b5-767bab111269

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanSpectralCouplingNonvanishing_arrowhead_coupling_eq_zero_of_apply_eq_zero

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
theorem _root_.solution
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0) :
    Function.Injective K := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply arrowhead_coupling_eq_zero_of_apply_eq_zero
    T B hB A K P d hrow hchar heval (p - q)
  rw [map_sub, hpq, sub_self]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
