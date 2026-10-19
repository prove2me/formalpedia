-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.gtSignedArrowheadCoupling_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/de77c6ca-ae69-49b3-8806-a047f68bdf4c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAmbientCharacteristicAtTransverseNode_gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanSpectralCouplingNonvanishing_arrowhead_isometric_coupling_injective_of_characteristic

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (B : E →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (A : F →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) lam))
    (K : E →ₗ[ℝ] F) (d : ℝ)
    (hrow :
      (gtRelativeCasimir (n := n) lam).comp B.toLinearMap =
        d • B.toLinearMap + A.comp K)
    (hchar : ∀ p : E,
      Polynomial.aeval (gtRelativeCasimir (n := n) lam)
        (gtChannelCharacteristicPolynomial n lam) (B p) = 0)
    (hnode : ∀ i : Fin (r + 1) × Bool,
      d ≠ signedNode (HigherChannel.ambientShift n lam) i) :
    Function.Injective K := by
  apply arrowhead_isometric_coupling_injective_of_characteristic
    (gtRelativeCasimir (n := n) lam) B A K
    (gtChannelCharacteristicPolynomial n lam) d hrow hchar
  exact gtChannelCharacteristicPolynomial_eval_ne_zero_of_forall_ne
    lam d hnode
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
