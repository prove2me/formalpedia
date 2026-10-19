-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor.gtAxisCompressedCharacteristicMinor_eq_sum_nodal_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/f38b5ce1-546d-4602-b05e-0b4f3b722bce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTCharacteristicResidue_FiniteInterlacing_gtChannelCharacteristic_derivative_eval_ne_zero

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) lam mu h)
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (p q : HarmonicYoungSpace (n := n) mu) :
    gtAxisCompressedCharacteristicMinor lam mu h hgram p q =
      ∑ channel : Fin (r + 2) × Bool,
        Polynomial.C
          (gtAxisCompressedSignedProjectorCoefficient
            lam mu h hgram p q channel) *
          Lagrange.nodal
            ((Finset.univ : Finset (Fin (r + 2) × Bool)).erase channel)
            (signedNode (ambientShift (n + 1) lam)) := by
  classical
  unfold gtAxisCompressedCharacteristicMinor
  rw [Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro channel _
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div
    (Finset.mem_univ channel),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ channel),
    Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ channel)]
  have hderivative :
      (gtChannelCharacteristicPolynomial (n + 1) lam).derivative.eval
        (signedNode (ambientShift (n + 1) lam) channel) ≠ 0 := by
    rcases channel with ⟨row, sign⟩
    exact FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
      hfinite row sign
  have hcharacteristic :
      Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 2) × Bool))
        (signedNode (ambientShift (n + 1) lam)) =
        gtChannelCharacteristicPolynomial (n + 1) lam := rfl
  rw [hcharacteristic]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  congr 1
  field_simp [hderivative]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
