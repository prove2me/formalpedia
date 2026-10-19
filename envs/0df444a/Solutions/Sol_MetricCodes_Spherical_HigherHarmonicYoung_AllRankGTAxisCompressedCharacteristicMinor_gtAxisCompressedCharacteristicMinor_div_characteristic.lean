-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor.gtAxisCompressedCharacteristicMinor_div_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/badc1f51-375d-4866-afe8-956a947a5aef

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
    (p q : HarmonicYoungSpace (n := n) mu)
    (z : ℝ)
    (hz : ∀ channel : Fin (r + 2) × Bool,
      z ≠ signedNode (ambientShift (n + 1) lam) channel) :
    (gtAxisCompressedCharacteristicMinor lam mu h hgram p q).eval z /
        (gtChannelCharacteristicPolynomial (n + 1) lam).eval z =
      ∑ channel : Fin (r + 2) × Bool,
        gtAxisCompressedSignedProjectorCoefficient
            lam mu h hgram p q channel /
          (z - signedNode (ambientShift (n + 1) lam) channel) := by
  classical
  let nodes : Fin (r + 2) × Bool → ℝ :=
    signedNode (ambientShift (n + 1) lam)
  let characteristic : Polynomial ℝ :=
    gtChannelCharacteristicPolynomial (n + 1) lam
  let weights : Fin (r + 2) × Bool → ℝ :=
    gtAxisCompressedSignedProjectorCoefficient lam mu h hgram p q
  have hnonzero : characteristic.eval z ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro channel _
    exact hz channel
  have hvalue := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (r + 2) × Bool)))
    (v := nodes) (x := z)
    (fun channel => characteristic.derivative.eval (nodes channel) *
      weights channel)
    (fun channel _ => hz channel)
  change
    (Lagrange.interpolate Finset.univ nodes
      (fun channel => characteristic.derivative.eval (nodes channel) *
        weights channel)).eval z / characteristic.eval z = _
  have hcharacteristic :
      Lagrange.nodal (Finset.univ : Finset (Fin (r + 2) × Bool)) nodes =
        characteristic := rfl
  rw [hvalue, hcharacteristic, mul_div_cancel_left₀ _ hnonzero]
  apply Finset.sum_congr rfl
  intro channel _
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
    (Finset.mem_univ channel)]
  have hderivative : characteristic.derivative.eval (nodes channel) ≠ 0 := by
    rcases channel with ⟨row, sign⟩
    exact FiniteInterlacing.gtChannelCharacteristic_derivative_eval_ne_zero
      hfinite row sign
  change
    (characteristic.derivative.eval (nodes channel))⁻¹ *
        (z - nodes channel)⁻¹ *
        (characteristic.derivative.eval (nodes channel) *
          weights channel) =
      weights channel / (z - nodes channel)
  field_simp [hderivative, sub_ne_zero.mpr (hz channel)]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
