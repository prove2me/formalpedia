-- Prove2me | solution 1 for HcInf.hasFDerivAt_tauR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:29.988981+00:00
-- url     : https://prove2.me/submissions/d167005b-8581-4c68-85ac-4af4c7403caf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
import Theorems.Thm_HcInf_smul_four
import Theorems.Thm_HcInf_key_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open HcS.BasicNotions Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
namespace HcInf
theorem _root_.solution (H X : Mat) (hN : IsUnit (H * ((1 + 1) + X) + ((1 + 1) - X)).det)
    (hS : IsUnit ((1 + 1) - X).det) :
    HasFDerivAt (tauR H) (ContinuousLinearMap.mulLeftRight ℝ Mat
      ((4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹))
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)) X := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hN
  have hA : HasFDerivAt (fun Z : Mat => (1 + 1) - Z) (-ContinuousLinearMap.id ℝ Mat) X :=
    (hasFDerivAt_id X).const_sub _
  have hB := (((hasFDerivAt_const (1 + 1 : Mat) X).add (hasFDerivAt_id X)).const_mul H).add hA
  have hI : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ Mat ↑u⁻¹ ↑u⁻¹)
      (H * ((1 + 1) + X) + ((1 + 1) - X)) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  have hC := hI.comp X hB
  have hD := ((hA.mul' hC).const_smul (4 : ℂ)).const_sub (1 + 1 : Mat)
  have hE : HasFDerivAt (tauR H) _ X := hD
  have hinv : (↑u⁻¹ : Mat) = (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  refine hE.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
  have hNi := Matrix.nonsing_inv_mul _ hN
  have hK := Matrix.mul_nonsing_inv _ hS
  have k := key_alg H X Y _ _ hNi hK
  change -((4 : ℂ) • (((1 + 1) - X) * (-(Units.val u⁻¹ * (H * (0 + Y) + -Y) * Units.val u⁻¹)) +
      (-Y) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))) =
    (4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹) * Y *
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)
  rw [hinv, ← Matrix.nonsing_inv_eq_ringInverse, smul_four, smul_four, smul_four, zero_add]
  calc _ = (1 + 1 + 1 + 1) * ((Y + ((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * (H * Y - Y)) *
          (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (((1 + 1 + 1 + 1) * (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ *
          H * ((1 + 1) - X)⁻¹ * Y)) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by rw [k]
    _ = _ := by noncomm_ring
end HcInf
