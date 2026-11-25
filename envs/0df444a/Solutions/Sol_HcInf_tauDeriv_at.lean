-- Prove2me | solution 1 for HcInf.tauDeriv_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:47.776056+00:00
-- url     : https://prove2.me/submissions/334d68a6-dddf-4b80-9b30-a5448c32ac6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_HasFDerivAtTauR
import Theorems.Thm_HcInf_hasFDerivAt_tauR
import Theorems.Thm_HcInf_nH_eq
import Theorems.Thm_HcInf_tauL_val


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
theorem _root_.solution (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hn : IsUnit (nH h (x : Mat)).det) :
    ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Mat) = chA h (x : Mat) * (Y : Mat) * chB h (x : Mat)) ∧
      HasFDerivAt (tauL h) f' x := by
  set ι : lieU P Q →L[ℝ] Mat := (lieU P Q).subtypeL with hι
  set L : Mat →L[ℝ] Mat :=
    ContinuousLinearMap.mulLeftRight ℝ Mat (chA h (x : Mat)) (chB h (x : Mat)) with hL
  have hM : HasFDerivAt (tauR (UpqT.mat h)) L (ι x) := hasFDerivAt_tauR (UpqT.mat h) (x : Mat) hn hx
  have c1 : Continuous fun y : lieU P Q => (1 + 1) - ι y := continuous_const.sub ι.continuous
  have c2 : Continuous fun y : lieU P Q => UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y) :=
    (continuous_const.mul (continuous_const.add ι.continuous)).add (continuous_const.sub ι.continuous)
  have hev : ∀ᶠ y in 𝓝 x, IsUnit ((1 + 1) - ι y) ∧
      IsUnit (UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y)) := by
    filter_upwards [c1.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hx)),
      c2.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hn))] with y h1 h2
    exact ⟨h1, h2⟩
  have heq : (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) =ᶠ[𝓝 x]
      (tauR (UpqT.mat h) ∘ ι) := by
    filter_upwards [hev] with y hy
    have hyD : y ∈ D0 P Q := (Matrix.isUnit_iff_isUnit_det _).1 hy.1
    have hyN : IsUnit (nH h (y : Mat)).det := (Matrix.isUnit_iff_isUnit_det _).1 hy.2
    have hu : IsUnit (UpqT.mat (h * cayF P Q y) + 1).det := by
      have e := hyN
      rw [nH_eq h y hyD, det_mul] at e
      exact isUnit_of_mul_isUnit_left e
    rw [tauL_val h y hyD hu, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hF : HasFDerivAt (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) (L.comp ι) x :=
    (HasFDerivAt.comp x hM ι.hasFDerivAt).congr_of_eventuallyEq heq
  have hclosed : IsClosed ((lieU P Q : Set Mat)) := (lieU P Q).closed_of_finiteDimensional
  have hmem : ∀ Y, (L.comp ι) Y ∈ lieU P Q := by
    intro Y
    exact hclosed.mem_of_tendsto (hF.lim_real Y) (Eventually.of_forall fun c =>
      (lieU P Q).smul_mem c ((lieU P Q).sub_mem (tauL h _).2 (tauL h x).2))
  refine ⟨(L.comp ι).codRestrict (lieU P Q) hmem, fun Y => ?_, ?_⟩
  · have hLY : L (ι Y) = chA h (x : Mat) * ι Y * chB h (x : Mat) :=
      ContinuousLinearMap.mulLeftRight_apply _ _ _ _ _
    exact hLY
  · have hF' := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
    refine hasFDerivAt_iff_isLittleO_nhds_zero.2 ?_
    rw [← Asymptotics.isLittleO_norm_left] at hF' ⊢
    refine hF'.congr_left fun k => ?_
    rfl
end HcInf
