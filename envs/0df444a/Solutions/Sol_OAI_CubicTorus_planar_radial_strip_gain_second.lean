-- Prove2me | solution 1 for OAI.CubicTorus.planar_radial_strip_gain_second
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:40:05.669929+00:00
-- url     : https://prove2.me/submissions/50adb966-08c0-4d52-8ee7-8a510e4fe45d

import Mathlib
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_planar_radial_strip_gain_first

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialAreaDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarSwap_measurePreserving : MeasurePreserving planarSwap :=
  volume_measurePreserving_piCongrLeft _ _

lemma planeSwap_single (j : Fin 2) : planeSwap (EuclideanSpace.single j 1)=
    EuclideanSpace.single (Equiv.swap 0 1 j) 1 := by
  ext k
  fin_cases j <;> fin_cases k <;> simp

lemma planeDivergence_swap {F : Plane →Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Plane) :
    planeDivergence (fun y ↦ planeSwap (F (planeSwap y))) x=planeDivergence F (planeSwap x) := by
  have hd := planeSwap.toContinuousLinearEquiv.hasFDerivAt.comp x
    (((hF.differentiable (by simp) _).hasFDerivAt).comp x planeSwap.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ planeSwap (F (planeSwap y))) _ x at hd
  rw [planeDivergence,hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    planeDivergence]
  simp
  rw [planeSwap_single,planeSwap_single]
  norm_num
  ring

lemma planarAdmissibleField_swap {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    PlanarAdmissibleField (fun y ↦ planeSwap (F (planeSwap y))) := by
  refine ⟨planeSwap.contDiff.comp (hF.1.comp planeSwap.contDiff),?_,?_⟩
  · intro n y
    change planeSwap (F (planeSwap (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))))=planeSwap (F (planeSwap y))
    rw [map_add]
    have he : planeSwap (WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        WithLp.toLp 2 (fun j ↦ ((n (Equiv.swap 0 1 j)) : ℝ)) := by ext j; rfl
    rw [he,hF.2.1]
  · intro y
    rw [planeSwap.norm_map]
    exact hF.2.2 _

lemma planeSwap_representative (y : TransverseProduct) :
    planeSwap (planarRepresentative y)=planarRepresentative (planarSwap y) := by
  ext j
  simp only [planeSwap_apply,planarRepresentative,planarSwap_apply]

lemma planarTorusPerimeter_swap_le (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)≤planarTorusPerimeter A := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  let G : Plane →Plane := fun y ↦ planeSwap (F (planeSwap y))
  have hG : PlanarAdmissibleField G := planarAdmissibleField_swap hF
  have hh := planarSwap_measurePreserving.setIntegral_preimage_emb planarSwap.measurableEmbedding
    (fun y ↦ planeDivergence G (planarRepresentative y)) A
  have he : (fun y ↦ planeDivergence G (planarRepresentative (planarSwap y)))=
      (fun y ↦ planeDivergence F (planarRepresentative y)) := by
    funext y
    rw [show planeDivergence G (planarRepresentative (planarSwap y))=planeDivergence F (planeSwap (planarRepresentative (planarSwap y))) from planeDivergence_swap hF.1 _,
      planeSwap_representative,planarSwap_involutive]
  rw [he] at hh
  rw [hh]
  exact le_iSup_of_le G (le_iSup_of_le hG le_rfl)

theorem planarTorusPerimeter_swap (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)=planarTorusPerimeter A := by
  refine le_antisymm (planarTorusPerimeter_swap_le A) ?_
  have hh := planarTorusPerimeter_swap_le (planarSwap ⁻¹' A)
  have he : planarSwap ⁻¹' (planarSwap ⁻¹' A)=A := by ext y; simp
  rwa [he] at hh

lemma planar_volume_swap (A : Set TransverseProduct) :
    volume.real (planarSwap ⁻¹' A)=volume.real A := by
  apply congrArg ENNReal.toReal
  exact planarSwap_measurePreserving.measure_preimage_emb planarSwap.measurableEmbedding A

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarSwap_continuous : Continuous planarSwap := by
  apply continuous_pi
  intro j
  simpa only [planarSwap_apply] using (continuous_apply (Equiv.swap 0 1 j) : Continuous (fun y : TransverseProduct ↦ y (Equiv.swap 0 1 j)))

lemma planarSwap_closure_subset (A : Set TransverseProduct) :
    closure (planarSwap ⁻¹' A)⊆planarSwap ⁻¹' closure A :=
  closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage planarSwap_continuous)

lemma planarRadialDownset_swap {A : Set TransverseProduct} (hd : PlanarRadialDownset A) :
    PlanarRadialDownset (planarSwap ⁻¹' A) := by
  intro y z hyz hz
  apply hd (planarSwap y) (planarSwap z) _ hz
  intro j
  simpa only [planarSwap_apply] using hyz (Equiv.swap 0 1 j)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SmoothSeamProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planar_radial_strip_gain_second_oai {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (hin : planarFirstAxisPoint (1/2)∈A)
    (hout : planarAxisPoint (1/2)∉closure A)
    {e j : ℝ} (he : 0≤e) (hj : j∈Icc 0 (21/100 : ℝ))
    (hedge : ∀ y∈closure A,y 0=((1/2 : ℝ) : AxisCircle) →2*‖y 1‖≤e)
    (hgap : j≤volume.real A-e) :
    ENNReal.ofReal (2*(1+(27/20)*j^2))≤planarTorusPerimeter A := by
  have hi : planarAxisPoint (1/2)∈planarSwap ⁻¹' A := by simpa using hin
  have ho : planarFirstAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
    intro hh
    apply hout
    simpa only [mem_preimage,planarSwap_firstAxisPoint] using planarSwap_closure_subset A hh
  have hb : ∀ y∈closure (planarSwap ⁻¹' A),y 1=((1/2 : ℝ) : AxisCircle) →2*‖y 0‖≤e := by
    intro y hy hy1
    have hh := hedge (planarSwap y) (planarSwap_closure_subset A hy) (by simpa using hy1)
    simpa using hh
  have hh := planar_radial_strip_gain_first (hA.preimage planarSwap_continuous)
    (planarRadialDownset_swap hd) hi ho he hj hb (by simpa only [planar_volume_swap] using hgap)
  simpa only [planarTorusPerimeter_swap] using hh

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.planar_radial_strip_gain_second_oai := @OAI.CubicTorus.planar_radial_strip_gain_second_oai
