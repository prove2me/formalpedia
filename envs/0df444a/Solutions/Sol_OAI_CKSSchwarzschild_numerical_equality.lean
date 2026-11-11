-- Prove2me | solution 1 for OAI.CKSSchwarzschild.numerical_equality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:50:32.956618+00:00
-- url     : https://prove2.me/submissions/335a58ad-b5f3-4ed5-b05b-f07b2b4aadd5

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_Q227CKS002
import Theorems.Thm_OAI_CKSSchwarzschild_source_minimum_area

section
-- module Solutions.Q227_CKS.Relativity_CKS_InducedSphereCalculus
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff

attribute [local instance] CKSLorentz.two_atLeastTwo

@[simp] lemma e_apply (i j : Ix) : e i j = if j = i then 1 else 0 := by
  simp [e, eq_comm]

@[simp] lemma pd_const (k : Ix) (c : ℝ) (x : E) : pd k (fun _ => c) x = 0 := by
  simp [pd]

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_HeatBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

open scoped Pointwise

lemma volume_preimage_isometry (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Ambient) :
    (volume : Measure Ambient) (u ⁻¹' s) = volume s := by
  have hm := u.toHomeomorph.toMeasurableEquiv.map_apply (μ := volume) s
  change (Measure.map u volume) s = volume (u ⁻¹' s) at hm
  rw [u.measurePreserving.map_eq] at hm
  exact hm.symm

lemma sphereCone_preimage (u : Ambient ≃ₗᵢ[ℝ] Ambient) (s : Set Sphere) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereHome u ⁻¹' s)) =
      u ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨r, hr, u v.1, ⟨sphereHome u v, hv, rfl⟩, (u.map_smul r v.1).symm⟩
  · rintro ⟨r, hr, _, ⟨v, hv, rfl⟩, hx⟩
    refine ⟨r, hr, u.symm v.1, ⟨sphereHome u.symm v, ?_, rfl⟩, ?_⟩
    · change sphereHome u (sphereHome u.symm v) ∈ s
      have h : sphereHome u (sphereHome u.symm v) = v := by
        apply Subtype.ext
        exact u.apply_symm_apply v.1
      simpa [h] using hv
    · apply u.injective
      simpa using hx

theorem sphereHome_measurePreserving (u : Ambient ≃ₗᵢ[ℝ] Ambient) :
    MeasurePreserving (sphereHome u) surfaceMeasure surfaceMeasure := by
  refine ⟨(sphereHome u).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereHome u).continuous.measurable hs,
    Measure.toSphere_apply' _ (hs.preimage (sphereHome u).continuous.measurable),
    Measure.toSphere_apply' _ hs, sphereCone_preimage, volume_preimage_isometry]

lemma sphereIntegral_apply (f : C(Sphere, ℝ)) :
    sphereIntegral f = ∫ x, f x ∂surfaceMeasure := by
  change inner ℝ (toL2 1) (toL2 f) = _
  rw [toL2, MeasureTheory.ContinuousMap.inner_toLp]
  simp

open scoped Manifold ContDiff Topology
open Set

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_FullSphereHeat
attribute [-simp] _root_.OAI.CKSSphericalChart.pair_add_left _root_.OAI.CKSSphericalChart.pair_add_right _root_.OAI.CKSSphericalChart.pair_neg_left _root_.OAI.CKSSphericalChart.pair_neg_right _root_.OAI.CKSSphericalChart.pair_smul_left _root_.OAI.CKSSphericalChart.pair_smul_right _root_.OAI.CKSSphericalChart.pair_zero_left _root_.OAI.CKSSphericalChart.pair_zero_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSInducedSphere
noncomputable section
open Set Filter Finset MeasureTheory
open scoped Topology ContDiff Manifold
open CKSSphericalHarmonics

@[simp] lemma pd_const_add (m : ℝ) (F : E → ℝ) (k : Ix) (x : E) :
    pd k (fun y => m + F y) x = pd k F x := by
  simp only [pd, fderiv_const_add]

@[simp] lemma pd_const_add_fun (m : ℝ) (F : E → ℝ) (k : Ix) :
    pd k (fun y => m + F y) = pd k F := by
  funext x
  exact pd_const_add m F k x

end
end CKSInducedSphere

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MeasureTheory Set

theorem sphereArea_eq_four_pi : sphereArea = 4 * Real.pi := by
  rw [sphereArea, sphereIntegral_apply]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.toSphere_real_apply_univ]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ADMAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter MeasureTheory CKSSphericalHarmonics CKSSphericalChart CKSInducedSphere
open scoped Topology ContDiff

lemma surfaceMeasure_real : surfaceMeasure.real univ = 4*Real.pi := by
  rw [← sphereArea_eq_four_pi,sphereArea,sphereIntegral_apply]
  simp

end
end CKSADM

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiCharge
attribute [-instance] _root_.OAI.CKSFullCutArea.surfaceCompact _root_.OAI.CKSSpatialManifold.spatialBilinearTriv_atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure)

lemma nullDirection_smooth : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞ nullDirection :=
by
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun _ : Sphere => (1:ℝ)) := contMDiff_const
  exact hc.prodMk_space (contMDiff_coe_sphere (E := E) (n := 2))

lemma rawCharge_integrable {M : Sphere → ℝ} (hM : SmoothSphere M) :
    Integrable (fun n => M n • nullDirection n) surfaceMeasure :=
  (hM.continuous.smul nullDirection_smooth.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma rawCharge_test {M : Sphere → ℝ} (hM : SmoothSphere M) (L : V →L[ℝ] ℝ) :
    L (rawCharge M) = ∫ n : Sphere, M n * L (nullDirection n) ∂surfaceMeasure := by
  rw [rawCharge, ← L.integral_comp_comm (rawCharge_integrable hM)]
  simp only [map_smul, smul_eq_mul]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiBalance
attribute [-instance] _root_.OAI.CKSSpatialManifold.spatialBilinearTriv_atlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure sphereIntegral sphereArea)

lemma charge_energy {M : Sphere → ℝ} (hM : SmoothSphere M) :
    (bondiCharge M).1 = (16*Real.pi)⁻¹ * ∫ n, M n ∂surfaceMeasure := by
  have h := rawCharge_test hM (ContinuousLinearMap.fst ℝ ℝ E)
  change (rawCharge M).1 = ∫ n, M n * 1 ∂surfaceMeasure at h
  simp only [mul_one] at h
  change (16*Real.pi)⁻¹ * (rawCharge M).1 = _
  rw [h]

lemma charge_momentum {M : Sphere → ℝ} (hM : SmoothSphere M) (i : Fin 3) :
    (bondiCharge M).2 i = (16*Real.pi)⁻¹ * ∫ n, M n * (n:E) i ∂surfaceMeasure := by
  have h := rawCharge_test hM
    ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ ℝ E))
  change (rawCharge M).2 i = ∫ n, M n * (n:E) i ∂surfaceMeasure at h
  change (16*Real.pi)⁻¹ * (rawCharge M).2 i = _
  rw [h]

end
end CKSLorentz

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory CKSLorentz CKSSphericalHarmonics
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma sphere_coordinate_integral (i : Fin 3) :
    (∫ n : Sphere, (n : E3) i ∂surfaceMeasure) = 0 := by
  let u : E3 ≃ₗᵢ[ℝ] E3 := LinearIsometryEquiv.neg ℝ
  have h := (sphereHome_measurePreserving u).integral_comp
    (sphereHome u).measurableEmbedding (fun n : Sphere => (n : E3) i)
  change (∫ n : Sphere, -(n : E3) i ∂surfaceMeasure) = _ at h
  rw [integral_neg] at h
  linarith

lemma constant_bondi_charge (m : ℝ) : bondiCharge (fun _ => 4*m) = (m,0) := by
  apply Prod.ext
  · rw [charge_energy contMDiff_const,integral_const,CKSADM.surfaceMeasure_real]
    change (16*Real.pi)⁻¹ * ((4*Real.pi) * (4*m)) = m
    field_simp
    ring
  · apply PiLp.ext
    intro i
    rw [charge_momentum contMDiff_const,integral_const_mul,sphere_coordinate_integral]
    simp
lemma bondi_charge {m : ℝ} (hm : 0 < m) : bondiCharge (cksData hm).massAspect = (m,0) :=
  constant_bondi_charge m

lemma numerical_equality_oai {m : ℝ} (hm : 0 < m) :
    Real.sqrt ((bondiCharge (cksData hm).massAspect).1^2 -
      ‖(bondiCharge (cksData hm).massAspect).2‖^2) =
    Real.sqrt (CKSSourceExterior.minimumEnclosingArea (smoothMetric hm) / (16*Real.pi)) := by
  rw [bondi_charge hm,source_minimum_area hm]
  simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero]
  congr 1
  field_simp
end CKSSchwarzschild

end

end OAI
end

theorem solution : type_of% @OAI.CKSSchwarzschild.numerical_equality_oai := @OAI.CKSSchwarzschild.numerical_equality_oai
