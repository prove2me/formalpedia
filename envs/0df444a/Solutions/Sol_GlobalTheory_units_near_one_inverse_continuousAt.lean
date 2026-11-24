-- Prove2me | solution 1 for GlobalTheory.units_near_one_inverse_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:46.606289+00:00
-- url     : https://prove2.me/submissions/cdb67889-8e98-4767-aeeb-c09a7863408a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)
end GlobalTheory
