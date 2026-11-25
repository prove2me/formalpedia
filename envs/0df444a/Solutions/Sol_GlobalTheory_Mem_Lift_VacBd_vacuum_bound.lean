-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacBd.vacuum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:42.769795+00:00
-- url     : https://prove2.me/submissions/a855321b-05e2-4e81-8744-505eced1be2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_dH_bound
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_heis_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_contDiff_omJ
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_sm_dH
import Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_fderiv_compress
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_add
import Theorems.Thm_GlobalTheory_Mem_Lift_dH_smul
import Theorems.Thm_GlobalTheory_RealWeil_Good_sm
import Theorems.Thm_GlobalTheory_RealWeil_Osc_good_proj
import Theorems.Thm_GlobalTheory_RealWeil_contDiff_gau
import Theorems.Thm_GlobalTheory_RealWeil_proj_heis_proj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacBd
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
namespace GlobalTheory.Mem.Lift.VacBd
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, (∃ C : ℝ, ∀ z x, ‖dH ρ z (proj h x)‖ ≤ C * ‖z‖ * ‖x‖) ∧ (∀ u v, ∃ C : ℝ, ∀ x, ‖dH ρ u (dH ρ v (proj h x))‖ ≤ C * ‖x‖) ∧ ∀ u v, ∃ lam : ℂ, ∀ x, proj h (dH ρ u (dH ρ v (proj h x))) = lam • proj h x := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h
  have hs : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨C, hC⟩ := dH_bound h (proj h) hs
  refine ⟨⟨C, hC⟩, fun u v => ?_, fun u v => ?_⟩
  · let T : B →L[ℂ] B := LinearMap.mkContinuous
      { toFun := fun x => dH ρ v (proj h x)
        map_add' := fun x y => by rw [map_add, dH_add v (hs x) (hs y)]
        map_smul' := fun a x => by rw [map_smul, dH_smul v a (hs x), RingHom.id_apply] } (C * ‖v‖) (hC v)
    obtain ⟨D, hD⟩ := dH_bound h T fun x => sm_dH h (hs x) v
    exact ⟨D * ‖u‖, hD u⟩
  · have hg : ContDiff ℝ ∞ (gau : V → ℂ) := contDiff_gau
    have hφ : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) * gau w + fderiv ℝ gau w v :=
      ((contDiff_omJ v).mul hg).add ((ContDiff.fderiv_right (m := ∞) hg (by simp)).clm_apply contDiff_const)
    refine ⟨_, fun x => fderiv_compress (proj h) (sm_dH h (hs x) v) hφ (fun w => ?_) 0 u⟩
    rw [heis_dH h (hs x), map_add, map_smul, proj_heis_proj hJ h,
      fderiv_compress (proj h) (hs x) hg (fun w => proj_heis_proj hJ h w x), add_smul, mul_smul _ (gau w)]
end GlobalTheory.Mem.Lift.VacBd
