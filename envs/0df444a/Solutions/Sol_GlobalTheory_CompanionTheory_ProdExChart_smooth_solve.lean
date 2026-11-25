-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.smooth_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:05.33214+00:00
-- url     : https://prove2.me/submissions/e880d93e-6aa7-43cc-a3e6-021ad8354eec

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdExChart
namespace GlobalTheory.CompanionTheory.ProdExChart
theorem _root_.solution {P F V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℝ V) (M : P → F →L[ℝ] V) (hM : ContDiff ℝ ∞ M) (hL : ∀ t c, M t c ∈ L)
    (h0 : ∀ y ∈ L, ∃ c, M 0 c = y) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ c : P → F, ContDiffOn ℝ ∞ c U ∧ ∀ t ∈ U, M t (c t) = y t := by
  have : CompleteSpace V := FiniteDimensional.complete ℝ V
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)
  have hp' : ∀ y (hy : y ∈ L), (p y : V) = y := fun y hy => by
    have := LinearMap.congr_fun hp ⟨y, hy⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    ((M 0 : F →ₗ[ℝ] V).codRestrict L (hL 0)) (by
      rw [LinearMap.range_eq_top]
      intro y
      obtain ⟨c, hc⟩ := h0 y y.2
      exact ⟨c, Subtype.ext hc⟩)
  let r : V →L[ℝ] F := LinearMap.toContinuousLinearMap (g ∘ₗ p)
  let π : V →L[ℝ] V := LinearMap.toContinuousLinearMap (L.subtype ∘ₗ p)
  have hπ : ∀ v, π v = (p v : V) := fun v => rfl
  have hr : ∀ v, M 0 (r v) = π v := fun v =>
    congrArg Subtype.val (LinearMap.congr_fun hg (p v))
  let N : P → V →L[ℝ] V := fun t => (M t).comp r + (1 - π)
  have hN : ContDiff ℝ ∞ N := (hM.clm_comp contDiff_const).add contDiff_const
  have hN0 : N 0 = 1 := by
    ext v
    simp [N, hr]
  refine ⟨N ⁻¹' {x | IsUnit x}, Units.isOpen.preimage hN.continuous, by simp [hN0], fun y hy hyL => ?_⟩
  refine ⟨fun t => r (Ring.inverse (N t) (y t)), ?_, ?_⟩
  · intro t ht
    obtain ⟨u, hu⟩ := (show IsUnit (N t) from ht)
    have h1 : ContDiffAt ℝ ∞ (fun t => Ring.inverse (N t)) t := by
      have := contDiffAt_ringInverse ℝ (n := ∞) u
      rw [hu] at this
      exact this.comp t hN.contDiffAt
    exact (r.contDiff.contDiffAt.comp t (h1.clm_apply hy.contDiffAt)).contDiffWithinAt
  · intro t ht
    have ht' : IsUnit (N t) := ht
    set v := Ring.inverse (N t) (y t) with hv
    have h1 : N t v = y t := by
      rw [hv, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ ht']; rfl
    have h2 : M t (r v) + (v - π v) = y t := h1
    have h3 := congrArg π h2
    rw [map_add, map_sub, hπ (M t (r v)), hp' _ (hL _ _), hπ (π v), hp' (π v) (p v).2, hπ (y t),
      hp' _ (hyL t), sub_self, add_zero] at h3
    exact h3
end GlobalTheory.CompanionTheory.ProdExChart
