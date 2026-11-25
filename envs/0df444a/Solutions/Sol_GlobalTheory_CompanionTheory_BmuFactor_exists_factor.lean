-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuFactor.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:26:14.349731+00:00
-- url     : https://prove2.me/submissions/ee1d7aa0-0492-45a6-8223-9ad7a0aae5be

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm Formalism.QuantumDeterminants
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuFactor
namespace GlobalTheory.CompanionTheory.BmuFactor
theorem _root_.solution {S E V : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : S →ₗ[ℂ] E) (B : S →ₗ[ℂ] V) (C : ℝ)
    (hb : ∀ v, ‖B v‖ ≤ C * ‖J v‖) : ∃ T : E →L[ℂ] V, ∀ v, B v = T (J v) := by
  have hker : LinearMap.ker J ≤ LinearMap.ker B := fun v hv => by
    have := hb v
    rw [LinearMap.mem_ker.1 hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let g : LinearMap.range J →ₗ[ℂ] V := ((LinearMap.ker J).liftQ B hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hg : ∀ v : S, g ⟨J v, LinearMap.mem_range_self J v⟩ = B v := fun v => by
    show (LinearMap.ker J).liftQ B hker (J.quotKerEquivRange.symm ⟨J v, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  have hgb : ∀ y : LinearMap.range J, ‖g y‖ ≤ C * ‖y‖ := by
    rintro ⟨_, v, rfl⟩
    exact (congrArg norm (hg v)).le.trans (hb v)
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exist_extension_of_finiteDimensional_range (g.mkContinuous _ hgb)
  refine ⟨T, fun v => ?_⟩
  have := congrArg (fun f => f ⟨J v, LinearMap.mem_range_self J _⟩) hT
  exact (hg v).symm.trans this
end GlobalTheory.CompanionTheory.BmuFactor
