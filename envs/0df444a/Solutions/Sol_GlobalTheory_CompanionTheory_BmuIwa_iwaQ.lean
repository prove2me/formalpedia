-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuIwa.iwaQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:57.176727+00:00
-- url     : https://prove2.me/submissions/103c8c42-42bc-4e42-81c3-5137df960dca

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwasawaDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_adapted_dec_left
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_adapted_pq
import Theorems.Thm_GlobalTheory_CompanionTheory_BmuIwa_Hq_eq_dp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuIwa
open Matrix CompanionTheory.Bmu CompanionTheory.D.gk.admitted.CholeskyDecomposition Formalism.QuantumDeterminants
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory.CompanionTheory.BmuIwa
theorem _root_.solution : IwaQ := by
  intro k r _ x hx
  have hx' : xᴴ * Hq k r * x = Hq k r := hx
  rw [Hq_eq_dp] at hx'
  obtain ⟨s, κ, hs, hκ, h1, h2, h3⟩ := adapted_dec_left (adapted_pq k r) x hx'
  rw [← Hq_eq_dp] at hs hκ
  exact ⟨s, hs, κ, hκ, h1, h2, h3⟩
end GlobalTheory.CompanionTheory.BmuIwa
