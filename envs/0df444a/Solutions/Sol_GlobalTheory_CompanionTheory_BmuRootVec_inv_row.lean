-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.inv_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:17:53.18889+00:00
-- url     : https://prove2.me/submissions/0319b106-ffe5-4674-9aa8-6b9fb7586fdd

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {n : ℕ} {Γ : Mat n} (hu : IsUnit Γ.det) {i : Fin n}
    (h : ∀ l, Γ i l = if l = i then 1 else 0) (l : Fin n) : Γ⁻¹ i l = if l = i then 1 else 0 := by
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv Γ hu) i) l
  rw [Matrix.mul_apply] at h1
  simp only [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [h1, Matrix.one_apply]
  simp only [eq_comm]
end GlobalTheory.CompanionTheory.BmuRootVec
