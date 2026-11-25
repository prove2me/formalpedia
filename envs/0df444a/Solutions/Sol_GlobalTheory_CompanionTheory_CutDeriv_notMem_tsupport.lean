-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CutDeriv.notMem_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:10:51.514933+00:00
-- url     : https://prove2.me/submissions/7f28850e-efd6-4952-8d8d-ec71da5ccb6e

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TruncatedDerivation
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CutDeriv
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.CutDeriv
theorem _root_.solution {ρ : Mat n → ℝ} {R : ℝ} (hR : 0 < R) (X : Mat n) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    {y : PI.MtM n}
    (hy : y ∉ (fun p : ℝ × Mat n => (Matrix.of.symm (R • (ex X p.1 * p.2)) : PI.MtM n)) '' (T ×ˢ tsupport ρ)) :
    ex X (-t) * (R⁻¹ • Matrix.of y) ∉ tsupport ρ := fun hs =>
  hy ⟨(t, ex X (-t) * (R⁻¹ • Matrix.of y)), ⟨ht, hs⟩, by
    simp only
    rw [← Matrix.mul_assoc, ← ex_add, add_neg_cancel, ex_zero, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hR.ne', one_smul]
    rfl⟩
end GlobalTheory.CompanionTheory.CutDeriv
