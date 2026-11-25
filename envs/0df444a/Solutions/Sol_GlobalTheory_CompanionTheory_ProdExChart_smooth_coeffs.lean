-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.smooth_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:42.663805+00:00
-- url     : https://prove2.me/submissions/99dfb22d-882a-42c3-9c5f-9ecc19f2759d

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_smooth_solve
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
theorem _root_.solution {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d e : ℕ}
    (L : Submodule ℝ V) (Z : Fin d → P → V) (Q : Fin e → V) (h3 : ∀ j, ContDiff ℝ ∞ (Z j))
    (h1 : ∀ j t, Z j t ∈ L) (hQ : ∀ i, Q i ∈ L)
    (h0 : ∀ y ∈ L, ∃ (a : Fin d → ℝ) (b : Fin e → ℝ), y = ∑ j, a j • Z j 0 + ∑ i, b i • Q i) :
    ∃ U : Set P, IsOpen U ∧ (0 : P) ∈ U ∧ ∀ y : P → V, ContDiff ℝ ∞ y → (∀ t, y t ∈ L) →
      ∃ (a : Fin d → P → ℝ) (b : Fin e → P → ℝ), (∀ j, ContDiffOn ℝ ∞ (a j) U) ∧
        (∀ i, ContDiffOn ℝ ∞ (b i) U) ∧ ∀ t ∈ U, y t = ∑ j, a j t • Z j t + ∑ i, b i t • Q i := by
  let A : Fin d → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ) := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ _ _)
  let B : Fin e → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] ℝ) := fun i =>
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)
  let M : P → ((Fin d → ℝ) × (Fin e → ℝ) →L[ℝ] V) := fun t =>
    ∑ j, (A j).smulRight (Z j t) + ∑ i, (B i).smulRight (Q i)
  have hM : ∀ t c, M t c = ∑ j, c.1 j • Z j t + ∑ i, c.2 i • Q i := fun t c => by
    simp [M, A, B]
  have hsm : ContDiff ℝ ∞ M :=
    (ContDiff.sum fun j _ => contDiff_const.smulRight (h3 j)).add contDiff_const
  obtain ⟨U, hU, hU0, hsol⟩ := smooth_solve L M hsm
    (fun t c => by
      rw [hM]
      exact Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (h1 j t))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hQ i)))
    (fun y hy => by
      obtain ⟨a, b, hab⟩ := h0 y hy
      exact ⟨(a, b), by rw [hM, hab]⟩)
  refine ⟨U, hU, hU0, fun y hy hyL => ?_⟩
  obtain ⟨c, hc, hc'⟩ := hsol y hy hyL
  refine ⟨fun j t => (c t).1 j, fun i t => (c t).2 i, fun j => (A j).contDiff.comp_contDiffOn hc,
    fun i => (B i).contDiff.comp_contDiffOn hc, fun t ht => ?_⟩
  rw [← hM, hc' t ht]
end GlobalTheory.CompanionTheory.ProdExChart
