-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_openPartialHomeomorph_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:34.855998+00:00
-- url     : https://prove2.me/submissions/562bbad6-1034-450f-9ce7-cf76b0e8eedf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) {Ψ : E → F} {x : E}
    (hΨ : AnalyticAt 𝕜 Ψ x) (hinj : Function.Injective (fderiv 𝕜 Ψ x)) :
    ∃ Φ : OpenPartialHomeomorph E F, (Φ : E → F) = Ψ ∧ x ∈ Φ.source ∧
      AnalyticOnNhd 𝕜 Φ.symm Φ.target := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have hsurj : Function.Surjective (fderiv 𝕜 Ψ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv 𝕜 Ψ x : E →ₗ[𝕜] F))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective (fderiv 𝕜 Ψ x) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hLe : (Le : E →L[𝕜] F) = fderiv 𝕜 Ψ x := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : E →L[𝕜] F) x := by rw [hLe]; exact hΨ.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hpS : x ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt 𝕜 Φ.symm (Φ x) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨ hLe.symm
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T, hTs, hTo, hTp⟩ := mem_nhds_iff.mp hs
  refine ⟨(Φ.symm.restrOpen T hTo).symm, rfl, ⟨hpS, hTp⟩, fun z hz => hsan z (hTs hz.2)⟩
end GlobalTheory.AffinePoints
