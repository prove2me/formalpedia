-- Prove2me | solution 1 for GlobalTheory.GaussWidths.mem_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:13.239597+00:00
-- url     : https://prove2.me/submissions/184a840d-5263-4d6e-bff3-6f9f9701e641

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSchwartzGaussWidth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.GaussWidths
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory.GaussWidths
theorem _root_.solution {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM
end GlobalTheory.GaussWidths
