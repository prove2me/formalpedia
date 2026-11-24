-- Prove2me | solution 1 for GlobalTheory.ThetaGen.exists_isHomogeneous_of_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:04.340871+00:00
-- url     : https://prove2.me/submissions/a4b70eba-a855-424b-9403-ca3a049160d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
namespace GlobalTheory.ThetaGen
theorem _root_.solution {X ι : Type} (θ : ι → X → ℂ) (d : ℕ) {f : X → ℂ}
    (hf : f ∈ Submodule.span ℂ (Set.range θ) ^ d) :
    ∃ F : MvPolynomial ι ℂ, F.IsHomogeneous d ∧
      ∀ z, f z = MvPolynomial.eval (fun c => θ c z) F := by
  have h : Submodule.span ℂ (Set.range θ) ^ d =
      Submodule.map (MvPolynomial.aeval θ).toLinearMap
        (MvPolynomial.homogeneousSubmodule ι ℂ d) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow]
    simp [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp,
      Function.comp_def]
  rw [h] at hf
  obtain ⟨F, hF, rfl⟩ := hf
  refine ⟨F, hF, fun z => ?_⟩
  have := MvPolynomial.comp_aeval_apply θ (Pi.evalAlgHom ℂ (fun _ : X => ℂ) z) F
  simpa using this
end GlobalTheory.ThetaGen
