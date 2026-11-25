-- Prove2me | solution 1 for GlobalTheory.exists_model_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:17.992803+00:00
-- url     : https://prove2.me/submissions/f0c9df08-5c7d-4997-9650-fc04a03c1db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Theorems.Thm_GlobalTheory_exists_integral_model


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {M : Type*} [Field M] [CharZero M] {L : Type*} [Field L] [Algebra M L] [IsAlgClosed L]
  {W : WeierstrassCurve M} [W.IsElliptic]
namespace GlobalTheory
theorem _root_.solution (hj : IsIntegral ℤ W.j) (h : HasRationalTorsion W L 12)
    (M' : Type*) [Field M'] [Algebra M M'] :
    ∃ (C : VariableChange M') (W₀ : WeierstrassCurve (𝓞 M')),
      C • W.baseChange M' = W₀.baseChange M' ∧ W₀.Δ = 1 := by
  have : IsIntegrallyClosedIn (𝓞 M) M := inferInstance
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model (𝓞 M) ⟨⟨W.j, hj⟩, rfl⟩ h
  refine ⟨C.map (algebraMap M M'), W₀.map (algebraMap (𝓞 M) (𝓞 M')), ?_, by rw [map_Δ, h₀, map_one]⟩
  rw [WeierstrassCurve.baseChange, map_variableChange, e]
  rfl
end GlobalTheory
