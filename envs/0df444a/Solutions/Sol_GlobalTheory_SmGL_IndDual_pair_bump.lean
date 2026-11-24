-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.pair_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:34.517083+00:00
-- url     : https://prove2.me/submissions/e439f847-078e-4532-9d4b-0cfd682108ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_isOpen_cell
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_mul
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_zero
import Theorems.Thm_GlobalTheory_SmGL_IndDual_pair_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution (hB : ∀ p : P, (p : G) ∈ K → ∀ w' w, B (τ p w') (σ p w) = B w' w)
    {J : Subgroup G} (hJ : IsOpen (J : Set G)) (hle : J ≤ K) (f' : smoothPart (ind P τ))
    (hf : ∀ j ∈ J, f'.1.1 j = f'.1.1 1) (w : fixed σ (J.subgroupOf P)) :
    pair μ hK σ τ B f' (bump σ hJ w) = (μ.real (K ∩ cell P J) : ℂ) * B (f'.1.1 1) w := by
  rw [pair_apply, setIntegral_congr_fun hK.measurableSet
    (g := (cell P J).indicator fun _ => B (f'.1.1 1) w), setIntegral_indicator (isOpen_cell hJ).measurableSet,
    setIntegral_const, Complex.real_smul]
  intro x hx
  rcases cell_cases (P := P) J x with h | ⟨p, j, hj, rfl⟩
  · simp [bump_zero _ _ _ h, h]
  · have hp : (p : G) ∈ K := by simpa using mul_mem hx (inv_mem (hle hj))
    have hm : (p : G) * j ∈ cell P J := ⟨p, by simpa using hj⟩
    simp only [Set.indicator_of_mem hm]
    rw [bump_mul _ _ _ _ hj, f'.1.2 p j, hB p hp, hf j hj]
end GlobalTheory.SmGL.IndDual
