-- Prove2me | solution 1 for GlobalTheory.JR.Hyp.integral_comp_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:59:45.343656+00:00
-- url     : https://prove2.me/submissions/65eb6baa-09ab-4a02-8a24-de59e0e79a6f

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierScaleEqTorusAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp
namespace GlobalTheory.JR.Hyp
theorem _root_.solution {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) [ν.IsAddHaarMeasure]
    (s : A.Kˣ) (g : A.K → ℂ) :
    ∫ b, g ((s : A.K) * b) ∂ν = ((A.absK (s : A.K) : ℂ))⁻¹ * ∫ b, g b ∂ν := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology A.K := by
    let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
    have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
    exact h.isEmbedding.secondCountableTopology
  have hme : MeasurableEmbedding (fun b : A.K => s • b) := (Homeomorph.smul s).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul ν s⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν) := by
    rw [hme.integral_map]; rfl
  have habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
    unfold Et.absK
    rw [dif_pos s.isUnit]
    congr 2
    ext; rfl
  rw [hint, hmap, integral_smul_measure, habs]
  simp [Complex.real_smul]
end GlobalTheory.JR.Hyp
