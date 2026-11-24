-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.mulLat_mem_Lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:04.894409+00:00
-- url     : https://prove2.me/submissions/6d52d3b5-0c16-445a-8861-368cdeaee288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Move_mem_mulLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Move
theorem _root_.solution (y : B.Aˣ) (hy : B.σ (y : B.A) = y) (M : Submodule K.O B.A) (hM : M ∈ B.Lin) :
    mulLat K.O (y : B.A) M ∈ B.Lin := by
  obtain ⟨⟨hfg, hsp⟩, hg, hσ⟩ := hM
  have hyi : B.σ ((y⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
    have h1 : B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((y⁻¹ : B.Aˣ) : B.A) = B.σ ((y⁻¹ : B.Aˣ) : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  refine ⟨⟨hfg.map _, ?_⟩, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ((mulLat K.O (y : B.A) M : Submodule K.O B.A) : Set B.A) =
        (LinearMap.mulLeft K.E (y : B.A)) '' (M : Set B.A) := by
      rw [mulLat, Submodule.map_coe]
      rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top]
    intro x
    exact ⟨((y⁻¹ : B.Aˣ) : B.A) * x, by simp⟩
  · rw [mem_mulLat] at hz ⊢
    rw [mul_left_comm]
    exact hg _ hz
  · rw [mem_mulLat] at hz ⊢
    have := hσ _ hz
    rwa [map_mul, hyi] at this
end GlobalTheory.UnitLemma.Move
