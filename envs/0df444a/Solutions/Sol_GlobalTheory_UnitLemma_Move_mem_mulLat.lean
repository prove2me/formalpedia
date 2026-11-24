-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Move.mem_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:34.560064+00:00
-- url     : https://prove2.me/submissions/5d0a48b5-94cf-43ee-9d60-05f2eba2b753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit

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
theorem _root_.solution (M : Submodule K.O B.A) (y : B.Aˣ) (z : B.A) :
    z ∈ mulLat K.O (y : B.A) M ↔ ((y⁻¹ : B.Aˣ) : B.A) * z ∈ M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩
end GlobalTheory.UnitLemma.Move
