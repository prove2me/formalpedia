-- Prove2me | solution 1 for GlobalTheory.UnitLemma.lattice_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:55.274886+00:00
-- url     : https://prove2.me/submissions/83f8765a-93c9-4ef8-87a8-128c67020409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_integral_sub
import Theorems.Thm_GlobalTheory_UnitLemma_Sandwich_sub_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a →
    ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧
        ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by
  intro K B hB a ha L hL
  obtain ⟨m₁, h₁⟩ := Sandwich.integral_sub B hB.2 a ha.2.1 L hL.2
  obtain ⟨m₂, h₂⟩ := Sandwich.sub_integral B a ha.2.1 L hL.1
  exact ⟨max m₁ m₂, fun n hn => ⟨h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn)⟩⟩
end GlobalTheory.UnitLemma
