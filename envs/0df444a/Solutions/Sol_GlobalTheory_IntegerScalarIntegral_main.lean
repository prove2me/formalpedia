-- Prove2me | solution 1 for GlobalTheory.IntegerScalarIntegral.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:23:34.4235+00:00
-- url     : https://prove2.me/submissions/d37e4dbb-e107-4bfb-b8c7-234fed6a6599

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntSmulIntegral
import Theorems.Thm_GlobalTheory_IntegerScalarIntegral_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IntegerScalarIntegral
open NumberField
namespace GlobalTheory.IntegerScalarIntegral
theorem _root_.solution : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y
end GlobalTheory.IntegerScalarIntegral
