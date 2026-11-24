-- Prove2me | solution 1 for GlobalTheory.NatMulIntegerMultiple.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:53.974382+00:00
-- url     : https://prove2.me/submissions/ca37fa14-31df-488c-8ff0-c39f2be1f003

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatMulEqInteger
import Theorems.Thm_GlobalTheory_NatMulIntegerMultiple_exists_nsmul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NatMulIntegerMultiple
open NumberField
namespace GlobalTheory.NatMulIntegerMultiple
theorem _root_.solution : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑L : Set V), ∃ (n : ℕ), n ≠ (0 : ℕ) ∧ n • x ∈ L :=
  fun L => exists_nsmul_mem L
end GlobalTheory.NatMulIntegerMultiple
