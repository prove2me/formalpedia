-- Prove2me | solution 1 for GlobalTheory.TargetStatementBis.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:13.481775+00:00
-- url     : https://prove2.me/submissions/ccf348a6-e2a1-4ae6-acf4-e06f8c17cfb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_Imports
import Theorems.Thm_GlobalTheory_TargetStatementBis_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetStatementBis
open NumberField
namespace GlobalTheory.TargetStatementBis
theorem _root_.solution : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v
end GlobalTheory.TargetStatementBis
