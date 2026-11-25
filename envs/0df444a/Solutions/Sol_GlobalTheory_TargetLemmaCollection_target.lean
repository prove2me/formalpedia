-- Prove2me | solution 1 for GlobalTheory.TargetLemmaCollection.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:24.641139+00:00
-- url     : https://prove2.me/submissions/d8ddee6a-a26c-479f-9f39-64abefe0f253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsExtraAlt
import Theorems.Thm_GlobalTheory_TargetLemmaCollection_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace GlobalTheory.TargetLemmaCollection
theorem _root_.solution : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
end GlobalTheory.TargetLemmaCollection
