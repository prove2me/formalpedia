-- Prove2me | solution 2 for GlobalTheory.SmulMemOfMemSpan.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:45.563159+00:00
-- url     : https://prove2.me/submissions/a2aad257-b735-4183-bd39-ce65acf7a927

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_Imports
import Theorems.Thm_GlobalTheory_SmulMemOfMemSpan_exists_smul_mem_of_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemOfMemSpan
namespace GlobalTheory.SmulMemOfMemSpan
theorem _root_.solution : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv
end GlobalTheory.SmulMemOfMemSpan
