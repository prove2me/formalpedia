-- Prove2me | solution 1 for GlobalTheory.FlagPts.regFns_le_fracAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:41:53.346534+00:00
-- url     : https://prove2.me/submissions/0fb4f0f9-a396-4e0c-b5f0-f36329a1e0c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TruncMatMemSubalgebra
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
namespace GlobalTheory.FlagPts
theorem _root_.solution [Fintype ι] (b : Frames k V) : regFns k V ≤ fracAlg b :=
  fun f hf => ⟨f, hf, 0, fun g _ => by simp⟩
end GlobalTheory.FlagPts
