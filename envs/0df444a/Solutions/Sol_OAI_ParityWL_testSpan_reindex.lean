-- Prove2me | solution 1 for OAI.ParityWL.testSpan_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:35:24.111222+00:00
-- url     : https://prove2.me/submissions/5d466391-3ff5-47d9-9b03-c12da6b71758

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean:L188-L207
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.testSpan_reindex. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra

-- ---- from OAI.Combinatorics.ParityLifts.TestAlgebra ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section AtomicTests

open scoped Classical

variable {k t : ℕ}

end AtomicTests

section TestAlgebra

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)

end TestAlgebra

section TestOperations

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma testSpan_reindex {k m t : ℕ} (hm : m ≤ t) (φ : Fin k → Fin m)
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    reindexLinear φ f ∈ testSpan G H m t := by
  have h : testSpan G H k t ≤ (testSpan G H m t).comap (reindexLinear φ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, rfl⟩
    let P := glueTest (fun _ : Unit => F) (fun _ => φ) hm
    have he : reindexLinear φ (testEval G H F) = testEval G H P := by
      funext a
      cases a with
      | inl x =>
        change F.count G (x ∘ φ) = P.count G x
        simp only [P, glueTest_count, Fintype.prod_unique]
      | inr x =>
        change F.count H (x ∘ φ) = P.count H x
        simp only [P, glueTest_count, Fintype.prod_unique]
    change reindexLinear φ (testEval G H F) ∈ testSpan G H m t
    rw [he]
    exact testEval_mem _ _ _
  exact h hf

end TestOperations

end ParityWL

end OAI

-- ---- platform node ----
open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical


theorem solution : type_of% @_root_.OAI.ParityWL.testSpan_reindex := @_root_.OAI.ParityWL.testSpan_reindex
