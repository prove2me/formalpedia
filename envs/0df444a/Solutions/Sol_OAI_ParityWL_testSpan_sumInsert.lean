-- Prove2me | solution 1 for OAI.ParityWL.testSpan_sumInsert
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:36:35.860637+00:00
-- url     : https://prove2.me/submissions/4ca218f4-121b-43a7-bfa9-955d301d6c06

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TestAlgebra.lean:L221-L235
-- (upload_full_project.md Phase 4): solution for node OAI.ParityWL.testSpan_sumInsert. The node keeps its source
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

-- ---- from OAI.Combinatorics.ParityLifts.Rerooting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section AddRoot

open scoped Classical

variable {N : Type} (D : RankedTree N)

end AddRoot

section ReRoot

open scoped Classical

variable {r k t : ℕ} (F : RootedTest r t) (ρ : Fin k → Fin r)

end ReRoot

section ForgetCount

open scoped Classical

variable {k t : ℕ} (F : RootedTest (k + 1) t) (i : Fin (k + 1)) (hk : k < t)
variable {V : Type} (G : SimpleGraph V) (x : Fin k → V)

lemma reRootTest_count [Fintype V] :
    (reRootTest F i.succAbove hk).count G x = ∑ y : V, F.count G (i.insertNth y x) := by
  unfold RootedTest.count
  rw [Fintype.card_congr (reRootMapsEquiv F i hk G x), Fintype.card_sigma, Nat.cast_sum]

end ForgetCount

end ParityWL

end OAI

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

lemma testSpan_sumInsert {k t : ℕ} (hk : k < t) (i : Fin (k + 1))
    {f : TuplePair V W (k + 1) → ℚ} (hf : f ∈ testSpan G H (k + 1) t) :
    sumInsertLinear i f ∈ testSpan G H k t := by
  have h : testSpan G H (k + 1) t ≤ (testSpan G H k t).comap (sumInsertLinear i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, rfl⟩
    have he : sumInsertLinear i (testEval G H F) = testEval G H (reRootTest F i.succAbove hk) := by
      funext a
      cases a with
      | inl x => exact (reRootTest_count F i hk G x).symm
      | inr x => exact (reRootTest_count F i hk H x).symm
    change sumInsertLinear i (testEval G H F) ∈ testSpan G H k t
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


theorem solution : type_of% @_root_.OAI.ParityWL.testSpan_sumInsert := @_root_.OAI.ParityWL.testSpan_sumInsert
