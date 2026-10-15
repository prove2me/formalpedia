-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.reindex_language
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:14:49.178999+00:00
-- url     : https://prove2.me/submissions/57126de8-fe92-4d12-8fb7-ad8247961cf6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean:L29-L44
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.reindex_language. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace TwoNFA

theorem reindex_language {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') :
    (A.reindex e).language = A.language := by
  ext w
  constructor
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e.symm q, p), haccept, ?_⟩
    have h := hrun.lift (fun c : Q' × Fin (w.length + 2) => (e.symm c.1, c.2))
      (p := fun c d => (c, d) ∈ A.step w) (fun _ _ h => h)
    simpa only [Function.onFun, reindex, relStar, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using h
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e q, p), ?_, ?_⟩
    · simpa only [reindex, Set.mem_preimage, Equiv.symm_apply_apply] using haccept
    · exact hrun.lift (fun c : Q × Fin (w.length + 2) => (e c.1, c.2))
        (fun c d h => by
          simpa only [Function.onFun, step, reindex, Set.mem_ofPred_eq,
            Equiv.symm_apply_apply] using h)

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.reindex_language := @_root_.OAI.TwoWayComplementation.TwoNFA.reindex_language
