-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:49:23.733617+00:00
-- url     : https://prove2.me/submissions/d3535a6d-8d63-435b-81a0-d4218a5cdfc0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/Matching.lean:L89-L113
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching

-- ---- from OAI.Combinatorics.SecondNeighborhood.Matching ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*}

section DecidableEq

variable [DecidableEq L] [DecidableEq R]

omit [DecidableEq R] in
theorem matching_card_le_cover_card {E : L → R → Prop}
    {M : Finset (L × R)} {A : Finset L} {B : Finset R}
    (hM : IsMatching E M) (hC : IsVertexCover E A B) :
    M.card ≤ A.card + B.card := by
  classical
  let ML := M.filter fun e => e.1 ∈ A
  let MR := M.filter fun e => e.1 ∉ A
  have hL : ML.card ≤ A.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he f hf hef
      exact hM.2.1 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  have hR : MR.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      rcases Finset.mem_filter.mp he with ⟨heM, heA⟩
      exact (hC e.1 e.2 (hM.1 e heM)).resolve_left heA
    · intro e he f hf hef
      exact hM.2.2 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hef
  calc
    M.card = ML.card + MR.card :=
      (Finset.card_filter_add_card_filter_not (s := M) (fun e => e.1 ∈ A)).symm
    _ ≤ A.card + B.card := Nat.add_le_add hL hR

end DecidableEq

section Finite

variable [Fintype L] [Fintype R]

end Finite

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card := @_root_.OAI.SeymourSecondNeighborhood.Bipartite.matching_card_le_cover_card
