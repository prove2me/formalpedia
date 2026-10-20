-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:48:40.685647+00:00
-- url     : https://prove2.me/submissions/46446b98-ea0e-44be-9b71-2a908bf61916

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/PruningDefinitions.lean:L171-L185
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.PruningDefinitions ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

noncomputable section

theorem conflictFree_iff_disjoint {r : V → V → Prop} {R C : Finset (V × V)} :
    ConflictFree r R C ↔ Disjoint (leftImage r R) (rightImage r C) := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro z hl hr
    obtain ⟨p, hp, hpi⟩ := mem_leftImage.mp hl
    obtain ⟨s, hs, hsj⟩ := mem_rightImage.mp hr
    exact h (p, z.2) hp (z.1, s) hs ⟨hpi, hsj⟩
  · intro h a ha b hb hc
    have hl : (b.1, a.2) ∈ leftImage r R :=
      mem_leftImage.mpr ⟨a.1, by simpa using ha, hc.1⟩
    have hr : (b.1, a.2) ∈ rightImage r C :=
      mem_rightImage.mpr ⟨b.2, by simpa using hb, hc.2⟩
    exact Finset.disjoint_left.mp h hl hr

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint := @_root_.OAI.SeymourSecondNeighborhood.Pruning.conflictFree_iff_disjoint
