-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:26:20.428502+00:00
-- url     : https://prove2.me/submissions/12a92768-f249-4229-b766-f26b60a78db2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/ExtremalCounting.lean:L53-L68
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalImages
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCompatibility
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ExtremalCounting

-- ---- from OAI.Combinatorics.SecondNeighborhood.ExtremalCounting ----
namespace OAI

namespace SeymourSecondNeighborhood.Extremal

open Pruning

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

theorem exists_maximizing_pair (r : V → V → Prop)
    (admissible : Finset (V × V) → Finset (V × V) → Prop)
    (hex : ∃ P Q, admissible P Q) :
    ∃ P Q, admissible P Q ∧ ∀ P' Q', admissible P' Q' →
      objective r P' Q' ≤ objective r P Q := by
  classical
  let candidates : Finset (Finset (V × V) × Finset (V × V)) :=
    Finset.univ.filter fun p => admissible p.1 p.2
  have hne : candidates.Nonempty := by
    obtain ⟨P, Q, h⟩ := hex
    exact ⟨(P, Q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  obtain ⟨p, hp, hmax⟩ := candidates.exists_max_image
    (fun p => objective r p.1 p.2) hne
  refine ⟨p.1, p.2, (Finset.mem_filter.mp hp).2, ?_⟩
  intro P Q h
  exact hmax (P, Q) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

end

end SeymourSecondNeighborhood.Extremal

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Extremal
open Pruning


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair := @_root_.OAI.SeymourSecondNeighborhood.Extremal.exists_maximizing_pair
