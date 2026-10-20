-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.det_matrixNTransposeMatchingMinor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:17:03.264622+00:00
-- url     : https://prove2.me/submissions/5ff1ef46-ef80-42fe-a3ca-12695790d84a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankGlobalMinors.lean:L94-L123
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.det_matrixNTransposeMatchingMinor_ne_zero. The node keeps its source
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
import Theorems.Thm_OAI_SeymourSecondNeighborhood_det_blockSupportedVariables_ne_zero

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankGlobalMinors ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem det_matrixNTransposeMatchingMinor_ne_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C))
    (hM : Bipartite.IsMatching (matrixNTransposeSupport r R C) M) :
    (matrixNTransposeMatchingMinor r R C M).det ≠ 0 := by
  classical
  have hdiag : ∀ e : ↥M, matrixNTransposeSupport r R C e.val.1 e.val.2 :=
    fun e => hM.1 e.val e.property
  change (supportedVariableMatrix (R := ℝ)
    (fun e f : ↥M => matrixNTransposeSupport r R C e.val.1 f.val.2)
    (fun e f : ↥M =>
      (Sum.inr (f.val.2.val.2, e.val.1.val.2) : CoefficientVariables X))).det ≠ 0
  apply det_blockSupportedVariables_ne_zero _ _
    (fun e : ↥M => (Fintype.equivFin X) e.val.1.val.1)
  · exact hdiag
  · intro i j hij
    exact congrArg (Fintype.equivFin X) (hij.1.symm.trans (hdiag j).1)
  · intro i j k l hij hkl hblock hlabel
    have hfirst : i.val.1.val.1 = k.val.1.val.1 :=
      (Fintype.equivFin X).injective hblock
    have hp : (j.val.2.val.2, i.val.1.val.2) =
        (l.val.2.val.2, k.val.1.val.2) := Sum.inr.inj hlabel
    have hlabelFirst := congrArg (fun p : X × X => p.1) hp
    have hlabelSecond := congrArg (fun p : X × X => p.2) hp
    have hrow : i.val.1 = k.val.1 :=
      Subtype.ext (Prod.ext hfirst hlabelSecond)
    have hcolFirst := hij.1.trans (hfirst.trans hkl.1.symm)
    have hcol : j.val.2 = l.val.2 :=
      Subtype.ext (Prod.ext hcolFirst hlabelFirst)
    exact ⟨Subtype.ext (hM.2.1 i.property k.property hrow),
      Subtype.ext (hM.2.2 j.property l.property hcol)⟩

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open scoped Matrix


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.det_matrixNTransposeMatchingMinor_ne_zero := @_root_.OAI.SeymourSecondNeighborhood.Pruning.det_matrixNTransposeMatchingMinor_ne_zero
