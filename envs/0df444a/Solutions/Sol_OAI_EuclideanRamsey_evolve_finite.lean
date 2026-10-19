-- Prove2me | solution 1 for OAI.EuclideanRamsey.evolve_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:12:07.937989+00:00
-- url     : https://prove2.me/submissions/1b5832bd-f686-426a-a40d-d3ac795a9553

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean:L186-L204
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.evolve_finite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging

-- ---- from OAI.Combinatorics.EuclideanRamsey.OrbitAveraging ----
namespace OAI

universe uGroup uAction uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

namespace OrbitWords
variable {letter : X → G} {w : X → G} {m : ℕ}
end OrbitWords

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H]

namespace Evolution
variable {w v u : X → G} {m n k : ℕ}
lemma trans (h : Evolution (H:=H) w m v n) (h' : Evolution (H:=H) v n u k) :
    Evolution (H:=H) w m u k := by
  induction h' with
  | refl => exact h
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average
end Evolution

lemma evolve_finite [Fintype X] (w : X → G) (m : ℕ)
    (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k},Evolution (H:=H) v n u k → ∀ x,Good x v n → Good x u k)
    (improve : ∀ {v n},Evolution (H:=H) w m v n → ∀ x,
      ∃ u k,Evolution (H:=H) v n u k ∧ Good x u k) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,Good x v n := by
  classical
  have aux (t : Finset X) : ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x∈t,Good x v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w,m,.refl _ _,by simp⟩
    | @insert x t hx ih =>
      obtain ⟨v,n,hev,hv⟩ := ih
      obtain ⟨u,k,heu,hu⟩ := improve hev x
      refine ⟨u,k,hev.trans heu,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hu
      · exact preserve heu y (hv y hy)
  simpa using aux Finset.univ

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H] [Fintype X]

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set
open scoped BigOperators


theorem solution.{uGroup,uAction,uPoint} : type_of% @_root_.OAI.EuclideanRamsey.evolve_finite.{uGroup,uAction,uPoint} := @_root_.OAI.EuclideanRamsey.evolve_finite.{uGroup,uAction,uPoint}
