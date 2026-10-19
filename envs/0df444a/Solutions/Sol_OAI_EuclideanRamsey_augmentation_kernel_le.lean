-- Prove2me | solution 1 for OAI.EuclideanRamsey.augmentation_kernel_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:44:58.862471+00:00
-- url     : https://prove2.me/submissions/a68d6729-141d-4292-a3d0-1a4c0402c4aa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean:L190-L208
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.augmentation_kernel_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.DerivedFractions ----
namespace OAI

universe uGroup uIndex uColor uPoint

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

namespace EuclideanRamsey
open scoped commutatorElement
variable {G : Type uGroup} [Group G]

end EuclideanRamsey

namespace EuclideanRamsey
variable {X : Type uPoint} {G : Type uGroup} [Group G]
lemma augmentation_kernel_le (x₀ : X) (Q : Subgroup (FreeGroup X)) [Q.Normal]
    (h : ∀ x y,(QuotientGroup.mk' Q) (FreeGroup.of x)=(QuotientGroup.mk' Q) (FreeGroup.of y)) :
    AugKernel X≤Q := by
  let q := QuotientGroup.mk' Q
  let t := q (FreeGroup.of x₀)
  let cy : Multiplicative ℤ →* (FreeGroup X ⧸ Q) :=
    { toFun := fun n => t^(Multiplicative.toAdd n)
      map_one' := by simp
      map_mul' := by intro a b; exact zpow_add t _ _ }
  have he : q=cy.comp (freeAugmentation X) := by
    apply FreeGroup.ext_hom
    intro x
    simpa [cy,freeAugmentation,t,q] using h x x₀
  intro g hg
  apply (QuotientGroup.eq_one_iff _).mp
  change q g=1
  rw [he,MonoidHom.comp_apply]
  change freeAugmentation X g=1 at hg
  rw [hg,map_one]
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


theorem solution.{uPoint} : type_of% @_root_.OAI.EuclideanRamsey.augmentation_kernel_le.{uPoint} := @_root_.OAI.EuclideanRamsey.augmentation_kernel_le.{uPoint}
