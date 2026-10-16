-- Prove2me | solution 1 for OAI.PermanentBorder.support_subset_cube_of_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:38:31.481248+00:00
-- url     : https://prove2.me/submissions/4ce87455-42cc-4b97-9019-71a320b92b3f

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Model.lean:L200-L214
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.support_subset_cube_of_limit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model

-- ---- from OAI.Algebra.Determinantal.Model ----
namespace OAI

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

end PermanentBorder.Polar

namespace PermanentBorder

open Filter
open scoped Topology

end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

theorem support_subset_cube_of_limit {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    p.support ⊆ exponentCube n := by
  classical
  intro d hd
  by_contra hn
  have hz : ∀ j, (P j).coeff d = 0 := by
    intro j
    apply notMem_support_iff.mp
    exact fun hj => hn (hP j hj)
  have ht : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (p.coeff d)) := by
    simpa only [hz] using hp d
  have he : p.coeff d = 0 := (tendsto_nhds_unique tendsto_const_nhds ht).symm
  exact mem_support_iff.mp hd he

end FixedCoefficientSpace

section DeterminantDegree
variable {σ : Type*} [Fintype σ]

end DeterminantDegree

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

end AffineSubstitution
end PermanentBorder

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section ScalarNormalization
variable {σ : Type*} [Fintype σ]

end ScalarNormalization
end PermanentBorder

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder
open MvPolynomial Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.support_subset_cube_of_limit := @_root_.OAI.PermanentBorder.support_subset_cube_of_limit
