-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.contMDiffAt_iff_expG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:45.016341+00:00
-- url     : https://prove2.me/submissions/8c273036-d4f3-4844-904f-0d6d9c431b2f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_chart_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {n : WithTop ℕ∞} {f : G → E'} {g : G} :
    (letI := h.chartedSpace; ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, E') n f g) ↔
      ContDiffAt ℝ n (fun Y : 𝔤 => f (g * h.expG Y)) 0 := by
  let := h.chartedSpace
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  have e1 : (extChartAt 𝓘(ℝ, 𝔤) g) g = 0 := by
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    exact h.chart_self g
  have e2 : f ∘ (extChartAt 𝓘(ℝ, 𝔤) g).symm = fun Y : 𝔤 => f (g * h.expG Y) := by
    funext Y
    simp only [extChartAt, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
      Function.comp_apply, id]
    rfl
  rw [e1, e2, modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ]
end GroundTheory.Automorphic.IsExpLieAlgebra
