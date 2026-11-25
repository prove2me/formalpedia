-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isInvariant_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:25.3735+00:00
-- url     : https://prove2.me/submissions/fa590768-3022-4743-a742-0acf856b1f23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
omit [MeasurableSpace G] [OpensMeasurableSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (v : H) : π.IsInvariant (π.cyclicSubspace v) := by
  refine IsInvariant.topologicalClosure ?_
  intro g x hx
  refine Submodule.span_induction (p := fun x _ => π g x ∈ Submodule.span ℂ _) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, π.map_mul_apply g h v⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx
end GroundTheory.Automorphic.UnitaryRep
