-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.iSup_range_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:51.786578+00:00
-- url     : https://prove2.me/submissions/fa3fd758-8e7e-43d7-a4ec-b09e92b5a8d0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (s : Finset (Representation.IntertwiningMap π ρ))
    (g : GL (Fin n) F) {y : U}
    (hy : y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) :
    ρ g y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap := by
  have hle : (⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) ≤
      (⨆ t ∈ s, LinearMap.range
        (t : Representation.IntertwiningMap π ρ).toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_comap, Representation.IntertwiningMap.toLinearMap_apply,
      ← Representation.IntertwiningMap.isIntertwining]
    exact (le_iSup₂ (f := fun t (_ : t ∈ s) =>
      LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap) t ht) ⟨π g x, rfl⟩
  exact hle hy
end GroundTheory.Automorphic.Parabolic
