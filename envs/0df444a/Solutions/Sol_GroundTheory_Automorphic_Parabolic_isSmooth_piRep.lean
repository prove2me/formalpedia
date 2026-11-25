-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_piRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:24.852207+00:00
-- url     : https://prove2.me/submissions/b88ff8cd-5198-4332-87bb-cdc57bc0b5f0

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsSmooth π) (m : ℕ) : IsSmooth (piRep π m) := by
  intro x
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h : ⋂ i, (stabilizerOf π (x i) : Set (GL (Fin n) F)) ∈ 𝓝 (1 : GL (Fin n) F) :=
    Filter.iInter_mem.2 fun i => (hπ (x i)).mem_nhds (one_mem _)
  refine Filter.mem_of_superset h fun g hg => ?_
  rw [SetLike.mem_coe, mem_stabilizerOf]
  funext i
  exact (Set.mem_iInter.1 hg i)
end GroundTheory.Automorphic.Parabolic
