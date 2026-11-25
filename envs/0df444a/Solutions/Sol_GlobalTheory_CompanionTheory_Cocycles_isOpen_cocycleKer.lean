-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Cocycles.isOpen_cocycleKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:43.716435+00:00
-- url     : https://prove2.me/submissions/826741d3-6218-410f-b20f-e21ac948ba47

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteContinuousCrossedHomomorphisms
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Cocycles
namespace GlobalTheory.CompanionTheory.Cocycles
theorem _root_.solution {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by
  have hU : IsOpen ((⋂ v : A.V, (stabilizer A.ρ v : Set G)) ∩ {g | f g = 0}) :=
    (isOpen_iInter_of_finite fun v => IsDiscreteRep.isOpen_stabilizer v).inter (hlc.isOpen_fiber 0)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨Set.mem_iInter.2 fun v => ?_, cocycle_map_one hf⟩) ?_
  · rw [SetLike.mem_coe, mem_stabilizer, map_one]
    rfl
  · rintro g ⟨hg1, hg2⟩
    refine ⟨LinearMap.ext fun v => ?_, hg2⟩
    exact (mem_stabilizer A.ρ v g).1 (Set.mem_iInter.1 hg1 v)
end GlobalTheory.CompanionTheory.Cocycles
