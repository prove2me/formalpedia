-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.isSimpleModule_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:54.45052+00:00
-- url     : https://prove2.me/submissions/4e594c2b-88c0-4e4f-96e1-009504611801

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_corner
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_idem_apply
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mem_span_orbit
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_HeckeAlgebraLevel_coe_smul_fixedVectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, fun x hx y => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    exact ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  · have hx0 : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
    let M : HeckeAlgebra μ →ₗ[ℂ] V :=
      { toFun := fun f => heckeAct μ ρ (idem μ hKc hKo * f : HeckeAlgebra μ) x
        map_add' := fun a b => by
          rw [mul_add, coe_add, heckeAct_add_left (mem _) (mem _) (hρ _)]
        map_smul' := fun c a => by
          simp only [RingHom.id_apply]
          rw [mul_smul_comm, coe_smul, heckeAct_smul_left c (mem _) (hρ _)] }
    let L : V →ₗ[ℂ] V := heckeRep (μ := μ) hρ (idem μ hKc hKo)
    have hspan : Submodule.span ℂ (range fun g => ρ g x) ≤ (LinearMap.range M).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact ⟨leftReg μ g (idem μ hKc hKo), (heckeAct_idem_apply hKc hKo g x.2).symm⟩
    obtain ⟨f, hf⟩ := hspan (mem_span_orbit hx0 (y : V))
    refine ⟨HeckeAlgebraLevel.corner hKc hKo f, Subtype.ext ?_⟩
    rw [LinearMap.toSpanSingleton_apply, HeckeAlgebraLevel.coe_smul_fixedVectors,
      heckeAct_corner hKc hKo x.2]
    refine hf.trans ?_
    exact heckeAct_idem_of_mem (μ := μ) hKc hKo y.2
end GroundTheory.Automorphic.HeckeAlgebra
