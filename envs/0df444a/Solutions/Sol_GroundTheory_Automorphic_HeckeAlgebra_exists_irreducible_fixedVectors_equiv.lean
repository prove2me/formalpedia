-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.exists_irreducible_fixedVectors_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:25.743388+00:00
-- url     : https://prove2.me/submissions/5d59f04f-13af-4ae9-9496-02b53d75714d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isSmooth_quotRep
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_isIrreducible_quotRep

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
open HeckeAlgebraLevel
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (M : Type*) [AddCommGroup M]
    [Module (HeckeAlgebraLevel μ K hKc hKo) M] [IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) M] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧
        Nonempty (fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] M) := by
  have hs := (isSimpleModule_iff_toSpanSingleton_surjective (R := HeckeAlgebraLevel μ K hKc hKo)
    (M := M)).1 inferInstance
  haveI := hs.1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  set I := LinearMap.ker (LinearMap.toSpanSingleton (HeckeAlgebraLevel μ K hKc hKo) M m)
  let eM : (HeckeAlgebraLevel μ K hKc hKo ⧸ I) ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] M :=
    LinearMap.quotKerEquivOfSurjective _ (hs.2 m hm)
  have hI : IsCoatom I := isSimpleModule_iff_isCoatom.1 (IsSimpleModule.congr eM)
  exact ⟨_, _, _, quotRep hKc hKo I, isSmooth_quotRep hKc hKo I, isIrreducible_quotRep hKc hKo I hI,
    ⟨(fixedQuotEquiv hKc hKo I).symm.trans eM⟩⟩
end GroundTheory.Automorphic.HeckeAlgebra
