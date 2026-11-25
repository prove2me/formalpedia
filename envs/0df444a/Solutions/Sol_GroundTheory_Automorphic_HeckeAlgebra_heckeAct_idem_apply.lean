-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeAct_idem_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:18.840142+00:00
-- url     : https://prove2.me/submissions/8ac3b8a4-1cde-440e-92c0-40223611797b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mul

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
theorem _root_.solution (g : G) {v : V} (hv : v ∈ fixedVectors ρ K) :
    heckeAct μ ρ (idem μ hKc hKo) (ρ g v) =
      heckeAct μ ρ (idem μ hKc hKo * leftReg μ g (idem μ hKc hKo) : HeckeAlgebra μ) v := by
  have hs := smooth_of_mem_fixedVectors hKo hv
  rw [heckeAct_mul _ _ hs]
  conv_lhs => rw [← heckeAct_idem_of_mem (μ := μ) hKc hKo hv]
  rw [heckeAct_ltrans g (idem μ hKc hKo).mem hs]
  rfl
end GroundTheory.Automorphic.HeckeAlgebra
