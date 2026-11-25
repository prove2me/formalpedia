-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.heckeAct_idem_eq_fixedProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:28.819864+00:00
-- url     : https://prove2.me/submissions/7087b736-11a5-4788-8750-921299bbd89d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
open GroundTheory.Automorphic.HeckeAlgebra
variable (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (hKc : IsCompact (K : Set G))
  (hKo : IsOpen (K : Set G))
variable {μ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution (hρ : IsSmooth ρ) (v : V) :
    heckeAct μ ρ (idem μ hKc hKo) v = fixedProj ρ hρ hKc hKo v := by
  have hw := heckeAct_idem_mem hKc hKo (ρ := ρ) (μ := μ) (hρ v)
  have h1 : (fixedProj ρ hρ hKc hKo (heckeAct μ ρ (idem μ hKc hKo) v) : V) =
      heckeAct μ ρ (idem μ hKc hKo) v := fixedProj_apply_of_mem hρ hKc hKo hw
  rw [← h1]
  congr 1
  refine eq_of_forall_dual fun φ => ?_
  let ψ : Module.Dual ℂ V := φ ∘ₗ fixedProj ρ hρ hKc hKo
  have := dual_heckeAct μ (idem μ hKc hKo).mem (hρ v) ψ
  rw [integral_idem_mul hKc hKo (F := fun g => ψ (ρ g v)) (fun k hk => by
    simp [ψ, fixedProj_apply_act hρ hKc hKo hk])] at this
  simpa [ψ] using this
end GroundTheory.Automorphic.HeckeAlgebra
