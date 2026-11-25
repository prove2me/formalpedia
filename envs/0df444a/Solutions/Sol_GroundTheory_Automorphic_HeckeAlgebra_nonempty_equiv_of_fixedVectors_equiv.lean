-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_of_fixedVectors_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:05.303632+00:00
-- url     : https://prove2.me/submissions/312f54a0-0b8c-42c5-84c8-1ec732afb454

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_nonempty_equiv_quotRep

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
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) [ρ.IsIrreducible]
    [σ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥)
    (e : fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  set I := LinearMap.ker (LinearMap.toSpanSingleton (HeckeAlgebraLevel μ K hKc hKo)
    (fixedVectors ρ K) ⟨v₀, hv₀⟩)
  have hIρ : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔
      heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Subtype.ext_iff]
    rfl
  have hIσ : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔
      heckeAct μ σ (h : HeckeAlgebra μ) (e ⟨v₀, hv₀⟩ : W) = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← e.map_eq_zero_iff, e.map_smul,
      Subtype.ext_iff]
    rfl
  have hw0 : (e ⟨v₀, hv₀⟩ : W) ≠ 0 := fun h =>
    h0 (congrArg Subtype.val (e.map_eq_zero_iff.1 (Subtype.ext h)))
  obtain ⟨A⟩ := nonempty_equiv_quotRep hKc hKo I hρ hv₀ h0 hIρ
  obtain ⟨B⟩ := nonempty_equiv_quotRep hKc hKo I hσ (e ⟨v₀, hv₀⟩).2 hw0 hIσ
  exact ⟨A.symm.trans B⟩
end GroundTheory.Automorphic.HeckeAlgebra
