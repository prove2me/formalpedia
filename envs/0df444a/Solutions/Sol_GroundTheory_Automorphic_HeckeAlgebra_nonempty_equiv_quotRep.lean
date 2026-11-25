-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.nonempty_equiv_quotRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:56.324855+00:00
-- url     : https://prove2.me/submissions/da4c8d70-18a1-4013-a223-12589b747c3a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_mul
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeAct_corner
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mem_span_orbit
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_heckeRep_apply


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
theorem _root_.solution (I : Submodule (HeckeAlgebraLevel μ K hKc hKo)
    (HeckeAlgebraLevel μ K hKc hKo)) (hρ : IsSmooth ρ) [ρ.IsIrreducible] {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors ρ K) (h0 : v₀ ≠ 0)
    (hI : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔ heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0) :
    Nonempty ((quotRep hKc hKo I).Equiv ρ) := by
  let Φ := orbitMap (μ := μ) v₀ (hρ v₀)
  have hΦ : ∀ f, Φ f = heckeAct μ ρ f v₀ := fun _ => rfl
  have crit : ∀ x : V, (∀ g, heckeAct μ ρ (idem μ hKc hKo) (ρ g x) = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hle : Submodule.span ℂ (range fun g => ρ g x) ≤
        LinearMap.ker (heckeRep (μ := μ) hρ (idem μ hKc hKo)) :=
      Submodule.span_le.2 (by
        rintro _ ⟨g, rfl⟩
        exact hx g)
    have := hle (mem_span_orbit hx0 v₀)
    rw [LinearMap.mem_ker, heckeRep_apply, heckeAct_idem_of_mem (μ := μ) hKc hKo hv₀] at this
    exact h0 this
  have key : ∀ φ g, heckeAct μ ρ (idem μ hKc hKo) (ρ g (Φ φ)) =
      heckeAct μ ρ (cornerₗ hKc hKo (leftReg μ g φ) : HeckeAlgebra μ) v₀ := by
    intro φ g
    rw [hΦ, heckeAct_ltrans g φ.mem (hρ v₀)]
    change heckeAct μ ρ (idem μ hKc hKo) (heckeAct μ ρ (leftReg μ g φ : HeckeAlgebra μ) v₀) = _
    rw [← heckeAct_mul _ _ (hρ v₀)]
    exact (heckeAct_corner hKc hKo hv₀ _).symm
  have hker : ∀ φ, Φ φ = 0 ↔ φ ∈ heckeKernel hKc hKo I := by
    intro φ
    constructor
    · intro h g
      rw [hI, ← key, h, map_zero]
      exact heckeAct_zero_right (idem μ hKc hKo).mem
    · intro h
      refine crit _ fun g => ?_
      rw [key, ← hI]
      exact h g
  have hint : ∀ g φ, Φ (leftReg μ g φ) = ρ g (Φ φ) := fun g φ =>
    (heckeAct_ltrans g φ.mem (hρ v₀)).symm
  have hsurj : Function.Surjective Φ := by
    intro w
    have hle : Submodule.span ℂ (range fun g => ρ g v₀) ≤ LinearMap.range Φ :=
      Submodule.span_le.2 (by
        rintro _ ⟨g, rfl⟩
        exact ⟨leftReg μ g (idem μ hKc hKo), by
          rw [hint, hΦ, heckeAct_idem_of_mem (μ := μ) hKc hKo hv₀]⟩)
    exact hle (mem_span_orbit h0 w)
  let T : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I →ₗ[ℂ] V :=
    (heckeKernel hKc hKo I).liftQ Φ (fun φ hφ => (hker φ).2 hφ)
  let Tint : Representation.IntertwiningMap (quotRep hKc hKo I) ρ :=
    { toLinearMap := T
      isIntertwining' := fun g => (heckeKernel hKc hKo I).linearMap_qext
        (LinearMap.ext fun φ => hint g φ) }
  refine ⟨Tint.ofBijective ⟨fun y z hyz => ?_, fun w => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
    obtain ⟨ψ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, map_sub,
      sub_eq_zero]
    exact hyz
  · obtain ⟨φ, rfl⟩ := hsurj w
    exact ⟨(heckeKernel hKc hKo I).mkQ φ, rfl⟩
end GroundTheory.Automorphic.HeckeAlgebra
