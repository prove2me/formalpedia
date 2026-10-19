-- Prove2me | solution 1 for MazurTransfer.ContinuousFirstCohomologyTrivialTargetInjection.coefficientMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T01:18:36.535728+00:00
-- url     : https://prove2.me/submissions/b9d76183-ca95-4cba-9c67-00b40c0f8c2d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an injective coefficient map into a trivial action induces
an injective map on continuous H1. Named downstream consumer: inheritance
of good-prime inertia vanishing by actual character-line Kummer lifts.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData

noncomputable section
namespace MazurTransfer.ContinuousH1TrivialTargetInjectionProofHelpers20261019
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologyCoefficientMap
variable (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
  [IsTopologicalGroup M] [IsTopologicalGroup N]
variable (i : M →* N) (hi : Function.Injective i)
  (he : ∀ (g : G) (m : M), i (g • m) = g • i m) (hc : Continuous i)
  (hN : ∀ (g : G) (n : N), g • n = n)
include hi hN

theorem eq_zero_of_map_eq_zero (x : H1 G M)
    (hx : coefficientMap G M N i he hc x = 0) : x = 0 := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro z hz
  have hz' := (classMap_eq_zero_iff G N _).mp hz
  obtain ⟨n, hn⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => i (Additive.toMul (z.val g) : M)) hz'
  have hz0 : z = 0 := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Additive.toMul.injective
    apply hi
    change i (Additive.toMul (z.val g) : M) = i 1
    rw [map_one]
    have hg : g • n / n = i (Additive.toMul (z.val g) : M) := hn g
    rw [← hg, hN]
    simp
  change classMap G M z = 0
  rw [hz0, map_zero]

theorem coefficientMap_injective : Function.Injective (coefficientMap G M N i he hc) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_map_eq_zero G M N i hi he hc hN
  rw [map_sub, hxy, sub_self]

end MazurTransfer.ContinuousH1TrivialTargetInjectionProofHelpers20261019

theorem solution (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
    [IsTopologicalGroup M] [IsTopologicalGroup N]
    (i : M →* N) (hi : Function.Injective i)
    (he : ∀ (g : G) (m : M), i (g • m) = g • i m) (hc : Continuous i)
    (hN : ∀ (g : G) (n : N), g • n = n) :
    Function.Injective (MazurTransfer.ContinuousFirstCohomologyCoefficientMap.coefficientMap G M N i he hc) := by
  exact MazurTransfer.ContinuousH1TrivialTargetInjectionProofHelpers20261019.coefficientMap_injective G M N i hi he hc hN
#print axioms solution
