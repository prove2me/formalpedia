-- Prove2me | solution 1 for MazurTransfer.ContinuousFirstCohomologyExactSequence.range_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T02:09:27.292781+00:00
-- url     : https://prove2.me/submissions/3259924f-c5eb-4815-9c54-aebbb9524deb

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a short exact sequence of discrete coefficient groups
is exact at the middle EXISTING continuous H1. Named downstream consumer:
continuous H1 kernel control for the actual ordered norm-character sequences.
No injectivity or surjectivity of the outer H1 maps is asserted.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyKernelLiftData
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoboundaryData

noncomputable section
namespace MazurTransfer.ContinuousH1ExactSequenceProofHelpers20261018
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologyCoefficientMap
open ContinuousFirstCohomologyKernelLift ContinuousFirstCohomologyCoboundary
variable (G M N P : Type) [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [IsTopologicalGroup M] [IsTopologicalGroup N] [IsTopologicalGroup P]
  [DiscreteTopology M] [DiscreteTopology N] [DiscreteTopology P] [ContinuousSMul G N]
variable (i : M →* N) (p : N →* P)
  (hei : ∀ (g : G) (m : M), i (g • m) = g • i m)
  (hep : ∀ (g : G) (n : N), p (g • n) = g • p n)

 theorem map_map_eq_zero (hzero : ∀ m : M, p (i m) = 1) (y : H1 G M) :
    coefficientMap G N P p hep continuous_of_discreteTopology
      (coefficientMap G M N i hei continuous_of_discreteTopology y) = 0 := by
  refine Quotient.inductionOn y ?_
  intro z
  change classMap G P (mapContinuousCocycles G N P p hep continuous_of_discreteTopology
    (mapContinuousCocycles G M N i hei continuous_of_discreteTopology z)) = 0
  have hz : mapContinuousCocycles G N P p hep continuous_of_discreteTopology
      (mapContinuousCocycles G M N i hei continuous_of_discreteTopology z) = 0 := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Additive.toMul.injective
    exact hzero (Additive.toMul (z.val g) : M)
  rw [hz, map_zero]

 theorem exists_lift_of_map_eq_zero (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : ∀ n : N, p n = 1 → ∃ m : M, i m = n)
    (x : H1 G N) (hx : coefficientMap G N P p hep continuous_of_discreteTopology x = 0) :
    ∃ y : H1 G M, coefficientMap G M N i hei continuous_of_discreteTopology y = x := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro z hz
  have hz' := (classMap_eq_zero_iff G P _).mp hz
  obtain ⟨c, hc⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => p (Additive.toMul (z.val g) : N)) hz'
  obtain ⟨b, hb⟩ := hp c
  let w : continuousCocycles G N := z - coboundary G N b
  have hw : ∀ g : G, p (Additive.toMul (w.val g) : N) = 1 := by
    intro g
    have hc' : g • c / c = p (Additive.toMul (z.val g) : N) := hc g
    change p ((Additive.toMul (z.val g) : N) / (g • b / b)) = 1
    rw [map_div, map_div, hep, hb, ← hc']
    simp
  have hwclass : classMap G N w = classMap G N z := by
    change classMap G N (z - coboundary G N b) = classMap G N z
    rw [map_sub, class_coboundary, sub_zero]
  exact ⟨classMap G M (liftCocycle G M N P i hi hei p hk w hw),
    (class_liftCocycle G M N P i hi hei p hk w hw).trans hwclass⟩

end MazurTransfer.ContinuousH1ExactSequenceProofHelpers20261018

open MazurTransfer
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologyCoefficientMap

theorem solution (G M N P : Type) [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [IsTopologicalGroup M] [IsTopologicalGroup N] [IsTopologicalGroup P]
  [DiscreteTopology M] [DiscreteTopology N] [DiscreteTopology P] [ContinuousSMul G N]
(i : M →* N) (p : N →* P)
  (hei : ∀ (g : G) (m : M), i (g • m) = g • i m)
  (hep : ∀ (g : G) (n : N), p (g • n) = g • p n) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : ∀ n : N, p n = 1 ↔ ∃ m : M, i m = n) :
    (coefficientMap G M N i hei continuous_of_discreteTopology).range =
      (coefficientMap G N P p hep continuous_of_discreteTopology).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact MazurTransfer.ContinuousH1ExactSequenceProofHelpers20261018.map_map_eq_zero G M N P i p hei hep
      (fun m => (hexact (i m)).mpr ⟨m, rfl⟩) y
  · intro hx
    exact MazurTransfer.ContinuousH1ExactSequenceProofHelpers20261018.exists_lift_of_map_eq_zero G M N P i p hei hep hi hp
      (fun n hn => (hexact n).mp hn) x hx


#print axioms solution
