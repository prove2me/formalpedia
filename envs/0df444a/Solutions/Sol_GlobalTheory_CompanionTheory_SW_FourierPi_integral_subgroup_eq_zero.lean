-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FourierPi.integral_subgroup_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.963597+00:00
-- url     : https://prove2.me/submissions/e2d93af1-8f8f-4a86-bb78-8d1efc5121cb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HarrisTaylorCardKilledByIdealEqAbsNormPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FourierPi
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {ψ : R → ℂ}
namespace GlobalTheory.CompanionTheory.SW.FourierPi
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] (A : AddSubgroup R)
    (hA : MeasurableSet (A : Set R)) (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (t a : R) (haA : a ∈ A)
    (hne : ψ (a * t) ≠ 1) : ∫ x in (A : Set R), ψ (x * t) ∂lam = 0 := by
  set f : R → ℂ := (A : Set R).indicator fun x => ψ (x * t) with hf
  have e1 : ∫ x, f x ∂lam = ∫ x in (A : Set R), ψ (x * t) ∂lam := integral_indicator hA
  have e2 : ∀ x, f (x + a) = ψ (a * t) * f x := by
    intro x
    by_cases hx : x ∈ A
    · have hxa : x + a ∈ A := A.add_mem hx haA
      simp only [hf, Set.indicator_of_mem (SetLike.mem_coe.2 hx), Set.indicator_of_mem (SetLike.mem_coe.2 hxa)]
      rw [add_mul, ha, mul_comm]
    · have hxa : x + a ∉ A := fun h => hx (by simpa using A.sub_mem h haA)
      simp only [hf, Set.indicator_of_notMem (show x ∉ (A : Set R) from hx),
        Set.indicator_of_notMem (show x + a ∉ (A : Set R) from hxa), mul_zero]
  have e3 : ∫ x, f x ∂lam = ψ (a * t) * ∫ x, f x ∂lam := by
    calc ∫ x, f x ∂lam = ∫ x, f (x + a) ∂lam := (integral_add_right_eq_self f a).symm
      _ = ∫ x, ψ (a * t) * f x ∂lam := by simp only [e2]
      _ = _ := integral_const_mul _ _
  rw [← e1]
  have e4 : (1 - ψ (a * t)) * ∫ x, f x ∂lam = 0 := by
    rw [sub_mul, one_mul, ← e3, sub_self]
  exact (mul_eq_zero.1 e4).resolve_left (sub_ne_zero.2 (Ne.symm hne))
end GlobalTheory.CompanionTheory.SW.FourierPi
