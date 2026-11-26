-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_shiftedChunk_lattice_integral_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:16:49.088169+00:00
-- url     : https://prove2.me/submissions/828ec607-5ddf-4487-9643-7db9af036fed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_shiftedChunk_lattice_badTimes_countable
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∀ δ : Real,
        (∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} ∂volume) = 0) := by
  intro h hh a b ha hab hoff δ
  -- The set of bad times (positive lattice-restricted charge) is countable.
  have hC := Kyprianou.Ch05.killedPotential_shiftedChunk_lattice_badTimes_countable
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
    h hh a b ha hab hoff δ
  -- A countable set has volume zero.
  have hnull : volume {t : Real | t ∈ Set.Ioc (0 : Real) δ ∧
      P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} ≠ 0} = 0 :=
    hC.measure_zero volume
  -- Hence the integrand vanishes for almost every time.
  have hae : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0 : Real) δ →
      P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} = 0 := by
    refine (ae_iff).mpr (measure_mono_null ?_ hnull)
    intro t ht
    simp only [Set.mem_setOf_eq, _root_.not_imp, ne_eq] at ht ⊢
    exact ht
  -- Transport to the restricted measure and conclude by congruence.
  have hEq : (fun t => P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}})
      =ᵐ[volume.restrict (Set.Ioc (0 : Real) δ)] 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mpr hae
  rw [lintegral_congr_ae hEq]
  simp
