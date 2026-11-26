-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_latticeSupport_reverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:52:36.53211+00:00
-- url     : https://prove2.me/submissions/c51fb63e-e17e-4764-af34-8ded40678561
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_offLattice_charge
import Theorems.Thm_Kyprianou_Ch05_killedPotential_apply_nonneg_halfline
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ → d = 0 →
    ∀ h : Real, 0 < h → ∀ q : Real, 0 ≤ q →
      ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
      Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0) := by
  intro hFin hd h hh q hq hU
  by_contra hPi
  have hne : (U q) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 :=
    Kyprianou.Ch05.killedPotential_firstJump_offLattice_charge
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
      hFin h hh hPi q hq
  have hhalf : (U q) (Set.Iio (0 : Real)) = 0 :=
    Kyprianou.Ch05.killedPotential_apply_nonneg_halfline
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential q hq
  have hmeas : MeasurableSet {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := by
    have heq : {z : Real | ∀ n : Int, z ≠ (n : Real) * h} =
        ⋂ n : Int, ({(n : Real) * h} : Set Real)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_singleton_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun n => (measurableSet_singleton _).compl)
  have hres : (U q) ({z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)) = 0 := by
    have hrw := hU
    rwa [Measure.restrict_apply hmeas] at hrw
  have hpart : (U q) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≤
      (U q) ({z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)) +
        (U q) (Set.Iio (0 : Real)) := by
    have hsub : {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ⊆
        ({z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)) ∪
          Set.Iio (0 : Real) := by
      intro z hz
      by_cases hz0 : 0 < z
      · exact Or.inl ⟨hz, hz0⟩
      · have hz0' : z ≠ 0 := by
          have h0 := hz 0
          simpa using h0
        exact Or.inr (lt_of_le_of_ne (not_lt.mp hz0) hz0')
    calc (U q) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≤
          (U q) (({z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)) ∪
            Set.Iio (0 : Real)) := measure_mono hsub
    _ ≤ (U q) ({z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)) +
          (U q) (Set.Iio (0 : Real)) := measure_union_le _ _
  rw [hres, hhalf, add_zero] at hpart
  exact hne (le_antisymm hpart bot_le)
