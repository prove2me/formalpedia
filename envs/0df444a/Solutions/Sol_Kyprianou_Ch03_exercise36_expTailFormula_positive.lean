-- Prove2me | solution 1 for Kyprianou.Ch03.exercise36_expTailFormula_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:54:54.093229+00:00
-- url     : https://prove2.me/submissions/86d0f16e-5ad0-4e10-879b-4ae0e6a188ce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_strictRunSupIoiPassageEquivV1
import Theorems.Thm_Kyprianou_Ch03_prod_expClock_randomThresholdV1
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch03_firstHittingIoi_eq_correctedUpTime
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_positiveDiscount_strictBarrier
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega OmegaE : Type} [MeasurableSpace Omega] [MeasurableSpace OmegaE]
    (P : Measure Omega) (Q : Measure OmegaE)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : ℝ) (hq : 0 < q) (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {eta : OmegaE | t < e eta}).toReal = Real.exp (-q * (t : ℝ))) :
    ∀ (phi : ℝ), (0 < phi ∧ L.ψ phi = q) →
    (∀ x : ℝ, 0 < x →
      ((P.prod Q) {pair : Omega × OmegaE |
        x < LevyExtrema.SBA.runSup (fun s => L.X s pair.1) (e pair.2)}).toReal =
      Real.exp (-phi * x)) := by
  classical
  intro phi hphi x hx
  have hmax : ∀ theta : ℝ, 0 ≤ theta → L.ψ theta = q → theta ≤ phi := by
    intro theta _ hr
    by_contra! hlt
    have hh := AvramDividend.Classical.levy_psi_root_shifted_increment_lower
      L q phi (theta - phi) hq hphi.1 (sub_pos.mpr hlt) hphi.2
    rw [show phi + (theta - phi) = theta by ring, hr, sub_self] at hh
    exact (not_lt_of_ge hh) (mul_pos (div_pos hq hphi.1) (sub_pos.mpr hlt))
  let tau : Omega → WithTop NNReal := firstHittingTime L.X (Set.Ioi x)
  have htau : Measurable tau := by
    have heq : tau = AvramDividend.Classical.twoSidedExitUpTime L x := by
      funext w
      exact firstHittingIoi_eq_correctedUpTime P F L x hx w
    rw [heq]
    exact AvramDividend.Classical.upperPassage_measurable_from_stopping L x
  let u : Omega → NNReal := fun w => (tau w).untopD 0
  have hfin : ∀ w, tau w ≠ ⊤ → tau w = (u w : WithTop NNReal) := by
    intro w hw
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hw
    have he : tau w = (a : WithTop NNReal) := by first | exact ha | exact ha.symm
    dsimp only [u]
    rw [he, WithTop.untopD_coe]
  have hset : {z : Omega × OmegaE |
      x < LevyExtrema.SBA.runSup (fun s => L.X s z.1) (e z.2)} =
      {z : Omega × OmegaE | tau z.1 < (e z.2 : WithTop NNReal)} := by
    ext z
    exact strictRunSupIoiPassageEquivV1 P F L x hx z.1 (e z.2)
  rw [hset, prod_expClock_randomThresholdV1 P Q tau htau q hq e hExponential]
  exact firstPassageTransform_positiveDiscount_strictBarrier P F L hNotDecreasing
    q hq phi ⟨hphi.1.le, hphi.2, hmax⟩ x hx u
    (fun w hw => hfin w (by simpa [tau, bne_iff_ne] using hw))
