-- Prove2me | solution 1 for Kyprianou.Ch04.downwardFirstPassageUndershootLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:03:21.850075+00:00
-- url     : https://prove2.me/submissions/5e35610d-c222-4968-b1ac-bfa5a8f1c86f

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_downwardPassageFiniteProbabilityBV
import Theorems.Thm_Kyprianou_Ch04_downwardPassageJointDeficitTailBV
open MeasureTheory AvramDividend.Classical Kyprianou.Ch04 Filter
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Corollary 4.12 (p. 105), including the conditional deficit distribution. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (hMeanPositive :
      0 < derivWithin L.ψ (Set.Ici (0 : Real)) 0) :
    let tau : Omega → WithTop NNReal := fun omega =>
      Kyprianou.Ch03.firstHittingTime L.X (Set.Iio 0) omega
    let rho : Real :=
      (L.drift - derivWithin L.ψ (Set.Ici (0 : Real)) 0) /
        L.drift
    (P {omega : Omega | tau omega ≠ ⊤}).toReal = rho ∧
    (∀ (finiteTime : Omega → NNReal),
      (∀ omega : Omega, tau omega ≠ ⊤ →
        tau omega = (finiteTime omega : WithTop NNReal)) →
      ∀ x : Real, 0 ≤ x →
        let ruinAndDeficit : Set Omega :=
          {omega : Omega |
            tau omega ≠ ⊤ ∧
              -(L.X (finiteTime omega) omega) ≤ x}
        let integratedTail : Real :=
          ∫ y in Set.Icc (0 : Real) x,
            (L.ν (Set.Iio (-y))).toReal ∂volume
        (P ruinAndDeficit).toReal =
          (1 / L.drift) * integratedTail ∧
        (0 < rho →
          (P ruinAndDeficit).toReal / rho =
            (1 / (L.drift * rho)) * integratedTail)) := by
  dsimp
  constructor
  · exact Kyprianou.Ch04.downwardPassageFiniteProbabilityBV
      P F L hBV hd hMeanPositive
  · intro finiteTime hFinite x hx
    have hJ := Kyprianou.Ch04.downwardPassageJointDeficitTailBV
      P F L hBV hd hMeanPositive finiteTime hFinite x hx
    refine ⟨hJ, ?_⟩
    intro hrho
    rw [hJ]
    have hd0 : (L.drift : ℝ) ≠ 0 := ne_of_gt hd
    have hρ0 :
        ((L.drift - derivWithin L.ψ (Set.Ici (0 : Real)) 0) /
          L.drift) ≠ 0 := ne_of_gt hrho
    field_simp [hd0, hρ0]
    <;> ring
