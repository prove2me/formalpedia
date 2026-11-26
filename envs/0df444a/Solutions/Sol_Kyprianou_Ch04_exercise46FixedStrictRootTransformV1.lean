-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FixedStrictRootTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:13:17.97128+00:00
-- url     : https://prove2.me/submissions/a5694686-318f-4541-b280-f4e0414c0021

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_upwardFirstPassageLaplaceTransform
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (hnd : ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)))
    (phi : Real) (hphi : 0 < phi) (hroot : L.ψ phi = 0)
    (hmax : ∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) :
    ∀ x : Real, 0 ≤ x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-(0 : Real) *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
      = Real.exp (-phi * x) := by
  obtain ⟨p, hp, hpr, hm, ht⟩ :=
    Kyprianou.Ch03.upwardFirstPassageLaplaceTransform P G L hnd 0 le_rfl
  have he : p = phi := le_antisymm (hmax p hp hpr) (hm phi hphi.le hroot)
  subst p
  intro x hx
  exact ht x hx
    (fun w => (Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0)
    (fun w hw => (WithTop.coe_untop₀_of_ne_top (by simpa using hw)).symm)
