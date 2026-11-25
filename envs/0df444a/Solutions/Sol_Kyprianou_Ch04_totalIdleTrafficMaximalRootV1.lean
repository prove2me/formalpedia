-- Prove2me | solution 1 for Kyprianou.Ch04.totalIdleTrafficMaximalRootV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:04:40.90851+00:00
-- url     : https://prove2.me/submissions/30ff806b-9993-4784-a4c3-d05ec4ca2707

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficPsiSignV1
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_driftpos_eventual_psi_above_no_standing_public
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence3
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    : let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) ∧
    (∀ phi : Real, 0 ≤ phi → L.ψ phi = 0 →
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) →
      (rho > 1 → 0 < phi) ∧ (rho ≤ 1 → phi = 0)) := by
  intro rho
  letI : IsProbabilityMeasure P := L.isProbability
  have hn : ¬ (∀ᵐ omega : Omega ∂P, Antitone (fun t : NNReal => L.X t omega)) := by
    intro hanti
    obtain ⟨theta, htheta, hlarge⟩ :=
      AvramDividend.Classical.p2m81_bv_driftpos_eventual_psi_above_no_standing_public
        L 1 zero_lt_one hd hBV
    have hp := hlarge theta le_rfl
    obtain ⟨hi, he⟩ := L.laplace 1 theta htheta
    have hle : (∫ omega, Real.exp (theta * L.X 1 omega) ∂P) ≤
        ∫ _ : Omega, (1 : Real) ∂P := by
      refine integral_mono_ae hi (integrable_const _) ?_
      filter_upwards [hanti] with omega ho
      have hx : L.X 1 omega ≤ 0 := by
        simpa [L.X_zero] using ho (show (0 : NNReal) ≤ 1 by norm_num)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos htheta hx)
    rw [he] at hle
    have hle' : Real.exp (L.ψ theta) ≤ 1 := by
      simpa [SpectrallyNegativeLevy.ψ] using hle
    linarith [Real.exp_le_one_iff.mp hle']
  refine ⟨hn, ?_⟩
  intro phi hp hz hm
  have he := Kyprianou.Ch03.firstPassageZero_consequence3 P F L hn phi ⟨hp, hz, hm⟩
  have hsign := Kyprianou.Ch04.totalIdleTrafficPsiSignV1 P F L hBV hd
  refine ⟨?_, ?_⟩
  · intro htraffic
    by_contra! h
    have hzero : phi = 0 := le_antisymm h hp
    exact (not_le_of_gt htraffic) (hsign.mpr (he.mp hzero))
  · intro htraffic
    exact he.mpr (hsign.mp htraffic)
