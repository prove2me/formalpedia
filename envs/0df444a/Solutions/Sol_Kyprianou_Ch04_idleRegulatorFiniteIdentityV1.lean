-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorFiniteIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:34:17.415139+00:00
-- url     : https://prove2.me/submissions/f090923b-ab1f-4587-9758-73bef4afa60c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorIncrementBoundsV1
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorDerivativeFromDyadicV1
import Theorems.Thm_Kyprianou_Ch04_bvDyadicDeficitZeroAeTimeV1
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorOccupationIntegralV1
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    ∀ᵐ omega ∂P, ∀ T : NNReal,
      ENNReal.ofReal (max w (supX T omega) - w) =
        ENNReal.ofReal L.drift *
          (∫⁻ t in Icc (0 : Real) (T : Real),
            (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume) := by
  classical
  intro supX W
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times L hBV,
    Kyprianou.Ch04.bvDyadicDeficitZeroAeTimeV1 P F L hBV] with omega hm hs
  let f : NNReal → Real := fun t => L.X t omega
  let R : NNReal → Real := fun t => max w (supX t omega)
  have hf (s t : NNReal) (hst : s ≤ t) :
      f t - f s ≤ L.drift * ((t : Real) - (s : Real)) := by
    have h := hm hst
    dsimp [f] at *
    linarith
  obtain ⟨hzero, hdom, hinc, hLip⟩ :=
    Kyprianou.Ch04.idleRegulatorIncrementBoundsV1 f L.drift w hd hw (L.X_zero omega) hf
  have hder := Kyprianou.Ch04.idleRegulatorDerivativeFromDyadicV1
    f R L.drift hd hdom hinc hLip hs
  let Rr : Real → Real := fun t => R t.toNNReal
  have hLipR : LipschitzWith L.drift.toNNReal Rr := by
    simpa [Rr, Function.comp_def] using hLip.comp Real.lipschitzWith_toNNReal
  have hfmeas : Measurable (fun t : Real => f t.toNNReal) :=
    (chat04_levy_joint_time_state_measurable L).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  intro T
  have he := Kyprianou.Ch04.idleRegulatorOccupationIntegralV1 Rr
    (fun t => f t.toNNReal) L.drift (T : Real) hd T.2 hLipR hfmeas hder
  have h0 : Rr 0 = w := by
    simp only [Rr, Real.toNNReal_zero]
    change max w (sSup (f '' Iic (0 : NNReal))) = w
    exact hzero
  rw [h0] at he
  simpa [Rr, f, R, W] using he
