-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialLaplaceFromSemigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:26:03.280557+00:00
-- url     : https://prove2.me/submissions/eb4cbfc1-784f-46fb-ad97-1483cf783e04

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch04_levyJointMeasurableVersionV1
import Theorems.Thm_Kyprianou_Ch05_killedPotential_expNeg_setLintegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The discounted occupation measure of an unkilled subordinator has resolvent Laplace transform when its marginal time-Laplace semigroup is exponential. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (death : Omega → WithTop NNReal)
    (hd : ∀ w, death w = ⊤)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (theta a : Real) (ha : 0 ≤ a)
    (hsem : ∀ t : NNReal, (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) =
      ENNReal.ofReal (Real.exp (-a * (t : Real))))
    (q : Real) (hq : 0 ≤ q) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U q)) =
      (ENNReal.ofReal (q + a))⁻¹ := by
  obtain ⟨Z, hmZ, hZ⟩ := Kyprianou.Ch04.levyJointMeasurableVersionV1 P Y hY.1
  let A : Measure Real := volume.restrict (Set.Ici 0)
  let c : Real → ENNReal := fun t => ENNReal.ofReal (Real.exp (-q*t))
  let T : Real × Omega → Real := fun p => Z p.1.toNNReal p.2
  have hc : Measurable c :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  have hT : Measurable T :=
    hmZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  let M := A.withDensity c
  have hm : U q = Measure.map T (M.prod P) := by
    ext B hB
    rw [Measure.map_apply hT hB, Measure.prod_apply (hT hB)]
    have hsec (t : Real) : P (Prod.mk t ⁻¹' (T ⁻¹' B)) =
        P {w : Omega | (Real.toNNReal t : WithTop NNReal) < death w ∧
          Y (Real.toNNReal t) w ∈ B} := by
      apply measure_congr
      filter_upwards [hZ] with w hw
      apply propext
      change Z t.toNNReal w ∈ B ↔ ((Real.toNNReal t : WithTop NNReal) < death w ∧
        Y (Real.toNNReal t) w ∈ B)
      have htop : (Real.toNNReal t : WithTop NNReal) < ⊤ := by
        first | exact WithTop.coe_lt_top _ | exact WithTop.coe_lt_top
      rw [hw, hd w]
      exact ⟨fun h => ⟨htop, h⟩, fun h => h.2⟩
    rw [(hPotential q hq).2 B hB]
    have hmeas : Measurable (fun t : Real => P (Prod.mk t ⁻¹' (T ⁻¹' B))) :=
      measurable_measure_prodMk_left (hT hB)
    change _ = ∫⁻ t, P (Prod.mk t ⁻¹' (T ⁻¹' B)) ∂(A.withDensity c)
    rw [lintegral_withDensity_eq_lintegral_mul A hc hmeas]
    simp_rw [Pi.mul_apply, hsec]
    rfl
  let f : Real → ENNReal := fun x => ENNReal.ofReal (Real.exp (-theta * x))
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  change (∫⁻ x, f x ∂(U q)) = _
  rw [hm, lintegral_map hf hT]
  rw [lintegral_prod (fun p : Real × Omega => f (T p)) (hf.comp hT).aemeasurable]
  have hinner (t : Real) : (∫⁻ w, f (T (t,w)) ∂P) =
      ENNReal.ofReal (Real.exp (-a * (t.toNNReal : Real))) := by
    calc
      _ = ∫⁻ w, f (Y t.toNNReal w) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hZ] with w hw
        simp [T, hw]
      _ = _ := hsem t.toNNReal
  simp_rw [hinner]
  have hmeas : Measurable (fun t : Real =>
      ENNReal.ofReal (Real.exp (-a * (t.toNNReal : Real)))) := by fun_prop
  change (∫⁻ t, _ ∂(A.withDensity c)) = _
  rw [lintegral_withDensity_eq_lintegral_mul A hc hmeas]
  calc
    _ = ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-(q+a)*t)) ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with t ht
      simp only [Pi.mul_apply, c, Real.coe_toNNReal _ ht,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ = _ := killedPotential_expNeg_setLintegral (q+a) (add_nonneg hq ha)
