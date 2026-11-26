-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineJumpOrdinaryPartialsChainRuleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:42:21.947504+00:00
-- url     : https://prove2.me/submissions/6d2e7fe1-5bcc-467e-b41e-6794ad6f357a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpTelescopingV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_jointContinuousPartialsPositiveTimeV1
import Theorems.Thm_Kyprianou_Ch04_jointContinuousPartialsClosedTimeV1
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Finite affine jump chain rule with the two supplied ordinary partial derivatives. -/
theorem solution (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (hp : ∀ r ∈ S, 0 < r) (hb : ∀ r ∈ S, r ≤ T)
    (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hft : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hfx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    let Y := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0
    let L := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0
    f T (Y T) = f 0 0 + (∫ u in Icc (0 : ℝ) (T : ℝ), ft u (Y u)) +
      d * (∫ u in Icc (0 : ℝ) (T : ℝ), fx u (Y u)) +
      ∑ r ∈ S, (f r (Y r) - f r (L r)) := by
  classical
  let G := fun z : ℝ × ℝ => f z.1 z.2
  let Y := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) ≤ u then j r else 0
  let L := fun u : ℝ => d*u + ∑ r ∈ S, if (r : ℝ) < u then j r else 0
  have hc := Kyprianou.Ch04.jointContinuousPartialsClosedTimeV1 f ft fx ht hx hf hft hfx
  have hτ : StrictMono (fun r : NNReal => (r : ℝ)) := fun _ _ h => h
  have h := Kyprianou.Ch04.bvFiniteJumpTelescopingV1
    (fun r : NNReal => (r : ℝ)) hτ j 0 d G hc S T T.coe_nonneg
      (fun r hr => hp r hr) (fun r hr => hb r hr)
  have hi (v : ℝ × ℝ) : IntervalIntegrable
      (fun u => fderiv ℝ G (u,Y u) v) volume 0 (T : ℝ) := by
    simpa only [zero_add,Y] using
      (Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
        (fun r : NNReal => (r : ℝ)) hτ j 0 d G hc v S T T.coe_nonneg
        (fun r hr => hp r hr) (fun r hr => hb r hr))
  have hv : ((1 : ℝ),d) = (1,0) + d • ((0 : ℝ),1) := by ext <;> simp
  have hsplit : (∫ u in 0..(T : ℝ), fderiv ℝ G (u,Y u) (1,d)) =
      (∫ u in 0..(T : ℝ), fderiv ℝ G (u,Y u) (1,0)) +
      d * (∫ u in 0..(T : ℝ), fderiv ℝ G (u,Y u) (0,1)) := by
    conv_lhs => rw [hv]
    simp only [map_add,map_smul,smul_eq_mul]
    rw [intervalIntegral.integral_add (hi (1,0)) ((hi (0,1)).const_mul d),
      intervalIntegral.integral_const_mul]
  have hI (v : ℝ × ℝ) : (∫ u in 0..(T : ℝ), fderiv ℝ G (u,Y u) v) =
      ∫ u in Icc (0 : ℝ) (T : ℝ), (ft u (Y u) * v.1 + fx u (Y u) * v.2) := by
    rw [intervalIntegral.integral_of_le T.coe_nonneg,integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (u,Y u) v = _
    rw [(Kyprianou.Ch04.jointContinuousPartialsPositiveTimeV1
      f ft fx ht hx hft hfx (u,Y u) hu.1).fderiv]
    simp
  simp only [zero_add] at h
  change f T (Y T) = f 0 0 + (∫ u in 0..(T : ℝ), fderiv ℝ G (u,Y u) (1,d)) +
    ∑ r ∈ S, (f r (Y r) - f r (L r)) at h
  rw [hsplit,hI (1,0),hI (0,1)] at h
  simpa [Y,L,mul_assoc,add_assoc] using h
