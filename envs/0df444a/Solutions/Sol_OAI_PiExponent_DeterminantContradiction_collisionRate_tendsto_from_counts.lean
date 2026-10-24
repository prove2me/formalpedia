-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collisionRate_tendsto_from_counts
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:18:11.337611+00:00
-- url     : https://prove2.me/submissions/45460f2d-85a5-4899-aa19-2c410be6d85b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu)
    (hrow : Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))))
    (hlow : Tendsto (fun H : Real => (lowIndexCount d H : Real) / H ^ d.m) atTop
      (nhds ((d.base.A : Real) ^ d.m /
        ((d.m.factorial : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i)))) :
    Tendsto (fun H : Real => collisionRate d H) atTop (nhds (collisionLimit d)) := by
  let w : Fin d.m → Real := fun i => MatrixArithmetic.logWeights (finiteDenominators d) i
  let a : Real := (d.K : Real) * (d.base.theta : Real) ^ d.m /
    (((d.m + 1).factorial : Real) * (d.v0 : Real) * ∏ i : Fin d.m, w i)
  let b : Real := (d.base.A : Real) ^ d.m /
    ((d.m.factorial : Real) * ∏ i : Fin d.m, w i)
  have hA : 0 < (d.base.A : Real) := lt_trans d.base.theta_pos d.base.theta_lt_A
  have hw : ∀ i : Fin d.m, 0 < w i := by
    intro i
    have hq : 2 ≤ d.q i.val := (d.approximations i.val).1
    have hq' : (1 : Real) < (d.q i.val : Real) := by
      exact_mod_cast (by omega : 1 < d.q i.val)
    have hlog : 0 < Real.log (d.q i.val : Real) := Real.log_pos hq'
    dsimp [w, MatrixArithmetic.logWeights]
    exact_mod_cast (Nat.ceil_pos.mpr hlog)
  have hprod : 0 < ∏ i : Fin d.m, w i := Finset.prod_pos (fun i hi => hw i)
  have hfactm : 0 < (d.m.factorial : Real) := by positivity
  have hfactsucc : 0 < ((d.m + 1).factorial : Real) := by positivity
  have hAm : 0 < (d.base.A : Real) ^ d.m := by positivity
  have hdenrow : 0 < ((d.m + 1).factorial : Real) * (d.v0 : Real) *
      ∏ i : Fin d.m, w i := by
    exact mul_pos (mul_pos (by positivity) d.v0_pos) hprod
  have hdenlow : 0 < (d.m.factorial : Real) * ∏ i : Fin d.m, w i := by
    exact mul_pos (by positivity) hprod
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hquot : Tendsto (fun H : Real =>
      ((actualRowCount d H : Real) / H ^ (d.m + 1)) /
        ((lowIndexCount d H : Real) / H ^ d.m)) atTop (nhds (a / b)) := by
    have hrow' : Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1))
        atTop (nhds a) := by simpa [a, w] using hrow
    have hlow' : Tendsto (fun H : Real => (lowIndexCount d H : Real) / H ^ d.m)
        atTop (nhds b) := by simpa [b, w] using hlow
    exact hrow'.div hlow' (ne_of_gt hb)
  have hscale : Tendsto (fun H : Real =>
      (collisionConstant * d.base.eta ^ 2) *
        (((actualRowCount d H : Real) / H ^ (d.m + 1)) /
          ((lowIndexCount d H : Real) / H ^ d.m))) atTop
      (nhds ((collisionConstant * d.base.eta ^ 2) * (a / b))) := by
    exact tendsto_const_nhds.mul hquot
  have hevent : ∀ᶠ H : Real in atTop,
      collisionRate d H = (collisionConstant * d.base.eta ^ 2) *
        (((actualRowCount d H : Real) / H ^ (d.m + 1)) /
          ((lowIndexCount d H : Real) / H ^ d.m)) := by
    have hden : ∀ᶠ H : Real in atTop,
        ((lowIndexCount d H : Real) / H ^ d.m) ≠ 0 :=
      hlow.eventually (eventually_ne_nhds (ne_of_gt (by simpa [b, w] using hb)))
    filter_upwards [eventually_ne_atTop (0 : Real), hden] with H hH hdenH
    dsimp [collisionRate, actualRowCount, lowIndexCount]
    dsimp [w] at hdenH
    have hcount : (lowIndexCount d H : Real) ≠ 0 := by
      intro hc
      apply hdenH
      simp [hc]
    rw [pow_succ]
    field_simp [hH, hcount]
    <;> ring
  have hfact : ((d.m + 1).factorial : Real) =
      ((d.m : Real) + 1) * (d.m.factorial : Real) := by
    rw [Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hlimit : (collisionConstant * d.base.eta ^ 2) * (a / b) =
      collisionLimit d := by
    dsimp [a, b, collisionLimit]
    rw [hfact]
    field_simp [ne_of_gt hdenrow, ne_of_gt hdenlow, ne_of_gt hAm,
      ne_of_gt d.v0_pos, ne_of_gt hprod]
  rw [← hlimit]
  exact hscale.congr' (hevent.mono fun H h => h.symm)