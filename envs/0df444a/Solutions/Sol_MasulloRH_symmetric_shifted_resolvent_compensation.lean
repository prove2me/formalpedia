-- Prove2me | solution 1 for MasulloRH.symmetric_shifted_resolvent_compensation
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T00:40:41.445975+00:00
-- url     : https://prove2.me/submissions/a35d42d8-d89e-4084-8a58-56c9004e01a9

import Mathlib

/-!
The sharp paired compensation constant for the literal resolvents with
real anchors 5/2 and 3, on 0 ≤ beta ≤ 1 and q ≥ 36.  This is a statement
about real variables; no assertion about symmetry of a zero divisor is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MasulloRH.Round8SymmetricCompensation

private noncomputable def pair (a x q : ℝ) : ℝ :=
  (a-x)/((a-x)^2+q)+(a+x)/((a+x)^2+q)

private theorem pair_identity (a x q : ℝ) (hq : 0 < q) :
    pair a x q = 2*a*(q+a^2-x^2) /
      (((a-x)^2+q)*((a+x)^2+q)) := by
  have h₁ : (a-x)^2+q ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (a+x)^2+q ≠ 0 := ne_of_gt (by positivity)
  unfold pair
  field_simp
  <;> ring

private theorem paired_bound (x q : ℝ) (hx : x^2 ≤ (1/4:ℝ)) (hq : 36 ≤ q) :
    200 * pair 2 x q ≤ 169 * pair (5/2) x q := by
  let v : ℝ := x^2
  let Q : ℝ := q-36
  let D₂ : ℝ := ((2-x)^2+q)*((2+x)^2+q)
  let D₅ : ℝ := ((5/2-x)^2+q)*((5/2+x)^2+q)
  have hv : 0 ≤ v := sq_nonneg x
  have hvu : v ≤ (1/4:ℝ) := hx
  have hQ : 0 ≤ Q := sub_nonneg.mpr hq
  have hq0 : 0 < q := by linarith
  have hD₂ : 0 < D₂ := by dsimp [D₂]; positivity
  have hD₅ : 0 < D₅ := by dsimp [D₅]; positivity
  have hv2 : v^2 ≤ (1/4:ℝ)^2 := pow_le_pow_left₀ hv hvu 2
  have hc₁ : 0 ≤ 6760+1234*v-4*v^2 := by nlinarith
  have hc₂ : 0 ≤ 40616-247*v-4*v^2 := by nlinarith
  have hcert : 0 ≤ 4*Q^3+(4*v+329)*Q^2+
      (6760+1234*v-4*v^2)*Q+v*(40616-247*v-4*v^2) := by positivity
  have hN : 0 ≤ 169*(5*(q+25/4-v))*D₂-200*(4*(q+4-v))*D₅ := by
    calc
      _ = (45/4)*(4*Q^3+(4*v+329)*Q^2+
          (6760+1234*v-4*v^2)*Q+v*(40616-247*v-4*v^2)) := by
        dsimp [D₂,D₅,v,Q]
        ring
      _ ≥ 0 := mul_nonneg (by norm_num) hcert
  rw [pair_identity 2 x q hq0, pair_identity (5/2) x q hq0]
  norm_num only
  change 200*(4*(q+4-v)/D₂) ≤ 169*(5*(q+25/4-v)/D₅)
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact (div_le_div_iff₀ hD₂ hD₅).2 (sub_nonneg.mp hN)

end MasulloRH.Round8SymmetricCompensation

/-- Paired anchor subtraction is dominated by 169/31 times the paired
resolvent difference.  Adding the same two Poisson terms to both sides
gives the symmetrized kernel-domination inequality. -/
theorem solution
    (β q : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hq : 36 ≤ q) :
    (5/2-β)/((5/2-β)^2+q) +
      (5/2-(1-β))/((5/2-(1-β))^2+q) ≤
    (169/31) *
      (((3-β)/((3-β)^2+q) - (5/2-β)/((5/2-β)^2+q)) +
        ((3-(1-β))/((3-(1-β))^2+q) -
          (5/2-(1-β))/((5/2-(1-β))^2+q))) := by
  let x : ℝ := β-1/2
  have hx : x^2 ≤ (1/4:ℝ) := by
    have h := mul_nonneg hβ₀ (sub_nonneg.mpr hβ₁)
    dsimp [x]
    nlinarith
  have h := MasulloRH.Round8SymmetricCompensation.paired_bound x q hx hq
  have hAnchorLeft : (5/2:ℝ)-β = 2-x := by dsimp [x]; ring
  have hAnchorRight : (5/2:ℝ)-(1-β) = 2+x := by dsimp [x]; ring
  have hOtherLeft : (3:ℝ)-β = 5/2-x := by dsimp [x]; ring
  have hOtherRight : (3:ℝ)-(1-β) = 5/2+x := by dsimp [x]; ring
  rw [hAnchorLeft,hAnchorRight,hOtherLeft,hOtherRight]
  dsimp [MasulloRH.Round8SymmetricCompensation.pair] at h
  linarith

#print axioms solution
