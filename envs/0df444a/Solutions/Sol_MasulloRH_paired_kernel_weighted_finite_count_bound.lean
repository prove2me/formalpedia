-- Prove2me | solution 1 for MasulloRH.paired_kernel_weighted_finite_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-22T00:47:36.107734+00:00
-- url     : https://prove2.me/submissions/0db4980e-3ddd-4c65-bada-2c8b49c1a2a8

import Mathlib


/-!
The sharp paired compensation constant for the literal resolvents with
real anchors 5/2 and 3, on 0 ≤ beta ≤ 1 and q ≥ 36.  This is a statement
about real variables; no assertion about symmetry of a zero divisor is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Round9KernelProof.Round8SymmetricCompensation

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

end Round9KernelProof.Round8SymmetricCompensation

/-- Paired anchor subtraction is dominated by 169/31 times the paired
resolvent difference.  Adding the same two Poisson terms to both sides
gives the symmetrized kernel-domination inequality. -/
theorem Round9KernelProof.symmetric_shifted_resolvent_compensation
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
  have h := Round9KernelProof.Round8SymmetricCompensation.paired_bound x q hx hq
  have hAnchorLeft : (5/2:ℝ)-β = 2-x := by dsimp [x]; ring
  have hAnchorRight : (5/2:ℝ)-(1-β) = 2+x := by dsimp [x]; ring
  have hOtherLeft : (3:ℝ)-β = 5/2-x := by dsimp [x]; ring
  have hOtherRight : (3:ℝ)-(1-β) = 5/2+x := by dsimp [x]; ring
  rw [hAnchorLeft,hAnchorRight,hOtherLeft,hOtherRight]
  dsimp [Round9KernelProof.Round8SymmetricCompensation.pair] at h
  linarith



/-!
Literal paired resolvent kernel at sigma = 13/8 and compensation 169/31.
The finite-family estimate uses only the stated real strip/height conditions
and nonnegative weights.  It asserts no zero identity or divisor symmetry.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace Round9KernelProof.Round9PairedKernel

noncomputable def poisson (β γ T : ℝ) : ℝ :=
  (13/8-β)/((13/8-β)^2+(γ-T)^2)

noncomputable def kernel (β γ T : ℝ) : ℝ :=
  poisson β γ T - (5/2-β)/((5/2-β)^2+γ^2) +
    (169/31)*((3-β)/((3-β)^2+γ^2)-(5/2-β)/((5/2-β)^2+γ^2))

noncomputable def pairedPoisson (β γ T : ℝ) : ℝ :=
  (poisson β γ T+poisson (1-β) γ T)/2

noncomputable def pairedKernel (β γ T : ℝ) : ℝ :=
  (kernel β γ T+kernel (1-β) γ T)/2

theorem domination (β γ T : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hgap : 36 ≤ γ^2) : pairedPoisson β γ T ≤ pairedKernel β γ T := by
  have h := Round9KernelProof.symmetric_shifted_resolvent_compensation β (γ^2) hβ₀ hβ₁ hgap
  dsimp [pairedPoisson,pairedKernel,kernel]
  linarith

private theorem poisson_nonnegative (β γ T : ℝ) (hβ : β ≤ 1) :
    0 ≤ poisson β γ T := by
  have hpos : 0 < (13/8:ℝ)-β := by linarith
  unfold poisson
  positivity

theorem nonnegative (β γ T : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hgap : 36 ≤ γ^2) : 0 ≤ pairedKernel β γ T := by
  have h₁ := poisson_nonnegative β γ T hβ₁
  have h₂ := poisson_nonnegative (1-β) γ T (by linarith)
  have hp : 0 ≤ pairedPoisson β γ T := by dsimp [pairedPoisson]; linarith
  exact hp.trans (domination β γ T hβ₀ hβ₁ hgap)

private theorem at_one_minimum (x : ℝ) (hx : x^2 ≤ (1/4:ℝ)) :
    (9288/20737:ℝ) ≤
      ((9/8-x)/((9/8-x)^2+1)+(9/8+x)/((9/8+x)^2+1))/2 := by
  let v : ℝ := x^2
  let D : ℝ := ((9/8-x)^2+1)*((9/8+x)^2+1)
  have hv : 0 ≤ v := sq_nonneg x
  have hvu : v ≤ (1/4:ℝ) := hx
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 ≤ 20737*((9/8)*(1+(9/8)^2-v))-9288*D := by
    calc
      _ = (9/8)*(1/4-v)*(8256*v+18415) := by dsimp [D,v]; ring
      _ ≥ 0 := by positivity
  have hid : ((9/8-x)/((9/8-x)^2+1)+(9/8+x)/((9/8+x)^2+1))/2 =
      (9/8)*(1+(9/8)^2-v)/D := by
    have h₁ : (9/8-x)^2+1 ≠ 0 := ne_of_gt (by positivity)
    have h₂ : (9/8+x)^2+1 ≠ 0 := ne_of_gt (by positivity)
    dsimp [D,v]
    field_simp
    <;> ring
  rw [hid]
  apply (le_div_iff₀ hD).2
  nlinarith only [hN]

private theorem at_one_le (a t : ℝ) (ha : 0 < a) (ht : t^2 ≤ 1) :
    a/(a^2+1) ≤ a/(a^2+t^2) := by
  apply (div_le_div_iff₀ (by positivity : 0 < a^2+1)
    (by positivity : 0 < a^2+t^2)).2
  exact mul_le_mul_of_nonneg_left (by linarith) ha.le

theorem poisson_window_response (β γ T : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hwindow : |γ-T| ≤ 1) : (9288/20737:ℝ) ≤ pairedPoisson β γ T := by
  let x : ℝ := β-1/2
  have hx : x^2 ≤ (1/4:ℝ) := by
    have h := mul_nonneg hβ₀ (sub_nonneg.mpr hβ₁)
    dsimp [x]
    nlinarith
  have ht : (γ-T)^2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (γ-T)) hwindow 2
    simpa only [sq_abs,one_pow] using h
  have hc := at_one_minimum x hx
  have hLeft : (13/8:ℝ)-β = 9/8-x := by dsimp [x]; ring
  have hRight : (13/8:ℝ)-(1-β) = 9/8+x := by dsimp [x]; ring
  rw [←hLeft,←hRight] at hc
  have h₁ := at_one_le ((13/8:ℝ)-β) (γ-T) (by linarith) ht
  have h₂ := at_one_le ((13/8:ℝ)-(1-β)) (γ-T) (by linarith) ht
  dsimp [pairedPoisson,poisson]
  linarith only [hc,h₁,h₂]

theorem window_response (β γ T : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hgap : 36 ≤ γ^2) (hwindow : |γ-T| ≤ 1) :
    (9288/20737:ℝ) ≤ pairedKernel β γ T :=
  (poisson_window_response β γ T hβ₀ hβ₁ hwindow).trans
    (domination β γ T hβ₀ hβ₁ hgap)

end Round9KernelProof.Round9PairedKernel

theorem Round9KernelProof.paired_compensated_kernel_window_bound
    (β γ T : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hgap : 36 ≤ γ^2) (hwindow : |γ-T| ≤ 1) :
    (9288/20737:ℝ) ≤
    (((13/8-β)/((13/8-β)^2+(γ-T)^2) - (5/2-β)/((5/2-β)^2+γ^2) +
        (169/31)*((3-β)/((3-β)^2+γ^2)-(5/2-β)/((5/2-β)^2+γ^2))) +
      ((13/8-(1-β))/((13/8-(1-β))^2+(γ-T)^2) -
        (5/2-(1-β))/((5/2-(1-β))^2+γ^2) +
        (169/31)*((3-(1-β))/((3-(1-β))^2+γ^2)-
          (5/2-(1-β))/((5/2-(1-β))^2+γ^2))))/2 := by
  exact Round9KernelProof.Round9PairedKernel.window_response β γ T hβ₀ hβ₁ hgap hwindow

theorem Round9KernelProof.paired_kernel_weighted_finite_count_bound
    {ι : Type*} [Fintype ι] (β γ w : ι → ℝ) (T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hβ : ∀ i, β i ∈ Set.Icc (0:ℝ) 1)
    (hgap : ∀ i, 36 ≤ (γ i)^2) :
    (9288/20737:ℝ) * (Finset.univ.filter (fun i => |γ i-T| ≤ 1)).sum w ≤
      ∑ i, w i *
        ((((13/8-β i)/((13/8-β i)^2+(γ i-T)^2) -
            (5/2-β i)/((5/2-β i)^2+(γ i)^2) +
            (169/31)*((3-β i)/((3-β i)^2+(γ i)^2)-
              (5/2-β i)/((5/2-β i)^2+(γ i)^2))) +
          ((13/8-(1-β i))/((13/8-(1-β i))^2+(γ i-T)^2) -
            (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2) +
            (169/31)*((3-(1-β i))/((3-(1-β i))^2+(γ i)^2)-
              (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2))))/2) := by
  classical
  change (9288/20737:ℝ) * (Finset.univ.filter (fun i => |γ i-T| ≤ 1)).sum w ≤
    ∑ i, w i * Round9KernelProof.Round9PairedKernel.pairedKernel (β i) (γ i) T
  rw [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : |γ i-T| ≤ 1
  · simp only [if_pos hi]
    have h := Round9KernelProof.Round9PairedKernel.window_response (β i) (γ i) T
      (hβ i).1 (hβ i).2 (hgap i) hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (hw i)
  · simp only [if_neg hi,mul_zero]
    exact mul_nonneg (hw i) (Round9KernelProof.Round9PairedKernel.nonnegative
      (β i) (γ i) T (hβ i).1 (hβ i).2 (hgap i))


theorem solution
    {ι : Type*} [Fintype ι] (β γ w : ι → ℝ) (T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hβ : ∀ i, β i ∈ Set.Icc (0:ℝ) 1)
    (hgap : ∀ i, 36 ≤ (γ i)^2) :
    (9288/20737:ℝ) * (Finset.univ.filter (fun i => |γ i-T| ≤ 1)).sum w ≤
      ∑ i, w i *
        ((((13/8-β i)/((13/8-β i)^2+(γ i-T)^2) -
            (5/2-β i)/((5/2-β i)^2+(γ i)^2) +
            (169/31)*((3-β i)/((3-β i)^2+(γ i)^2)-
              (5/2-β i)/((5/2-β i)^2+(γ i)^2))) +
          ((13/8-(1-β i))/((13/8-(1-β i))^2+(γ i-T)^2) -
            (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2) +
            (169/31)*((3-(1-β i))/((3-(1-β i))^2+(γ i)^2)-
              (5/2-(1-β i))/((5/2-(1-β i))^2+(γ i)^2))))/2) := by
  exact Round9KernelProof.paired_kernel_weighted_finite_count_bound β γ w T hw hβ hgap

#print axioms solution
