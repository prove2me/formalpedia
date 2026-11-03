-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_coupling_polynomial_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:08:41.875623+00:00
-- url     : https://prove2.me/submissions/4ccb43d7-309f-4eaf-a87e-c0abadf6230f

import Mathlib
import Definitions.Def_OAIQ050L014
import Theorems.Thm_OAI_Laughlin_Spin_oscillatorArray_polynomial_s50
import Theorems.Thm_OAI_Laughlin_Spin_source_highest_coupling_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_ScaleLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem spin_fraction_sub_tendsto (B S : ℕ → ℕ) (b : ℝ)
    (hB : Tendsto B atTop atTop) (hS : Tendsto S atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/(S n : ℝ)) atTop (𝓝 b)) (k : ℕ) :
    Tendsto (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) atTop (𝓝 b) := by
  have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hS
  have ht := hfrac.sub (hi.const_mul (k : ℝ))
  have he : (fun n => (B n : ℝ)/(S n : ℝ)-(k : ℝ)*(S n : ℝ)⁻¹) =ᶠ[atTop]
      (fun n => ((B n-k : ℕ) : ℝ)/(S n : ℝ)) := by
    filter_upwards [hB.eventually (eventually_ge_atTop k)] with n hn
    rw [Nat.cast_sub hn]
    ring
  simpa using ht.congr' he

theorem first_spin_fraction_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop)
    (hfrac : Tendsto (fun n => (B n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 b)) :
    Tendsto (fun n => (A n : ℝ)/((A n : ℝ)+B n)) atTop (𝓝 (1-b)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hfrac
  apply ht.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop 1)] with n hn
  have hp : (0 : ℝ) < (A n : ℝ)+B n := by
    have h : (0 : ℝ) < A n := by exact_mod_cast (show 0 < A n by omega)
    positivity
  field_simp
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_LoweringLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem coupled_denominator_scale_tendsto (S : ℕ → ℕ) (hS : Tendsto S atTop atTop)
    (z n : ℕ) :
    Tendsto (fun j => ((((S j-2*z : ℕ) : ℝ)-(n : ℝ))/(S j : ℝ))) atTop (𝓝 1) := by
  have hself : Tendsto (fun j => (S j : ℝ)/(S j : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    apply (tendsto_const_nhds (x := (1 : ℝ))).congr'
    filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
    have hn : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
    rw [div_self hn]
  have ht := spin_fraction_sub_tendsto S S 1 hS hS hself (2*z+n)
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop (2*z+n))] with j hj
  rw [Nat.cast_sub (by omega : 2*z+n ≤ S j),Nat.cast_sub (by omega : 2*z ≤ S j)]
  push_cast
  ring

theorem normalized_ladder_factor_tendsto (C S : ℕ → ℕ) (c : ℝ)
    (hC : Tendsto C atTop atTop) (hS : Tendsto S atTop atTop)
    (hc : Tendsto (fun j => (C j : ℝ)/(S j : ℝ)) atTop (𝓝 c)) (z n k : ℕ) :
    Tendsto (fun j => ladder (C j) k /
      Real.sqrt (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n))) atTop
      (𝓝 (Real.sqrt ((((k : ℝ)+1)*c)/((n : ℝ)+1)))) := by
  have hnum := (spin_fraction_sub_tendsto C S c hC hS hc k).const_mul ((k : ℝ)+1)
  have hden := (coupled_denominator_scale_tendsto S hS z n).const_mul ((n : ℝ)+1)
  have ht := (hnum.div hden (by positivity)).sqrt
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [hS.eventually (eventually_ge_atTop 1)] with j hj
  have hp : (S j : ℝ) ≠ 0 := by exact_mod_cast (show S j ≠ 0 by omega)
  simp only [Pi.div_apply]
  have he : (((k : ℝ)+1)*(((C j-k : ℕ) : ℝ)/(S j : ℝ))) /
      (((n : ℝ)+1)*((((S j-2*z : ℕ) : ℝ)-n)/(S j : ℝ))) =
      (((k : ℝ)+1)*((C j-k : ℕ) : ℝ)) /
        (((n : ℝ)+1)*(((S j-2*z : ℕ) : ℝ)-n)) := by field_simp
  rw [he,Real.sqrt_div (by positivity)]
  rfl

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_ArrayLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

theorem couplingArray_tendsto (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z n p : ℕ) (hp : p ≤ z+n) :
    Tendsto (fun j => couplingArray (A j) (B j) z n p) atTop (𝓝 (oscillatorArray b z n p)) := by
  have hS : Tendsto (fun j => A j+B j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right (A j) (B j)) hA
  induction n generalizing p with
  | zero =>
    exact source_highest_coupling_tendsto_s50 A B b hA hB hb0 hb1 hfrac z p (by omega)
  | succ n ih =>
    let d : ℕ → ℝ := fun j => Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight (A j) (B j) z : ℝ)-n))
    have hfirst : Tendsto (fun j => if p=0 then 0 else
        (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) atTop
        (𝓝 (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*
          oscillatorArray b z n (p-1))) := by
      by_cases hp0 : p=0
      · simp only [hp0,ite_true]; exact tendsto_const_nhds
      · simp only [hp0,ite_false]
        have hf := normalized_ladder_factor_tendsto A (fun j => A j+B j) (1-b) hA hS
          (by simpa only [Nat.cast_add] using first_spin_fraction_tendsto A B b hA hfrac) z n (p-1)
        exact hf.mul (ih (p-1) (by omega))
    have hsecond : Tendsto (fun j => if p ≤ z+n then
        (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) atTop
        (𝓝 (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*
          oscillatorArray b z n p else 0)) := by
      by_cases hpn : p ≤ z+n
      · simp only [hpn,ite_true]
        have hf := normalized_ladder_factor_tendsto B (fun j => A j+B j) b hB hS
          (by simpa only [Nat.cast_add] using hfrac) z n (z+n-p)
        exact hf.mul (ih p hpn)
      · simp only [hpn,ite_false]; exact tendsto_const_nhds
    have ht := hfirst.add hsecond
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun j => by
      change (if p=0 then 0 else (ladder (A j) (p-1)/d j)*couplingArray (A j) (B j) z n (p-1)) +
        (if p ≤ z+n then (ladder (B j) (z+n-p)/d j)*couplingArray (A j) (B j) z n p else 0) = _
      change _ = ((if p=0 then 0 else _) + (if p ≤ z+n then _ else 0))/d j
      split_ifs <;> ring)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem source_coupling_polynomial_tendsto_s50_oai (A B : ℕ → ℕ) (b : ℝ)
    (hA : Tendsto A atTop atTop) (hB : Tendsto B atTop atTop)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hfrac : Tendsto (fun j => (B j : ℝ)/((A j : ℝ)+B j)) atTop (𝓝 b))
    (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    Tendsto (fun j => couplingArray (A j) (B j) z (T-z) p) atTop
      (𝓝 (couplingPolynomialCoefficient (Real.sqrt b) (Real.sqrt (1-b)) z (T-z) p)) := by
  rw [← oscillatorArray_polynomial_s50 b hb0 hb1 z (T-z) p (by omega)]
  exact couplingArray_tendsto A B b hA hB hb0 hb1 hfrac z (T-z) p (by omega)

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_coupling_polynomial_tendsto_s50_oai := @OAI.Laughlin.Spin.source_coupling_polynomial_tendsto_s50_oai
