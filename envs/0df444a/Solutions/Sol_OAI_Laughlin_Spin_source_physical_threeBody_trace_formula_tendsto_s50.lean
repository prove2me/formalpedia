-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_physical_threeBody_trace_formula_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:42:36.239202+00:00
-- url     : https://prove2.me/submissions/6292e265-d895-4813-b079-da60502e86ce

import Mathlib
import Definitions.Def_OAIQ050L019
import Theorems.Thm_OAI_Laughlin_Spin_physicalThreeBodyTraceFormula_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_ErrorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sourceAlpha_factor (t : ℕ) (e : ℕ × ℕ × ℤ) :
    sourceAlpha t e = (e.2.2 : ℝ)/(10^7) * alphaRadical t e.1 e.2.1 := rfl

theorem real_list_sum_scale {I : Type*} (l : List I) (c : ℝ) (f : I → ℝ) :
    (l.map (fun i => c*f i)).sum = c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_IntegerPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators
open Polynomial

theorem U_general_sum (c z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    U c z T p = ∑ h ∈ Finset.range (p+1),
      (-1 : ℤ)^(z-h) * (z.choose h : ℤ) * ((T-z).choose (p-h) : ℤ) * (c : ℤ)^(p-h) := by
  unfold U
  rw [ite_eq_left ⟨hz,hp⟩,← List.sum_toFinset _ (List.nodup_range.filter _)]
  simp only [List.toFinset_filter,List.toFinset_range]
  apply Finset.sum_subset
  · intro h hh
    simp only [Finset.mem_filter,Finset.mem_range] at hh ⊢
    omega
  · intro h hh hn
    simp only [Finset.mem_range,Finset.mem_filter,decide_eq_true_eq,not_and] at hh hn
    by_cases hhz : h ≤ z
    · have hbound : ¬ p+z ≤ T+h := hn (by omega)
      rw [Nat.choose_eq_zero_of_lt (by omega : T-z < p-h)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : z < h)]
      simp

theorem weightedIntegerCouplingPolynomial_coeff (c z n p : ℕ) (hp : p ≤ z+n) :
    (weightedIntegerCouplingPolynomial c z n).coeff p = U c z (z+n) p := by
  rw [U_general_sum c z (z+n) p (by omega) hp]
  simp only [Nat.add_sub_cancel_left]
  unfold weightedIntegerCouplingPolynomial
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro h hh
  have hneg : (Polynomial.X-1 : Polynomial ℤ) = Polynomial.X+C (-1) := by simp [sub_eq_add_neg]
  rw [hneg,coeff_X_add_C_pow]
  rw [show (C (c : ℤ)*Polynomial.X+1 : Polynomial ℤ)^n = ((Polynomial.X+1)^n).comp (C (c : ℤ)*Polynomial.X) by simp]
  rw [comp_C_mul_X_coeff]
  rw [show (Polynomial.X+1 : Polynomial ℤ) = Polynomial.X+C 1 by simp,coeff_X_add_C_pow]
  simp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_PolynomialCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Polynomial

theorem threeBody_scaled_polynomial (u w : ℝ) (hw : w^2=2) (hw0 : w ≠ 0) (z n : ℕ) :
    couplingPolynomial u (w*u) z n = C (u^(z+n)*w^z) *
      ((Certificate.weightedIntegerCouplingPolynomial 2 z n).map (Int.castRingHom ℝ)).comp (C w⁻¹*X) := by
  have h2 : (2 : ℝ)*w⁻¹=w := by
    field_simp
    nlinarith only [hw]
  simp only [Certificate.weightedIntegerCouplingPolynomial,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,Polynomial.map_C,
    Int.coe_castRingHom,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,Polynomial.add_comp,
    Polynomial.X_comp,Polynomial.C_comp,Polynomial.one_comp]
  norm_num only [Nat.cast_ofNat,Int.cast_natCast]
  rw [show C (2 : ℝ)*(C w⁻¹*X) = C w*X by rw [← mul_assoc,← C_mul,h2]]
  have he : C u*X-C (w*u) = C (u*w)*(C w⁻¹*X-1) := by
    have hc : u*w*w⁻¹=u := by field_simp
    simp only [mul_sub,← mul_assoc,← C_mul,mul_one,hc]
    rw [mul_comm w u]
  have hf : C (w*u)*X+C u = C u*(C w*X+1) := by
    simp only [mul_add,← mul_assoc,← C_mul,mul_one]
    rw [mul_comm w u]
  unfold couplingPolynomial
  rw [he,hf,mul_pow,mul_pow,← C_pow,← C_pow]
  simp only [pow_add,mul_pow,C_mul]
  ring

theorem threeBody_polynomialCoefficient_factorial (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * (Real.sqrt (1/3))^T *
      (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  have hs : Real.sqrt (2/3) = Real.sqrt 2 * Real.sqrt (1/3) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hT : z+(T-z)=T := by omega
  unfold couplingPolynomialCoefficient
  rw [hs,threeBody_scaled_polynomial _ _ (Real.sq_sqrt (by norm_num)) (by positivity),
    coeff_C_mul,comp_C_mul_X_coeff,coeff_map,
    Certificate.weightedIntegerCouplingPolynomial_coeff 2 z (T-z) p (by omega)]
  simp only [Int.coe_castRingHom,hT,monomialNormFactor,inv_pow]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem threeBodyRadical_factorial (z T p : ℕ) :
    threeBodyRadical z T p =
      (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z)) := by
  let a := (Real.sqrt (1/3))^T * (Real.sqrt 2)^z / (Real.sqrt 2)^p *
      sqrtFactorial p * sqrtFactorial (T-p) / (sqrtFactorial z*sqrtFactorial (T-z))
  have ha : 0 ≤ a := by dsimp [a]; unfold sqrtFactorial; positivity
  have hs : a^2 = (2 : ℝ)^((z : ℤ)-p) *
    ((p.factorial : ℝ)*((T-p).factorial : ℝ) /
      ((3 : ℝ)^T * (z.factorial : ℝ)*((T-z).factorial : ℝ))) := by
    dsimp [a]
    simp only [div_pow,mul_pow,sqrtFactorial]
    have hr (c : ℝ) (hc : 0 ≤ c) (n : ℕ) : (Real.sqrt c ^ n)^2 = c^n := by
      rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt hc]
    rw [hr _ (by norm_num),hr _ (by norm_num),hr _ (by norm_num)]
    simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_natCast,div_pow,one_pow]
    ring
  change Real.sqrt _ = a
  rw [← hs,Real.sqrt_sq ha]

theorem source_threeBody_radical_coefficient (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    couplingPolynomialCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p =
      (Certificate.U 2 z T p : ℝ) * threeBodyRadical z T p := by
  rw [threeBody_polynomialCoefficient_factorial z T p hz hp,threeBodyRadical_factorial]
  ring

theorem threeBody_alpha_radical_cancel (z T t p j : ℕ) (hT : p+j=T) :
    alphaRadical t p j * threeBodyRadical z T p = threeBodyRadical z T t := by
  have hj : T-p=j := by omega
  have he : ((p : ℤ)-t)+((z : ℤ)-p)=(z : ℤ)-t := by omega
  have hs : (alphaRadical t p j * threeBodyRadical z T p)^2 = (threeBodyRadical z T t)^2 := by
    simp only [alphaRadical,threeBodyRadical,mul_pow]
    repeat rw [Real.sq_sqrt (by positivity)]
    rw [hT,hj]
    calc
      _ = ((2 : ℝ)^((p : ℤ)-t)*(2 : ℝ)^((z : ℤ)-p)) *
        ((t.factorial : ℝ)*(T-t).factorial/(3^T*z.factorial*(T-z).factorial)) := by field_simp
      _ = _ := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),he]
  have hl : 0 ≤ alphaRadical t p j * threeBodyRadical z T p := by
    unfold alphaRadical threeBodyRadical; positivity
  have hr : 0 ≤ threeBodyRadical z T t := Real.sqrt_nonneg _
  nlinarith only [hs,hl,hr]

theorem threeBodyRadical_sq_choose (z T p : ℕ) (hz : z ≤ T) (hp : p ≤ T) :
    (threeBodyRadical z T p)^2 =
      (2 : ℝ)^z * (T.choose z : ℝ) / ((3 : ℝ)^T * (2 : ℝ)^p * (T.choose p : ℝ)) := by
  have hc (k : ℕ) (hk : k ≤ T) : (T.choose k : ℝ) * (k.factorial : ℝ) * ((T-k).factorial : ℝ) = T.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hcp : (T.choose p : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.choose_pos hp))
  unfold threeBodyRadical
  rw [Real.sq_sqrt (by positivity),zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  apply (eq_div_iff (by positivity : (3 : ℝ)^T*2^p*(T.choose p : ℝ) ≠ 0)).mpr
  have hzfac := hc z hz
  have hpfac := hc p hp
  field_simp
  nlinarith only [hzfac,hpfac]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

 theorem threeBodyInner_certificate (z T t : ℕ) (hz : z ≤ T)
    (entries : List (ℕ × ℕ × ℤ)) :
    threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T t entries =
      (threeBodyRadical z T t / 10^7) * (Certificate.X entries z T : ℝ) := by
  induction entries with
  | nil => simp [threeBodyInner,Certificate.X]
  | cons e es ih =>
    simp only [threeBodyInner,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    change _ = (threeBodyRadical z T t/10^7) *
      (((if e.1+e.2.1=T then e.2.2*Certificate.U 2 z T e.1 else 0)+Certificate.X es z T : ℤ) : ℝ)
    rw [Int.cast_add]
    by_cases he : e.1+e.2.1=T
    · rw [ite_eq_left he,ite_eq_left he,sourceAlpha_factor,
        source_threeBody_radical_coefficient z T e.1 hz (by omega)]
      simp only [Int.cast_mul]
      have hc := threeBody_alpha_radical_cancel z T t e.1 e.2.1 he
      calc
        _ = ((e.2.2 : ℝ)*(Certificate.U 2 z T e.1 : ℝ)/10^7) *
            (alphaRadical t e.1 e.2.1 * threeBodyRadical z T e.1) +
            threeBodyRadical z T t/10^7 * (Certificate.X es z T : ℝ) := by ring
        _ = _ := by rw [hc]; ring
    · simp [he]

theorem threeBodyLevel_certificate (z T : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (hz : z ≤ T) (ht : row.1 ≤ T) :
    (let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
      (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2) =
      (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ) := by
  dsimp only
  rw [threeBodyInner_certificate z T row.1 hz,
    source_threeBody_radical_coefficient z T row.1 hz ht]
  calc
    _ = (1/(10^14) : ℝ)*(threeBodyRadical z T row.1)^2 * (Certificate.X row.2.2 z T : ℝ) *
        ((Certificate.X row.2.2 z T : ℝ)+2*(row.2.1 : ℝ)*(Certificate.U 2 z T row.1 : ℝ)) := by ring
    _ = _ := by
      rw [threeBodyRadical_sq_choose z T row.1 hz ht]
      unfold rationalThreeBodyLevel
      push_cast
      ring

theorem source_threeBody_trace_certificate_identity (z : ℕ) :
    limitThreeBodyTraceFormula z = (Certificate.e z : ℝ) := by
  unfold limitThreeBodyTraceFormula threeBodyTraceFormula
  have he : Certificate.rows.map (fun row =>
      (((List.range 16).filter (fun T => max z row.1 ≤ T)).map (fun T =>
      let a := threeBodyInner (fun z T p => couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) p) z T row.1 row.2.2;
      2*((row.2.1 : ℝ)/10^7)*couplingPolynomialCoefficient
        (Real.sqrt (1/3)) (Real.sqrt (2/3)) z (T-z) row.1*a+a^2)).sum) =
      Certificate.rows.map (fun row => (((List.range 16).filter (fun T => max z row.1 ≤ T)).map
        (fun T => (1/(10^14) : ℝ)*(rationalThreeBodyLevel z T row : ℝ))).sum) := by
    apply List.map_congr_left; intro row hrow
    apply congrArg List.sum
    apply List.map_congr_left; intro T hT
    simp only [List.mem_filter,decide_eq_true_eq,max_le_iff] at hT
    exact threeBodyLevel_certificate z T row hT.2.1 hT.2.2
  rw [he]
  simp_rw [real_list_sum_scale]
  unfold Certificate.e rationalThreeBodyLevel
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  simp only [List.map_map,Function.comp_def]
  push_cast
  ring

 theorem source_physical_threeBody_trace_formula_tendsto_s50_oai (z : ℕ) :
    Filter.Tendsto (fun Q => physicalThreeBodyTraceFormula Q z) Filter.atTop
      (nhds (Certificate.e z : ℝ)) := by
  rw [← source_threeBody_trace_certificate_identity]
  exact physicalThreeBodyTraceFormula_tendsto_s50 z

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_physical_threeBody_trace_formula_tendsto_s50_oai := @OAI.Laughlin.Spin.source_physical_threeBody_trace_formula_tendsto_s50_oai
