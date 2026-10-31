-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.exact_four
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:20:05.503483+00:00
-- url     : https://prove2.me/submissions/81d2ed2b-236a-4011-ad59-a1ace708b549

import Mathlib
import Definitions.Def_OAIQ030L001
import Definitions.Def_OAIQ030L035
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate10_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate11_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate12_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate13_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate14_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate15_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate16_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate17_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate18_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate19_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate20_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate21_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate22_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate23_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate7_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate8_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate9_certificate
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_fourCertificate_of_tables

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

lemma RowEntry.balance {t : Fin 8} (a : RowEntry t) :
    t.val+a.output.val = a.val.1.val+a.val.2.val := by
  dsimp [RowEntry.output]; have := a.property; omega

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Polynomial
open Polynomial

lemma rootFactorial_pos (n : ℕ) : 0 < rootFactorial n :=
  Real.sqrt_pos.mpr (by exact_mod_cast n.factorial_pos)
lemma rootFactorial_ne_zero (n : ℕ) : rootFactorial n ≠ 0 := (rootFactorial_pos n).ne'

lemma monomialWeight_roots (T p : ℕ) : monomialWeight T p = rootFactorial p * rootFactorial (T-p) :=
  Real.sqrt_mul (by positivity) _

lemma integerCoupling_coeff (c z l p : ℕ) :
    (integerCoupling c z l).coeff p =
      ∑ h ∈ Finset.range (p+1), (-1:ℚ)^(z-h) * (z.choose h) *
        (l.choose (p-h)) * (c:ℚ)^(p-h) := by
  have h₁ (h : ℕ) : ((X-1:ℚ[X])^z).coeff h = (-1:ℚ)^(z-h) * (z.choose h) := by
    simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-1:ℚ) z h
  have h₂ (h : ℕ) : ((C (c:ℚ)*X+1 : ℚ[X])^l).coeff h = (l.choose h : ℚ) * (c:ℚ)^h := by
    have he : ((X+1:ℚ[X])^l).comp (C (c:ℚ)*X) = (C (c:ℚ)*X+1)^l := by simp
    rw [← he,comp_C_mul_X_coeff,coeff_X_add_one_pow]
  simp only [integerCoupling,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,h₁,h₂]
  apply Finset.sum_congr rfl
  intro h hh
  ring

lemma uCoefficient_eq_coeff {z T : ℕ} (hz : z ≤ T) (c p : ℕ) :
    uCoefficient c z T p = (integerCoupling c z (T-z)).coeff p := by
  rw [uCoefficient,ite_eq_left hz,integerCoupling_coeff]

lemma couplingPolynomial_equal (a : ℝ) (z l : ℕ) :
    couplingPolynomial a a z l =
      C (a^(z+l)/(rootFactorial z * rootFactorial l)) *
        (integerCoupling 1 z l).map (algebraMap ℚ ℝ) := by
  have ha : C a * X - C a = C a * (X-1) := by ring
  have hb : C a * X + C a = C a * (X+1) := by ring
  have he : (integerCoupling 1 z l).map (algebraMap ℚ ℝ) = (X-1)^z*(X+1)^l := by
    simp [integerCoupling]
  rw [he]
  have hc : a^(z+l)/(rootFactorial z*rootFactorial l) =
      (1/(rootFactorial z*rootFactorial l))* a^z * a^l := by rw [pow_add]; ring
  rw [hc]
  simp only [couplingPolynomial,ha,hb,mul_pow,C_mul,C_pow,rootFactorial]
  ring

lemma balancedCouplingCoefficient_rational {z T : ℕ} (hz : z ≤ T) (p : ℕ) :
    balancedCouplingCoefficient z T p = (uCoefficient 1 z T p : ℝ) *
      (rootFactorial p * rootFactorial (T-p)) /
        ((Real.sqrt 2)^T * rootFactorial z * rootFactorial (T-z)) := by
  rw [balancedCouplingCoefficient,ite_eq_left hz,couplingPolynomial_equal,
    coeff_C_mul,coeff_map,monomialWeight_roots,uCoefficient_eq_coeff hz,
    Nat.add_sub_of_le hz]
  change _ = (algebraMap ℚ ℝ _) * _ / _
  simp only [one_div,inv_pow]
  ring

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma sqrt_natpow_sq {x : ℝ} (h : 0 ≤ x) (n : ℕ) : (Real.sqrt x ^ n)^2 = x^n := by
  rw [← pow_mul,mul_comm n 2,pow_mul,Real.sq_sqrt h]

lemma sum_fibers_multiply {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f : α → S) (g : β → S) :
    (∑ i, (∑ a, if o a=i then f a else 0)*g i) = ∑ a, f a*g (o a) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Coefficients. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma two_pow_odd_sqrt {r : ℕ} (hr : Odd r) :
    (2:ℝ)^((r+1)/2) = Real.sqrt 2 ^ (r+1) := by
  have he : 2*((r+1)/2) = r+1 := by obtain ⟨k,hk⟩ := hr; omega
  calc
    (2:ℝ)^((r+1)/2) = (Real.sqrt 2 ^ 2)^((r+1)/2) := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    _ = Real.sqrt 2^(r+1) := by rw [← pow_mul,he]

lemma coupling_exponent_identity {p j k T r : ℕ} (ht : p+j+k=T) (hr : r ≤ j+k)
    (ho : Odd r) :
    Real.sqrt 2 * (2:ℝ)^T = (2:ℝ)^((r+1)/2) * Real.sqrt 2 ^ p *
      Real.sqrt 2 ^ (j+k) * Real.sqrt 2 ^ (T-r) := by
  rw [two_pow_odd_sqrt ho]
  have hpow : (2:ℝ)^T = Real.sqrt 2^(2*T) := by
    rw [pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hpow,← pow_add,← pow_add,← pow_add,← pow_succ']
  congr 1
  omega

lemma fourWeightCoefficientStar_rational {D r : ℕ} (hD : r ≤ D) (ho : Odd r)
    (T p j k : ℕ) :
    fourWeightCoefficientStar D T r p j k =
      (vCoefficient D T r p j k : ℝ) * (2:ℝ)^((r+1)/2) * Real.sqrt 2 ^ p *
        rootFactorial p * rootFactorial j * rootFactorial k * copyNormalization D r /
        ((2:ℝ)^T * rootFactorial (T-D)) := by
  by_cases hT : D ≤ T
  · by_cases ht : r ≤ j+k ∧ p+j+k=T
    · have hr : D-r ≤ T-r := Nat.sub_le_sub_right hT r
      have he₁ : j+k-j=k := by omega
      have he₂ : T-r-p=j+k-r := by omega
      have he₃ : T-r-(D-r)=T-D := by omega
      rw [fourWeightCoefficientStar,ite_eq_left hT,fourBodyCoefficientStar,ite_eq_left ht,
        balancedCouplingCoefficient_rational ht.1,balancedCouplingCoefficient_rational hr,
        he₁,he₂,he₃,vCoefficient,ite_eq_left ⟨hT,ht.1,ht.2⟩]
      push_cast
      unfold copyNormalization
      have he := coupling_exponent_identity ht.2 ht.1 ho
      field_simp [rootFactorial_ne_zero,
        Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
      linear_combination
        (uCoefficient 1 r (j+k) j : ℝ) * (uCoefficient 1 (D-r) (T-r) p : ℝ) * he
    · simp only [fourWeightCoefficientStar,ite_eq_left hT,fourBodyCoefficientStar,ite_eq_right ht]
      have hn : ¬ (D ≤ T ∧ r ≤ j+k ∧ p+j+k=T) := by tauto
      simp only [vCoefficient,ite_eq_right hn,Rat.cast_zero,zero_mul,zero_div]
  · have hn : ¬ (D ≤ T ∧ r ≤ j+k ∧ p+j+k=T) := by tauto
    simp [fourWeightCoefficientStar,hT,vCoefficient]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalExterior
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Exterior. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma word_empty (n : ℕ) (js : List (Fin n)) (x : Hilbert n) :
    word js x ∅ = (wordSign js : ℂ) * x js.toFinset := by
  induction js generalizing x with
  | nil => simp [wordSign,word]
  | cons j js ih =>
    rw [word_cons,Module.End.mul_apply,ih]
    by_cases h : j ∈ js
    · simp [wordSign,h,transition_apply,List.mem_toFinset]
    · simp only [wordSign,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,
        transition_apply,List.mem_toFinset,h,decide_false,ite_true,flip_of_not_mem
          (show j ∉ js.toFinset by simpa using h),List.toFinset_cons,sign,ite_false]
      ring

lemma word_adjoint_vacuum {n : ℕ} (js : List (Fin n)) :
    (word js).adjoint (vacuum n) = (wordSign js : ℂ) • EuclideanSpace.single js.toFinset 1 := by
  apply ext_inner_right ℂ
  intro x
  simp only [LinearMap.adjoint_inner_left,inner_vacuum_left,word_empty,inner_smul_left,
    EuclideanSpace.inner_single_left,map_ratCast]
  simp

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma limitingPair_roots {p x y : ℕ} (h : x+y=p+1) :
    limitingExteriorPairCoefficient p x y = ((x:ℝ)-(y:ℝ))*rootFactorial p /
      (Real.sqrt 2^p*rootFactorial x*rootFactorial y) := by
  have he : Real.sqrt ((2:ℝ)^p) = Real.sqrt 2^p :=
    (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr (sqrt_natpow_sq (by norm_num) p).symm
  unfold limitingExteriorPairCoefficient
  rw [ite_eq_left h,Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2^p * x.factorial),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2^p),he]
  dsimp [rootFactorial]
  ring

lemma four_pair_normalization {D : ℕ} (r : FourCopy D) (a : FourTerm D) :
    fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) *
      limitingExteriorPairCoefficient (fourTermP a) (fourTermX a) (fourTermY a) =
      copyNormalization D r.val.val * (fourTermCoefficient D r.val.val a:ℝ) /
        (rootFactorial (fourTermX a)*rootFactorial (fourTermY a)*
          rootFactorial (fourTermJ a)*rootFactorial (fourTermK a)) := by
  rw [← show fourWeightCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) =
      fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) by
      simp [fourWeightCoefficientStar]]
  rw [fourWeightCoefficientStar_rational (Nat.le_of_lt_succ r.val.isLt) r.property,
    limitingPair_roots (fourTerm_balance a).1,Nat.sub_self,rootFactorial_zero,mul_one]
  unfold fourTermCoefficient
  push_cast
  field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
  simp only [rootFactorial_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExteriorTermExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exterior Term Expansion. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators

lemma localPairStar_sum {n p : ℕ} (hp : p+1 < n) :
    localPairStar n p = ∑ i : Fin ((p+2)/2),
      (limitingExteriorPairCoefficient p i.val (p+1-i.val):ℂ) •
        (annihilation (pairRight hp i) * annihilation (pairLeft hp i)) := by
  classical
  symm
  unfold localPairStar pairAnnihilator
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_bij_ne_zero (fun i _ _ => (pairLeft hp i,pairRight hp i))
  · simp
  · intro i hi h0 j hj h0' e
    exact Fin.ext (congrArg (fun a : Fin n × Fin n => a.1.val) e)
  · intro a ha h0
    have hlt : a.1 < a.2 := by
      by_contra h
      exact h0 (by simp [h])
    have he : a.1.val+a.2.val=p+1 := by
      by_contra h
      exact h0 (by simp [limitingExteriorPairCoefficient,h])
    let i : Fin ((p+2)/2) := ⟨a.1.val,by have := a.1.isLt; have := a.2.isLt; omega⟩
    have e₁ : pairLeft hp i=a.1 := rfl
    have e₂ : pairRight hp i=a.2 := Fin.ext (by dsimp [pairRight,i]; omega)
    refine ⟨i,Finset.mem_univ _,?_,by rw [e₁,e₂]⟩
    have ey : p+1-i.val=a.2.val := by dsimp [i]; omega
    simpa only [e₁,e₂,ey,ite_eq_left hlt] using h0
  · intro i hi h0
    have ht : pairLeft hp i < pairRight hp i := by have := i.isLt; change i.val < p+1-i.val; omega
    change _ = if pairLeft hp i < pairRight hp i then _ else _
    rw [ite_eq_left ht]
    rfl

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma fourLocalHighestStar_terms {D : ℕ} (hD : D ≤ 23) (r : FourCopy D) :
    fourLocalHighestStar hD r = ∑ a : FourTerm D,
      (fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) *
        limitingExteriorPairCoefficient (fourTermP a) (fourTermX a) (fourTermY a):ℂ) •
          Occupation.word (fourTermLabels hD a) := by
  classical
  rw [fourLocalHighestStar,← (orbitalTripleEquiv D).sum_comp]
  simp only [fourHighestRowsStar]
  conv_rhs => rw [Fintype.sum_sigma]; simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_sigma] 
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro j hj
  rw [Occupation.localPairStar_sum (by change D-n.val+1 < 25; omega)]
  simp only [Finset.mul_sum, mul_smul_comm,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fourTermP,fourTermJ,fourTermK,fourTermX,fourTermY,fourTermLabels,
    localTripleP,localTripleJ,localTripleK,orbitalTripleEquiv,Occupation.pairLeft,Occupation.pairRight,
    Occupation.word_cons,Occupation.word_nil,one_mul,mul_assoc]
  rfl

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCreatedGram
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Created Gram. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators

lemma wordSign_ne_zero_nodup {n : ℕ} (js : List (Fin n)) (h : wordSign js ≠ 0) : js.Nodup := by
  induction js with
  | nil => simp
  | cons j js ih =>
    by_cases hj : j ∈ js
    · exact False.elim (h (by simp [wordSign,hj]))
    · exact List.nodup_cons.mpr ⟨hj,ih (by intro he; apply h; simp [wordSign,hj,he])⟩

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct
open Spin

lemma rootSetWeight_sq {n : ℕ} (A : Finset (Fin n)) :
    rootSetWeight A^2 = (setFactorial A:ℝ) := by
  simp [rootSetWeight,setFactorial,← Finset.prod_pow]

lemma fourColumn_support {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25))
    (h : A ∉ fourKeys hD) : fourColumn hD r A = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  by_cases he : (fourTermLabels hD a).toFinset=A
  · have hz : Occupation.wordSign (fourTermLabels hD a)=0 := by
      by_contra hz
      apply h
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,Occupation.wordSign_ne_zero_nodup _ hz⟩,he⟩
    simp [he,hz]
  · simp [he]

lemma four_term_denominator {D : ℕ} (hD : D ≤ 23) (r : ℕ) (a : FourTerm D) :
    copyNormalization D r * (fourTermCoefficient D r a : ℝ) *
        (Occupation.wordSign (fourTermLabels hD a):ℝ) /
      (rootFactorial (fourTermX a)*rootFactorial (fourTermY a)*
        rootFactorial (fourTermJ a)*rootFactorial (fourTermK a)) =
      copyNormalization D r *
        (fourTermCoefficient D r a * Occupation.wordSign (fourTermLabels hD a):ℚ) /
          rootSetWeight (fourTermLabels hD a).toFinset := by
  by_cases hs : Occupation.wordSign (fourTermLabels hD a)=0
  · simp [hs]
  · have hn := Occupation.wordSign_ne_zero_nodup _ hs
    rw [rootSetWeight,List.prod_toFinset _ hn]
    simp only [fourTermLabels,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,
      Rat.cast_mul]
    ring

lemma four_created_column {D : ℕ} (hD : D ≤ 23) (r : FourCopy D) (A : Finset (Fin 25)) :
    ((fourLocalHighestStar hD r).adjoint (Occupation.vacuum 25)) A =
      ((copyNormalization D r.val.val * (fourColumn hD r.val.val A:ℝ) / rootSetWeight A : ℝ):ℂ) := by
  rw [fourLocalHighestStar_terms]
  simp only [fourColumn,Rat.cast_sum]
  rw [Finset.mul_sum,Finset.sum_div]
  simp only [map_sum,map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,
    Occupation.word_adjoint_vacuum,smul_smul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,PiLp.single_apply,
    smul_eq_mul,map_mul,Complex.conj_ofReal,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : (fourTermLabels hD a).toFinset=A
  · simp only [he,← Complex.ofReal_ratCast,← Complex.ofReal_mul]
    rw [four_pair_normalization]
    have hd := four_term_denominator hD r.val.val a
    rw [he] at hd
    push_cast
    norm_cast
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hne : A ≠ (fourTermLabels hD a).toFinset := Ne.symm he
    simp only [ite_eq_right he,ite_eq_right hne,Rat.cast_zero,mul_zero,zero_div,Complex.ofReal_zero]

lemma createdGram_rational {D : ℕ} (hD : D ≤ 23) (u v : FourCopy D) :
    Occupation.createdGram (fourLocalHighestStar hD) u v =
      ((copyNormalization D u.val.val * (rationalCreatedGram hD u v:ℝ) *
        copyNormalization D v.val.val : ℝ):ℂ) := by
  unfold Occupation.createdGram
  simp only [PiLp.inner_apply,RCLike.inner_apply,
    four_created_column,Complex.conj_ofReal]
  have he : (∑ A : Finset (Fin 25),
      (copyNormalization D u.val.val * (fourColumn hD u.val.val A:ℝ) / rootSetWeight A)*
      (copyNormalization D v.val.val * (fourColumn hD v.val.val A:ℝ) / rootSetWeight A)) =
      ∑ A ∈ fourKeys hD,
      (copyNormalization D u.val.val * (fourColumn hD u.val.val A:ℝ) / rootSetWeight A)*
      (copyNormalization D v.val.val * (fourColumn hD v.val.val A:ℝ) / rootSetWeight A) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro A ha hnot
    simp [fourColumn_support hD u.val.val A hnot]
  simp only [← Complex.ofReal_mul,← Complex.ofReal_sum]
  simp only [mul_comm (copyNormalization D v.val.val * _ / _)
    (copyNormalization D u.val.val * _ / _)]
  rw [he]
  congr 1
  simp only [rationalCreatedGram,Rat.cast_sum,Rat.cast_div,Rat.cast_mul,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A ha
  rw [← rootSetWeight_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourRows
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma fourRowScale_swap (t D i k : ℕ) : fourRowScale t D i k = fourRowScale t D k i := by
  have he : t+i+k=t+k+i := by omega
  simp only [fourRowScale,he]
  split_ifs <;> ring

lemma fourRowScale_sq (t D i k : ℕ) : (fourRowScale t D i k)^2 = (fourRowFactor t D i k : ℝ) := by
  by_cases h : D ≤ t+i+k
  · simp only [fourRowScale,fourRowFactor,ite_eq_left h,div_pow,mul_pow,rootFactorial_sq,
      sqrt_natpow_sq (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    rw [← pow_mul,← pow_add]
    simp only [Nat.mul_comm]
  · simp [fourRowScale,fourRowFactor,h]

lemma rowNormalization_four {t : Fin 8} (a : RowEntry t) {D r : ℕ}
    (hr : r ≤ D) (ho : Odd r) (k : ℕ) :
    rowNormalization t.val a.val.1.val a.val.2.val *
        fourWeightCoefficientStar D (t.val+a.output.val+k) r a.val.1.val a.val.2.val k =
      ((vCoefficient D (t.val+a.output.val+k) r a.val.1.val a.val.2.val k *
        (2:ℚ)^((r+1)/2+a.val.1.val) : ℚ) : ℝ) * copyNormalization D r *
        fourRowScale t.val D a.output.val k := by
  by_cases hD : D ≤ t.val+a.output.val+k
  · rw [fourWeightCoefficientStar_rational hr ho,fourRowScale,ite_eq_left hD]
    dsimp [rowNormalization,RowEntry.output]
    push_cast
    have ht : (Real.sqrt 2 ^ a.val.1.val)^2 = (2:ℝ)^a.val.1.val := sqrt_natpow_sq (by norm_num) _
    field_simp [rootFactorial_ne_zero,Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
    linear_combination (vCoefficient D (t.val+(a.val.1.val+a.val.2.val-t.val)+k)
      r a.val.1.val a.val.2.val k : ℝ) * (2:ℝ)^((r+1)/2) * copyNormalization D r * ht
  · simp [fourWeightCoefficientStar,vCoefficient,fourRowScale,hD]

lemma sum_fibers_cross {α β S : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [CommSemiring S] (o : α → β) (f g : α → β → S) :
    (∑ i, ∑ k, (∑ a, if o a=i then f a k else 0) *
      (∑ b, if o b=k then g b i else 0)) = ∑ a, ∑ b, f a (o b)*g b (o a) := by
  calc
    _ = ∑ i, ∑ b, g b i*(∑ a, if o a=i then f a (o b) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [mul_comm] using sum_fibers_multiply o (fun b => g b i)
        (fun k => ∑ a, if o a=i then f a k else 0)
    _ = ∑ b, ∑ i, (∑ a, if o a=i then f a (o b) else 0)*g b i := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = ∑ b, ∑ a, f a (o b)*g b (o a) := by
      simp only [sum_fibers_multiply]
    _ = _ := Finset.sum_comm

lemma rowFourMatrix_regroup (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ)
    (D : ℕ) (r : RowData) (u v : FourCopy D) :
    rowFourMatrix s D r u v = -(∑ i : Fin 9, ∑ k : Fin 9,
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+i.val+k.val) u.val.val a.val.1.val a.val.2.val k.val else 0) *
      (∑ b : RowEntry r.t, if b.output=k then r.alpha b *
        s D (r.t.val+i.val+k.val) v.val.val b.val.1.val b.val.2.val i.val else 0)) := by
  classical
  have hf (i k : Fin 9) (w : FourCopy D) :
      (∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+i.val+k.val) w.val.val a.val.1.val a.val.2.val k.val else 0) =
      ∑ a : RowEntry r.t, if a.output=i then r.alpha a *
        s D (r.t.val+a.output.val+k.val) w.val.val a.val.1.val a.val.2.val k.val else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · rw [h]
    · rfl
  have hk (i k : Fin 9) : r.t.val+i.val+k.val=r.t.val+k.val+i.val := by omega
  conv_rhs => arg 1; arg 2; ext i; arg 2; ext k; arg 2; rw [hk i k]
  simp_rw [hf]
  rw [sum_fibers_cross]
  unfold rowFourMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [a.balance]
  have he : r.t.val+b.output.val+a.output.val=a.val.1.val+a.val.2.val+b.output.val := by
    have := a.balance; omega
  rw [he]
  ring

lemma RationalRow.fourSum_normalized (r : RationalRow) (D : ℕ) (s : FourCopy D) (i k : Fin 9) :
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) s.val.val a.val.1.val a.val.2.val k.val else 0) =
      (r.fourSum D s.val.val i k : ℝ) * copyNormalization D s.val.val *
        fourRowScale r.t.val D i.val k.val := by
  unfold RationalRow.fourSum
  push_cast
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a.output=i
  · simp only [ite_eq_left h,RationalRow.toReal]
    rw [mul_assoc,← h,rowNormalization_four a (Nat.le_of_lt_succ s.val.isLt) s.property]
    push_cast
    ring
  · simp [h]

lemma RationalRow.fourMatrix_eq (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    rowFourMatrix fourWeightCoefficientStar D r.toReal u v =
      copyNormalization D u.val.val * (r.fourMatrix D u v : ℝ) * copyNormalization D v.val.val := by
  rw [rowFourMatrix_regroup]
  change -(∑ i : Fin 9, ∑ k : Fin 9,
    (∑ a : RowEntry r.t, if a.output=i then r.toReal.alpha a *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) u.val.val a.val.1.val a.val.2.val k.val else 0) *
    (∑ b : RowEntry r.t, if b.output=k then r.toReal.alpha b *
      fourWeightCoefficientStar D (r.t.val+i.val+k.val) v.val.val b.val.1.val b.val.2.val i.val else 0)) = _
  have he (i k : Fin 9) : r.t.val+i.val+k.val=r.t.val+k.val+i.val := by omega
  conv_lhs => arg 1; arg 2; ext i; arg 2; ext k; arg 2; rw [he i k]
  simp only [RationalRow.fourSum_normalized]
  simp only [RationalRow.fourMatrix,Rat.cast_neg,Rat.cast_sum,Rat.cast_mul]
  simp only [mul_neg,neg_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourRowScale_swap r.t.val D k.val i.val,← fourRowScale_sq]
  ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

lemma uCoefficient_eq_fast (c z T p : ℕ) : uCoefficient c z T p = uFast c z T p := by
  simp only [uCoefficient,uFast,chooseFast_eq]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma vCoefficient_eq_fast (D T r p j k : ℕ) : vCoefficient D T r p j k = vFast D T r p j k := by
  simp only [vCoefficient,vFast,uCoefficient_eq_fast]

lemma fourTermCoefficient_eq_eval (D r : ℕ) (a : FourTerm D) :
    fourTermCoefficient D r a = fourTermEval D r a := by
  simp only [fourTermCoefficient,fourTermEval,vCoefficient_eq_fast]

lemma fourColumn_eq_fiber {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25))
    (s : Finset (FourTerm D)) (hs : ∀ a, (fourTermLabels hD a).toFinset=A ↔ a ∈ s) :
    fourColumn hD r A = ∑ a ∈ s, fourTermEval D r a * Occupation.wordSign (fourTermLabels hD a) := by
  simp only [fourColumn,hs,fourTermCoefficient_eq_eval,Finset.sum_ite_mem,Finset.univ_inter]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntegerFourRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four Rows. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma uFast_eq_int (c z T p : ℕ) : uFast c z T p = (uInt c z T p:ℚ) := by
  simp [uFast,uInt]

end LaughlinGap.Spin
namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma vFast_eq_int (D T r p j k : ℕ) : vFast D T r p j k = (vInt D T r p j k:ℚ) := by
  simp [vFast,vInt,uFast_eq_int]

lemma fourSumEval_eq_integer (a : Fin 8) (D s : ℕ) (i k : Fin 9) :
    (exactRows a).fourSumEval D s i k = (fourSumInteger a D s i k:ℚ)/10000000 := by
  simp only [RationalRow.fourSumEval,fourSumInteger,exactRows,vFast_eq_int,Int.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs
  · push_cast; ring
  · simp

lemma fourRowWeight_eq {D : ℕ} (hD : D ≤ 23) (a : Fin 8) (i k : Fin 9) :
    fourRowFactor a.val D i.val k.val / (100000000000000:ℚ) =
      (fourRowWeight D a i k:ℚ) / fourMatrixDenominator D := by
  by_cases h : D ≤ a.val+i.val+k.val
  · simp only [fourRowFactor,fourRowWeight,ite_eq_left h,fourMatrixDenominator]
    have hT : a.val+i.val+k.val ≤ 23 := by have := a.isLt; have := i.isLt; have := k.isLt; omega
    have he : 2*(a.val+i.val+k.val)+a.val ≤ 53 := by
      have := a.isLt; have := i.isLt; have := k.isLt; omega
    have hf : (a.val+i.val+k.val-D).factorial *
        (23-D).descFactorial (23-(a.val+i.val+k.val)) = (23-D).factorial := by
      convert Nat.factorial_mul_descFactorial (show 23-(a.val+i.val+k.val) ≤ 23-D by omega) using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      omega
    have hp : (2:ℚ)^(2*(a.val+i.val+k.val)+a.val) *
        2^(53-(2*(a.val+i.val+k.val)+a.val)) = (2:ℚ)^53 := by
      rw [← pow_add,Nat.add_sub_of_le he]
    have hfc : ((a.val+i.val+k.val-D).factorial:ℚ) *
        ((23-D).descFactorial (23-(a.val+i.val+k.val)):ℚ) = ((23-D).factorial:ℚ) := by
      exact_mod_cast hf
    push_cast
    field_simp
    nlinarith [hp,hfc]
  · simp [fourRowFactor,fourRowWeight,h]

lemma exactFourEval_eq {D : ℕ} (hD : D ≤ 23) (u v : ℕ) :
    (∑ a : Fin 8, (exactRows a).fourMatrixEval D u v) = exactFourEval D u v := by
  simp only [RationalRow.fourMatrixEval,fourSumEval_eq_integer,exactFourEval,exactFourInteger,
    Int.cast_neg,Int.cast_sum,Int.cast_mul,Finset.sum_neg_distrib,neg_div,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := fourRowWeight_eq hD a i k
  calc
    _ = (fourRowFactor a.val D i.val k.val/100000000000000) *
        (fourSumInteger a D u i k:ℚ) * (fourSumInteger a D v k i:ℚ) := by dsimp [exactRows]; ring
    _ = _ := by rw [hh]; ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CachedIntegerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cached Integer Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

lemma exactFourEval_table (D : ℕ) (S : Fin ((D+1)/2) → Fin 8 → Fin 9 → Fin 9 → ℤ)
    (hS : ∀ u a i k, fourSumInteger a D (2*u.val+1) i k = S u a i k)
    (u v : Fin ((D+1)/2)) :
    exactFourEval D (2*u.val+1) (2*v.val+1) = integerTableEval D S u v := by
  simp only [exactFourEval,exactFourInteger,integerTableEval,hS]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCertificate
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Certificate. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

lemma copyNormalization_sq (D r : ℕ) :
    copyNormalization D r ^ 2 = (copyNormalizationSq D r:ℝ) := by
  simp [copyNormalization,copyNormalizationSq,mul_pow]

lemma createdGram_eq_diagonal {D : ℕ} (hD : D ≤ 23) :
    Occupation.createdGram (fourLocalHighestStar hD) =
      copyDiagonal D * (rationalCreatedGram hD).map (algebraMap ℚ ℂ) * copyDiagonal D := by
  ext u v
  simp only [copyDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply]
  rw [createdGram_rational]
  push_cast
  rfl

lemma rationalFourComparison_real (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    (rationalFourComparison rows ε D).map (algebraMap ℚ ℝ) =
      Matrix.diagonal (fun u : FourCopy D => copyNormalization D u.val.val) *
        fourComparisonStar (fun a => (rows a).toReal) (ε:ℝ) D *
      Matrix.diagonal (fun u : FourCopy D => copyNormalization D u.val.val) := by
  ext u v
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.map_apply,
    rationalFourComparison,fourComparisonStar,Matrix.add_apply,Matrix.sub_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,RationalRow.fourMatrix_eq]
  change (((if u=v then ((if u.val.val=1 then 2 else 0)+ε)*copyNormalizationSq D u.val.val else 0) -
      copyNormalizationSq D u.val.val * (∑ a, (rows a).fourMatrix D u v) *
        copyNormalizationSq D v.val.val : ℚ) : ℝ) = _
  by_cases h : u=v
  · subst v
    simp only [ite_true,Matrix.one_apply_eq,mul_one,fourCopyTarget,and_self]
    by_cases hu : u.val.val=1
    all_goals simp only [hu,ite_true,ite_false]; push_cast
    all_goals simp only [← Finset.mul_sum,← Finset.sum_mul,← copyNormalization_sq]; ring
  · have ht : ¬ (u.val.val=1 ∧ v.val.val=1) := by
      rintro ⟨hu,hv⟩
      exact h (Subtype.ext (Fin.ext (hu.trans hv.symm)))
    simp only [ite_eq_right h,Matrix.one_apply_ne h,mul_zero,add_zero,fourCopyTarget,ite_eq_right ht,
      zero_sub]
    push_cast
    simp only [← Finset.mul_sum,← Finset.sum_mul,← copyNormalization_sq]
    ring

lemma rationalFourComparison_eq (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    (rationalFourComparison rows ε D).map (algebraMap ℚ ℂ) =
      copyDiagonal D * (fourComparisonStar (fun a => (rows a).toReal) (ε:ℝ) D).map
        (algebraMap ℝ ℂ) * copyDiagonal D := by
  have h := congrArg (fun A : Matrix (FourCopy D) (FourCopy D) ℝ =>
    A.map (algebraMap ℝ ℂ)) (rationalFourComparison_real rows ε D)
  convert h using 1
  · ext u v
    simp [Matrix.map_apply]
  · simp only [Matrix.map_mul,Matrix.diagonal_map (map_zero _)]
    rfl

lemma fourCertificate_of_rational (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23)
    (h : ((rationalFourCompression rows ε hD).map (algebraMap ℚ ℂ)).PosSemidef) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  have he : (copyDiagonal D).conjTranspose=copyDiagonal D := by
    simp [copyDiagonal]
  have hp := h.mul_mul_conjTranspose_same (copyDiagonal D)
  rw [he] at hp
  unfold FourCertificate
  rw [createdGram_eq_diagonal]
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  rw [rationalFourCompression,Matrix.map_mul,Matrix.map_mul,rationalFourComparison_eq]
  simp only [Matrix.mul_assoc]

lemma rational_ldl_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M L : Matrix κ κ ℚ) (d : κ → ℚ) (hd : ∀ i, 0 ≤ d i)
    (he : M = L * Matrix.diagonal d * L.transpose) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => (d i:ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simpa only [← Complex.ofReal_ratCast,Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,
      and_true] using (Rat.cast_nonneg (K := ℝ)).mpr (hd i)
  have hh := hp.mul_mul_conjTranspose_same (L.map (algebraMap ℚ ℂ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [he,Matrix.map_mul,Matrix.map_mul]
  congr 1
  · congr 1
    ext i j
    by_cases h : i=j <;> simp [h]
  · ext i j
    simp [Matrix.conjTranspose_apply]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Tables. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

lemma rationalCreatedGram_of_columns {D : ℕ} (hD : D ≤ 23) {K : ℕ}
    (keys : Fin K → Finset (Fin 25)) (cols : Matrix (Fin ((D+1)/2)) (Fin K) ℚ)
    (hk : fourKeys hD=Finset.univ.image keys) (hi : Function.Injective keys)
    (hc : ∀ u a, fourColumn hD (2*u.val+1) (keys a)=cols u a)
    (u v : Fin ((D+1)/2)) :
    rationalCreatedGram hD ((fourCopyEquiv D).symm u) ((fourCopyEquiv D).symm v) =
      ∑ a : Fin K, cols u a * cols v a / setFactorial (keys a) := by
  unfold rationalCreatedGram
  rw [hk,Finset.sum_image (fun _ _ _ _ h => hi h)]
  simp only [fourCopyEquiv_symm_val,hc]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CheckedTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Tables. -/

noncomputable section


namespace LaughlinGap.Arithmetic

lemma checkMatrix_sound {n m : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → Fin m → α) (h : checkMatrix A B = true) : ∀ i j, A i j = B i j := by
  intro i j
  unfold checkMatrix at h
  have hh := List.all_eq_true.mp h i (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp hh j (List.mem_finRange j))

end LaughlinGap.Arithmetic

namespace LaughlinGap.Arithmetic

lemma checkVector_sound {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) (h : checkVector A B = true) : ∀ i, A i = B i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end LaughlinGap.Arithmetic

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable5

lemma s_0_0_checked : ∀ i k : Fin 9, fourSumInteger 0 5 1 i k = s_0_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_1_checked : ∀ i k : Fin 9, fourSumInteger 1 5 1 i k = s_0_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_2_checked : ∀ i k : Fin 9, fourSumInteger 2 5 1 i k = s_0_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_3_checked : ∀ i k : Fin 9, fourSumInteger 3 5 1 i k = s_0_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_4_checked : ∀ i k : Fin 9, fourSumInteger 4 5 1 i k = s_0_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_5_checked : ∀ i k : Fin 9, fourSumInteger 5 5 1 i k = s_0_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_6_checked : ∀ i k : Fin 9, fourSumInteger 6 5 1 i k = s_0_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_0_7_checked : ∀ i k : Fin 9, fourSumInteger 7 5 1 i k = s_0_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_0_checked : ∀ i k : Fin 9, fourSumInteger 0 5 3 i k = s_1_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_1_checked : ∀ i k : Fin 9, fourSumInteger 1 5 3 i k = s_1_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_2_checked : ∀ i k : Fin 9, fourSumInteger 2 5 3 i k = s_1_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_3_checked : ∀ i k : Fin 9, fourSumInteger 3 5 3 i k = s_1_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_4_checked : ∀ i k : Fin 9, fourSumInteger 4 5 3 i k = s_1_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_5_checked : ∀ i k : Fin 9, fourSumInteger 5 5 3 i k = s_1_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_6_checked : ∀ i k : Fin 9, fourSumInteger 6 5 3 i k = s_1_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_1_7_checked : ∀ i k : Fin 9, fourSumInteger 7 5 3 i k = s_1_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_0_checked : ∀ i k : Fin 9, fourSumInteger 0 5 5 i k = s_2_0 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_1_checked : ∀ i k : Fin 9, fourSumInteger 1 5 5 i k = s_2_1 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_2_checked : ∀ i k : Fin 9, fourSumInteger 2 5 5 i k = s_2_2 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_3_checked : ∀ i k : Fin 9, fourSumInteger 3 5 5 i k = s_2_3 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_4_checked : ∀ i k : Fin 9, fourSumInteger 4 5 5 i k = s_2_4 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_5_checked : ∀ i k : Fin 9, fourSumInteger 5 5 5 i k = s_2_5 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_6_checked : ∀ i k : Fin 9, fourSumInteger 6 5 5 i k = s_2_6 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma s_2_7_checked : ∀ i k : Fin 9, fourSumInteger 7 5 5 i k = s_2_7 i k := by
  apply Arithmetic.checkMatrix_sound
  decide +kernel

lemma sums_checked : ∀ u : Fin 3, ∀ a i k, fourSumInteger a 5 (2*u.val+1) i k = sums u a i k := by
  intro u a i k
  fin_cases u <;> fin_cases a
  · exact s_0_0_checked i k
  · exact s_0_1_checked i k
  · exact s_0_2_checked i k
  · exact s_0_3_checked i k
  · exact s_0_4_checked i k
  · exact s_0_5_checked i k
  · exact s_0_6_checked i k
  · exact s_0_7_checked i k
  · exact s_1_0_checked i k
  · exact s_1_1_checked i k
  · exact s_1_2_checked i k
  · exact s_1_3_checked i k
  · exact s_1_4_checked i k
  · exact s_1_5_checked i k
  · exact s_1_6_checked i k
  · exact s_1_7_checked i k
  · exact s_2_0_checked i k
  · exact s_2_1_checked i k
  · exact s_2_2_checked i k
  · exact s_2_3_checked i k
  · exact s_2_4_checked i k
  · exact s_2_5_checked i k
  · exact s_2_6_checked i k
  · exact s_2_7_checked i k
end SumTable5
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate5

lemma keys_checked : fourKeys (by omega : 5 ≤ 23) = Finset.univ.image keys := by decide +kernel
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma fibers_checked_0 : ∀ b : FourTerm 5,
    (fourTermLabels (by omega : 5 ≤ 23) b).toFinset=keys 0 ↔ b ∈ fibers 0 := by decide +kernel
lemma fibers_checked : ∀ a : Fin 1, ∀ b : FourTerm 5,
    (fourTermLabels (by omega : 5 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a
  fin_cases a
  · exact fibers_checked_0
lemma columns_checked_0 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(0 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(1 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*(2 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 3, ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 5 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 5 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
lemma gram_checked_0 : ∀ v : Fin 3, (∑ a : Fin 1, columns (0 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 3, (∑ a : Fin 1, columns (1 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 3, (∑ a : Fin 1, columns (2 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 3, ∀ v : Fin 3, (∑ a : Fin 1, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
lemma rows_table_checked_0 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (0 : Fin 3) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (1 : Fin 3) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 3, integerTableEval 5 SumTable5.sums (2 : Fin 3) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 3, ∀ v : Fin 3, integerTableEval 5 SumTable5.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
lemma rows_checked (u v : Fin 3) : exactFourEval 5 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 5 SumTable5.sums SumTable5.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (0 : Fin 3) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (1 : Fin 3) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) (2 : Fin 3) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 3, ∀ v : Fin 3, (Z * tableComparison 5 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
lemma compression_checked_0 : ∀ v : Fin 3, (W * Z) (0 : Fin 3) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 3, (W * Z) (1 : Fin 3) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 3, (W * Z) (2 : Fin 3) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 3, ∀ v : Fin 3, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
lemma ldl_checked_0 : ∀ v : Fin 3, (∑ k : Fin 3, L (0 : Fin 3) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 3, (∑ k : Fin 3, L (1 : Fin 3) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 3, (∑ k : Fin 3, L (2 : Fin 3) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 3, ∀ v : Fin 3, (∑ k : Fin 3, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
lemma diag_checked : ∀ u : Fin 3, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 5 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 5 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 5 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 5 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 5 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate5
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate6. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate6

lemma keys_checked : fourKeys (by omega : 6 ≤ 23) = Finset.univ.image keys := by decide +kernel
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma fibers_checked_0 : ∀ b : FourTerm 6,
    (fourTermLabels (by omega : 6 ≤ 23) b).toFinset=keys 0 ↔ b ∈ fibers 0 := by decide +kernel
lemma fibers_checked : ∀ a : Fin 1, ∀ b : FourTerm 6,
    (fourTermLabels (by omega : 6 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a
  fin_cases a
  · exact fibers_checked_0
lemma columns_checked_0 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(0 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(1 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*(2 : Fin 3).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 3, ∀ v : Fin 1, (∑ b ∈ fibers v, fourTermEval 6 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 6 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
lemma gram_checked_0 : ∀ v : Fin 3, (∑ a : Fin 1, columns (0 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 3, (∑ a : Fin 1, columns (1 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 3, (∑ a : Fin 1, columns (2 : Fin 3) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 3, ∀ v : Fin 3, (∑ a : Fin 1, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 6 (by omega) := by
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 6 (by omega) by simpa using this
  apply fourCertificate_of_rational exactRows (1/200000) (by omega : 6 ≤ 23)
  have hg : rationalCreatedGram (by omega : 6 ≤ 23) = 0 := by
    ext u v
    obtain ⟨u,rfl⟩ := (fourCopyEquiv 6).symm.surjective u
    obtain ⟨v,rfl⟩ := (fourCopyEquiv 6).symm.surjective v
    rw [rationalCreatedGram_of_columns (by omega : 6 ≤ 23) keys columns keys_checked keys_injective]
    · have hz : Z=0 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
      simpa only [hz,Matrix.zero_apply] using gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 6 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  simpa [rationalFourCompression,hg] using (Matrix.PosSemidef.zero : (0 : Matrix (FourCopy 6) (FourCopy 6) ℂ).PosSemidef)
end Certificate6
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ZeroCertificates
attribute [-simp] _root_.OAI.LaughlinGap.RealOccupation.fourCopyEquiv_symm_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Certificates. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

lemma fourCertificate_of_empty_keys {ι : Type*} [Fintype ι] (rows : ι → RationalRow) (ε : ℚ)
    {D : ℕ} (hD : D ≤ 23) (hk : fourKeys hD=∅) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  apply fourCertificate_of_rational rows ε hD
  have hg : rationalCreatedGram hD=0 := by ext u v; simp [rationalCreatedGram,hk]
  simpa [rationalFourCompression,hg] using (Matrix.PosSemidef.zero : (0 : Matrix (FourCopy D) (FourCopy D) ℂ).PosSemidef)

lemma keys_empty_1 : fourKeys (by omega : 1 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_2 : fourKeys (by omega : 2 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_3 : fourKeys (by omega : 3 ≤ 23)=∅ := by decide +kernel
lemma keys_empty_4 : fourKeys (by omega : 4 ≤ 23)=∅ := by decide +kernel

lemma certificate_1 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 1
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_1 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma certificate_2 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 2
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_2 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma certificate_3 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 3
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_3 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
lemma certificate_4 : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 4
    (by omega) := by
  convert fourCertificate_of_empty_keys exactRows (1/200000) _ keys_empty_4 using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Main. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

lemma exact_four_oai (d : Fin 23) :
    FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000)
      (d.val+1) (by omega) := by
  fin_cases d
  · exact certificate_1
  · exact certificate_2
  · exact certificate_3
  · exact certificate_4
  · exact Certificate5.certificate
  · exact Certificate6.certificate
  · exact Certificate7.certificate
  · exact Certificate8.certificate
  · exact Certificate9.certificate
  · exact Certificate10.certificate
  · exact Certificate11.certificate
  · exact Certificate12.certificate
  · exact Certificate13.certificate
  · exact Certificate14.certificate
  · exact Certificate15.certificate
  · exact Certificate16.certificate
  · exact Certificate17.certificate
  · exact Certificate18.certificate
  · exact Certificate19.certificate
  · exact Certificate20.certificate
  · exact Certificate21.certificate
  · exact Certificate22.certificate
  · exact Certificate23.certificate

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.exact_four_oai := @OAI.LaughlinGap.RealOccupation.exact_four_oai
