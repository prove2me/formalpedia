-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.fourCertificate_of_tables
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T04:21:53.283988+00:00
-- url     : https://prove2.me/submissions/19c4a47a-584c-48de-afbc-2a8952fe055a

import Mathlib
import Definitions.Def_OAIQ030L035

section
-- module Solutions.OAIQ030_LG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRowComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Row Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma sum_row_fiber {S : Type*} [AddCommMonoid S] (t : Fin 8) (i : Fin 9)
    (f : Fin 8 → Fin 9 → S) :
    (∑ a : RowEntry t, if a.output=i then f a.val.1 a.val.2 else 0) =
      ∑ p : Fin 8, ∑ j : Fin 9, if p.val+j.val=t.val+i.val then f p j else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun a : Fin 8 × Fin 9 =>
    if a.1.val+a.2.val=t.val+i.val then f a.1 a.2 else 0)]
  symm
  apply Finset.sum_congr_set (s := {a : Fin 8 × Fin 9 | t.val ≤ a.1.val+a.2.val ∧
      a.1.val+a.2.val ≤ t.val+8})
  · intro a ha
    change t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8 at ha
    have he : a.1.val+a.2.val=t.val+i.val ↔ RowEntry.output (⟨a,ha⟩ : RowEntry t)=i := by
      simp only [RowEntry.output,Fin.ext_iff]
      omega
    simp only [he]
  · intro a ha
    change ¬ (t.val ≤ a.1.val+a.2.val ∧ a.1.val+a.2.val ≤ t.val+8) at ha
    have hi := i.isLt
    have hn : a.1.val+a.2.val ≠ t.val+i.val := by omega
    simp only [ite_eq_right hn]

lemma sum_fixed_pair {S : Type*} [AddCommMonoid S] (T : ℕ) (p : Fin 8)
    (f : Fin 9 → S) :
    (∑ j : Fin 9, if p.val+j.val=T then f j else 0) =
      if h : p.val ≤ T ∧ T-p.val < 9 then f ⟨T-p.val,h.2⟩ else 0 := by
  classical
  by_cases h : p.val ≤ T ∧ T-p.val < 9
  · rw [dite_eq_left h]
    rw [Finset.sum_eq_single (⟨T-p.val,h.2⟩ : Fin 9)]
    · simp only [Nat.add_sub_of_le h.1,ite_true]
    · intro j hj hn
      have he : p.val+j.val ≠ T := by
        intro he
        apply hn
        apply Fin.ext
        dsimp
        omega
      simp only [ite_eq_right he]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro j hj
    have he : p.val+j.val ≠ T := by have := j.isLt; omega
    simp only [ite_eq_right he]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma RationalRow.fourSum_eq_fast (r : RationalRow) (D s : ℕ) (i k : Fin 9) :
    r.fourSum D s i k = r.fourSumFast D s i k := by
  rw [RationalRow.fourSum,sum_row_fiber r.t i (fun p j =>
    r.alpha p j * vCoefficient D (r.t.val+i.val+k.val) s p.val j.val k.val *
      (2:ℚ)^((s+1)/2+p.val))]
  simp only [sum_fixed_pair,RationalRow.fourSumFast]

lemma RationalRow.fourMatrix_eq_fast (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    r.fourMatrix D u v = r.fourMatrixFast D u.val.val v.val.val := by
  simp only [RationalRow.fourMatrix,RationalRow.fourMatrixFast,RationalRow.fourSum_eq_fast]

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

lemma RationalRow.fourMatrix_eq_eval (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    r.fourMatrix D u v = r.fourMatrixEval D u.val.val v.val.val := by
  simp only [RationalRow.fourMatrix_eq_fast,RationalRow.fourMatrixFast,RationalRow.fourMatrixEval,
    RationalRow.fourSumFast,RationalRow.fourSumEval,vCoefficient_eq_fast]

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

lemma fourCertificate_of_tables_oai (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23)
    (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (hY : ∀ u v : Fin ((D+1)/2),
      (∑ a, (rows a).fourMatrixEval D (2*u.val+1) (2*v.val+1))=Y u v)
    (hZ : ∀ u v : Fin ((D+1)/2), rationalCreatedGram hD
      ((fourCopyEquiv D).symm u) ((fourCopyEquiv D).symm v)=Z u v)
    (hp : ((Z * tableComparison D ε Y * Z).map (algebraMap ℚ ℂ)).PosSemidef) :
    FourCertificate (fun a => (rows a).toReal) (ε:ℝ) D hD := by
  apply fourCertificate_of_rational rows ε hD
  rw [← Matrix.posSemidef_submatrix_equiv (fourCopyEquiv D).symm]
  have hB : (rationalFourComparison rows ε D).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm = tableComparison D ε Y := by
    ext u v
    simp only [rationalFourComparison,Matrix.submatrix_apply,fourCopyEquiv_symm_val,
      Equiv.apply_eq_iff_eq,RationalRow.fourMatrix_eq_eval,hY,tableComparison]
    rfl
  have hG : (rationalCreatedGram hD).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm=Z := Matrix.ext hZ
  have he : (rationalFourCompression rows ε hD).submatrix (fourCopyEquiv D).symm
      (fourCopyEquiv D).symm = Z * tableComparison D ε Y * Z := by
    unfold rationalFourCompression
    rw [Matrix.submatrix_mul _ _ _ _ _ (fourCopyEquiv D).symm.bijective,
      Matrix.submatrix_mul _ _ _ _ _ (fourCopyEquiv D).symm.bijective,hG,hB]
  simpa only [Matrix.submatrix_map,he] using hp

end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.LaughlinGap.RealOccupation.fourCertificate_of_tables_oai.{u_1} := @OAI.LaughlinGap.RealOccupation.fourCertificate_of_tables_oai.{u_1}
