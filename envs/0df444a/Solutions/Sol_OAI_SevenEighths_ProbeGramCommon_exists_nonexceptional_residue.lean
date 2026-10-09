-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.exists_nonexceptional_residue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:56:47.553221+00:00
-- url     : https://prove2.me/submissions/14422d91-8f00-47b5-807c-278a1770a723

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Calibration
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive b hb
  have hg := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive _ e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Correlation
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCommonLinear
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

theorem fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by
  rw [fullCorrelation_bezout n₁ n₂ a b k hab]
  calc
    _ ≤ ∑t : R,‖f (b*k+n₁*t)*star (g (-a*k+n₂*t))‖ := norm_sum_le _ _
    _ ≤ ∑_t : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul,norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf _)).trans (hg _)
    _ = _ := by simp

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimePower
namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

local instance instInfiniteRingOfIntegers_solutions_r7688ed_1 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramLocalExtension
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma finiteField_local_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u v k : F) (huv : u≠0 ∨ v≠0) :
    ‖localCorrelation χ u v k‖≤(Fintype.card F:ℝ) := by
  rcases huv with hu|hv
  · exact fullCorrelation_bezout_norm u v u⁻¹ 0 k (by simp [hu]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)
  · exact fullCorrelation_bezout_norm u v 0 v⁻¹ k (by simp [hv]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)

theorem localExtension_periodic (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈P) (h₂ : n₂-m₂∈P) (hk : k-l∈P) :
    localExtension P hg c n₁ n₂ k=localExtension P hg c m₁ m₂ l := by
  have he₁ := Ideal.Quotient.eq.mpr h₁
  have he₂ := Ideal.Quotient.eq.mpr h₂
  have hek := Ideal.Quotient.eq.mpr hk
  have hm₁ : n₁∈P↔m₁∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₁,Ideal.Quotient.eq_zero_iff_mem]
  have hm₂ : n₂∈P↔m₂∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₂,Ideal.Quotient.eq_zero_iff_mem]
  simp only [localExtension,hm₁,hm₂,he₁,he₂,hek]

theorem localExtension_norm (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤ c) (n₁ n₂ k : O) :
    ‖localExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm P:ℝ)^c := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  unfold localExtension
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  have huv : Ideal.Quotient.mk P n₁≠0 ∨ Ideal.Quotient.mk P n₂≠0 := by
    by_contra hh
    push Not at hh
    exact hn ⟨Ideal.Quotient.eq_zero_iff_mem.mp hh.1,Ideal.Quotient.eq_zero_iff_mem.mp hh.2⟩
  have hh := finiteField_local_norm (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
    (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k) huv
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm P:ℝ)^(c-1)*(Ideal.absNorm P:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hh
    _ = _ := by rw [←pow_succ,Nat.sub_add_cancel hc]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramGlobalExtension
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCorrelation CenteredMomentCanonical CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma globalExtension_norm (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i) (n₁ n₂ k : O) :
    ‖globalExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm (∏i,P i^c i):ℝ) := by
  rw [globalExtension,norm_prod]
  calc
    _ ≤ ∏i,(Ideal.absNorm (P i):ℝ)^c i :=
      Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>localExtension_norm (P i) (hg i) (c i) (hc i) n₁ n₂ k)
    _ = _ := by simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]

theorem globalExtension_periodic (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈∏i,P i) (h₂ : n₂-m₂∈∏i,P i) (hk : k-l∈∏i,P i) :
    globalExtension P hg c n₁ n₂ k=globalExtension P hg c m₁ m₂ l := by
  apply Finset.prod_congr rfl
  intro i hi
  have hle : (∏i,P i)≤P i := Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))
  exact localExtension_periodic (P i) (hg i) (c i) n₁ n₂ m₁ m₂ k l (hle h₁) (hle h₂) (hle hk)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramMean
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_power_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2) (e : ℕ) (he : ¬6∣e) :
    actualSextic P hg^e≠1 := by
  intro h
  have hd := (orderOf_dvd_iff_pow_eq_one).mpr h
  rw [actualSextic_order_six P hg hchar] at hd
  exact he hd

theorem primePower_mean_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) [Fintype (O⧸P^c)] (d : O) :
    (∑x : O⧸P^c,(actualSextic P hg^e)
      (Ideal.Quotient.mk P d*primePowerReduction P hc x))=0 := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  simp_rw [map_mul]
  rw [←Finset.mul_sum,sum_reduction _ (primePowerReduction_surjective P hc),
    MulChar.sum_eq_zero_of_ne_one (actualSextic_power_nonprincipal P hg hchar e he),mul_zero,mul_zero]

theorem crt_joint_mean_zero (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : (O⧸Q)→(O⧸Q*P^c)→ℂ) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P d*
        primePowerReduction P hc ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).2))*
      F ((Ideal.quotientMulEquivQuotientProd Q (P^c) hcop x).1) y)=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have heq := E.toEquiv.sum_comp (fun p : (O⧸Q)×(O⧸P^c)=>
    (actualSextic P hg^e) (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y)
  change (∑x : O⧸Q*P^c,(actualSextic P hg^e)
    (Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2)*F (E x).1 y)=0
  calc
    _ = ∑p : (O⧸Q)×(O⧸P^c),(actualSextic P hg^e)
        (Ideal.Quotient.mk P d*primePowerReduction P hc p.2)*F p.1 y := heq
    _ = 0 := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.sum_mul,primePower_mean_zero P hg hchar c e hc he d,zero_mul]
      simp

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriod
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramArithmetic
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma gramPeriodicMonoid_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) : ‖gramPeriodicMonoid C B D n‖≤1 := by
  rw [gramPeriodicMonoid,MonoidHom.mul_apply,norm_mul]
  change ‖star (C.residueMonoid n)‖*_≤1
  rw [norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one n)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported n)

lemma gramPeriodicMonoid_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (gramPeriodicMonoid C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change star (C.residueMonoid x)*_=star (C.residueMonoid y)*_
  congr 1
  · apply congrArg star
    apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma gramCoefficientExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖gramCoefficientExtension S hS σ n‖≤1 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [norm_mul,norm_inv,calibrationForSet_tau_norm,inv_one,one_mul]
    exact gramPeriodicMonoid_norm _ _ _ _
  · simp

theorem gramCoefficientExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ x=gramCoefficientExtension S hS σ y := by
  have hr : physicalRay x=physicalRay y := Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  have hm := gramPeriodicMonoid_periodic (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) x y (Ideal.mul_le_left hxy)
  simp only [gramCoefficientExtension,hr,hm]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramNumerator
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  · apply map_dvd Ideal.absNorm
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨u.val*λ₀^a*(2:O)^b,by rw [hk];ring⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointFixed
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma primaryCoefficient_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖primaryCoefficient S hS σ n‖≤1 := by
  unfold primaryCoefficient
  split_ifs
  · exact gramCoefficientExtension_norm _ _ _ _
  · simp

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma primaryCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ x=primaryCoefficient S hS σ y := by
  have hg := gramCoefficientExtension_periodic S hS σ x y (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hp : λ₀^2∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  have hi : (λ₀^2∣x-1)↔(λ₀^2∣y-1) := by
    constructor
    · intro h
      convert (preTransparency := .instances) dvd_sub h hp using 1 ; ring
    · intro h
      convert (preTransparency := .instances) dvd_add hp h using 1 ; ring
  simp only [primaryCoefficient,hi,hg]

lemma jointFixed_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) :
    ‖jointFixed S hS σ C u a b r hr n₁ n₂‖≤1 := by
  unfold jointFixed
  simp only [norm_mul,norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (primaryCoefficient_norm _ _ _ _)).trans (primaryCoefficient_norm _ _ _ _)

lemma jointFixed_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ m₁ m₂ : O)
    (h₁ : n₁-m₁∈jointFixedModulus S hS) (h₂ : n₂-m₂∈jointFixedModulus S hS) :
    jointFixed S hS σ C u a b r hr n₁ n₂=jointFixed S hS σ C u a b r hr m₁ m₂ := by
  have hc₁ := primaryCoefficient_periodic S hS σ (C*n₁) (C*m₁)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₁)
  have hc₂ := primaryCoefficient_periodic S hS σ (C*n₂) (C*m₂)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₂)
  have hb₁ := numeratorBadTwist_periodic u a b r hr n₁ m₁ (Ideal.mul_le_right h₁)
  have hb₂ := numeratorBadTwist_periodic (-u) a b r hr n₂ m₂ (Ideal.mul_le_right h₂)
  have hfour (x y : O) (h : x-y∈jointFixedModulus S hS) : (4:O)∣x-y :=
    (show (4:O)∣72 from ⟨18,by norm_num⟩).trans (Ideal.mem_span_singleton.mp (Ideal.mul_le_right h))
  have hp : sexticReciprocityPhase n₁ n₂=sexticReciprocityPhase m₁ m₂ := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub n₁ m₁ (hfour _ _ h₁),
      QuadraticGaussRay.residue_eq_of_four_dvd_sub n₂ m₂ (hfour _ _ h₂)]
  simp only [jointFixed,hc₁,hc₂,hb₁,hb₂,hp]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJoint
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma jointExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i)
    (n₁ n₂ : O) : ‖jointExtension S hS σ C k u a b r hr P hg c n₁ n₂‖≤Ideal.absNorm (∏i,P i^c i) := by
  rw [jointExtension,norm_mul]
  have ha : ‖jointFixed S hS σ C u a b r hr n₁ n₂*
      (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))‖≤1 := by
    rw [norm_mul,norm_mul,norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (jointFixed_norm _ _ _ _ _ _ _ _ _ _ _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _))
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using globalExtension_norm P hg c hc n₁ n₂ k)

lemma jointExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      jointExtension S hS σ C k u a b r hr P hg c m₁ m₂ := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n₁ n₂ m₁ m₂
    (Ideal.mul_le_left (Ideal.mul_le_left h₁)) (Ideal.mul_le_left (Ideal.mul_le_left h₂))
  have hm₁ := idealRowHom_congr_mod (Ideal.span {r}) n₁ m₁ (Ideal.mul_le_right h₁)
  have hm₂ := idealRowHom_congr_mod (Ideal.span {r}) n₂ m₂ (Ideal.mul_le_right h₂)
  have he := globalExtension_periodic P hg c n₁ n₂ m₁ m₂ k k
    (Ideal.mul_le_right (Ideal.mul_le_left h₁)) (Ideal.mul_le_right (Ideal.mul_le_left h₂)) (by simp)
  simp only [jointExtension,hf,hm₁,hm₂,he]

lemma jointExtension_dilation_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (d n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)=
      jointExtension S hS σ C k u a b r hr P hg c (d*m₁) (d*m₂) := by
  apply jointExtension_periodic
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₁
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₂

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramMeanLift
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O

theorem joint_mean_of_local_factor (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤ c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : O→O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : O⧸Q*P^c) (y : O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=>F x.out y.out) d
  convert (preTransparency := .instances) hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointMean
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem jointExtension_local_factor (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (e : ℕ) (he : e≠0)
    (hfactor : Ideal.span {r}=J*p^e) (n₁ n₂ : O) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      (actualSextic p hgp^e) (Ideal.Quotient.mk p n₁)*
        jointRemainder S hS σ C k u a b r hr P hg c J n₁ n₂ := by
  have hf : idealRowHom n₁ (Ideal.span {r})=
      idealRowHom n₁ J*(actualSextic p hgp^e) (Ideal.Quotient.mk p n₁) := by
    rw [hfactor,map_mul,map_pow,idealRowHom_prime n₁ p hgp,MulChar.pow_apply' _ he]
  rw [jointExtension,hf,jointRemainder]
  ring

lemma jointRemainder_periodic_first (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n m y : O) (h : n-m∈jointFixedModulus S hS*(∏i,P i)*J) :
    jointRemainder S hS σ C k u a b r hr P hg c J n y=
      jointRemainder S hS σ C k u a b r hr P hg c J m y := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n y m y
    (Ideal.mul_le_left (Ideal.mul_le_left h)) (by simp)
  have hm := idealRowHom_congr_mod J n m (Ideal.mul_le_right h)
  have hg' := globalExtension_periodic P hg c n y m y k k
    (Ideal.mul_le_right (Ideal.mul_le_left h)) (by simp) (by simp)
  simp only [jointRemainder,hf,hm,hg']

theorem jointExtension_mean_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (hchar : ringChar (O⧸p)≠2)
    (e : ℕ) (he : ¬6∣e) (hfactor : Ideal.span {r}=J*p^e)
    (hcop : IsCoprime (jointFixedModulus S hS*(∏i,P i)*J) (p^e))
    [Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J)] [Fintype (O⧸p^e)]
    [Fintype (O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e)] (d : O) :
    (∑x : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
      ∑y : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
        jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out))=0 := by
  have he0 : e≠0 := by intro h;exact he (h ▸ dvd_zero 6)
  have he1 : 1≤e := Nat.one_le_iff_ne_zero.mpr he0
  simp_rw [jointExtension_local_factor S hS σ C k u a b r hr P hg c J p hgp e he0 hfactor]
  apply joint_mean_of_local_factor _ p hgp hchar e e he1 he hcop
    (fun x y=>jointRemainder S hS σ C k u a b r hr P hg c J (d*x) (d*y)) _ d
  intro x z y hxz
  apply jointRemainder_periodic_first
  rw [←mul_sub]
  exact (jointFixedModulus S hS*(∏i,P i)*J).mul_mem_left d hxz

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointPeriod
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramPrimeSeparation
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma maximal_coprime_of_not_dvd (p J : Id) [p.IsMaximal] (h : ¬p∣J) : IsCoprime J p := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have he : p=J⊔p := Ideal.IsMaximal.eq_of_le inferInstance htop le_sup_right
  apply h
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_left

theorem exists_prime_separation (I p : Id) (hI : I≠0) [p.IsMaximal] (hp0 : p≠0) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧ IsCoprime J p ∧ J≠0 := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  obtain ⟨J,hJ,hnd⟩ := (FiniteMultiplicity.of_prime_left hp hI).exists_eq_pow_mul_and_not_dvd
  have he : multiplicity p I=(normalizedFactors I).count p := by
    simpa only [normalize_eq] using multiplicity_eq_count_normalizedFactors hp.irreducible hI
  refine ⟨J,?_,maximal_coprime_of_not_dvd p J hnd,?_⟩
  · rw [←he,mul_comm]
    exact hJ
  · intro hz
    rw [hz,mul_zero] at hJ
    exact hI hJ

theorem exists_nonexceptional_separation (L R I p : Id) (hI : I≠0)
    [p.IsMaximal] (hp0 : p≠0) (hL : ¬p∣L) (hR : ¬p∣R) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧
      IsCoprime (L*R*J) (p^((normalizedFactors I).count p)) ∧ J≠0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_prime_separation I p hI hp0
  exact ⟨J,hJ,((maximal_coprime_of_not_dvd p L hL).mul_left
    (maximal_coprime_of_not_dvd p R hR)).mul_left hcop |>.pow_right,hJ0⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramResidue
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue_oai (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.ProbeGramCommon.exists_nonexceptional_residue_oai.{u_1} := @OAI.SevenEighths.ProbeGramCommon.exists_nonexceptional_residue_oai.{u_1}
