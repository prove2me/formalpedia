-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.sourceTruncation_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:00:31.309215+00:00
-- url     : https://prove2.me/submissions/5835e89f-798b-42a7-a31c-54e5e35a7efa

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_original_window_mobius_lattice

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Calibration
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

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

omit [Fintype R] in
theorem fullCorrelation_swap (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (j : R) :
    fullCorrelation left right f g j = star (fullCorrelation right left g f (-j)) := by
  classical
  simp only [fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  have heq : left x - right y = j ↔ right y - left x = -j := by
    constructor <;> intro h <;> linear_combination -h
  by_cases h : left x - right y = j
  · simp [h, heq.mp h, star_mul]
  · simp [h, not_congr heq |>.mp h]

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

theorem reductionMultiplicity_mul_card (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm

theorem reductionMultiplicity_eq_pow (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]

theorem fullCorrelation_unit_right (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_reduction_unit_right (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))

theorem fullCorrelation_reduction_unit_left (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring

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

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCommonSum
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
lemma fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=>rfl)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CRT
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem fullCorrelation_ringEquiv (e : A ≃+* B) (u v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => f (e x)) (fun y => g (e y)) k =
      fullCorrelation (fun x => e v * x) (fun y => e u * y) f g (e k) := by
  unfold fullCorrelation
  apply Fintype.sum_equiv e.toEquiv
  intro x
  apply Fintype.sum_equiv e.toEquiv
  intro y
  have heq : v * x - u * y = k ↔ e v * e x - e u * e y = e k := by
    rw [← map_mul, ← map_mul, ← map_sub, e.injective.eq_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, heq]

theorem fullCorrelation_pi {ι : Type*} [Fintype ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, Fintype (R i)]
    (u v k : ∀ i, R i) (f g : ∀ i, R i → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (fun x => v i * x) (fun y => u i * y) (f i) (g i) (k i) := by
  classical
  have hterm (x y : ∀ i, R i) :
      (if v * x - u * y = k then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if v i * x i - u i * y i = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, v i * x i - u i * y i = k i
    · have heq : v * x - u * y = k := funext h
      simp only [heq, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have hne : v * x - u * y ≠ k := fun heq => hi (congrFun heq i)
      rw [if_neg hne]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, R i, ∏ i, ∑ y : R i,
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : R i) =>
        if v i * x i - u i * y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => ∑ y : R i,
      if v i * x - u i * y = k i then f i x * star (g i y) else (0 : ℂ))).symm

end
end SevenEighths.CenteredMomentCorrelation

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

local instance instInfiniteRingOfIntegers_solutions_re04d4f_1 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

theorem primePowerReduction_multiplicity (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P

section Local
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]

local instance instInfiniteRingOfIntegers_solutions_re04d4f_2 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation.instFieldQuotientRingOfIntegersIdeal_definitions
theorem primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by
  rw [fullCorrelation_reduction_unit_right _ (primePowerReduction_surjective P hc),
    primePowerReduction_multiplicity, Nat.cast_pow]
  rfl

end Local
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

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (actualSextic P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

theorem canonicalCRTCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    canonicalCRTCharacter P hg c hc hcop (Ideal.Quotient.mk (∏ i, P i ^ c i) x) =
      CanonicalRowCompletion.idealRowHom x (∏ i, P i ^ c i) := by
  simp only [canonicalCRTCharacter, crtCharacter_apply,
    IdealGaussCRT.quotientProdEquivPi_mk, canonicalPrimePowerCharacter_mk, map_prod]

theorem canonicalCRTCorrelation {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i ^ c i)] [∀ i, Fintype (O ⧸ P i ^ c i)]
    (u v k : O ⧸ ∏ i, P i ^ c i) :
    let e := IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
      (pairwise_isCoprime_pow P c hcop)
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i)) k = _
  rw [fullCorrelation_ringEquiv (IdealGaussCRT.quotientProdEquivPi _ _) u v k
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i)), fullCorrelation_pi]

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

theorem supportedModulusCharacter_mul (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) (x : O) :
    supportedModulusCharacter (d * a) (supported_mul_elements d a hd ha) (Ideal.Quotient.mk _ x) =
      supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ x) := by
  simp only [supportedModulusCharacter_mk, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCommonActual
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma actualCommon_parameter (C : O) (hC : Supported (Ideal.span {C})) (n₁ n₂ a b k : O)
    (hab : a*n₁+b*n₂=1) :
    letI := finite_quotient_span (supported_element_ne_zero C hC)
    letI : Fintype (ResidueQ C) := Fintype.ofFinite _
    actualCommon C hC n₁ n₂ k=
      ∑t : ResidueQ C,
        supportedModulusCharacter C hC (Ideal.Quotient.mk _ (b*k)+Ideal.Quotient.mk _ n₁*t)*
          star (supportedModulusCharacter C hC (Ideal.Quotient.mk _ (-a*k)+Ideal.Quotient.mk _ n₂*t)) := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  have hh : Ideal.Quotient.mk (Ideal.span {C}) a*Ideal.Quotient.mk _ n₁+
      Ideal.Quotient.mk _ b*Ideal.Quotient.mk _ n₂=1 := by rw [←map_mul,←map_mul,←map_add,hab,map_one]
  rw [actualCommon,fullCorrelation_bezout _ _ _ _ _ hh]
  simp only [map_mul,map_neg]

theorem actual_common_lift_bezout (C n₁ n₂ a b k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hab : a*n₁+b*n₂=1) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      (idealRowHom (b*k) (Ideal.span {n₁})*star (idealRowHom (-a*k) (Ideal.span {n₂})))*
        actualCommon C hC n₁ n₂ k := by
  have hc := supported_element_ne_zero C hC
  have h₁n := supported_element_ne_zero n₁ h₁
  have h₂n := supported_element_ne_zero n₂ h₂
  let := finite_quotient_span hc
  let := finite_quotient_span (mul_ne_zero hc h₁n)
  let := finite_quotient_span (mul_ne_zero hc h₂n)
  let : Fintype (ResidueQ C) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₁)) := Fintype.ofFinite _
  let : Fintype (ResidueQ (C*n₂)) := Fintype.ofFinite _
  change fullModulusCorrelation (C*n₁) (C*n₂) _ _ (C*k)=_
  rw [fullModulusCorrelation_parameter C n₁ n₂ a b k hc h₁n hab,
    actualCommon_parameter C hC n₁ n₂ a b k hab,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨t,rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [leftParam_mk,rightParam_mk,supportedModulusCharacter_mul C n₁ hC h₁,
    supportedModulusCharacter_mul C n₂ hC h₂]
  have hleft : idealRowHom (b*k+n₁*t) (Ideal.span {n₁})=idealRowHom (b*k) (Ideal.span {n₁}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  have hright : idealRowHom (-a*k+n₂*t) (Ideal.span {n₂})=idealRowHom (-a*k) (Ideal.span {n₂}) := by
    apply idealRowHom_congr_mod
    exact Ideal.mem_span_singleton.mpr ⟨t,by ring⟩
  simp only [←map_mul,←map_add]
  simp only [supportedModulusCharacter_mk,hleft,hright,star_mul]
  ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCommonPhase
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_bezout_inverse (n m a b : O) (hn : Supported (Ideal.span {n}))
    (hab : a*n+b*m=1) :
    idealRowHom b (Ideal.span {n})=star (idealRowHom m (Ideal.span {n})) := by
  have he : idealRowHom (b*m) (Ideal.span {n})=1 := by
    rw [←idealRowHom_one_supported (Ideal.span {n}) hn]
    apply idealRowHom_congr_mod
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-a,?_⟩
    linear_combination hab
  rw [idealRowHom_argument_mul] at he
  let := finite_quotient_span (supported_element_ne_zero n hn)
  let : Fintype (ResidueQ n) := Fintype.ofFinite _
  change supportedModulusCharacter n hn (Ideal.Quotient.mk _ b)=
    star (supportedModulusCharacter n hn (Ideal.Quotient.mk _ m))
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  exact eq_inv_of_mul_eq_one_left he

theorem actual_common_lift (C n₁ n₂ k : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : ConcretePrimeRowBridge.goodLambda^2∣n₁-1)
    (hp₂ : ConcretePrimeRowBridge.goodLambda^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) (C*k)=
      idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        sexticReciprocityPhase n₁ n₂*actualCommon C hC n₁ n₂ k := by
  obtain ⟨a,b,hab⟩ := hn
  rw [actual_common_lift_bezout C n₁ n₂ a b k hC h₁ h₂ hab]
  have h₁b := supported_bezout_inverse n₁ n₂ a b h₁ hab
  have h₂a := supported_bezout_inverse n₂ n₁ b a h₂ (by simpa only [add_comm] using hab)
  have he : idealRowHom (-a*k) (Ideal.span {n₂})=
      idealRowHom a (Ideal.span {n₂})*idealRowHom (-k) (Ideal.span {n₂}) := by
    rw [show -a*k=a*(-k) by ring,idealRowHom_argument_mul]
  rw [idealRowHom_argument_mul,he,h₁b,h₂a,star_mul,star_star]
  let := finite_quotient_span (supported_element_ne_zero n₁ h₁)
  let : Fintype (ResidueQ n₁) := Fintype.ofFinite _
  have hphase := supported_opposite_phase n₁ n₂ h₁ h₂ hp₁ hp₂ ⟨a,b,hab⟩
  calc
    _ = idealRowHom k (Ideal.span {n₁})*star (idealRowHom (-k) (Ideal.span {n₂}))*
        (idealRowHom n₁ (Ideal.span {n₂})*star (idealRowHom n₂ (Ideal.span {n₁})))*actualCommon C hC n₁ n₂ k := by ring
    _ = _ := by rw [hphase]

end SevenEighths.ProbeGramCommon
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

theorem primePower_common_extension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤ c) [Fintype (O⧸P^c)] (n₁ n₂ k : O)
    (hn : n₁∉P ∨ n₂∉P) :
    fullCorrelation (fun x : O⧸P^c=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸P^c=>Ideal.Quotient.mk _ n₁*y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) (Ideal.Quotient.mk _ k)=
      localExtension P hg c n₁ n₂ k := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  have hn' : ¬(n₁∈P ∧ n₂∈P) := by tauto
  rw [localExtension,if_neg hn']
  rcases hn with h₁|h₂
  · have hu : IsUnit (Ideal.Quotient.mk (P^c) n₁) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₁ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨u,hu⟩ := hu
    rw [←hu]
    unfold primePowerRow
    rw [primePower_localCorrelation]
    simp only [primePowerReduction,Ideal.Quotient.factor_mk,hu]
  · have hv : IsUnit (Ideal.Quotient.mk (P^c) n₂) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₂ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨v,hv⟩ := hv
    rw [←hv]
    unfold primePowerRow
    rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
      primePowerReduction_multiplicity,Nat.cast_pow]
    change (Ideal.absNorm P:ℂ)^(c-1)*localCorrelation (actualSextic P hg^c)
      (primePowerReduction P hc (Ideal.Quotient.mk _ n₁)) (primePowerReduction P hc v)
      (primePowerReduction P hc (Ideal.Quotient.mk _ k))=_
    simp only [hv,primePowerReduction,Ideal.Quotient.factor_mk]

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

theorem canonical_common_extension (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,goodLambda∉P i) (c : ι→ℕ) (hc : ∀i,1≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k)=globalExtension P hg c n₁ n₂ k := by
  have hpc : Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
    intro i j hij
    exact (hcop hij).pow
  have he := canonicalCRTCorrelation P hg c hc hcop
    (Ideal.Quotient.mk _ n₁) (Ideal.Quotient.mk _ n₂) (Ideal.Quotient.mk _ k)
  have hprod : fullCorrelation (fun x : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸∏i,P i^c i=>Ideal.Quotient.mk _ n₁*y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop)
      (Ideal.Quotient.mk _ k) =
      ∏i,fullCorrelation (fun x : O⧸P i^c i=>Ideal.Quotient.mk _ n₂*x)
        (fun y : O⧸P i^c i=>Ideal.Quotient.mk _ n₁*y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (Ideal.Quotient.mk _ k) := by
    simpa only [IdealGaussCRT.quotientProdEquivPi_mk
      (fun i => P i ^ c i) hpc] using he
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i hi
  apply primePower_common_extension
  by_contra h
  push Not at h
  obtain ⟨a,b,hab⟩ := hn
  have hmem : (1:O)∈P i := by
    rw [←hab]
    exact (P i).add_mem ((P i).mul_mem_left a h.1) ((P i).mul_mem_left b h.2)
  exact (Ideal.IsMaximal.ne_top (I:=P i) inferInstance) ((Ideal.eq_top_iff_one (P i)).mpr hmem)

theorem actualCommon_eq_globalExtension (C : O) (hC : Supported (Ideal.span {C}))
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i)
    (c : ι→ℕ) (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ k : O) (hn : IsCoprime n₁ n₂) :
    actualCommon C hC n₁ n₂ k=globalExtension P hg c n₁ n₂ k := by
  let := finite_quotient_span (supported_element_ne_zero C hC)
  let : Fintype (O⧸Ideal.span {C}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq he
  have hchar : (supportedModulusCharacter C hC : (O⧸Ideal.span {C})→ℂ)=
      (fun x=>canonicalCRTCharacter P hg c hc hcop (e x)) := by
    funext x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show e (Ideal.Quotient.mk _ x)=Ideal.Quotient.mk _ x from Ideal.quotEquivOfEq_mk he x,
      canonicalCRTCharacter_mk,supportedModulusCharacter_mk,he]
  rw [actualCommon,hchar,fullCorrelation_ringEquiv e]
  simp only [e,Ideal.quotEquivOfEq_mk]
  exact canonical_common_extension P hg c hc hcop n₁ n₂ k hn

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPuncture
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

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

lemma gramPeriodicMonoid_zero (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) (hn : ¬IsCoprime B n) :
    gramPeriodicMonoid C B D n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hn]
  change star (C.residueMonoid n)*
    ((((1:O→*ℂ) n*coprimalityMask B n)*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
      movingNumeratorRow D.numeratorGood D.numeratorSupported n)=0
  rw [hm]
  simp

lemma gramPeriodicMonoid_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    gramPeriodicMonoid C B D n=(C.residueMonoid n)⁻¹*idealRowHom C.generator (Ideal.span {n}) := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [if_pos hc]
  simp only [MonoidHom.one_apply,hm,one_mul,one_pow] at he
  change star (C.residueMonoid n)*_=_
  rw [←he]
  congr 1
  let := finite_quotient_span C.generator_ne_zero
  let : Fintype (O⧸Ideal.span {C.generator}) := Fintype.ofFinite _
  change star (C.residue (Ideal.Quotient.mk _ n))=(C.residue (Ideal.Quotient.mk _ n))⁻¹
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']

theorem lowArithmeticCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s : {I : Id // Supported I}) :
    lowArithmeticCoefficient (calibrationForSet S hS) s=
      (calibrationForSet S hS).tau⁻¹*
        gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
          (calibrationLowData S hS) (primaryGenerator s.val) := by
  let C := calibrationForSet S hS
  have hn := supported_primaryGenerator_ne_zero s.val s.property
  have he := (primaryGenerator_spec s.val hn).1
  have hp := (primaryGenerator_spec s.val hn).2
  have hsupp := (supported_span_primaryGenerator_iff s.val).mpr s.property
  have hb := calibration_generator_bad S hS hbad
  by_cases hc : IsCoprime C.generator (primaryGenerator s.val)
  · have hguard : ∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact (calibration_coprime_iff_excluded_span S hS _).mp hc
    rw [lowArithmeticCoefficient,if_pos hguard,
      gramPeriodicMonoid_primary C C.generator (calibrationLowData S hS) hb.1 hb.2 _ hsupp hp hc,he]
    ring
  · have hguard : ¬∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact fun h=>hc ((calibration_coprime_iff_excluded_span S hS _).mpr h)
    rw [lowArithmeticCoefficient,if_neg hguard,gramPeriodicMonoid_zero C C.generator (calibrationLowData S hS) _ hc,mul_zero]

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

theorem lowGramCoefficient_eq_extension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      gramCoefficientExtension S hS σ (primaryGenerator s.val) := by
  unfold lowGramCoefficient gramCoefficientExtension
  change (if physicalRay (primaryGenerator s.val)=σ then _ else 0)=_
  rw [lowArithmeticCoefficient_periodic S hS hbad s]

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

lemma numeratorExtension_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

lemma numeratorExtension_neg_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointSource
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : Supported (Ideal.span {C}))
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ : O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : λ₀^2∣n₁-1) (hp₂ : λ₀^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring

lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryGenerator s.val) := by
  have hp : λ₀^2∣primaryGenerator s.val-1 := (primaryGenerator_spec s.val
    (supported_primaryGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,if_pos hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryGenerator (supportedIdealProduct D J).val=primaryGenerator D.val*primaryGenerator J.val :=
  primaryGenerator_mul _ _

lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramPoisson
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2=
      ‖eisEmbedding h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1,
    (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramShell
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramWindowMobius
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖eisEmbedding (primaryGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCommonSource
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma common_column_ratio (C I : SupportedIdeal) (Y : ℝ) :
    (Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y=(Ideal.absNorm I.val:ℝ)/commonResidualScale C Y := by
  rw [supported_dilation_norm,Nat.cast_mul,commonResidualScale,div_div_eq_mul_div]
  ring
lemma common_kernel_scale (C I J : SupportedIdeal) (k : O) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/commonResidualScale C Y)*((Ideal.absNorm J.val:ℝ)/commonResidualScale C Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ,common_column_ratio,common_column_ratio,
    map_mul,norm_mul,mul_pow,primary_norm]
  unfold frequencyScale
  ring

theorem original_common_window_source (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : O)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P)) (he : C.val=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let N:=commonResidualScale C Y
    let hN:=commonResidualScale_pos C Y hY
    let F:=lowGaussColumns W hW N hN
    (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)=
      ∑D∈divisorPool F Subtype.val,(moebius D:ℂ)*∑'n : O,∑'m : O,
        jointExtension S hS σ (primaryGenerator C.val) k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
          shellProfile W v U (frequencyScale C k Y Q) (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
            (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  dsimp only
  have hpc : λ₀^2∣primaryGenerator C.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).2
  rw [←original_window_mobius_lattice S hS hbad σ (primaryGenerator C.val) k hpc
    u a b r hr P hg c W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
    U v (frequencyScale C k Y Q)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs with hIJ
  · have hni : Supported (Ideal.span {primaryGenerator I.val}) := (supported_span_primaryGenerator_iff _).mpr I.property
    have hnj : Supported (Ideal.span {primaryGenerator J.val}) := (supported_span_primaryGenerator_iff _).mpr J.property
    have hpi : λ₀^2∣primaryGenerator I.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2
    have hpj : λ₀^2∣primaryGenerator J.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).2
    have hij : IsCoprime (primaryGenerator I.val) (primaryGenerator J.val) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
        (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hIJ
    have hf : Ideal.span {primaryGenerator C.val}=∏i,P i^c i := by
      rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1,he]
    rw [jointExtension_source S hS σ (primaryGenerator C.val) k
      ((supported_span_primaryGenerator_iff _).mpr C.property) u a b r hr hpr hk P hg c hc hcop hf
      _ _ hni hnj hpi hpj hij]
    rw [lowGramCoefficient_eq_primary S hS hbad σ,lowGramCoefficient_eq_primary S hS hbad σ,
      common_kernel_scale C I J k Y Q hY hQ,common_column_ratio,common_column_ratio]
    simp only [supported_dilation_generator,shellProfile,star_mul]
    ring
  · rfl

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCanonical
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramLatticeWindow
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    Summable (fun m : O×O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramCanonicalSource
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0<commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=>canonicalJoint S hS σ C k (primaryGenerator D*n) (primaryGenerator D*m))).tsum_prod.symm

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramWeightedFrequency
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramSourceDivisors
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceDivisors_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    D∈sourceDivisors W hW Y hY C ↔
      D.val∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val := Finset.mem_preimage

lemma sourceDivisors_sum (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (C : SupportedIdeal) (f : Id→ℂ) :
    (∑D∈sourceDivisors W hW Y hY C,f D.val)=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,f D := by
  apply Finset.sum_bij (fun D _=>D.val)
  · intro D hD;exact (sourceDivisors_mem W hW Y hY C D).mp hD
  · intro D hD E hE h;exact Subtype.val_injective h
  · intro D hD
    refine ⟨⟨D,divisorPool_supported _ _ hD⟩,?_,rfl⟩
    exact (sourceDivisors_mem W hW Y hY C _).mpr hD
  · intro D hD;rfl

lemma sourceMobiusWeight_rectangle (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) (hC : C∈F) (f : SupportedIdeal→ℂ) :
    (∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*f D)=
      ∑D∈sourceDivisors W hW Y hY C,(moebius D.val:ℂ)*f D := by
  rw [←Finset.sum_subset (show sourceDivisors W hW Y hY C⊆sourceDivisorUnion F W hW Y hY from
    fun D hD=>Finset.mem_biUnion.mpr ⟨C,hC,hD⟩) (by intro D hD hn;simp only [sourceMobiusWeight,if_neg hn,zero_mul])]
  exact Finset.sum_congr rfl (fun D hD=>by rw [sourceMobiusWeight,if_pos hD])

theorem originalCommonBlock_eq_rectangle (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (C : SupportedIdeal) (hC : C∈F)
    (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
        canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
          ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C))
          (Y/(gramIdealNorm C*gramIdealNorm D)) := by
  rw [sourceMobiusWeight_rectangle F W hW Y hY C hC]
  rw [originalCommonBlock_eq_lattice S hS hbad σ C k W hW Y Q hY hQ U v]
  rw [←sourceDivisors_sum W hW Y hY C]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  rw [frequencyScale_ratio]
  congr 1
  simp only [commonResidualScale,gramIdealNorm,div_div]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramTruncation
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sourceTruncation_eq_canonical_oai (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (E : Finset GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceTruncation S hS σ F E W hW Y Q hY U v=sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v := by
  unfold sourceTruncation sourceCanonicalSum
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  simp_rw [originalCommonBlock_eq_rectangle S hS hbad σ F C hC _ W hW Y Q hY hQ U v]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun D hD=>(Finset.mul_sum ..).symm)

end SevenEighths.ProbeGramCommon
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeGramCommon.sourceTruncation_eq_canonical_oai := @OAI.SevenEighths.ProbeGramCommon.sourceTruncation_eq_canonical_oai
