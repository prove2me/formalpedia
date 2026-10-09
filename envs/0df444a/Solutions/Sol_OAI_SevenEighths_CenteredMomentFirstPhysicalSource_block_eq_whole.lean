-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentFirstPhysicalSource.block_eq_whole
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:39:31.835712+00:00
-- url     : https://prove2.me/submissions/ec2f25a7-dca8-4d12-b8e4-6a8917bab634

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end IdealGaussCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace ActualEisensteinCubic

theorem canonical_finite_prime_gauss_transform_scalar
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

theorem canonical_finite_prime_gauss_transform_conj
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    finiteSexticQuotientRow_inv_eq_star]

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

theorem canonical_principal_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj P hcop hgood hchar j hj0 hj6 φ (e h)

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Support
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Fourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

theorem quotientTrace_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    (h : Residue m) (x : Residue d) :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPoisson
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFirstPoisson
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma principalCRT_scaled_left (a b : O) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : O) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

theorem residueGauss_inverse (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    residueGauss d hd χ⁻¹ h = star (residueGauss d hd χ (-h)) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  have htrace (x : Residue d) : star (quotientTrace d hd x) = quotientTrace d hd (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((quotientTrace d hd).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [residueGauss, tsum_fintype, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

end SevenEighths.CenteredMomentFirstPoisson
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationCRT
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem coprime_mixed_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss a ha χa (frequencyReduction a (a*b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
          quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Active
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
open CanonicalRowCompletion CenteredMomentCanonical

theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2

theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)

variable {ι : Type*}

open ConcreteTraceCRT EisensteinSchwartzPoisson

end SevenEighths.CenteredMomentActive
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Primitive
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimitive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma sqrt_absNorm (r : O) :
    Real.sqrt (Ideal.absNorm (Ideal.span {r}) : ℝ) = ‖eisEmbedding r‖ := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

end SevenEighths.CenteredMomentPrimitive
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstMixed
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstMixed
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem frequencyReduction_comp (d n M : O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [frequencyReduction_mk]

theorem three_factor_mixed_fourier (a b c : O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        quotientTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          quotientTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
      G (frequencyReduction c (b*c) (dvd_mul_left _ _) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (dvd_mul_left _ _) x) =
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (mul_ne_zero hb hc) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (dvd_mul_right _ _) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (dvd_mul_left _ _) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end SevenEighths.CenteredMomentFirstMixed

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstReduced
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstReduced
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

theorem principalSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (j : ι → ℕ) (r : O) (hr : Ideal.span {r}=∏ i,P i) (x y : Residue r) :
    principalSexticRow P hcop hg j r hr (x*y)=
      principalSexticRow P hcop hg j r hr x*principalSexticRow P hcop hg j r hr y := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul,principalSexticRow_mk P hcop hg j r hr (x*y),
    principalSexticRow_mk P hcop hg j r hr x,principalSexticRow_mk P hcop hg j r hr y,
    finiteSexticRow_mul P hg j x y]

end SevenEighths.CenteredMomentFirstReduced

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstActiveFourier
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstActiveFourier
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

theorem shifted_active_fourier {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6) (v h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  change finiteSexticRow P hg j v*(star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j)=_
  ring

theorem tripleFourier_active {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : a≠0) (hb : b≠0)
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

end SevenEighths.CenteredMomentFirstActiveFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentFirstActiveFourier CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSectors
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonSectors
open CenteredMomentCompleteCommon CenteredMomentSupport IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem primeSupport_mul (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    primeSupport (I*J)=primeSupport I∪primeSupport J := by
  simp only [primeSupport,normalizedFactors_mul hI hJ,Multiset.toFinset_add]

theorem supportExtract_of_subset (I : Ideal O) (hI : I≠0) (S : Finset (Ideal O))
    (hS : primeSupport I⊆S) : supportExtract I S=I := by
  unfold supportExtract
  rw [Multiset.filter_eq_self.mpr (fun P hP => hS (Multiset.mem_toFinset.mpr hP))]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_of_disjoint (I : Ideal O) (S : Finset (Ideal O))
    (hS : Disjoint (primeSupport I) S) : supportExtract I S=1 := by
  unfold supportExtract
  rw [Multiset.filter_eq_nil.mpr (fun P hP => Finset.disjoint_left.mp hS (Multiset.mem_toFinset.mpr hP))]
  rfl

theorem reconstructed_commonSupport (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonSupport (C*a) (D*b)=primeSupport C := by
  unfold commonSupport
  rw [primeSupport_mul C a hC ha,primeSupport_mul D b hD hb,← hCD]
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  have h₃ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff ha hb).mpr hab
  ext P
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hc|ha',hd|hb'⟩
    · exact hc
    · exact hc
    · exact hd
    · exact False.elim (Finset.disjoint_left.mp h₃ ha' hb')
  · exact fun hp => ⟨Or.inl hp,Or.inl hp⟩

theorem reconstructed_commonParts (C D a b : Ideal O)
    (hC : C≠0) (hD : D≠0) (ha : a≠0) (hb : b≠0)
    (hCD : primeSupport C=primeSupport D)
    (hCa : IsCoprime C a) (hCb : IsCoprime C b) (hab : IsCoprime a b) :
    commonPart (C*a) (D*b)=C ∧ commonPart (D*b) (C*a)=D := by
  have hs := reconstructed_commonSupport C D a b hC hD ha hb hCD hCa hCb hab
  have h₁ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha).mpr hCa
  have h₂ := (IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hb).mpr hCb
  constructor
  · rw [commonPart_eq_supportExtract,hs,supportExtract_mul C a hC ha,
      supportExtract_of_subset C hC _ (Finset.Subset.refl _),supportExtract_of_disjoint a _ h₁.symm,mul_one]
  · rw [commonPart_eq_supportExtract,commonSupport_comm (D*b) (C*a),hs,
      supportExtract_mul D b hD hb,
      supportExtract_of_subset D hD _ (by rw [hCD]),supportExtract_of_disjoint b _ h₂.symm,mul_one]

end SevenEighths.CenteredMomentCommonSectors

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstNormalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstNormalization
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentSupportedCorrelation CenteredMomentFirstReduced CenteredMomentFirstActiveFourier
open CenteredMomentGaussEnergy CenteredMomentPrimitive CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem residueGauss_eq_norm_mul_gaussRow (a : O) (ha : Supported (Ideal.span {a})) (h : O) :
    residueGauss a (supported_element_ne_zero a ha) (supportedModulusCharacter a ha) (Ideal.Quotient.mk _ h)=
      (‖eisEmbedding a‖:ℂ)*gaussRow a ha h := by
  have hn : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  rw [gaussRow,residueGauss_supported_mk,sqrt_absNorm]
  field_simp

theorem normalized_active_coefficient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h /
      (‖eisEmbedding (a*(b*r))‖^2:ℝ) =
      (canonicalNormalizedGauss P hcop hg j /
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)*(‖eisEmbedding r‖:ℂ)))*
      (CanonicalRowCompletion.idealRowHom (b*r) (Ideal.span {a})*
        star (CanonicalRowCompletion.idealRowHom (a*r) (Ideal.span {b}))*finiteSexticRow P hg j (a*b))*
      (star (finiteSexticRow P hg j h)*gaussRow a ha h*star (gaussRow b hb (-h))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hna : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  have hnb : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb)))
  have hnr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb) har hbr,
    residueGauss_inverse,← map_neg,residueGauss_eq_norm_mul_gaussRow a ha,
    residueGauss_eq_norm_mul_gaussRow b hb,← MulChar.star_apply',
    supportedModulusCharacter_mk,supportedModulusCharacter_mk]
  simp only [canonicalNormalizedGauss,map_mul,norm_mul,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentFirstNormalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstFrequency
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstNormalization CenteredMomentFirstReduced CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentPrimitive CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem normalized_dilated_frequency {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    let ρ := finiteSexticRow P hg j
    tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G e*
      ((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*
      tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
        (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/(‖eisEmbedding r‖:ℂ))*star (ρ h)*
        originalPhase e r ρ a b*
        ((gaussRow a ha h/(‖eisEmbedding a‖:ℂ))*star (gaussRow b hb (-h)/(‖eisEmbedding b‖:ℂ))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have he := normalized_active_coefficient P hcop hg hchar j hj0 hj6 a b ha hb har hbr h
  dsimp only at he
  rw [Complex.ofReal_div]
  calc
    _ = (k:ℂ)*tripleRow a b (finitePrimeModulus P) (supportedModulusCharacter a ha)
        (supportedModulusCharacter b hb)⁻¹
        (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) e*
        (tripleFourier a b (finitePrimeModulus P) (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹
          (principalSexticRow P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)) h /
          (‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2:ℝ)) := by ring
    _ = _ := by
      rw [he,tripleRow,← MulChar.star_apply',supportedModulusCharacter_mk,
        supportedModulusCharacter_mk,
        principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P) e]
      simp only [originalPhase,Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring

end SevenEighths.CenteredMomentFirstFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Scale
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

end SevenEighths.CenteredMomentScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentFirstAssembly
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

theorem dilated_frequency_whole_kernel {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    dilatedFrequency P hcop hg j e a b ha hb k h *
      windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀ *
      paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)=
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        star (ρ h)*originalPhase e r ρ a b *
        (gaussRow a ha h*star (gaussRow b hb (-h)))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log (‖eisEmbedding a‖^2/A₀)) (Real.log (‖eisEmbedding b‖^2/B₀)) := by
  dsimp only
  have haN : 0<‖eisEmbedding a‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha))
  have hbN : 0<‖eisEmbedding b‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb))
  have hrN : 0<‖eisEmbedding (finitePrimeModulus P)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  have hhN : 0<‖eisEmbedding h‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
  have hk' : 0<k/‖eisEmbedding (finitePrimeModulus P)‖^2 := div_pos hk (sq_pos_of_pos hrN)
  rw [show dilatedFrequency P hcop hg j e a b ha hb k h=_ from
    normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e a b ha hb har hbr k h]
  rw [wholeKernel_actual W V _ _ _ _ K₀ H₀ A₀ B₀ hk' (sq_pos_of_pos hhN)
    (sq_pos_of_pos haN) (sq_pos_of_pos hbN) hK₀ hH₀ hA₀ hB₀]
  have harg : k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2=
      (k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2) := by
    simp only [map_mul,norm_mul]
    ring
  rw [harg]
  simp only [windows,Real.sqrt_sq haN.le,Real.sqrt_sq hbN.le,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  have hA : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hB : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  have hr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrN.ne'
  have ha' : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr haN.ne'
  have hb' : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hbN.ne'
  have alg (c r a b A B x y u v : ℂ) (hr : r≠0) (ha : a≠0) (hb : b≠0)
      (hA : A≠0) (hB : B≠0) :
      (c/r*x*(u/a*(v/b)))*y=c/(r*A*B)*x*(u*v)*((A*B/(a*b))*y) := by
    field_simp
  convert (preTransparency := .instances) alg ((k:ℂ)*canonicalNormalizedGauss P hcop hg j)
    (‖eisEmbedding (finitePrimeModulus P)‖:ℂ) (‖eisEmbedding a‖:ℂ) (‖eisEmbedding b‖:ℂ)
    (Real.sqrt A₀:ℂ) (Real.sqrt B₀:ℂ)
    (star (finiteSexticRow P hg j h)*originalPhase e (finitePrimeModulus P) (finiteSexticRow P hg j) a b)
    (windows V (k/‖eisEmbedding (finitePrimeModulus P)‖^2) (‖eisEmbedding h‖^2)
      (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀*
      paperRadialFourier W ((k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2)))
    (gaussRow a ha h) (star (gaussRow b hb (-h))) hr ha' hb' hA hB using 1 <;>
    simp only [windows,Complex.star_def] <;> ring

end SevenEighths.CenteredMomentFirstWholeKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

lemma active_span_dvd (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D):Ideal.span {activeConductor C D}∣C:=by
  have hh:=activeConductor_span_dvd C D
  rw [(fixed_common_parts C D hC hD hCD).1] at hh
  exact hh

lemma element_coprime_active (C D B:Ideal O)(hC:C≠0)(hD:D≠0)(hB:B≠0)
    (hCD:primeSupport C=primeSupport D)(S:Finset (Ideal O))(a:columns C B hB S):
    IsCoprime (element C B hB S a) (activeConductor C D):=by
  rw [←Ideal.isCoprime_span_singleton_iff,element_span]
  exact (Finset.mem_filter.mp a.property).2.symm.of_isCoprime_of_dvd_right (active_span_dvd C D hC hD hCD)

theorem block_eq_whole_oai (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0<K)(hK₀:0<K₀)(hH₀:0<H₀)(hA₀:0<A₀)(hB₀:0<B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖eisEmbedding r‖^2)/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
            (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)):=by
  dsimp only
  have he:primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E≠0:=
    supported_element_ne_zero _ (subsetGenerator_supported C D hC E)
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
  unfold block scalar
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hcop:IsCoprime (element C C hC.1 S a) (element C D hD.1 S b)↔
      IsCoprime (a:Ideal O) (b:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,element_span,element_span]
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true,hcop]
    have hh:=dilated_frequency_whole_kernel (activePrime C D) (activeCoprime C D)
      (activeGood C D hC) (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)
      (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
      (element C C hC.1 S a) (element C D hD.1 S b)
      (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
      ((hcop.mpr hab).mul_right (element_coprime_active C D C hC.1 hD.1 hC.1 hCD S a))
      (element_coprime_active C D D hC.1 hD.1 hD.1 hCD S b)
      _ hk h (hrows h hh) W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
    dsimp only at hh
    change inactiveWeight C D E * (_*_*_*_)=_
    calc
      _=inactiveWeight C D E*(coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (dilatedFrequency (activePrime C D) (activeCoprime C D) (activeGood C D hC)
          (activeExponent C D) (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
          (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2) h *
        windows V _ _ _ _ K₀ H₀ A₀ B₀ * EisensteinSchwartzPoisson.paperRadialFourier W _):=by
          dsimp [dilatedFrequency,activeFunction,activeConductor];ring
      _=_:=by rw [hh];dsimp only [activeConductor];ring
  · simp [hab,hcop]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.block_eq_whole_oai := @OAI.SevenEighths.CenteredMomentFirstPhysicalSource.block_eq_whole_oai
