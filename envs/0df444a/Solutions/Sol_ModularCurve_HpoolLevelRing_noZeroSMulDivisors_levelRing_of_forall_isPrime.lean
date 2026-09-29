-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.noZeroSMulDivisors_levelRing_of_forall_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/212230d3-075f-58fa-b3c0-8d72e85b4bdb

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime.ModularCurve ModularCurve.HpoolLevelRing P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime.ModularCurve.HpoolLevelRing"

namespace Ideal
p2m_export "Ideal" "Quotient.algebraMap_eq Quotient.eq_zero_iff_mem Quotient.eq map_span isUnit_iff span Quotient.mk map mem_span_singleton' IsPrime comap Quotient.mk_surjective"
namespace Quotient
p2m_export "Ideal.Quotient" "algebraMap_eq eq_zero_iff_mem ring mk algebra mk_surjective"
p2m_open "Ideal.Quotient Ideal"

variable {A : Type*} [CommRing A]

theorem mem_span_singleton_of_mul_mem {a x y : A} (ha : IsSMulRegular A a)
    (hx : ∀ z : A, x * z ∈ Ideal.span {a} → z ∈ Ideal.span {a}) (h : a * y ∈ Ideal.span {x}) :
    y ∈ Ideal.span {x} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp h
  have hz' : x * z ∈ Ideal.span {a} := Ideal.mem_span_singleton'.mpr ⟨y, by rw [mul_comm x z, hz, mul_comm]⟩
  obtain ⟨z', hz''⟩ := Ideal.mem_span_singleton'.mp (hx z hz')
  have : a * y = a * (z' * x) := by rw [← hz, ← hz'']; ring
  exact Ideal.mem_span_singleton'.mpr ⟨z', (ha this).symm⟩

theorem isSMulRegular_quotient_span_singleton_swap {a x : A} (ha : IsSMulRegular A a)
    (hx : IsSMulRegular (A ⧸ Ideal.span {a}) x) : IsSMulRegular (A ⧸ Ideal.span {x}) a := by
  intro y₁ y₂ h
  obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective y₁
  obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective y₂
  change a • Ideal.Quotient.mk (Ideal.span {x}) y₁ = a • Ideal.Quotient.mk (Ideal.span {x}) y₂ at h
  simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] at h
  rw [Ideal.Quotient.eq, ← mul_sub] at h
  rw [Ideal.Quotient.eq]
  refine mem_span_singleton_of_mul_mem ha (fun z hz => ?_) h
  have h0 : x • Ideal.Quotient.mk (Ideal.span {a}) z = x • (0 : A ⧸ Ideal.span {a}) := by
    rw [smul_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hx h0)

end Ideal.Quotient

section LocalisedQuotient

variable {A : Type*} [CommRing A]

namespace IsLocalization p2m_export "IsLocalization" "Away mk'_spec mk'_eq_mul_mk'_one subsingleton Away.algebraMap_isUnit map mk' mk'_surjective flat isDomain_of_le_nonZeroDivisors map_under map_eq_zero_iff isPrincipalIdealRing_of_isPrincipalIdealRing" end IsLocalization
p2m_open_scoped "IsLocalization" in

theorem IsLocalization.isSMulRegular_quotient_map_of_notMem (M : Submonoid A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization M S] (I : Ideal A) [I.IsPrime] {x : A} (hx : x ∉ I) :
    IsSMulRegular (S ⧸ I.map (algebraMap A S)) (algebraMap A S x) := by

  haveI : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) M) (S ⧸ I.map (algebraMap A S)) := inferInstance
  set N := Algebra.algebraMapSubmonoid (A ⧸ I) M with hN
  by_cases h0 : (0 : A ⧸ I) ∈ N
  ·
    haveI : Subsingleton (S ⧸ I.map (algebraMap A S)) := IsLocalization.subsingleton h0
    exact fun _ _ _ => Subsingleton.elim _ _
  ·
    have hle : N ≤ nonZeroDivisors (A ⧸ I) := fun n hn =>
      mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hn))
    haveI : IsDomain (S ⧸ I.map (algebraMap A S)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    have hinj : Function.Injective (algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S))) :=
      IsLocalization.injective _ hle
    have hne : algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S)) (Ideal.Quotient.mk I x) ≠ 0 := by
      rw [Ne, _root_.map_eq_zero_iff (algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S))) hinj, Ideal.Quotient.eq_zero_iff_mem]
      exact hx

    have key : ∀ y : S ⧸ I.map (algebraMap A S),
        algebraMap A S x • y = algebraMap (A ⧸ I) (S ⧸ I.map (algebraMap A S)) (Ideal.Quotient.mk I x) * y := by
      intro y
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      rfl
    intro y₁ y₂ h
    simp only [key] at h
    exact mul_left_cancel₀ hne h

end LocalisedQuotient

namespace ModularCurve
namespace HpoolLevelRing
p2m_export "ModularCurve.HpoolLevelRing" "neZero_of_fact_prime Afin AfinAway levelRing"
p2m_open "ModularCurve.HpoolLevelRing ModularCurve"

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] neZero_of_fact_prime

set_option synthInstance.maxHeartbeats 800000 in

theorem aeval_algebraMap_eq (f : ℤ) (u : Afin p) (g : ℤ[X]) :
    Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) u) g = algebraMap (Afin p) (AfinAway p f) (Polynomial.aeval (R := ℤ) u g : Afin p) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1

theorem span_natCast_eq_map (f : ℤ) (l : ℕ) :
    Ideal.span {((l : ℕ) : AfinAway p f)} = (Ideal.span {((l : ℕ) : Afin p)}).map (algebraMap (Afin p) (AfinAway p f)) := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

theorem isSMulRegular_levelRing_natCast' (f : ℤ) (hf : f ≠ 0) (u : Afin p) (g : ℤ[X]) (l : ℕ) (hl : l.Prime)
    (hdom : (Ideal.span {((l : ℕ) : Afin p)}).IsPrime)
    (hne : (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((l : ℕ) : Afin p)}) :
    IsSMulRegular (levelRing p f u g) ((l : ℕ) : AfinAway p f) := by

  have hfA : (algebraMap ℤ (Afin p) f) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℤ (Afin p)).injective_int]
    exact hf
  haveI : IsDomain (AfinAway p f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (AfinAway p f) (powers_le_nonZeroDivisors_of_noZeroDivisors hfA)

  have hlA : ((l : ℕ) : Afin p) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hlAf : ((l : ℕ) : AfinAway p f) ≠ 0 := by
    rw [← map_natCast (algebraMap (Afin p) (AfinAway p f)), Ne,
      map_eq_zero_iff _ (IsLocalization.injective (AfinAway p f) (powers_le_nonZeroDivisors_of_noZeroDivisors hfA))]
    exact hlA
  have ha : IsSMulRegular (AfinAway p f) ((l : ℕ) : AfinAway p f) := (IsRegular.of_ne_zero hlAf).left.isSMulRegular

  have hx : IsSMulRegular (AfinAway p f ⧸ Ideal.span {((l : ℕ) : AfinAway p f)})
      (Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) u) g) := by
    rw [aeval_algebraMap_eq, span_natCast_eq_map]
    haveI := hdom
    exact IsLocalization.isSMulRegular_quotient_map_of_notMem (Submonoid.powers (algebraMap ℤ (Afin p) f))
      (AfinAway p f) _ hne
  exact Ideal.Quotient.isSMulRegular_quotient_span_singleton_swap ha hx

theorem isSMulRegular_levelRing_natCast (f : ℤ) (hf : f ≠ 0) (u : Afin p) (g : ℤ[X]) (l : ℕ) (hl : l.Prime)
    (hdom : (Ideal.span {((l : ℕ) : Afin p)}).IsPrime)
    (hne : (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((l : ℕ) : Afin p)}) :
    IsSMulRegular (levelRing p f u g) ((l : ℕ) : Localization.Away f) := by
  have h := isSMulRegular_levelRing_natCast' p f hf u g l hl hdom hne
  intro y₁ y₂ hy
  apply h
  simpa only [← map_natCast (algebraMap (Localization.Away f) (AfinAway p f)), algebraMap_smul] using hy

end ModularCurve.HpoolLevelRing

section AlgebraSMul

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

namespace IsSMulRegular p2m_export "IsSMulRegular" "zero of_ne_zero" end IsSMulRegular
p2m_open_scoped "IsSMulRegular" in

theorem IsSMulRegular.of_isUnit_algebraMap {v : R} (hv : IsUnit v) : IsSMulRegular B v := fun x y h =>
  (hv.map (algebraMap R B)).mul_left_cancel (by simpa only [Algebra.smul_def] using h)

p2m_open_scoped "IsSMulRegular" in

theorem IsSMulRegular.mul_algebraMap {a b : R} (ha : IsSMulRegular B a) (hb : IsSMulRegular B b) :
    IsSMulRegular B (a * b) := fun x y h =>
  hb (ha (by simpa only [Algebra.smul_def, map_mul, mul_assoc] using h))

end AlgebraSMul

namespace ModularCurve
namespace HpoolLevelRing
p2m_export "ModularCurve.HpoolLevelRing" "neZero_of_fact_prime Afin AfinAway levelRing"
p2m_open "ModularCurve.HpoolLevelRing ModularCurve"

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] neZero_of_fact_prime

section PID

private theorem _root_.IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] : IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (I.comap (algebraMap R S))).principal
  refine ⟨⟨algebraMap R S x, ?_⟩⟩
  rw [← IsLocalization.map_under M S I]
  change Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) I) = Ideal.span {algebraMap R S x}
  rw [show Ideal.comap (algebraMap R S) I = Ideal.span {x} from hx, Ideal.map_span, Set.image_singleton]

p2m_alias "P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime.IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing" "IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing"
end PID

theorem isSMulRegular_levelRing_of_ne_zero (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)})
    (r : Localization.Away f) (hr : r ≠ 0) : IsSMulRegular (levelRing p f u g) r := by

  have hunit : ∀ v : Localization.Away f, IsUnit v → IsSMulRegular (levelRing p f u g) v := fun v hv =>
    IsSMulRegular.of_isUnit_algebraMap hv

  have hint : ∀ n : ℕ, n ≠ 0 → IsSMulRegular (levelRing p f u g) ((n : ℕ) : Localization.Away f) := by
    intro n hn
    induction n using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact absurd rfl hn
    | h₂ n hu =>
      obtain rfl := Nat.isUnit_iff.mp hu
      rw [Nat.cast_one]; exact hunit 1 isUnit_one
    | h₃ n q hn0 hq ih =>
      rw [Nat.cast_mul]
      refine IsSMulRegular.mul_algebraMap ?_ (ih (by rintro rfl; exact hn (mul_zero _)))
      have hq' : q.Prime := Nat.prime_iff.mpr hq
      by_cases hqf : (q : ℤ) ∣ f
      ·
        refine hunit _ ?_
        obtain ⟨m, hm⟩ := hqf
        have hfu : IsUnit (algebraMap ℤ (Localization.Away f) f) := IsLocalization.Away.algebraMap_isUnit f
        have hqm : IsUnit (algebraMap ℤ (Localization.Away f) q * algebraMap ℤ (Localization.Away f) m) := by
          rwa [← map_mul, ← hm]
        simpa only [map_natCast] using isUnit_of_mul_isUnit_left hqm
      · have hqp : q ≠ p := by rintro rfl; exact hqf hpf
        exact isSMulRegular_levelRing_natCast p f hf u g q hq' (hprime q hq' hqp) (hne q hq' hqp)

  obtain ⟨⟨n, s⟩, hns⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
  simp only at hns
  subst hns
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  have hs : IsUnit (IsLocalization.mk' (Localization.Away f) (1 : ℤ) s) :=
    isUnit_iff_exists_inv.mpr ⟨algebraMap ℤ (Localization.Away f) s, by rw [IsLocalization.mk'_spec, map_one]⟩
  refine IsSMulRegular.mul_algebraMap ?_ (hunit _ hs)
  have hn : n ≠ 0 := by
    rintro rfl
    exact hr (by rw [IsLocalization.mk'_eq_mul_mk'_one, map_zero, zero_mul])

  have hN := hint n.natAbs (Int.natAbs_ne_zero.mpr hn)
  rcases Int.natAbs_eq n with h | h
  · rw [h, map_natCast]; exact hN
  · rw [h, map_neg, map_natCast,
      show (-((n.natAbs : ℕ) : Localization.Away f)) = (-1 : Localization.Away f) * ((n.natAbs : ℕ) : Localization.Away f) by ring]
    exact IsSMulRegular.mul_algebraMap (hunit _ (isUnit_iff_exists_inv.mpr ⟨-1, by ring⟩)) hN

theorem noZeroSMulDivisors_levelRing (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)}) :
    NoZeroSMulDivisors (Localization.Away f) (levelRing p f u g) := by
  refine ⟨fun {r m} h => or_iff_not_imp_left.mpr fun hr => ?_⟩
  have h0 : r • (0 : levelRing p f u g) = 0 := by rw [Algebra.smul_def, mul_zero]
  exact isSMulRegular_levelRing_of_ne_zero f hf hpf u g hprime hne r hr (show r • m = r • 0 by rw [h, h0])

theorem isTorsionFree_levelRing (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)}) :
    Module.IsTorsionFree (Localization.Away f) (levelRing p f u g) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  exact ⟨fun r hr => isSMulRegular_levelRing_of_ne_zero f hf hpf u g hprime hne r hr.ne_zero⟩

theorem free_levelRing (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)})
    [Module.Finite (Localization.Away f) (levelRing p f u g)] :
    Module.Free (Localization.Away f) (levelRing p f u g) := by
  haveI : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : IsPrincipalIdealRing (Localization.Away f) :=
    IsLocalization.isPrincipalIdealRing_of_isPrincipalIdealRing (Submonoid.powers f) (Localization.Away f)
  haveI := isTorsionFree_levelRing f hf hpf u g hprime hne
  exact Module.free_of_finite_type_torsion_free'

theorem flat_levelRing (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)})
    [Module.Finite (Localization.Away f) (levelRing p f u g)] :
    Module.Flat (Localization.Away f) (levelRing p f u g) := by
  haveI := free_levelRing f hf hpf u g hprime hne
  exact Module.Flat.of_free

end ModularCurve.HpoolLevelRing

theorem solution
    (p : ℕ) [Fact p.Prime] (f : ℤ) (hf : f ≠ 0) (hpf : (p : ℤ) ∣ f) (u : Afin p) (g : ℤ[X])
    (hprime : ∀ q : ℕ, q.Prime → q ≠ p → (Ideal.span {((q : ℕ) : Afin p)}).IsPrime)
    (hne : ∀ q : ℕ, q.Prime → q ≠ p → (Polynomial.aeval (R := ℤ) u g : Afin p) ∉ Ideal.span {((q : ℕ) : Afin p)}) :
    NoZeroSMulDivisors (Localization.Away f) (levelRing p f u g) :=
  ModularCurve.HpoolLevelRing.noZeroSMulDivisors_levelRing f hf hpf u g hprime hne

end S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_noZeroSMulDivisors_levelRing_of_forall_isPrime (solution)
