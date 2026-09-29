-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_forall_etale_levelRing_of_etale_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/1f56b963-1bbd-54a0-b7cc-8b3c713d45bf

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open Polynomial ModularCurve ModularCurve.HpoolLevelRing
open scoped TensorProduct

namespace SpreadProof

universe u

theorem isEtaleAt_of_etale_fiber {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (P : Ideal R) [P.IsPrime] (hP : Algebra.Etale P.ResidueField (P.Fiber S))
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = P) :
    Algebra.IsEtaleAt R q := by
  classical
  haveI : q.LiesOver P := ⟨by rw [Ideal.under_def, hq]⟩
  let F := P.Fiber S
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.Etale P.ResidueField F := hP
  haveI : Subsingleton (Ω[F⁄P.ResidueField]) := inferInstance
  have h1 : Subsingleton (F ⊗[S] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquiv R P.ResidueField S F).toEquiv.subsingleton
  let Sq := Localization.AtPrime q
  let k := q.ResidueField
  let ψ : P.ResidueField →ₐ[R] k := Ideal.ResidueField.mapₐ P q (Algebra.ofId R S) (by exact hq.symm)
  let φ : F →ₐ[R] k := Algebra.TensorProduct.lift ψ (IsScalarTower.toAlgHom R S k) (fun _ _ => Commute.all _ _)
  letI : Algebra F k := φ.toRingHom.toAlgebra
  haveI : IsScalarTower S F k := IsScalarTower.of_algebraMap_eq (fun s => by
    show algebraMap S k s = φ (algebraMap S F s)
    have : algebraMap S F s = (1 : P.ResidueField) ⊗ₜ[R] s := rfl
    rw [this, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl)
  have h2 : Subsingleton (k ⊗[S] Ω[S⁄R]) := by
    haveI := h1
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange S F k k (Ω[S⁄R])).symm.toEquiv.subsingleton
  have h3 : Subsingleton (k ⊗[Sq] (Sq ⊗[S] Ω[S⁄R])) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S Sq k k (Ω[S⁄R])).toEquiv.subsingleton_congr.mpr h2
  have h4 : Subsingleton (Sq ⊗[S] Ω[S⁄R]) :=
    (IsLocalRing.subsingleton_tensorProduct (R := Sq) (M := Sq ⊗[S] Ω[S⁄R])).mp h3
  have h5 : (⟨q, inferInstance⟩ : PrimeSpectrum S) ∉ Module.support S Ω[S⁄R] := by
    rw [Module.notMem_support_iff]
    exact (IsLocalizedModule.iso q.primeCompl (TensorProduct.mk S Sq Ω[S⁄R] 1)).subsingleton_congr.mpr h4
  haveI : Algebra.IsUnramifiedAt R q := by
    have : (⟨q, inferInstance⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := by
      rw [Algebra.unramifiedLocus_eq_compl_support]; exact h5
    exact this
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q

theorem etale_of_localizations
    {R₁ T S₀ S₁ B : Type*} [CommRing R₁] [CommRing T] [CommRing S₀] [CommRing S₁] [CommRing B]
    [Algebra R₁ T] [Algebra R₁ S₁] [Algebra S₀ S₁] [Algebra S₀ B] [Algebra S₁ B] [Algebra T B] [IsScalarTower S₀ S₁ B]
    (M : Submonoid R₁) (hT : IsLocalization M T)
    (N : Submonoid S₀) (hB : IsLocalization (N.map (algebraMap S₀ S₁)) B)
    (hMN : Algebra.algebraMapSubmonoid S₁ M ≤ N.map (algebraMap S₀ S₁))
    (hdvd : ∀ y ∈ N.map (algebraMap S₀ S₁), ∃ m ∈ Algebra.algebraMapSubmonoid S₁ M, y ∣ m)
    (htow : (algebraMap T B).comp (algebraMap R₁ T) = (algebraMap S₁ B).comp (algebraMap R₁ S₁))
    [Algebra.Etale R₁ S₁] : Algebra.Etale T B := by
  letI : Algebra R₁ B := ((algebraMap S₁ B).comp (algebraMap R₁ S₁)).toAlgebra
  haveI : IsScalarTower R₁ S₁ B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R₁ T B := IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun htow x).symm)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S₁ M) B :=
    (IsLocalization.iff_of_le_of_exists_dvd _ _ hMN hdvd).mpr hB
  have hPO : Algebra.IsPushout R₁ S₁ T B := Algebra.isPushout_of_isLocalization M T S₁ B
  have hPO' := hPO.symm
  let e : T ⊗[R₁] S₁ ≃ₐ[T] B := Algebra.IsPushout.equiv R₁ T S₁ B
  exact Algebra.Etale.of_equiv e

end SpreadProof

set_option maxHeartbeats 8000000 in
open SpreadProof in
theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (u : Afin p) (g : ℤ[X])
    [Module.Finite (Localization.Away (p : ℤ)) (levelRing p p u g)]
    [Module.Flat (Localization.Away (p : ℤ)) (levelRing p p u g)]
    (hgen : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime], P = ⊥ →
      Algebra.Etale P.ResidueField (P.Fiber (levelRing p p u g)))
    (hℓet : ∀ (P : Ideal (Localization.Away (p : ℤ))) [P.IsPrime],
      P = Ideal.span {algebraMap ℤ (Localization.Away (p : ℤ)) ℓ} →
      Algebra.Etale P.ResidueField (P.Fiber (levelRing p p u g))) :
    ∃ c : ℤ, c ≠ 0 ∧ ¬ (ℓ : ℤ) ∣ c ∧ (p : ℤ) ∣ c ∧
      ∀ f : ℤ, f ≠ 0 → c ∣ f → Algebra.Etale (Localization.Away f) (levelRing p f u g) := by
  classical

  haveI : IsDomain (Localization.Away (p : ℤ)) := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  haveI : IsNoetherianRing (Localization.Away (p : ℤ)) := IsLocalization.isNoetherianRing (Submonoid.powers (p : ℤ)) (Localization.Away (p : ℤ)) inferInstance
  haveI : Algebra.FiniteType (Localization.Away (p : ℤ)) (levelRing p p u g) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (p : ℤ)) (levelRing p p u g) := (Algebra.FinitePresentation.of_finiteType (R := (Localization.Away (p : ℤ))) (A := (levelRing p p u g))).mp inferInstance

  have hgen' : ∀ (q : Ideal (levelRing p p u g)) [q.IsPrime], q.comap (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g)) = ⊥ → Algebra.IsEtaleAt (Localization.Away (p : ℤ)) q :=
    fun q _ hq => isEtaleAt_of_etale_fiber ⊥ (hgen ⊥ rfl) q hq
  set Pℓ : Ideal (Localization.Away (p : ℤ)) := Ideal.span {algebraMap ℤ (Localization.Away (p : ℤ)) ℓ} with hPℓ
  have hPℓ_prime : Pℓ.IsPrime := by
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hprime : Prime (ℓ : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : ℓ.Prime))
    have h1 : Pℓ = (Ideal.span {(ℓ : ℤ)}).map (algebraMap ℤ (Localization.Away (p : ℤ))) := by
      rw [hPℓ, Ideal.map_span, Set.image_singleton]
    rw [h1]
    refine IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (p : ℤ)) (Localization.Away (p : ℤ)) _
      ((Ideal.span_singleton_prime hℓ0).mpr hprime) ?_
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    have : (ℓ : ℤ) ∣ (p : ℤ) ^ k := Ideal.mem_span_singleton.mp hk
    have hℓp : ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
      rw [Int.natCast_dvd_natCast]
      intro h
      exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)
    exact hℓp (hprime.dvd_of_dvd_pow this)
  have hTet' : ∀ P ∈ ({Pℓ} : Finset (Ideal (Localization.Away (p : ℤ)))), ∀ (q : Ideal (levelRing p p u g)) [q.IsPrime],
      q.comap (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g)) = P → Algebra.IsEtaleAt (Localization.Away (p : ℤ)) q := by
    intro P hP q _ hq
    rw [Finset.mem_singleton] at hP
    subst hP
    haveI := hPℓ_prime
    exact isEtaleAt_of_etale_fiber Pℓ (hℓet Pℓ rfl) q hq

  obtain ⟨c, hc0, hcT, het⟩ := Algebra.exists_etale_localizationAway_of_forall_isEtaleAt hgen' {Pℓ}
    (fun P hP => by rw [Finset.mem_singleton] at hP; exact hP ▸ hPℓ_prime) hTet'
  have hcℓ : c ∉ Pℓ := hcT Pℓ (Finset.mem_singleton_self _)

  obtain ⟨n, a, hca⟩ := IsLocalization.Away.surj (p : ℤ) c
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp only [map_zero, mul_eq_zero] at hca
    rcases hca with h | h
    · exact hc0 h
    · exact (IsLocalization.Away.algebraMap_pow_isUnit (S := (Localization.Away (p : ℤ))) (p : ℤ) n).ne_zero h
  have hℓa : ¬ (ℓ : ℤ) ∣ a := by
    rintro ⟨b, rfl⟩
    apply hcℓ
    have hu : IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) (p : ℤ) ^ n) := IsLocalization.Away.algebraMap_pow_isUnit (p : ℤ) n
    have : c = algebraMap ℤ (Localization.Away (p : ℤ)) (ℓ * b) * ↑(hu.unit⁻¹) := by
      rw [← hca, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this, map_mul, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hℓp : ¬ (ℓ : ℤ) ∣ (p : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro h
    exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)
  refine ⟨p * a, mul_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero) ha0, ?_, dvd_mul_right _ _, ?_⟩
  · intro h
    rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : ℓ.Prime))).dvd_or_dvd h with h | h
    · exact hℓp h
    · exact hℓa h

  intro f hf hCf
  have hpf : (p : ℤ) ∣ f := (dvd_mul_right _ _).trans hCf
  have haf : a ∣ f := (dvd_mul_left _ _).trans hCf
  have hpu : IsUnit (algebraMap ℤ (Localization.Away (p : ℤ)) (p : ℤ) ^ n) := IsLocalization.Away.algebraMap_pow_isUnit (p : ℤ) n
  have hassoc : Associated c (algebraMap ℤ (Localization.Away (p : ℤ)) a) := by
    rw [← hca]; exact associated_mul_unit_right c _ hpu
  haveI : IsLocalization.Away (algebraMap ℤ (Localization.Away (p : ℤ)) a) (Localization.Away c) := IsLocalization.Away.of_associated hassoc
  haveI hR₁pa : IsLocalization.Away ((p : ℤ) * a) (Localization.Away c) :=
    IsLocalization.Away.mul' (Localization.Away (p : ℤ)) (Localization.Away c) (p : ℤ) a

  let N₁ : Submonoid ℤ := Submonoid.closure {(p : ℤ) * a, f}
  have hle₁ : Submonoid.powers ((p : ℤ) * a) ≤ N₁ :=
    Submonoid.powers_le.mpr (Submonoid.subset_closure (Set.mem_insert _ _))
  haveI hTN₁ : IsLocalization N₁ (Localization.Away f) := by
    refine IsLocalization.of_le (Submonoid.powers f) N₁
      (Submonoid.powers_le.mpr (Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))) ?_
    intro r hr
    induction hr using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]; exact IsLocalization.Away.isUnit_of_dvd (x := f) hCf
      · rw [Set.mem_singleton_iff.mp hx]; exact IsLocalization.Away.algebraMap_isUnit f
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  letI algR₁T : Algebra (Localization.Away c) (Localization.Away f) :=
    @IsLocalization.localizationAlgebraOfSubmonoidLe ℤ _ (Localization.Away c) _ _ (Localization.Away f) _ _
      (Submonoid.powers ((p : ℤ) * a)) N₁ hle₁ hR₁pa hTN₁
  have towR₁T := @IsLocalization.localization_isScalarTower_of_submonoid_le ℤ _ (Localization.Away c) _ _
    (Localization.Away f) _ _ (Submonoid.powers ((p : ℤ) * a)) N₁ hle₁ hR₁pa hTN₁
  have hT₁ := @IsLocalization.isLocalization_of_submonoid_le ℤ _ (Localization.Away c) _ _ (Localization.Away f) _ _
      (Submonoid.powers ((p : ℤ) * a)) N₁ hle₁ hR₁pa hTN₁ algR₁T towR₁T

  let NA : Submonoid (Afin p) := Submonoid.closure {algebraMap ℤ (Afin p) (p : ℤ), algebraMap ℤ (Afin p) f}
  have hleA : Submonoid.powers (algebraMap ℤ (Afin p) (p : ℤ)) ≤ NA :=
    Submonoid.powers_le.mpr (Submonoid.subset_closure (Set.mem_insert _ _))
  haveI hAfN : IsLocalization NA (AfinAway p f) := by
    refine IsLocalization.of_le (Submonoid.powers (algebraMap ℤ (Afin p) f)) NA
      (Submonoid.powers_le.mpr (Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))) ?_
    intro r hr
    induction hr using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · rw [hx]; exact IsLocalization.Away.isUnit_of_dvd (x := algebraMap ℤ (Afin p) f) (map_dvd _ hpf)
      · rw [Set.mem_singleton_iff.mp hx]; exact IsLocalization.Away.algebraMap_isUnit (algebraMap ℤ (Afin p) f)
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  letI algApAf : Algebra (AfinAway p p) (AfinAway p f) :=
    @IsLocalization.localizationAlgebraOfSubmonoidLe (Afin p) _ (AfinAway p p) _ _ (AfinAway p f) _ _
      (Submonoid.powers (algebraMap ℤ (Afin p) (p : ℤ))) NA hleA inferInstance hAfN
  have towA := @IsLocalization.localization_isScalarTower_of_submonoid_le (Afin p) _ (AfinAway p p) _ _
    (AfinAway p f) _ _ (Submonoid.powers (algebraMap ℤ (Afin p) (p : ℤ))) NA hleA inferInstance hAfN
  haveI hAf₁ := @IsLocalization.isLocalization_of_submonoid_le (Afin p) _ (AfinAway p p) _ _ (AfinAway p f) _ _
    (Submonoid.powers (algebraMap ℤ (Afin p) (p : ℤ))) NA hleA inferInstance hAfN algApAf towA

  let Ip : Ideal (AfinAway p p) := Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p p) u) g}
  have hI : Ip.map (algebraMap (AfinAway p p) (AfinAway p f)) =
      Ideal.span {Polynomial.aeval (algebraMap (Afin p) (AfinAway p f) u) g} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
      Subsingleton.elim ((algebraMap (AfinAway p p) (AfinAway p f)).comp (algebraMap ℤ (AfinAway p p)))
        (algebraMap ℤ (AfinAway p f)),
      ← @IsScalarTower.algebraMap_apply (Afin p) (AfinAway p p) (AfinAway p f) _ _ _ _ _ _ towA u]

  let eL : (AfinAway p f ⧸ Ip.map (algebraMap (AfinAway p p) (AfinAway p f))) ≃ₐ[Localization.Away f]
      levelRing p f u g := Ideal.quotientEquivAlgOfEq (Localization.Away f) hI

  letI algRoneSone : Algebra (Localization.Away c) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) :=
    (Localization.awayMap (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g)) c).toAlgebra
  haveI hetale : Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) := het

  set L' := AfinAway p f ⧸ Ip.map (algebraMap (AfinAway p p) (AfinAway p f)) with hL'
  have hunitL' : ∀ x : ℤ, x ∣ f → IsUnit ((x : ℤ) : L') := by
    intro x hx
    have h1 : IsUnit (algebraMap ℤ (AfinAway p f) x) := by
      rw [IsScalarTower.algebraMap_apply ℤ (Afin p) (AfinAway p f)]
      exact IsLocalization.Away.isUnit_of_dvd (x := algebraMap ℤ (Afin p) f) (map_dvd _ hx)
    have h2 := h1.map (Ideal.Quotient.mk (Ip.map (algebraMap (AfinAway p p) (AfinAway p f))))
    rwa [eq_intCast (algebraMap ℤ (AfinAway p f)) x,
      map_intCast (Ideal.Quotient.mk (Ip.map (algebraMap (AfinAway p p) (AfinAway p f)))) x] at h2
  have hcSzero : algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c * ((p : ℤ) : (levelRing p p u g)) ^ n = ((a : ℤ) : (levelRing p p u g)) := by
    have := congrArg (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g)) hca
    have hcomp : ∀ z : ℤ, algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) (algebraMap ℤ (Localization.Away (p : ℤ)) z) = ((z : ℤ) : (levelRing p p u g)) := fun z =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g)).comp (algebraMap ℤ (Localization.Away (p : ℤ)))) (Int.castRingHom (levelRing p p u g))) z)
    rwa [map_mul, map_pow, hcomp, hcomp] at this

  let N₀ : Submonoid (levelRing p p u g) := Submonoid.closure {algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c, ((p : ℤ) : (levelRing p p u g)), ((a : ℤ) : (levelRing p p u g)), ((f : ℤ) : (levelRing p p u g))}
  have hle₀ : Submonoid.powers (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c) ≤ N₀ :=
    Submonoid.powers_le.mpr (Submonoid.subset_closure (Set.mem_insert _ _))
  haveI hLpN0 : IsLocalization N₀ L' := by
    refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (levelRing p p u g) (NA.map (algebraMap (Afin p) (AfinAway p p)))) N₀ ?_ ?_
    · refine Submonoid.map_le_iff_le_comap.mpr (Submonoid.map_le_iff_le_comap.mpr (Submonoid.closure_le.mpr ?_))
      have hcomp : ∀ z : ℤ, algebraMap (AfinAway p p) (levelRing p p u g) (algebraMap (Afin p) (AfinAway p p) (algebraMap ℤ (Afin p) z)) =
          ((z : ℤ) : (levelRing p p u g)) := fun z =>
        RingHom.congr_fun (Subsingleton.elim (((algebraMap (AfinAway p p) (levelRing p p u g)).comp
          (algebraMap (Afin p) (AfinAway p p))).comp (algebraMap ℤ (Afin p))) (Int.castRingHom (levelRing p p u g))) z
      rintro x (hx | hx)
      · rw [hx]
        show algebraMap (AfinAway p p) (levelRing p p u g) (algebraMap (Afin p) (AfinAway p p) (algebraMap ℤ (Afin p) p)) ∈ N₀
        rw [hcomp]
        exact Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · rw [Set.mem_singleton_iff.mp hx]
        show algebraMap (AfinAway p p) (levelRing p p u g) (algebraMap (Afin p) (AfinAway p p) (algebraMap ℤ (Afin p) f)) ∈ N₀
        rw [hcomp]
        exact Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))
    · intro r hr
      induction hr using Submonoid.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx | hx | hx
        · rw [hx]
          have ha : IsUnit ((a : ℤ) : L') := hunitL' a haf
          rw [← map_intCast (algebraMap (levelRing p p u g) L') a, ← hcSzero, map_mul] at ha
          exact isUnit_of_mul_isUnit_left ha
        · rw [hx, map_intCast (algebraMap (levelRing p p u g) L') (p : ℤ)]; exact hunitL' p hpf
        · rw [hx, map_intCast (algebraMap (levelRing p p u g) L') a]; exact hunitL' a haf
        · rw [Set.mem_singleton_iff.mp hx, map_intCast (algebraMap (levelRing p p u g) L') f]; exact hunitL' f dvd_rfl
      | one => simp
      | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy
  letI algSoneLp : Algebra (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) L' :=
    @IsLocalization.localizationAlgebraOfSubmonoidLe (levelRing p p u g) _ (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) _ _ L' _ _
      (Submonoid.powers (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) N₀ hle₀ inferInstance hLpN0
  have towS := @IsLocalization.localization_isScalarTower_of_submonoid_le (levelRing p p u g) _ (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) _ _
    L' _ _ (Submonoid.powers (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) N₀ hle₀ inferInstance hLpN0
  have hLpSone := @IsLocalization.isLocalization_of_submonoid_le (levelRing p p u g) _ (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) _ _ L' _ _
    (Submonoid.powers (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)) N₀ hle₀ inferInstance hLpN0 algSoneLp towS

  haveI := towS
  have hEt' : Algebra.Etale (Localization.Away f) L' := by
    have testCS : (CommRing.toCommSemiring : CommSemiring (Localization.Away c)) = OreLocalization.instCommSemiring := rfl
    refine SpreadProof.etale_of_localizations _ (by convert hT₁ using 2 <;> with_unfolding_all rfl) N₀
      (by convert hLpSone using 2 <;> with_unfolding_all rfl) ?_ ?_ ?_
    ·
      have hp' := Submonoid.mem_map_of_mem (algebraMap (levelRing p p u g) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)))
        (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) : ((p : ℤ) : (levelRing p p u g)) ∈ N₀)
      have ha' := Submonoid.mem_map_of_mem (algebraMap (levelRing p p u g) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)))
        (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) : ((a : ℤ) : (levelRing p p u g)) ∈ N₀)
      have hf' := Submonoid.mem_map_of_mem (algebraMap (levelRing p p u g) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c)))
        (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))) : ((f : ℤ) : (levelRing p p u g)) ∈ N₀)
      simp only [map_intCast, map_natCast, Int.cast_natCast] at hp' ha' hf'
      intro y hy
      simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map] at hy
      obtain ⟨r, ⟨z, hz, rfl⟩, rfl⟩ := hy
      induction hz using Submonoid.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · subst hx
          simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, map_mul, map_natCast, map_intCast]
          exact mul_mem hp' ha'
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          simp only [eq_intCast, map_intCast]
          exact hf'
      | one => simp only [map_one]; exact one_mem _
      | mul x y _ _ hx hy => simp only [map_mul]; exact mul_mem hx hy
    ·
      have hcS' := congrArg (algebraMap (levelRing p p u g) (Localization.Away (algebraMap (Localization.Away (p : ℤ)) (levelRing p p u g) c))) hcSzero
      simp only [map_mul, map_pow, map_intCast, Int.cast_natCast] at hcS'
      intro y hy
      obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
      clear hy
      induction hs using Submonoid.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx | hx | hx
        · refine ⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _
            (Submonoid.subset_closure (Set.mem_insert ((p : ℤ) * a) ({f} : Set ℤ)))), ?_⟩
          subst hx
          simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, map_mul, map_natCast, map_intCast]
          exact (Dvd.intro _ hcS').trans (dvd_mul_left _ _)
        · refine ⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _
            (Submonoid.subset_closure (Set.mem_insert ((p : ℤ) * a) ({f} : Set ℤ)))), ?_⟩
          subst hx
          simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, map_mul, map_natCast, map_intCast]
          exact dvd_mul_right _ _
        · refine ⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _
            (Submonoid.subset_closure (Set.mem_insert ((p : ℤ) * a) ({f} : Set ℤ)))), ?_⟩
          subst hx
          simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, map_mul, map_natCast, map_intCast]
          exact dvd_mul_left _ _
        · refine ⟨_, Submonoid.mem_map_of_mem _ (Submonoid.mem_map_of_mem _
            (Submonoid.subset_closure (Set.mem_insert_of_mem _ (rfl : f ∈ ({f} : Set ℤ))))), ?_⟩
          rw [Set.mem_singleton_iff] at hx; subst hx
          simp only [eq_intCast, map_intCast]
          exact dvd_rfl
      | one => exact ⟨1, one_mem _, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨m₁, hm₁, h₁⟩ := hx
        obtain ⟨m₂, hm₂, h₂⟩ := hy
        exact ⟨m₁ * m₂, mul_mem hm₁ hm₂, by rw [map_mul]; exact mul_dvd_mul h₁ h₂⟩
    ·
      exact IsLocalization.ringHom_ext (Submonoid.powers ((p : ℤ) * a)) (RingHom.ext_int _ _)
  exact Algebra.Etale.of_equiv eL

end S_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_levelRing_of_etale_fiber (solution)
