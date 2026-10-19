-- Prove2me | solution 1 for OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:10:01.670921+00:00
-- url     : https://prove2.me/submissions/ab816064-4c41-45a4-847a-ae9c31ea8fac

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.AlternatingLocalization
universe uR uK uAZero uS uL uI uk
open scoped BigOperators
variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
theorem aux_ufu {I : Type*} {R : Type*} {K : Type*} [DecidableEq I] [CommRing R] [Field K] (f : R →+* K) (t : Finset I)
    (x : Finset I → R) (hx : ∀ S ⊆ t, IsUnit (x S)) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t (fun S => f (x S)) := by
  classical
  refine ⟨∏ S ∈ t.powerset, (if h : S ⊆ t then (hx S h).unit else 1) ^ subsetSign S, ?_⟩
  have key : ∀ w : Rˣ, ∀ n : ℤ, f ((w ^ n : Rˣ) : R) = (f (w : R)) ^ n := by
    intro w n
    have : f ((w ^ n : Rˣ) : R) = ((Units.map (f : R →* K) (w ^ n) : Kˣ) : K) := rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  unfold alternatingProduct
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun S hS => ?_
  have hS' : S ⊆ t := Finset.mem_powerset.1 hS
  rw [dif_pos hS', key, IsUnit.unit_spec]

theorem aux_ue {I : Type*} {R : Type*} {K : Type*} {k : Type*} [DecidableEq I] [CommRing R] [Field K] [Field k] (f : R →+* K) (res : R →+* k)
    (t : Finset I) (p : I) (hp : p ∈ t) (x : Finset I → K)
    (hedge : ∀ S ∈ (t.erase p).powerset, ∃ v : Rˣ,
      f (v : R) = x (insert p S) / x S ∧ res (v : R) = 1) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t x ∧ res (v : R) = 1 := by
  choose! v hv1 hv2 using hedge
  have key : ∀ w : Rˣ, ∀ n : ℤ, f ((w ^ n : Rˣ) : R) = (f (w : R)) ^ n := by
    intro w n
    have : f ((w ^ n : Rˣ) : R) = ((Units.map (f : R →* K) (w ^ n) : Kˣ) : K) := rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have key2 : ∀ w : Rˣ, ∀ n : ℤ, res ((w ^ n : Rˣ) : R) = (res (w : R)) ^ n := by
    intro w n
    have : res ((w ^ n : Rˣ) : R) = ((Units.map (res : R →* k) (w ^ n) : kˣ) : k) := rfl
    rw [this, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  set s := t.erase p with hs
  have hps : p ∉ s := Finset.notMem_erase p t
  have ht : t = insert p s := (Finset.insert_erase hp).symm
  refine ⟨∏ S ∈ s.powerset, (v S) ^ (-subsetSign S), ?_, ?_⟩
  · rw [Units.coe_prod, map_prod]
    unfold alternatingProduct
    rw [ht, Finset.powerset_insert, Finset.prod_union, Finset.prod_image, ← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl fun S hS => ?_
      rw [key, hv1 S hS]
      have hpS : p ∉ S := fun h => hps (Finset.mem_powerset.1 hS h)
      have : subsetSign (insert p S) = -subsetSign S := by
        simp [subsetSign, Finset.card_insert_of_notMem hpS, pow_succ]
      rw [this, div_zpow, zpow_neg, zpow_neg]
      rw [div_eq_mul_inv, inv_inv, mul_comm]
    · intro S₁ h₁ S₂ h₂ h
      have h1 : p ∉ S₁ := fun h' => hps (Finset.mem_powerset.1 h₁ h')
      have h2 : p ∉ S₂ := fun h' => hps (Finset.mem_powerset.1 h₂ h')
      rw [← Finset.erase_insert h1, ← Finset.erase_insert h2]
      exact congrArg (fun T => Finset.erase T p) h
    · rw [Finset.disjoint_left]
      intro S h1 h2
      obtain ⟨T, _, rfl⟩ := Finset.mem_image.1 h2
      exact hps (Finset.mem_powerset.1 h1 (Finset.mem_insert_self p T))
  · rw [Units.coe_prod, map_prod]
    refine Finset.prod_eq_one fun S hS => ?_
    rw [key2, hv2 S hS, one_zpow]


theorem solution (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (prime : I → ℕ)
    (hcover : ∀ p ∈ u.primeFactors, ∃ i ∈ t, prime i = p)
    (x y : Finset I → R) (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (hedge : ∀ m : MaximalSpectrum R, ∀ i ∈ t, (prime i : R) ∈ m.asIdeal →
      ∀ S ∈ (t.erase i).powerset, ∃ v : (AtMaximal R m)ˣ,
        toFraction K m (v : AtMaximal R m) =
          algebraMap R K (x (insert i S)) / algebraMap R K (x S) ∧
        IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1) :
    ∃ b : R, algebraMap R K b =
      alternatingProduct t (fun S => algebraMap R K (x S)) := by
  classical
  set a := alternatingProduct t (fun S => algebraMap R K (x S)) with ha
  have hmem : ∀ m : MaximalSpectrum R, a ∈ (toFraction K m).range := by
    intro m
    by_cases hA : ∃ i ∈ t, (prime i : R) ∈ m.asIdeal
    · obtain ⟨i, hi, him⟩ := hA
      obtain ⟨v, hv, -⟩ := aux_ue (toFraction K m : AtMaximal R m →+* K)
        (IsLocalRing.residue (AtMaximal R m)) t i hi (fun S => algebraMap R K (x S))
        (hedge m i hi him)
      exact ⟨v, hv⟩
    · have hu' : (u : R) ∉ m.asIdeal := by
        intro hum
        have hprod : (u : R) = ∏ p ∈ u.primeFactors, ((p : R) ^ (u.factorization p)) := by
          conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hu]
          rw [Nat.prod_factorization_eq_prod_primeFactors]
          push_cast; rfl
        rw [hprod] at hum
        have := m.isMaximal.isPrime
        obtain ⟨p, hp, hpm⟩ := (Ideal.IsPrime.prod_mem_iff).1 hum
        have hpm' := m.isMaximal.isPrime.mem_of_pow_mem _ hpm
        obtain ⟨i, hi, hip⟩ := hcover p hp
        exact hA ⟨i, hi, by rw [hip]; exact hpm'⟩
      have hunit : ∀ S ⊆ t, IsUnit (algebraMap R (AtMaximal R m) (x S)) := by
        intro S hS
        have h2 : IsUnit (algebraMap R (AtMaximal R m) ((u : R) ^ 2)) := by
          apply IsLocalization.map_units (AtMaximal R m) (⟨(u : R) ^ 2, ?_⟩ : m.asIdeal.primeCompl)
          intro h; exact hu' (m.isMaximal.isPrime.mem_of_pow_mem _ h)
        rw [← hnorm S hS, map_mul] at h2
        exact isUnit_of_mul_isUnit_left h2
      obtain ⟨v, hv⟩ := aux_ufu (toFraction K m : AtMaximal R m →+* K) t
        (fun S => algebraMap R (AtMaximal R m) (x S)) hunit
      refine ⟨v, ?_⟩
      rw [ha, show (fun S => algebraMap R K (x S)) = (fun S => (toFraction K m : AtMaximal R m →+* K)
        (algebraMap R (AtMaximal R m) (x S))) from funext fun S => ((toFraction K m).commutes (x S)).symm]
      exact hv
  have hinf : a ∈ (⨅ v : MaximalSpectrum R,
      Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro m
    obtain ⟨w, hw⟩ := hmem m
    have := (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField K
      m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors (AtMaximal R m) a).1 ⟨w, hw⟩
    exact this
  rw [MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at hinf
  obtain ⟨b, hb⟩ := hinf
  exact ⟨b, hb⟩
