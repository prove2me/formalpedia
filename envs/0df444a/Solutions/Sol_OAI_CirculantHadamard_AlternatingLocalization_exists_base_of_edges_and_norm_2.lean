-- Prove2me | solution 2 for OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:58:12.217049+00:00
-- url     : https://prove2.me/submissions/81f23a83-ad39-4232-a293-ab3f69bac1ba

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean:L294-L323
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_CirculantHadamard_AlternatingLocalization_exists_unit_of_edges
import Theorems.Thm_OAI_CirculantHadamard_AlternatingLocalization_exists_unit_of_factor_units

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalizationIntersection ----
namespace OAI

universe uR uK

/-!
# Recovering a global coefficient from its local representations

The denominator-ideal argument works in any commutative algebra. It identifies
the intersection of maximal localizations inside a fraction field with the
base ring, both as subalgebra membership and through actual local elements.
-/

namespace CirculantHadamard

section FractionField

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Membership in every maximal localization, realized inside a common fraction
field, gives a base-ring representative. -/
theorem exists_base_of_mem_all_maximal_localizations
    {z : K}
    (hz : ∀ m : MaximalSpectrum R,
      z ∈ Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = z := by
  have hzall : z ∈ (⨅ m : MaximalSpectrum R,
      Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :=
    Algebra.mem_iInf.mpr hz
  rw [MaximalSpectrum.iInf_localization_eq_bot R K] at hzall
  exact Algebra.mem_bot.mp hzall

/-- A fraction-field element represented by an actual element of each maximal
local ring is the image of a base-ring element. -/
theorem exists_base_of_localization_images
    {z : K}
    (hz : ∀ m : MaximalSpectrum R, ∃ y : Localization.AtPrime m.asIdeal,
      Localization.mapToFractionRing K m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal)
        m.asIdeal.primeCompl_le_nonZeroDivisors y = z) :
    ∃ r : R, algebraMap R K r = z := by
  apply exists_base_of_mem_all_maximal_localizations
  intro m
  obtain ⟨y, hy⟩ := hz m
  change ∃ (a s : R) (_ : s ∈ m.asIdeal.primeCompl),
    z = algebraMap R K a * (algebraMap R K s)⁻¹
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
    (Localization.AtPrime m.asIdeal) z).mp ⟨y, hy⟩

end FractionField

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uR uK uAZero uS uL uI uk

/-!
# Local representatives of the fixed alternating product

All local rings are actual localizations at maximal ideals. Their maps
into the common fraction field are canonical. The adjoined-root comparison
map is constructed from the actual base-ring inclusion and cyclotomic relation.
Membership in every maximal localization implies membership in the base ring.
-/

noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

end ActualComparisonMap

/-- A finite prime factorization supplies the away-from-u unit, including u=1. -/
theorem natCast_isUnit_of_primeFactors {R : Type uR} [CommRing R]
    (u : ℕ) (hu : u ≠ 0) (hprime : ∀ p ∈ u.primeFactors, IsUnit (p : R)) :
    IsUnit (u : R) := by
  rw [← Nat.prod_primeFactorsList hu, Nat.cast_list_prod]
  apply List.prod_isUnit
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact hprime p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)

theorem local_norm_factor_isUnit {R : Type uR} [CommRing R]
    (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal)
    (x y : R) (hnorm : x * y = (u : R) ^ 2) :
    IsUnit (algebraMap R (AtMaximal R m) x) := by
  have huunit : IsUnit (u : AtMaximal R m) :=
    natCast_isUnit_of_primeFactors u hu (fun p hp => by
      have h := (IsLocalization.AtPrime.isUnit_to_map_iff
        (AtMaximal R m) m.asIdeal (p : R)).mpr (havoid p hp)
      simpa only [map_natCast] using h)
  apply isUnit_of_mul_isUnit_left (y := algebraMap R (AtMaximal R m) y)
  rw [← map_mul, hnorm, map_pow, map_natCast]
  exact huunit.pow 2

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The away-from-u case uses only the evaluated norm identity and avoidance
of the actual rational prime factors of u. -/
theorem exists_local_unit_away (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (x y : Finset I → R)
    (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) =
        alternatingProduct t (fun S => algebraMap R K (x S)) := by
  obtain ⟨v, hv⟩ := exists_unit_of_factor_units (toFraction K m).toRingHom t
    (fun S => algebraMap R (AtMaximal R m) (x S))
    (fun S hS => local_norm_factor_isUnit m u hu havoid (x S) (y S) (hnorm S hS))
  refine ⟨v, ?_⟩
  change toFraction K m (v : AtMaximal R m) = alternatingProduct t
    (fun S => toFraction K m (algebraMap R (AtMaximal R m) (x S))) at hv
  simpa only [AlgHom.commutes] using hv

/-- Every maximal ideal is covered either by a genuine prime-direction edge
comparison or by the norm argument. Local character comparison supplies the
edge hypotheses, without assuming that the product belongs to the base ring. -/
theorem exists_base_of_edges_and_norm (u : ℕ) (hu : u ≠ 0)
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
  apply exists_base_of_localization_images
  intro m
  by_cases hm : ∃ p ∈ u.primeFactors, (p : R) ∈ m.asIdeal
  · obtain ⟨p, hp, hpm⟩ := hm
    obtain ⟨i, hi, hpi⟩ := hcover p hp
    have him : (prime i : R) ∈ m.asIdeal := by rw [hpi]; exact hpm
    obtain ⟨v, hv, _⟩ := exists_unit_of_edges (toFraction K m).toRingHom
      (IsLocalRing.residue (AtMaximal R m)) t i hi
      (fun S => algebraMap R K (x S)) (hedge m i hi him)
    exact ⟨v, hv⟩
  · have havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal := by
      intro p hp hpm
      exact hm ⟨p, hp, hpm⟩
    obtain ⟨v, hv⟩ := exists_local_unit_away (K := K) m u hu t x y hnorm havoid
    exact ⟨v, hv⟩

end MaximalCover

section ConcreteComparison

open CyclicRing

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.AlternatingLocalization
open scoped BigOperators


theorem solution.{uR,uK,uI} : type_of% @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm.{uR,uK,uI} := @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_base_of_edges_and_norm.{uR,uK,uI}
