-- Prove2me | solution 1 for OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_edges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:08:31.750194+00:00
-- url     : https://prove2.me/submissions/5a2e1e9e-a969-4c72-a932-7aa4110a3c91

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
variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]
theorem solution (f : R →+* K) (res : R →+* k)
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
