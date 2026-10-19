-- Prove2me | solution 2 for OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_edges
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:51:10.312554+00:00
-- url     : https://prove2.me/submissions/619e4275-90d3-4bf9-850f-7a1940f6a1be

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean:L221-L249
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_edges. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uG uH

/-!
# Alternating products over literal finite subsets

The exponent is `(-1)^card S`. Pairing subsets along `p` follows from the
powerset decomposition, with the quotient orientation `x S / x (insert p S)`.

The definition and pairing are valid in a division commutative monoid, so they
apply both to actual field values and to units. Cancellation of a constant
family is stated in a commutative group. No local comparison, nonvanishing,
integrality, or torsion statement is assumed or inferred.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

theorem subsetSign_insert [DecidableEq I] (p : I) (S : Finset I) (hp : p ∉ S) :
    subsetSign (insert p S) = -subsetSign S := by
  simp only [subsetSign, Finset.card_insert_of_notMem hp, pow_succ, mul_neg_one]

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

/-- A single direction pairs each omitted-`p` subset with its insertion.
The exponent at the inserted subset is the negative of the original one. -/
theorem alternatingProduct_insert [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∉ t) :
    alternatingProduct (insert p t) x =
      ∏ S ∈ t.powerset, (x S / x (insert p S)) ^ subsetSign S := by
  unfold alternatingProduct
  rw [Finset.prod_powerset_insert hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
  rw [subsetSign_insert p S hpS, zpow_neg, div_zpow, div_eq_mul_inv]

theorem alternatingProduct_pair [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∈ t) :
    alternatingProduct t x =
      ∏ S ∈ (t.erase p).powerset, (x S / x (insert p S)) ^ subsetSign S := by
  calc
    alternatingProduct t x = alternatingProduct (insert p (t.erase p)) x := by
      rw [Finset.insert_erase hp]
    _ = _ := alternatingProduct_insert (t.erase p) x p (Finset.notMem_erase p t)

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

end FiniteUniverse

end CirculantHadamard

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.AlternatingLocalization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

theorem exists_unit_of_edges (f : R →+* K) (res : R →+* k)
    (t : Finset I) (p : I) (hp : p ∈ t) (x : Finset I → K)
    (hedge : ∀ S ∈ (t.erase p).powerset, ∃ v : Rˣ,
      f (v : R) = x (insert p S) / x S ∧ res (v : R) = 1) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t x ∧ res (v : R) = 1 := by
  classical
  let edge : Finset I → Rˣ := fun S =>
    if hS : S ∈ (t.erase p).powerset then Classical.choose (hedge S hS) else 1
  have hedge' : ∀ S ∈ (t.erase p).powerset,
      f (edge S : R) = x (insert p S) / x S ∧ res (edge S : R) = 1 := by
    intro S hS
    simpa only [edge, dite_eq_left hS] using Classical.choose_spec (hedge S hS)
  let v : Rˣ := ∏ S ∈ (t.erase p).powerset, (edge S)⁻¹ ^ subsetSign S
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  let tok : Rˣ →* k := res.toMonoidHom.comp (Units.coeHom R)
  refine ⟨v, ?_, ?_⟩
  · change toK v = alternatingProduct t x
    rw [alternatingProduct_pair t x p hp]
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_congr rfl
    intro S hS
    change (f (edge S : R))⁻¹ ^ subsetSign S = _
    rw [(hedge' S hS).1, inv_div]
  · change tok v = 1
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_eq_one
    intro S hS
    change (res (edge S : R))⁻¹ ^ subsetSign S = 1
    rw [(hedge' S hS).2, inv_one, one_zpow]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

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


theorem solution.{uR,uK,uI,uk} : type_of% @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_edges.{uR,uK,uI,uk} := @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_edges.{uR,uK,uI,uk}
