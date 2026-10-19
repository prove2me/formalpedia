-- Prove2me | solution 2 for OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_factor_units
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:53:35.058918+00:00
-- url     : https://prove2.me/submissions/9ac83566-1a46-47e7-b3f8-fa0c246db04e

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingLocalization.lean:L251-L268
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_factor_units. The node keeps its source
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

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

theorem alternatingProduct_congr (t : Finset I) (x y : Finset I → G)
    (h : ∀ S ⊆ t, x S = y S) :
    alternatingProduct t x = alternatingProduct t y := by
  apply Finset.prod_congr rfl
  intro S hS
  rw [h S (Finset.mem_powerset.mp hS)]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

/-- In particular this applies to the homomorphism from local units to the
fraction field, retaining the single fixed alternating product. -/
theorem map_alternatingProduct (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (alternatingProduct t x) = alternatingProduct t (fun S => f (x S)) := by
  simp only [alternatingProduct, map_prod, map_zpow]

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

/-- Ordinary local units give an actual local unit representative of the fixed
field product. The representatives are not independently chosen field values. -/
theorem exists_unit_of_factor_units (f : R →+* K) (t : Finset I)
    (x : Finset I → R) (hx : ∀ S ⊆ t, IsUnit (x S)) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t (fun S => f (x S)) := by
  classical
  let units : Finset I → Rˣ := fun S => if hS : S ⊆ t then (hx S hS).unit else 1
  have hval : ∀ S ⊆ t, (units S : R) = x S := by
    intro S hS
    simp only [units, dite_eq_left hS, IsUnit.unit_spec]
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  refine ⟨alternatingProduct t units, ?_⟩
  change toK (alternatingProduct t units) = _
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change f (units S : R) = f (x S)
  rw [hval S hS]

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


theorem solution.{uR,uK,uI} : type_of% @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_factor_units.{uR,uK,uI} := @_root_.OAI.CirculantHadamard.AlternatingLocalization.exists_unit_of_factor_units.{uR,uK,uI}
