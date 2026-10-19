-- Prove2me | solution 2 for OAI.CirculantHadamard.sum_subsetSign_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:11:53.002761+00:00
-- url     : https://prove2.me/submissions/408fccc8-2651-4950-a349-1a506c2800fa

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean:L48-L67
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.sum_subsetSign_eq_zero. The node keeps its source
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

/-- The signed subset count vanishes by pairing along an actual element of `t`. -/
theorem sum_subsetSign_eq_zero (t : Finset I) (ht : t.Nonempty) :
    ∑ S ∈ t.powerset, subsetSign S = 0 := by
  classical
  obtain ⟨p, hp⟩ := ht
  have hpaired :
      (∑ S ∈ (t.erase p).powerset, subsetSign (insert p S)) =
        -(∑ S ∈ (t.erase p).powerset, subsetSign S) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    exact subsetSign_insert p S
      (fun h => (Finset.notMem_erase p t) ((Finset.mem_powerset.mp hS) h))
  calc
    _ = ∑ S ∈ (insert p (t.erase p)).powerset, subsetSign S := by
      rw [Finset.insert_erase hp]
    _ = (∑ S ∈ (t.erase p).powerset, subsetSign S) +
        ∑ S ∈ (t.erase p).powerset, subsetSign (insert p S) :=
      Finset.sum_powerset_insert (Finset.notMem_erase p t) subsetSign
    _ = 0 := by rw [hpaired, add_neg_cancel]

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

end FiniteUniverse

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution.{uI} : type_of% @_root_.OAI.CirculantHadamard.sum_subsetSign_eq_zero.{uI} := @_root_.OAI.CirculantHadamard.sum_subsetSign_eq_zero.{uI}
