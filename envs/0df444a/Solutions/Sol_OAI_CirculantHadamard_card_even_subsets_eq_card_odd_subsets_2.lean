-- Prove2me | solution 2 for OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:13:32.194748+00:00
-- url     : https://prove2.me/submissions/6f1b6144-89aa-41d9-bf06-57a68ffbc443

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/AlternatingProducts.lean:L69-L98
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets. The node keeps its source
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
import Theorems.Thm_OAI_CirculantHadamard_sum_subsetSign_eq_zero

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

theorem subsetSign_of_even (S : Finset I) (h : Even S.card) : subsetSign S = 1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = 1)

theorem subsetSign_of_odd (S : Finset I) (h : Odd S.card) : subsetSign S = -1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = -1)

/-- The even-cardinality and odd-cardinality subset filters have equal size. -/
theorem card_even_subsets_eq_card_odd_subsets (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by
  classical
  have heven : (∑ S ∈ t.powerset.filter (fun S => Even S.card), subsetSign S) =
      ((t.powerset.filter (fun S => Even S.card)).card : ℤ) := by
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Even S.card), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_even S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hodd : (∑ S ∈ t.powerset.filter (fun S => ¬ Even S.card), subsetSign S) =
      -((t.powerset.filter (fun S => Odd S.card)).card : ℤ) := by
    have hfilter : t.powerset.filter (fun S => ¬ Even S.card) =
        t.powerset.filter (fun S => Odd S.card) := by
      ext S
      simp only [Finset.mem_filter, Nat.not_even_iff_odd]
    rw [hfilter]
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Odd S.card), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_odd S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hsum := Finset.sum_filter_add_sum_filter_not t.powerset
    (fun S : Finset I => Even S.card) subsetSign
  rw [heven, hodd, sum_subsetSign_eq_zero t ht] at hsum
  exact Int.natCast_inj.mp (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum))

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


theorem solution.{uI} : type_of% @_root_.OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets.{uI} := @_root_.OAI.CirculantHadamard.card_even_subsets_eq_card_odd_subsets.{uI}
