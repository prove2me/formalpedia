-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:15:15.167819+00:00
-- url     : https://prove2.me/submissions/fc104fcd-27be-422e-aabb-07d728fc3b9a

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryCharacterSum.lean:L120-L147
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryCharacterSum ----
namespace OAI

universe uG uR uA uI uT uK uk uB

/-!
# Finite character sums and the surviving empty subset

Translation of a finite group permutes its elements. Consequently a character
with one value different from `1` has zero total sum in a domain. In a family
indexed by subsets, this removes every nonempty subset once its actual
character has such a witness.

The unit-denominator formulation takes place in the coefficient ring itself,
so it can subsequently be mapped to a residue field of characteristic two.
It does not require a map from a characteristic-zero field to that residue
field. Nontriviality of the actual subset characters is supplied by their
primitive primary components, rather than assumed of all characters.
-/

namespace CirculantHadamard.BinaryCharacterSum

open scoped BigOperators

section CharacterSum

variable {G : Type uG} {R : Type uR} [Group G] [Fintype G] [CommRing R]

/-- A nontrivial value of a character forces its finite sum to vanish.
The proof uses the permutation of `G` given by left translation. -/
theorem character_sum_eq_zero [IsDomain R] (χ : G →* R)
    (hχ : ∃ g : G, χ g ≠ 1) : (∑ g : G, χ g) = 0 := by
  classical
  obtain ⟨g, hg⟩ := hχ
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul] using
    (Group.mulLeft_bijective g).sum_comp (fun h : G => χ h)

end CharacterSum

section ActualGroupRing

variable {A : Type uA} {R : Type uR} [CommRing A] [CommRing R] {n : ℕ} [NeZero n]

/-- Evaluation of the actual all-ones group-ring element is the complete
character sum. `JOver` is not the scalar unit of the group ring. -/
theorem evaluate_J_eq_sum (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) =
      ∑ g : Multiplicative (ZMod n), χ g := by
  rw [CyclicRing.evaluate_apply]
  simp only [BinaryCoefficients.JOver_apply, map_one, one_mul]
  exact (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n)).sum_comp _

/-- A witnessed nontrivial character annihilates the actual group-ring `J`. -/
theorem evaluate_J_eq_zero [IsDomain R] (φ : A →+* R)
    (χ : Multiplicative (ZMod n) →* R)
    (hχ : ∃ g : Multiplicative (ZMod n), χ g ≠ 1) :
    CyclicRing.evaluate φ χ (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = 0 := by
  rw [evaluate_J_eq_sum]
  exact character_sum_eq_zero χ hχ

/-- At the trivial character, the actual group-ring `J` evaluates to `n`. -/
theorem evaluate_J_trivial (φ : A →+* R) :
    CyclicRing.evaluate φ (1 : Multiplicative (ZMod n) →* R)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n) = (n : R) := by
  rw [CyclicRing.evaluate_apply]
  simp

end ActualGroupRing

/-- First prove the character sum in its domain, then change coefficient
rings. This does not assume nontriviality of the reduced characters and also
allows the coefficients `d S` to lie in a localization of the original ring. -/
theorem subset_map_evaluate_J_mul
    {I : Type uI} {A : Type uA} {R : Type uR} {T : Type uT} [Fintype I] [DecidableEq I] [CommRing A]
    [CommRing R] [IsDomain R] [CommRing T] {n : ℕ} [NeZero n]
    (φ : A →+* R) (ψ : R →+* T)
    (χ : Finset I → Multiplicative (ZMod n) →* R)
    (ε d : Finset I → T) (hε : ε ∅ = 1) (htrivial : χ ∅ = 1)
    (hnonempty : ∀ S : Finset I, S.Nonempty →
      ∃ g : Multiplicative (ZMod n), χ S g ≠ 1) :
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
      (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
      (n : T) * d ∅ := by
  classical
  calc
    (∑ S : Finset I, ε S * ψ (CyclicRing.evaluate φ (χ S)
        (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d S) =
        ε ∅ * ψ (CyclicRing.evaluate φ (χ ∅)
          (AddMonoidAlgebra.ofCoeff (BinaryCoefficients.JOver A) : CyclicRing.Elem A n)) * d ∅ := by
      apply Finset.sum_eq_single ∅
      · intro S _ hS
        rw [evaluate_J_eq_zero φ (χ S)
          (hnonempty S (Finset.nonempty_iff_ne_empty.mpr hS))]
        simp
      · simp
    _ = (n : T) * d ∅ := by
      rw [hε, one_mul, htrivial, evaluate_J_trivial, map_natCast]

section SubsetSum

variable {I : Type uI} {G : Type uG} {R : Type uR} [Fintype I] [DecidableEq I]
    [Group G] [Fintype G] [CommRing R] [IsDomain R]

end SubsetSum

section Residue

variable {R : Type uR} {k : Type uk} [CommRing R] [CommRing k] [Nontrivial k] [CharP k 2]

end Residue

section ActualSubsetCharacters

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations

variable (u : ℕ) [NeZero (u ^ 2)] (hu : 0 < u)

end ActualSubsetCharacters

end CirculantHadamard.BinaryCharacterSum

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryCharacterSum
open scoped BigOperators


theorem solution.{uR,uA,uI,uT} : type_of% @_root_.OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul.{uR,uA,uI,uT} := @_root_.OAI.CirculantHadamard.BinaryCharacterSum.subset_map_evaluate_J_mul.{uR,uA,uI,uT}
