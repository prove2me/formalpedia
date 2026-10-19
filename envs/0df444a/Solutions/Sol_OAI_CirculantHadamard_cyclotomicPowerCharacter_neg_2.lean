-- Prove2me | solution 2 for OAI.CirculantHadamard.cyclotomicPowerCharacter_neg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:26:12.503556+00:00
-- url     : https://prove2.me/submissions/469bf347-ab54-4c63-92c3-5bd44c2fb0e4

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicIntegerEvaluation.lean:L50-L77
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.cyclotomicPowerCharacter_neg. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicIntegerEvaluation ----
namespace OAI

universe uA

/-!
# Integer cyclic evaluation and actual cyclotomic conjugation

The coefficient map is the integer cast into the cyclotomic quotient. The
character sends the cyclic generator to its adjoined root. The root-inverting
automorphism therefore carries evaluation to evaluation of the actual cyclic
group-ring involution.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial
open scoped BigOperators

variable (A : Type uA) [CommRing A] (n : ℕ) [NeZero n]

variable (hn : 0 < n)
variable [IsDomain (AdjoinRoot (cyclotomic n A))]
variable [CharZero (AdjoinRoot (cyclotomic n A))]

/-- The actual character intertwines negation of its index and the proved
cyclotomic conjugation. -/
theorem cyclotomicPowerCharacter_neg (a : ZMod n) :
    CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
        (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd (-a)) =
      RamifiedConjugation.cyclotomicConjugation A n hn
        (CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
          (RamifiedConjugation.root_pow_order A n) (Multiplicative.ofAdd a)) := by
  let χ := CyclicPolynomial.powerCharacter n (AdjoinRoot.root (cyclotomic n A))
    (RamifiedConjugation.root_pow_order A n)
  have hnonzero : χ (Multiplicative.ofAdd a) ≠ 0 :=
    pow_ne_zero a.val
      ((RamifiedConjugation.root_isPrimitiveRoot A n hn).isUnit (ne_of_gt hn)).ne_zero
  apply mul_right_cancel₀ hnonzero
  have hleft : χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) = 1 := by
    rw [← map_mul]
    change χ (Multiplicative.ofAdd (-a + a)) = 1
    simp
  change χ (Multiplicative.ofAdd (-a)) * χ (Multiplicative.ofAdd a) =
    RamifiedConjugation.cyclotomicConjugation A n hn
      (χ (Multiplicative.ofAdd a)) * χ (Multiplicative.ofAdd a)
  rw [hleft]
  symm
  change RamifiedConjugation.cyclotomicConjugation A n hn
      (AdjoinRoot.root (cyclotomic n A) ^ a.val) *
    AdjoinRoot.root (cyclotomic n A) ^ a.val = 1
  rw [map_pow, RamifiedConjugation.cyclotomicConjugation_root, ← mul_pow,
    RamifiedConjugation.root_pow_pred_mul_root A n hn, one_pow]

end CirculantHadamard

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open Polynomial
open scoped BigOperators


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.cyclotomicPowerCharacter_neg.{uA} := @_root_.OAI.CirculantHadamard.cyclotomicPowerCharacter_neg.{uA}
