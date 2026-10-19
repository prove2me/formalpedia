-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:05:35.384986+00:00
-- url     : https://prove2.me/submissions/c8af9dde-db22-417b-8b5e-fb61b7e753f1

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean:L255-L270
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryBlocks ----
namespace OAI

universe uR uS

/-!
# The actual four-block decomposition and partial evaluations

The Chinese remainder equivalence transports the actual cyclic group ring,
not just a coefficient count. Coefficients of its four slices are the original
signs. Partial evaluation is a ring homomorphism defined on the product group
algebra and intertwines coefficient conjugation with index reversal.
-/

noncomputable section

namespace CirculantHadamard.BinaryBlocks

open CyclicRing
open scoped BigOperators

section Evaluation

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (m : ℕ)

variable [NeZero m]

end Evaluation

section Star

variable {R : Type uR} {S : Type uS} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
variable (m : ℕ) [NeZero m]

theorem fourthRoot_character_star (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by
  have hi3 : i ^ 3 = -i := by
    rw [pow_succ, hi]
    ring
  intro a
  fin_cases a
  · change i ^ 0 = star (i ^ 0)
    simp
  · change i ^ 3 = star (i ^ 1)
    simp [hi3, hstar]
  · change i ^ 2 = star (i ^ 2)
    rw [hi]
    simp
  · change i ^ 1 = star (i ^ 3)
    simp [hi3, hstar]

end Star

end CirculantHadamard.BinaryBlocks

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryBlocks
open CyclicRing
open scoped BigOperators


theorem solution.{uS} : type_of% @_root_.OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star.{uS} := @_root_.OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star.{uS}
