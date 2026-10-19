-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:04:08.256978+00:00
-- url     : https://prove2.me/submissions/904d4d6d-9107-4f25-8b4d-25096fb9aa42

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryBlocks.lean:L216-L236
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar. The node keeps its source
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

/-- Intertwining is proved on the actual ring maps, with both parts of the star. -/
theorem partialEval_groupStar (φ : R →+* S) (z : S) (hz : z ^ 4 = 1)
    (hφ : ∀ r, φ (star r) = star (φ r))
    (hchar : ∀ a : ZMod 4, z ^ (-a).val = star (z ^ a.val))
    (f : ProductElem R m) :
    partialEval m φ z hz (groupStar f) = ringStar (partialEval m φ z hz f) := by
  have hs (a : ZMod 4 × ZMod m) (r : R) :
      partialEval m φ z hz (groupStar (AddMonoidAlgebra.single a r)) =
        ringStar (partialEval m φ z hz (AddMonoidAlgebra.single a r)) := by
    rw [groupStar_single, partialEval_single, partialEval_single, ringStar_single]
    change AddMonoidAlgebra.single (-a.2) (φ (star r) * z ^ (-a.1).val) =
      AddMonoidAlgebra.single (-a.2) (star (φ r * z ^ a.1.val))
    rw [hφ, hchar, star_mul, mul_comm]
  have he : (partialEval m φ z hz).comp groupStarRingHom =
      (ringStarRingHom m).comp (partialEval m φ z hz) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      exact hs 0 r
    · intro a
      exact hs a 1
  exact RingHom.congr_fun he f

end Star

end CirculantHadamard.BinaryBlocks

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryBlocks
open CyclicRing
open scoped BigOperators


theorem solution.{uR,uS} : type_of% @_root_.OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar.{uR,uS} := @_root_.OAI.CirculantHadamard.BinaryBlocks.partialEval_groupStar.{uR,uS}
