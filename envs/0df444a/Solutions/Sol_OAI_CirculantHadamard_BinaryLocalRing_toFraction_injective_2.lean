-- Prove2me | solution 2 for OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:10:18.311502+00:00
-- url     : https://prove2.me/submissions/59981510-3ec5-406c-b435-930e820801b2

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/BinaryLocalRing.lean:L58-L69
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective. The node keeps its source
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

-- ---- from OAI.LinearAlgebra.CirculantHadamard.BinaryLocalRing ----
namespace OAI

/-!
# One concrete local ring and residue field

For the actual cyclotomic coefficient algebra `B u`, choose a maximal ideal
containing two. Both first-order calculations use the same localization and
the same residue field. The choices depend only on `u`, not on a character or
on which of the three norm elements is being considered.
-/

noncomputable section

namespace CirculantHadamard.BinaryLocalRing

open CyclotomicRings

/- Name the canonical localization algebra directly. This avoids searching
through iterated-localization algebra instances for these concrete carriers. -/
theorem toFraction_injective (u : ℕ) : Function.Injective (toFraction u) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (twoIdeal u).primeCompl (toFraction u).toRingHom).2
  intro a b
  change toLocal u a = toLocal u b ↔
    toFraction u (toLocal u a) = toFraction u (toLocal u b)
  rw [toFraction_toLocal, toFraction_toLocal]
  constructor
  · intro h
    exact congrArg (algebraMap (B u) (FractionRing (B u))) (toLocal_injective u h)
  · intro h
    exact congrArg (toLocal u) (IsFractionRing.injective (B u) (FractionRing (B u)) h)

end CirculantHadamard.BinaryLocalRing

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.BinaryLocalRing
open CyclotomicRings


theorem solution : type_of% @_root_.OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective := @_root_.OAI.CirculantHadamard.BinaryLocalRing.toFraction_injective
