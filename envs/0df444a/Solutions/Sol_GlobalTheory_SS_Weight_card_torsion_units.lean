-- Prove2me | solution 1 for GlobalTheory.SS.Weight.card_torsion_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:01.800169+00:00
-- url     : https://prove2.me/submissions/101e3cfb-0514-4d9c-8555-3e3e3dcbdb47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors
namespace GlobalTheory.SS.Weight
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K] (l : ℕ) (hl : (l : K) ≠ 0)
    (n : ℕ) : Nat.card {x : Additive Kˣ // l ^ n • x = 0} = l ^ n := by
  haveI : NeZero ((l ^ n : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hl⟩
  haveI : NeZero (l ^ n) := NeZero.of_neZero_natCast K
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K (l ^ n)
end GlobalTheory.SS.Weight
