-- Prove2me | solution 1 for GlobalTheory.TateSeq.tower_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:54.3698+00:00
-- url     : https://prove2.me/submissions/21229697-3c80-4c51-9dbc-228128d418df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.TateSeq
theorem _root_.solution {l : ℕ} {e : ℕ → M} (he : ∀ n, l • e (n + 1) = e n) (k n : ℕ) :
    l ^ k • e (n + k) = e n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ← add_assoc, he, ih]
end GlobalTheory.TateSeq
