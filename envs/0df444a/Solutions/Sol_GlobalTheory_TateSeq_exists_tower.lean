-- Prove2me | solution 1 for GlobalTheory.TateSeq.exists_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:36.238516+00:00
-- url     : https://prove2.me/submissions/75e4a6ac-a168-4a3a-83f5-2079e07a4520

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
theorem _root_.solution (l : ℕ) (hd : ∀ (n : ℕ) (y : M), l ^ n • y = 0 → ∃ x : M, l • x = y)
    (b : M) (hb : l • b = 0) :
    ∃ e : ℕ → M, e 0 = 0 ∧ e 1 = b ∧ ∀ n, l • e (n + 1) = e n := by
  choose g hg using hd
  let E : (n : ℕ) → {x : M // l ^ (n + 1) • x = 0} := fun n =>
    Nat.rec ⟨b, by simpa using hb⟩
      (fun n x => ⟨g (n + 1) x.1 x.2, by
        rw [pow_succ, mul_smul, hg]; exact x.2⟩) n
  refine ⟨fun n => Nat.casesOn n 0 (fun k => (E k).1), rfl, rfl, ?_⟩
  intro n
  cases n with
  | zero => exact hb
  | succ k => exact hg _ _ _
end GlobalTheory.TateSeq
