-- Prove2me | solution 1 for GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:10.940305+00:00
-- url     : https://prove2.me/submissions/a302dc3d-addf-4153-a4d1-e57cc3facdd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevelStatement
import Theorems.Thm_GlobalTheory_HilbFam_exists_eq_split_of_hasLevel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F), 0 < N → HasLevel N L → ∃ (𝔞 𝔟 : Frac F) (x : F), L = split 𝔞 𝔟 x := by
  first | exact @GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | exact GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | (intros; apply GlobalTheory.HilbFam.exists_eq_split_of_hasLevel <;> assumption)
end _root_.GlobalTheory.T
