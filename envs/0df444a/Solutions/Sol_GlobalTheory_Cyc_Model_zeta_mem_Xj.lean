-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.zeta_mem_Xj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:48.90637+00:00
-- url     : https://prove2.me/submissions/2bd02775-f1ef-40f8-9f94-7a395cc31ee8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution (K : FinExt l) (j : ℕ) {ζ : PadicComplex l} (h : IsPrimitiveRoot ζ (l ^ (j + 1))) :
    ζ ∈ Xj K j := by
  apply AddSubgroup.le_topologicalClosure
  refine (le_iSup₂_of_le (j + 1) (Nat.lt_succ_self j) le_rfl : Xlev K (j + 1) ≤ _) ?_
  refine AddSubgroup.subset_closure ⟨ζ, 1, h, ⟨⟨1, one_mem _, rfl⟩, by simp⟩, (mul_one _).symm⟩
end GlobalTheory.Cyc.Model
