-- Prove2me | solution 1 for GlobalTheory.Cyc.mem_fixingSubgroup_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:12.624131+00:00
-- url     : https://prove2.me/submissions/c01fb65f-d184-4f21-8bb7-faa9c46fa372

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (S : Set (Om l)) (g : GQ l) :
    g ∈ (IntermediateField.adjoin ℚ_[l] S).fixingSubgroup ↔ ∀ x ∈ S, g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact hg x (IntermediateField.subset_adjoin _ _ hx)
  · intro hg x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap x => exact g.commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
end GlobalTheory.Cyc
