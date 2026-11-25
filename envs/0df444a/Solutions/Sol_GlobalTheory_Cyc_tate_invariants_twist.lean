-- Prove2me | solution 1 for GlobalTheory.Cyc.tate_invariants_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:18:24.562126+00:00
-- url     : https://prove2.me/submissions/3e731095-11dc-4ec0-a9f6-817faaeb1055

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantsOfSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsTwist
import Theorems.Thm_GlobalTheory_Cyc_invariants_of_subgroup
import Theorems.Thm_GlobalTheory_CyclotomicTowerSubgroupInclusions_invariants_twist


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
namespace GlobalTheory.Cyc
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ GK K, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC K.1) :=
  fun l _ act χ hact hχ K =>
    invariants_of_subgroup hact χ (Gj K 2) (Ks K 2)
      (GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist l act χ hact hχ K 2 ⟨by norm_num, fun _ => le_rfl⟩) K
end GlobalTheory.Cyc
