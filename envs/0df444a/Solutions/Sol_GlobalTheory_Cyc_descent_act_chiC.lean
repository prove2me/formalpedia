-- Prove2me | solution 1 for GlobalTheory.Cyc.descent_act_chiC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:54.976851+00:00
-- url     : https://prove2.me/submissions/75599cb7-28fb-4d06-8b5f-867d6c13d32d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantsOfSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g h : GQ l) : act g (chiC χ i h) = chiC χ i h := by
  unfold chiC
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l), ← PadicComplex.coe_eq, hact.1,
    AlgEquiv.commutes]
end GlobalTheory.Cyc
