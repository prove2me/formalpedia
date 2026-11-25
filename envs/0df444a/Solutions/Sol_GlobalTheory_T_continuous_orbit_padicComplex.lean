-- Prove2me | solution 1 for GlobalTheory.T.continuous_orbit_padicComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:11.275116+00:00
-- url     : https://prove2.me/submissions/270e165b-c7f1-459b-b6ec-fde4413384e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplexStatement
import Theorems.Thm_GlobalTheory_Cyc_IsActC_continuous_orbit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
end _root_.GlobalTheory.T
