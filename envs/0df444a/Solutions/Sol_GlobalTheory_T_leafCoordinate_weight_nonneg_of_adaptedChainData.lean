-- Prove2me | solution 1 for GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:17.314753+00:00
-- url     : https://prove2.me/submissions/52fde877-1984-403b-9b6a-527cfc88fff0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeafCoordinateWeightNonnegOfAdaptedChainDataStatement
import Theorems.Thm_GlobalTheory_LeafCoordWeight_weight_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  first | exact @GlobalTheory.LeafCoordWeight.weight_nonneg | exact GlobalTheory.LeafCoordWeight.weight_nonneg | (intros; apply GlobalTheory.LeafCoordWeight.weight_nonneg <;> assumption)
end _root_.GlobalTheory.T
