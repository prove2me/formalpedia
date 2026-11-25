-- Prove2me | solution 1 for GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:21.008725+00:00
-- url     : https://prove2.me/submissions/72a6f9e5-a9e6-42c1-ba81-4e018eedd923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearSubstCoordinateIntegralOfDegreeLtStatement
import Theorems.Thm_GlobalTheory_MainTerm_linPull_coord_int_of_degree_lt


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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  first | exact @GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | exact GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | (intros; apply GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt <;> assumption)
end _root_.GlobalTheory.T
