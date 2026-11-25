-- Prove2me | solution 1 for GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:45:13.59818+00:00
-- url     : https://prove2.me/submissions/4ce0c21d-a6a8-4c7e-b70e-bd7a2fd0293d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSqStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_MainTerm_coeff_low_good


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
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  first | exact @GlobalTheory.MainTerm.coeff_low_good | exact GlobalTheory.MainTerm.coeff_low_good | (intros; apply GlobalTheory.MainTerm.coeff_low_good <;> assumption)
end _root_.GlobalTheory.T
