-- Prove2me | solution 1 for GlobalTheory.T.zetaSeries_leaf_mainTerm_curveSystem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:53.136744+00:00
-- url     : https://prove2.me/submissions/bd29a664-c9d9-45ce-8172-979c027377e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesLeafMainTermCurveSystem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ZetaSeriesLeafMainTermCurveSystemStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_MainTerm_zeta_leaf_main_term


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
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
  first | exact @GlobalTheory.MainTerm.zeta_leaf_main_term | exact GlobalTheory.MainTerm.zeta_leaf_main_term | (intros; apply GlobalTheory.MainTerm.zeta_leaf_main_term <;> assumption)
end _root_.GlobalTheory.T
