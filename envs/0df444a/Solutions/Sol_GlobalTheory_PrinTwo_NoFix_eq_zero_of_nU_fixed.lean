-- Prove2me | solution 1 for GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:37.774068+00:00
-- url     : https://prove2.me/submissions/2d542ceb-072a-4b4d-88ca-8d87bde65961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesZeroOfCoordinateZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramifiedPrincipalSeriesNoInvariant
import Theorems.Thm_GlobalTheory_PrinTwo_NoFix_eq_zero_of_fixed_of
import Theorems.Thm_GlobalTheory_T_principal_series_coordinate_near_infinity
import Theorems.Thm_GlobalTheory_T_principal_series_zero_of_coordinate_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo
namespace GlobalTheory.PrinTwo.NoFix
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 :=
  fun _ _ _ _ _ _ _ h₁ h₂ hne f hf =>
    GlobalTheory.PrinTwo.NoFix.eq_zero_of_fixed_of GlobalTheory.T.principal_series_zero_of_coordinate_zero GlobalTheory.T.principal_series_coordinate_near_infinity h₁ h₂ hne f hf
end GlobalTheory.PrinTwo.NoFix
