-- Prove2me | solution 1 for GlobalTheory.PeriodLin.exists_period_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:49.571081+00:00
-- url     : https://prove2.me/submissions/afa4d1cd-1a2c-4ea9-a57e-920a1d87c465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsPeriodMulVec
import Theorems.Thm_GlobalTheory_PeriodConn_isPeriod_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.PeriodLin
open NumberField AlgebraicGeometry CategoryTheory Limits
open scoped Matrix nonZeroDivisors
namespace GlobalTheory.PeriodLin
namespace _root_.GlobalTheory.PeriodLin
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P → IsUnit h₀.det → (∀ j j', h₀ j j' ≠ 0 → ty j = ty j') → ∃ P' : D.La →+ (Fin g → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P' ∧ ∀ a, P' a = h₀ *ᵥ P a := by
  intro E _ _ _ H D g ty P h₀ hP hu hty
  refine ⟨(h₀.mulVecLin).toAddMonoidHom.comp P,
    _root_.GlobalTheory.PeriodConn.isPeriod_mulVec hP (isUnit_iff_ne_zero.mp hu) fun i j hij => ?_,
    fun a => rfl⟩
  by_contra hne
  exact hij (hty i j hne)
end _root_.GlobalTheory.PeriodLin
end GlobalTheory.PeriodLin
