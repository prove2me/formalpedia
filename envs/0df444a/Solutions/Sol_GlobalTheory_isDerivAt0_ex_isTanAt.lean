-- Prove2me | solution 1 for GlobalTheory.isDerivAt0_ex_isTanAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:26:05.114992+00:00
-- url     : https://prove2.me/submissions/c731f4fc-2e9c-430f-91ab-be2a7deea9fe

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangent
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt0_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) ty P → (∀ w v, IsDerivAt0 (fun z => (F.ex k P z).left) w v → IsTanAt (F.u k P) v) ∧ (∀ w, ∃! v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsDerivAt0 (fun z => (F.ex k P z).left) w v) ∧ ∀ v : (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left), IsTanAt (F.u k P) v → ∃! w, IsDerivAt0 (fun z => (F.ex k P z).left) w v := by
  intro E _ _ _ H Dw l Xo σ' g ty F k P hP
  have h0 := (F.ex_ker k P hP 0).2 (zero_mem _)
  refine ⟨fun w v hv => ⟨((HolHom.isDerivAt0_iff _ _ _).1 hv).over, ?_⟩, fun w => ?_, fun v hv => ?_⟩
  · exact hv.1.trans (congrArg (·.left) h0)
  · obtain ⟨v, hv, -⟩ := (F.ex_diff k P hP).1 w
    exact ⟨v.left, hv, fun v' hv' =>
      ((HolHom.isDerivAt0_iff _ _ _).1 hv').unique ((HolHom.isDerivAt0_iff _ _ _).1 hv)⟩
  · exact (F.ex_diff k P hP).2 (Over.homMk v hv.1) (hv.2.trans (congrArg (·.left) h0).symm)
end GlobalTheory
