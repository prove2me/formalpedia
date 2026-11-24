-- Prove2me | solution 1 for GlobalTheory.TanDeriv.deriv_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:28.538776+00:00
-- url     : https://prove2.me/submissions/35b37f48-b440-4c48-a90f-3f4c789bffb1

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuli
import Theorems.Thm_GlobalTheory_TanDeriv_derivative_tangent_combination_universal_group_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanDeriv
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
namespace GlobalTheory.TanDeriv
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  intro E _ _ _ H Dw l Xo S _ x m v a w hv0 hw U h hv f
  exact derivative_tangent_combination_universal_group_eval Xo x v a w hv0 hw U h hv f
end GlobalTheory.TanDeriv
