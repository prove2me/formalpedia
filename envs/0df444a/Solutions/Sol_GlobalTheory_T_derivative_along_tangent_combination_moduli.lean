-- Prove2me | solution 1 for GlobalTheory.T.derivative_along_tangent_combination_moduli
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:09.174962+00:00
-- url     : https://prove2.me/submissions/b68f8bc0-5fa4-4245-ac46-b58672fcd4ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuli
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuliStatement
import Theorems.Thm_GlobalTheory_TanDeriv_deriv_comb


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  first | exact @GlobalTheory.TanDeriv.deriv_comb | exact GlobalTheory.TanDeriv.deriv_comb | (intros; apply GlobalTheory.TanDeriv.deriv_comb <;> assumption)
end _root_.GlobalTheory.T
