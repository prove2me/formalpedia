-- Prove2me | solution 1 for GlobalTheory.TanDeriv.derivative_tangent_combination_universal_group_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:06.090909+00:00
-- url     : https://prove2.me/submissions/d3949307-8569-4e14-b983-1e5508e3c70f

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
import Theorems.Thm_GlobalTheory_TanDeriv_derivAt_sum
import Theorems.Thm_GlobalTheory_TanMod_TanSp_pt_sum
import Theorems.Thm_GlobalTheory_TanMod_smT_zero_of


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.TanMod
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} [GrpObj G]
variable [IsCommMonObj G]
namespace GlobalTheory.TanDeriv
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hv0 : ∀ i, IsTanAt x (v i)) (hw : IsCombAt x v a w)
    (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)) :
    (evAt w U h f).snd = ∑ i, a i * (evAt (v i) U (hv i) f).snd := by
  let b : Fin m → TanSp x Xo.univ.t.G := fun i =>
    TanSp.mk (Over.homMk (v i) (hv0 i).1) (smT_zero_of x _ (hv0 i).2)
  refine derivAt_sum b a w ?_ U h hv f
  obtain ⟨u, hu, rfl⟩ := hw
  have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
  subst hub
  rw [List.prod_ofFn, ← TanSp.pt_sum]
end GlobalTheory.TanDeriv
