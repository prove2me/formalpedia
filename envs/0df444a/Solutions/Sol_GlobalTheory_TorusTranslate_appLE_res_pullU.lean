-- Prove2me | solution 1 for GlobalTheory.TorusTranslate.appLE_res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:37:17.890797+00:00
-- url     : https://prove2.me/submissions/85e9b490-3a06-4de7-9bdb-4e3fcc9fe58a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate
namespace GlobalTheory.TorusTranslate
theorem _root_.solution {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h (pullU f U u)).val = (g.appLE U ⊤ hg).hom u.val := by
  subst e
  have : f.app U ≫ Y.presheaf.map (homOfLE h).op ≫ m.appLE W ⊤ hm = (m ≫ f).appLE U ⊤ hg := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  exact congrArg (fun φ => φ.hom u.val) this
end GlobalTheory.TorusTranslate
