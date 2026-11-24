-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.appLE_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:58.990211+00:00
-- url     : https://prove2.me/submissions/f1deb73e-c2bd-4e7b-8cd2-0faaa19652ed

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.InvFieldRing
theorem _root_.solution {Y Z Q : Scheme.{0}} (g : Z ⟶ Y) (k : Q ⟶ Z) (V : Y.Opens) (W : Z.Opens) (W' : Q.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ k ⁻¹ᵁ W) (f : Γ(Y, V)) :
    (k.appLE W W' e').hom ((g.appLE V W e).hom f) = ((k ≫ g).appLE V W' (e'.trans (k.preimage_mono e))).hom f := by
  rw [← Scheme.Hom.appLE_comp_appLE k g V W W' e e']
  rfl
end GlobalTheory.InvFieldRing
