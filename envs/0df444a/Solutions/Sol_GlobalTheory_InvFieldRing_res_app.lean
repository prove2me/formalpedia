-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.res_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:59:06.722169+00:00
-- url     : https://prove2.me/submissions/bd920737-46b0-4c3c-9123-a5f6b5ab716b

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
theorem _root_.solution {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V W : Y.Opens} (h : W ≤ V) (h' : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    resG Z h' ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  change (f.app V ≫ Z.presheaf.map (homOfLE h').op).hom a = (Y.presheaf.map (homOfLE h).op ≫ f.app W).hom a
  rw [Scheme.Hom.naturality]
  rfl
end GlobalTheory.InvFieldRing
