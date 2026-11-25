-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.appLE_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:44.840433+00:00
-- url     : https://prove2.me/submissions/cb559ac4-ad0d-4bbb-9291-abaf7b3c4c16

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
theorem _root_.solution {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (V : Y.Opens) (W : Z.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by
  subst hg
  rfl
end GlobalTheory.InvFieldRing
