-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.valR_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:52.130256+00:00
-- url     : https://prove2.me/submissions/0f968f82-031b-42c0-81a0-4ee534655417

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
import Theorems.Thm_GlobalTheory_InvFieldRing_valR_of

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
variable {A : Type} [CommRing A] {Y : Scheme.{0}}
namespace GlobalTheory.InvFieldRing
theorem _root_.solution (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f * g) = valR x V f * valR x V g := by
  simp only [valR_of x V h, map_mul]
end GlobalTheory.InvFieldRing
