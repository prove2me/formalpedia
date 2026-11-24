-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.valR_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:53:59.658665+00:00
-- url     : https://prove2.me/submissions/1e7babcb-2eba-465b-8f94-1053d7ef30c9

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
theorem _root_.solution {Z : Scheme.{0}} (x : Sp A ⟶ Z) (g : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ g ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Y, V)) : valR x W ((g.appLE V W e).hom f) = valR (x ≫ g) V f := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := h.trans (x.preimage_mono e)
  rw [valR_of x W h, valR_of (x ≫ g) V h', ← Scheme.Hom.appLE_comp_appLE x g V W ⊤ e h]
  rfl
end GlobalTheory.InvFieldRing
