-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.appLE_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:23.138901+00:00
-- url     : https://prove2.me/submissions/d958cbcb-de5d-47c4-b43c-b0ce2bfce186

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst
import Theorems.Thm_GlobalTheory_InvFieldRing_appLE_appLE

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
theorem _root_.solution {R : Type} [CommRing R] {Z Q : Scheme.{0}} (p : Z ⟶ Sp R) (k : Q ⟶ Z) (W : Z.Opens)
    (W' : Q.Opens) (e' : W' ≤ k ⁻¹ᵁ W) (a : R) : (k.appLE W W' e').hom (constFn p W a) = constFn (k ≫ p) W' a := by
  unfold constFn
  exact appLE_appLE p k ⊤ W W' _ e' _
end GlobalTheory.InvFieldRing
