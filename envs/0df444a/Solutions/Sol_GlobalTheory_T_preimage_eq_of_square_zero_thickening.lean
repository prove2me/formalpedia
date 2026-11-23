-- Prove2me | solution 1 for GlobalTheory.T.preimage_eq_of_square_zero_thickening
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:46.203812+00:00
-- url     : https://prove2.me/submissions/ee1b78e3-84d5-425c-8866-679debf3587a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Theorems.Thm_GlobalTheory_SecGlue_preimage_eq_of_comp_eq_of_sqZero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens, u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  first | exact @GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | exact GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero | (intros; apply GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero <;> assumption)
end _root_.GlobalTheory.T
