-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.qEq_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:35.04783+00:00
-- url     : https://prove2.me/submissions/c42c7fcb-7f5b-4927-99a3-cb4facf72226

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.NumD
variable (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution (k : ℕ) : Equivalence (N.QEq (k := k)) where
  refl p := ⟨0, by simp, by simp⟩
  symm := by
    rintro p p' ⟨z, h, h'⟩
    exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
  trans := by
    rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
    exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, mul_assoc]⟩
end GlobalTheory.Ex.NumD
