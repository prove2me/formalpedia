-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:02:08.406525+00:00
-- url     : https://prove2.me/submissions/4bd15176-a2f1-4853-a53a-028ac109ce42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
omit [GrpObj A]
namespace GlobalTheory.PairingLevels
namespace Rep
theorem _root_.solution (h : Rep L D f) (h' : Rep L D' f') : Rep L (D + D') (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hD, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hD', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_,
    fun Z r z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv Z r z J hJ) (hv' Z r z J hJ))⟩
  rw [Fintype.sum_sum_type, ← hD, ← hD']; rfl
end Rep
end GlobalTheory.PairingLevels
