-- Prove2me | solution 1 for GlobalTheory.FamFree.zero_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:06:57.788806+00:00
-- url     : https://prove2.me/submissions/a40c2465-a11c-4e88-b651-362fb823ca50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_sval_zero_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamFree
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X)
    (h : ∀ j, (s.s α).f j = 0) : ∀ j, (s.s (α + k • mu)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := F) hG k mu α
  refine sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]
end GlobalTheory.FamFree
