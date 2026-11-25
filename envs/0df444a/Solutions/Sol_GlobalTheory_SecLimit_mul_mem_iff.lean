-- Prove2me | solution 1 for GlobalTheory.SecLimit.mul_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:33.888549+00:00
-- url     : https://prove2.me/submissions/8bbee406-a146-46ac-9aae-5538af1a6e17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]
variable {L}
variable {φ : K → (Y ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.SecLimit
theorem _root_.solution (hL : L.IsLB) {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (h : FormEq (Sum.elim φ φ₃) (Sum.elim ε ε₃) φ' ε')
    (w : Vals L Y) : w * evU u ∈ secVals L φ' ε' ↔ w ∈ secVals L φ ε := by
  constructor
  · rintro ⟨s, hs⟩
    have hu' := DVR.invGen_isGen L _ _ u hu
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ) (ε' := ε) hL (fun U _ q => by
      have := h U q
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.id_comp] at this ⊢
      rw [← this]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]) (pullMulSec s (𝟙 Y) (LB.invGen L _ _ u) hu')
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu' _ z J.2, val_inv, Category.comp_id, Units.mul_inv_eq_iff_eq_mul]
    exact congrFun (congrFun (congrFun (congrFun hs Z) r) z) J
  · rintro ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_sec (φ' := φ') (ε' := ε') hL (fun U _ q => by
      simpa only [Category.id_comp] using h U q) (pullMulSec s (𝟙 Y) u hu)
    refine ⟨t, ?_⟩
    funext Z r z J
    refine (ht Z r z J.1 J.2).trans ?_
    rw [sval_pullMulSec _ _ _ hu _ z J.2, Category.comp_id]
    rfl
end GlobalTheory.SecLimit
