-- Prove2me | solution 1 for GlobalTheory.QkPairing.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:47.292133+00:00
-- url     : https://prove2.me/submissions/47f23ae4-a25f-40a6-b10c-3e630110a664

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ClosedPointWeilPower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_WeilQkPairingExistsUniqueTorus
import Theorems.Thm_GlobalTheory_QkPairing_exists_const
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.QkPairing
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
namespace GlobalTheory.QkPairing
theorem _root_.solution (p p' : QkPt D F k) : ∃ ζ : Fˣ, IsRatio p p' ζ.val := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub 1 p'.g.b p.g.b k
  obtain ⟨N', hN', vN'⟩ := exists_cubN D.cub 1 p.g.b p'.g.b k
  obtain ⟨ζ, hζ⟩ := exists_const D.P.isLB (F := F)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (p.g.s p'.y) N)
      (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ (p'.g.s p.y) N')))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p.g.isGen _) hN)
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (p'.g.isGen _) hN'))) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 4 ⊕ Fin 8) (K' := Fin 4 ⊕ Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p.g.b p'.y h) rfl)
        (prod_neg _ _ (prod_sum₂ (K := Fin 4) (K' := Fin 8) (U := U) _ (prod_gt p'.g.b p.y h) rfl))).trans ?_
      rw [cPoint_y, cPoint_y]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, mul_comm p.g.b p'.g.b]
      module)
  refine ⟨ζ, fun T σ z J hJ => ?_⟩
  have e := hζ _ σ.left z J hJ
  rw [val_mul hJ, val_inv, val_mul hJ, val_mul hJ, vN T σ z J hJ, vN' T σ z J hJ, MonObj.comp_one] at e
  rw [← e, ← Units.val_mul, inv_mul_cancel_right]
end GlobalTheory.QkPairing
