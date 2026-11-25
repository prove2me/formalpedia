-- Prove2me | solution 1 for GlobalTheory.UT.CoefPhi.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:51:23.454799+00:00
-- url     : https://prove2.me/submissions/4f8d1095-7d4b-4955-ae07-b8367bbbe5f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFrameRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubNMul
import Theorems.Thm_GlobalTheory_UT_CoefBasic_prod_line
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_gt


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.CoefPhi
open GlobalTheory.UT.CoefBasic
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.UT.CoefPhi
theorem _root_.solution {k : ℕ} (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) (g₀ : GtPtF D F)
    (ω₀ : Frm D F k g₀.b) (h₀ : ω₀.IsGen) (b : TF (R := R) F ⟶ D.P.A) (hb : b = g₀.b * p.g.b) :
    ∃ ω₁ : Frm D F k b, ω₁.IsGen ∧ ∀ z J, Good D.P.L z J → val ω₁ (𝟙 _) z J =
      val ω₀ (𝟙 _) z J * val w (𝟙 _) z J * val (g₀.s p.y) (𝟙 _) z J * cubN (th D z J) k 1 p.g.b g₀.b := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p.g.b g₀.b k
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      refine Eq.trans (prod_sum₂ (K := (Fin 2 ⊕ Fin 2) ⊕ Fin 4) (K' := Fin 8) (U := U) _
        (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 4) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (prod_line k g₀.b h) (prod_line k p.g.b h))
          (prod_gt g₀.b p.y h)) rfl) ?_
      rw [prod_line, cPoint_y, hb, mul_comm g₀.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ ω₀ w) (g₀.s p.y)) N)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ hw) (g₀.isGen _)) hN)
  refine ⟨u, hu, fun z J hJ => ?_⟩
  have e := vN _ (𝟙 _) z J hJ
  simp only [Category.id_comp, Over.id_left] at e
  exact (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) e))
end GlobalTheory.UT.CoefPhi
