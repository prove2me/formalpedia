-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.univ_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:30.110792+00:00
-- url     : https://prove2.me/submissions/83b4de2c-34e7-4fd2-9332-0482de8394a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_mul
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_pow
import Theorems.Thm_GlobalTheory_UT_SymFrame_normd_one
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_triv
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_kap
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_nu
import Theorems.Thm_GlobalTheory_UT_SymFrame_comp_id_pow
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_cub
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_sym
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_cubN
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UT.SymFrame
theorem _root_.solution (hG : GlobalFnsSt) {N : ℕ} {ν : LB.Gen (nuLB D N)} (hν : Normd ν)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ) (b : Y ⟶ D.P.A) (z : Y.left) (J)
    (hJ : Good D.P.L z J) :
    cubV D.cub z J (b ^ N) (b ^ N)⁻¹ (b ^ N) * (val D.sym (b ^ N).left z J)⁻¹ * cubN (cubV D.cub z J) N 1 b (b ^ N) *
      val ν b.left z J ^ N * val κ b.left z J ^ 2 = 1 := by
  have key := (((((grep_cub (D := D) (𝟙 D.P.A ^ N) (𝟙 D.P.A ^ N)⁻¹ (𝟙 D.P.A ^ N)).mul
    (grep_sym (𝟙 D.P.A ^ N)).inv).mul (grep_cubN (𝟙 _) (𝟙 D.P.A ^ N) N)).mul ((grep_nu ν hν.1 (𝟙 _)).pow N)).mul
    ((grep_kap κ hκ.1 (𝟙 _)).pow 2)).triv hG (fun U _ h => by
      rw [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, mul_comm (𝟙 D.P.A) (𝟙 D.P.A ^ N)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y J) := isCub_cubV D.cub hJ
      have e : (1 : 𝟙_ _ ⟶ D.P.A) ≫ 𝟙 D.P.A ^ N = 1 :=
        (comp_id_pow _ _).trans (one_pow _)
      beta_reduce
      rw [e, C.face₃, C.N_one, Category.comp_id, normd_one hν hJ, normd_one hκ hJ,
        normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ]
      simp) Y b z J hJ
  have e : b ≫ 𝟙 D.P.A ^ N = b ^ N := comp_id_pow _ _
  have e' : b ≫ (𝟙 D.P.A ^ N)⁻¹ = (b ^ N)⁻¹ := by rw [← e]; exact map_inv (preHom (G := D.P.A) b) (𝟙 D.P.A ^ N)
  beta_reduce at key
  rwa [e', e, Category.comp_id] at key
end GlobalTheory.UT.SymFrame
