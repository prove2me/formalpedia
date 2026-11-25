-- Prove2me | solution 1 for GlobalTheory.UT.PhiOrder.exists_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:17:23.6328+00:00
-- url     : https://prove2.me/submissions/768ecf29-0dee-4f8c-9011-c10de0683d11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SymmetricFramePhiPowOrderEqId
import Theorems.Thm_GlobalTheory_UT_PhiOrder_weight_eq
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_mul
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_inv
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_prod
import Theorems.Thm_GlobalTheory_UT_PhiOrder_Rep_pow
import Theorems.Thm_GlobalTheory_UT_PhiOrder_rep_cubN
import Theorems.Thm_GlobalTheory_UT_PhiOrder_rep_cub
import Theorems.Thm_GlobalTheory_UT_PhiOrder_rep_sym
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.PhiOrder
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D}
namespace GlobalTheory.UT.PhiOrder
theorem _root_.solution (m k : ℕ) (hk : k = 2 * m + 1) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ k) (k ^ 2) 1), Normd κ ∧
      ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val κ x.left z J =
        (th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k) * (val D.sym (x ^ k).left z J)⁻¹ * pot (th D z J) x (2 * k)) ^ m *
          (pot (th D z J) x k ^ (k + 2 * m))⁻¹ := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := ((((rep_cub (D := D) k).mul (rep_sym k).inv).mul
    (Rep.prod rep_cubN (2 * k))).pow m).mul ((Rep.prod rep_cubN k).pow (k + 2 * m)).inv
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB (K' := Fin 3)
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ k).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)]) (fun U _ h => by
      rw [hw U h, Fin.prod_univ_three]
      exact weight_eq (fun a : D.P.A ⟶ D.P.A => h a.left) (𝟙 _) m k hk) t ht
  refine ⟨κ, ⟨hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun T x z J hJ => (vκ _ _ z J hJ).trans (hv T x z J hJ)⟩
  have C : IsCub (th D (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  have e := (vκ _ _ y J hJ).trans (hv (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 y J hJ)
  have s₁ := val_corr hJ D.sym_rig (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at s₁
  simp only [one_pow, C.face, C.N_one, Finset.prod_const_one, inv_one, _root_.mul_one, _root_.one_mul] at e
  rw [o, s₁, inv_one, one_pow] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e
end GlobalTheory.UT.PhiOrder
