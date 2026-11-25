-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:10.906518+00:00
-- url     : https://prove2.me/submissions/0c7e14be-0212-429f-8639-f55768a9c364

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_GlobalTheory_FamIntAt_exists_psi_of_psiIn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_psi_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_nsmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tau_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FamIntAt
theorem _root_.solution {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) :
    ∃ Ψ : LB.Sec (LB.LinComb D.toPre.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.toPre.c χ).left)
      (fun _ => -1)), ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) (FractionRing R)) (z : T.left) (J),
        Good D.toPre.P.L z J → sval Ψ ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J =
          (val (D.toPre.psi χ) (σ.left ≫ jFK (R := R) (FractionRing R)) z J).val := by
  by_cases h : χ = 0
  swap
  · obtain ⟨Ψ, hΨ⟩ := exists_psi_of_psiIn (D.psi_pos χ h)
    exact ⟨Ψ, fun T σ z J hJ => hΨ _ _ z J hJ⟩
  subst h
  have c0 : D.toPre.c 0 = 1 := by
    have m : D.toPre.c (0 + 0) = D.toPre.c 0 * D.toPre.c 0 := D.toPre.c_add 0 0
    rw [add_zero] at m
    exact mul_eq_left.1 m.symm
  have c1 : (D.toPre.c 0).left = eSec D.toPre.P.A := by
    rw [c0, Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  obtain ⟨Ψ, hΨ⟩ := exists_sec D.toPre.P.isLB (Y := Spec (CommRingCat.of R)) (K' := PUnit)
    (φ' := fun _ => (D.toPre.c 0).left) (ε' := fun _ => -1) (fun U _ h => by rw [c1])
    (Geo.Tor.genSec (LB.invGen D.toPre.P.L _ _ D.toPre.rig) (invGen_isGen _ _ _ _ D.toPre.rig_gen))
  refine ⟨Ψ, fun T σ z J hJ => (hΨ _ _ z J hJ).trans ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val
    ((val_inv _ _).trans ?_)))⟩
  have C : IsCub (th D.toPre z J) := isCub_cubV D.toPre.cub hJ
  have t := tau_mul σ hJ D.tau_bimult 0 0 0
  have q := UUA.psi_add σ hJ (0 : D.toPre.X) 0
  have c2 : cP D.toPre T 0 = 1 := by simpa using cPoint_nsmul D.toPre T 0 0
  have hpt : ∀ a b c : D.toPre.X, a = b → val (D.toPre.tau a c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.tau b c) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b c rfl; rfl
  have hpp : ∀ a b : D.toPre.X, a = b → val (D.toPre.psi a) (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
      val (D.toPre.psi b) (σ.left ≫ jFK (R := R) (FractionRing R)) z J := by rintro a b rfl; rfl
  rw [hpt _ _ _ (add_zero 0), c2, C.face] at t
  rw [hpp _ _ (add_zero 0), ← mul_left_cancel t, _root_.one_mul, _root_.mul_assoc] at q
  have q' := (mul_eq_left.1 q.symm)
  have e : val D.toPre.rigK (σ.left ≫ jFK (R := R) (FractionRing R)) z J =
    val D.toPre.rig ((σ.left ≫ jFK (R := R) (FractionRing R)) ≫ jK R) z J := val_pull hJ _ _ _
  rw [e] at q'
  exact (eq_inv_of_mul_eq_one_left q').symm
end GlobalTheory.FamIntAt
