-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:18.633587+00:00
-- url     : https://prove2.me/submissions/ae24457a-c3c9-40e0-ac57-65da4410b05e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_GlobalTheory_UU_BoxSec_Rep_mul
import Theorems.Thm_GlobalTheory_UU_BoxSec_Rep_out
import Theorems.Thm_GlobalTheory_UU_BoxSec_Rep_congr
import Theorems.Thm_GlobalTheory_UU_BoxSec_exists_sum
import Theorems.Thm_GlobalTheory_UU_BoxSec_comp_cT
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_fam
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_cub
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_cub_inv
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_sym_inv
import Theorems.Thm_GlobalTheory_UU_BoxSec_rep_rig
import Theorems.Thm_GlobalTheory_UU_BoxSec_cT_add
import Theorems.Thm_GlobalTheory_UU_BoxSec_box_form
import Theorems.Thm_GlobalTheory_UU_BoxSec_form_add
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (ρ₀ : D.P.A ⊗ D.P.A ⟶ T₀) (α β : D.X), (∀ (n : ℕ) (f : Fin n → SecBT D T₀ 2 α) (f' : Fin n → SecBT D T₀ 2 β), ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))), ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval d (lift x y).left z J = ∑ i, sval (f i) (lift (lift x y ≫ ρ₀) x).left z J * sval (f' i) (lift (lift x y ≫ ρ₀) y).left z J) ∧ ∀ (a b : D.X) (g : SecBT D T₀ 1 a) (g' : SecBT D T₀ 1 b), α = a + b → β = a - b → ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))), ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval d (lift x y).left z J = (kapV D a b z J x y).val * (sval g (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval g' (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro R _ _ D T₀ ρ₀ α β
  refine ⟨fun n f f' => ?_, fun a b g g' hα hβ => ?_⟩
  · choose s hs using fun i => ((rep_fam D ρ₀ (fst D.P.A D.P.A) (f i)).mul
      (rep_fam D ρ₀ (snd D.P.A D.P.A) (f' i))).out D.P.isLB _ _ (fun _ _ h => (box_form D α β h).symm)
    obtain ⟨d, hd⟩ := exists_sum _ _ s
    refine ⟨d, fun T x y z J hJ => (hd _ _ z J hJ).trans (Finset.sum_congr rfl fun i _ => ?_)⟩
    rw [hs i T (lift x y) z J hJ, lift_fst, lift_snd]
  · subst hα hβ
    let x := fst D.P.A D.P.A
    let y := snd D.P.A D.P.A
    have hc : cT D (D.P.A ⊗ D.P.A) (a - b) * cT D _ b = cT D _ a := by rw [← cT_add, sub_add_cancel]
    obtain ⟨d, hd⟩ := (((((((rep_cub D x y y⁻¹).mul (rep_sym_inv D y)).mul ((rep_rig D).mul (rep_rig D))).mul
      (rep_cub D (cT D _ a) (cT D _ b) x)).mul (rep_cub D (cT D _ b) y y⁻¹)).mul
      (((rep_cub_inv D (cT D _ a) x y).mul (rep_cub_inv D (cT D _ b) x y⁻¹)).mul
        (rep_cub_inv D (cT D _ (a - b)) (cT D _ b) y))).mul
      ((rep_fam D ρ₀ (x * y) g).mul (rep_fam D ρ₀ (x * y⁻¹) g'))).out D.P.isLB _ _ (fun _ _ h =>
        (form_add D h x y _ _ _ hc).trans (by rw [← cT_add]; exact (box_form D (a + b) (a - b) h).symm))
    refine ⟨d, fun T p q z J hJ => (hd T (lift p q) z J hJ).trans ?_⟩
    have e₁ : lift p q ≫ x = p := lift_fst _ _
    have e₂ : lift p q ≫ y = q := lift_snd _ _
    have e₃ : lift p q ≫ y⁻¹ = q⁻¹ := by rw [GrpObj.comp_inv, e₂]
    have e₄ : lift p q ≫ (x * y) = p * q := by rw [MonObj.comp_mul, e₁, e₂]
    have e₅ : lift p q ≫ (x * y⁻¹) = p * q⁻¹ := by rw [MonObj.comp_mul, e₁, e₃]
    simp only [e₁, e₂, e₃, e₄, e₅, comp_cT]
    congr 1
    simp only [kapV, kap0, rigV, mul_inv, sq, Units.val_mul]
end GlobalTheory.UU.BoxSec
