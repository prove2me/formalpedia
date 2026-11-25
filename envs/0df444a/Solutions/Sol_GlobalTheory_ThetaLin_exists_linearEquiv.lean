-- Prove2me | solution 1 for GlobalTheory.ThetaLin.exists_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:10.274286+00:00
-- url     : https://prove2.me/submissions/720e50c6-2ed3-4eb4-8918-b18d86aa4b45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Theorems.Thm_GlobalTheory_ThetaLin_gs_scal_comp
import Theorems.Thm_GlobalTheory_UU_SecMod_sval_add
import Theorems.Thm_GlobalTheory_UU_SecMod_sval_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ThetaLin
namespace GlobalTheory.ThetaLin
theorem _root_.solution {F : Type} [CommRing F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) (pr m : Y ⟶ X) (τ σ : Y ⟶ Y) (hm : τ ≫ pr = m) (h₁ : σ ≫ τ = 𝟙 Y)
    (h₂ : τ ≫ σ = 𝟙 Y) (hq : τ ≫ q = q) (k : ℤ)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![k, -k])) (hu : u.IsGen) :
    ∃ Φ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) ≃ₗ[F]
        SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ v (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval (Φ v).sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := by
  have ex : ∀ v : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∃ w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval w.sec r z J = (val u r z J).val * sval v.sec (r ≫ τ) z J := fun v => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k)
      (fun U _ h => by
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
          hm, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
      (pullMulSec v.sec τ u hu)
    exact ⟨SecMod.mk q s', fun Z r z J hJ =>
      (hs' Z r z J hJ).trans ((sval_pullMulSec _ _ u hu r z hJ).trans (_root_.mul_comm _ _))⟩
  choose f hf using ex
  have ext : ∀ v w : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)),
      (∀ y J, Good L y J → sval v.sec (𝟙 Y) y J = sval w.sec (𝟙 Y) y J) → v = w :=
    fun v w h => SecMod.ext (sec_ext_val hL h)
  let Φ₀ : SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) →ₗ[F]
      SecMod q (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => k)) :=
    { toFun := f
      map_add' := fun v w => ext _ _ fun y J hJ => by
        rw [SecMod.sval_add hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_add hJ, mul_add]
      map_smul' := fun c v => ext _ _ fun y J hJ => by
        rw [RingHom.id_apply, SecMod.sval_smul hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, SecMod.sval_smul hJ,
          gs_scal_comp q (𝟙 Y ≫ τ), Category.assoc, hq, Category.id_comp q, mul_left_comm] }
  refine ⟨LinearEquiv.ofBijective Φ₀ ⟨fun v w h => ext _ _ fun y J hJ => ?_, fun w => ?_⟩, hf⟩
  · have e : f v = f w := h
    have := (hf v _ σ y J hJ).symm.trans (e ▸ hf w _ σ y J hJ)
    rwa [h₁, Units.mul_right_inj] at this
  · have hv := DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _ hu) σ
    have h₃ : σ ≫ m = pr := by rw [← hm, ← Category.assoc, h₁, Category.id_comp]
    obtain ⟨s, hs⟩ := exists_sec (φ' := fun _ : Fin 1 => pr) (ε' := fun _ => k) hL (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        h₃, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv, mul_inv_cancel_left])
      (pullMulSec w.sec σ _ hv)
    refine ⟨SecMod.mk q s, ext _ _ fun y J hJ => (hf _ _ _ y J hJ).trans ?_⟩
    rw [SecMod.sec_mk, hs _ _ y J hJ, sval_pullMulSec _ σ _ hv _ y hJ, val_pull hJ, val_inv, Category.assoc, h₂,
      Category.comp_id, mul_left_comm, Units.mul_inv, _root_.mul_one]
end GlobalTheory.ThetaLin
