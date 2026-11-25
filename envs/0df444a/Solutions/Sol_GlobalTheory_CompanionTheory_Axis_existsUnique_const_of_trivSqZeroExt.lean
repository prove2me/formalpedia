-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Axis.existsUnique_const_of_trivSqZeroExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:08.526051+00:00
-- url     : https://prove2.me/submissions/4964cccb-4d3c-4f63-9ec7-11d4a6324994

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUniqueConstantOfCompatibleFamily
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
namespace GlobalTheory.CompanionTheory.Axis
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (M : Type) [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (F' : C ⥤ CommAlgCat.{0} (TrivSqZeroExt R M)) (bc : BC F F') :
    Stein F' → ∀ z : ∀ T : C, M ⊗[R] F.obj T,
      (∀ (T T' : C) (φ : T ⟶ T'), z T' = (mp F φ).toLinearMap.lTensor M (z T)) →
      ∃! m : M, ∀ T, z T = m ⊗ₜ[R] (1 : F.obj T) := by
  intro hS z hz
  choose e he using bc.bij
  have hpure : ∀ (T : C) (r : TrivSqZeroExt R M) (b : F.obj T), e T (r ⊗ₜ[R] b) = r • bc.α T b := by
    intro T r b
    have h : (r ⊗ₜ[R] b : TrivSqZeroExt R M ⊗[R] F.obj T) = r • ((1 : TrivSqZeroExt R M) ⊗ₜ[R] b) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h, map_smul, he]
  have hnat : ∀ {T T' : C} (φ : T ⟶ T') (x : TrivSqZeroExt R M ⊗[R] F.obj T),
      e T' ((mp F φ).toLinearMap.lTensor _ x) = mp F' φ (e T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
      rw [LinearMap.lTensor_tmul, hpure, hpure, map_smul]
      exact congrArg (r • ·) (bc.naturality φ b)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  let jj : ∀ T : C, M ⊗[R] F.obj T →ₗ[R] TrivSqZeroExt R M ⊗[R] F.obj T :=
    fun T ↦ (TrivSqZeroExt.inrHom R M).rTensor _
  have hsnd : ∀ (T : C) (x : M ⊗[R] F.obj T),
      (TrivSqZeroExt.sndHom R M).rTensor _ (jj T x) = x := by
    intro T x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcomm : ∀ {T T' : C} (φ : T ⟶ T') (x : M ⊗[R] F.obj T),
      jj T' ((mp F φ).toLinearMap.lTensor M x) = (mp F φ).toLinearMap.lTensor _ (jj T x) := by
    intro T T' φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [jj]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hconst : ∀ (T : C) (r : TrivSqZeroExt R M),
      algebraMap (TrivSqZeroExt R M) (F'.obj T) r = e T (r ⊗ₜ[R] (1 : F.obj T)) := by
    intro T r
    rw [hpure, map_one, Algebra.algebraMap_eq_smul_one]
  let w : C0 F' := fun T ↦ e T (jj T (z T))
  have hw : d0 F' w = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [w, Pi.zero_apply]
    rw [← hnat, ← hcomm, ← hz, sub_self]
  obtain ⟨r, hr⟩ := (hS.1 w).1 hw
  have hjjr : ∀ T : C, jj T (z T) = r ⊗ₜ[R] (1 : F.obj T) := by
    intro T
    apply (e T).injective
    rw [← hconst]
    exact (congrFun hr T).symm
  refine ⟨r.snd, fun T ↦ ?_, fun m₂ hm₂ ↦ ?_⟩
  · rw [← hsnd T (z T), hjjr T]
    simp
  · have h0 : algebraMap (TrivSqZeroExt R M) (C0 F') (TrivSqZeroExt.inr (m₂ - r.snd)) = 0 := by
      funext T
      have hd : (m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have h1 : z T = r.snd ⊗ₜ[R] (1 : F.obj T) := by
          rw [← hsnd T (z T), hjjr T]
          simp
        rw [TensorProduct.sub_tmul, ← hm₂ T, ← h1, sub_self]
      have h2 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) = 0 := by
        have : jj T ((m₂ - r.snd) ⊗ₜ[R] (1 : F.obj T)) =
            (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) ⊗ₜ[R] (1 : F.obj T) := by
          simp [jj]
        rw [← this, hd, map_zero]
      change algebraMap (TrivSqZeroExt R M) (F'.obj T) _ = 0
      rw [hconst, h2, map_zero]
    have h3 : (TrivSqZeroExt.inr (m₂ - r.snd) : TrivSqZeroExt R M) = 0 :=
      hS.2 (h0.trans (map_zero _).symm)
    have h4 := congrArg TrivSqZeroExt.snd h3
    simpa [sub_eq_zero] using h4
end GlobalTheory.CompanionTheory.Axis
