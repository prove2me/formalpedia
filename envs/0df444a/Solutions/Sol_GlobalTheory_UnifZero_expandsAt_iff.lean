-- Prove2me | solution 1 for GlobalTheory.UnifZero.expandsAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:21.019492+00:00
-- url     : https://prove2.me/submissions/8cd16261-857c-4a51-a800-7ee859b1766c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_resTop_inj
import Theorems.Thm_GlobalTheory_UnifZero_unit_pow_mul_app
import Theorems.Thm_GlobalTheory_UnifZero_app_mul_unit
import Theorems.Thm_GlobalTheory_UnifZero_appTop_scal
import Theorems.Thm_GlobalTheory_UnifZero_scal_specMap
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
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
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
variable {R I}
namespace GlobalTheory.UnifZero
theorem _root_.solution (e k : ℕ)
    {σ : LB.Sec (LB.LinComb (zeroPre R I).LG.L (K := Fin 1)
      (fun _ => 𝟙 (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (fun _ => (k : ℤ)))}
    {f : ∀ α : (zeroData R I).toPre.X, (zeroData R I).toPre.SecB k α} {a b : R}
    (ha : SecConst σ (scal (𝟙 _) a)) (hb : SecConst (f PUnit.unit) (scal (𝟙 _) b)) :
    (zeroPre R I).ExpandsAt e k σ f ↔ a - b ∈ I ^ (e + 1) := by
  let p := pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e)
  let q := pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e)
  haveI : IsIso q := (inferInstance : IsIso (pullback.snd (𝟙 _) (thick R I e)))
  have hp : ∀ x : R, scal p x = scal q (Ideal.Quotient.mk _ x) := fun x => by
    rw [← scal_specMap]
    exact congrArg (scal · x) ((Category.comp_id _).symm.trans pullback.condition)
  have hG : ∀ x : R, (fstG I e (𝟙_ _)).left.appTop.hom (scal (𝟙 _) x) = scal p x := fun x =>
    (appTop_scal _ _ _).trans (congrArg (scal · x) (Category.comp_id _))
  have hB : ∀ x : R, ((zeroPre R I).gt e).pG.left.appTop.hom (scal (𝟙 _) x) = scal p x := fun x =>
    (appTop_scal _ _ _).trans (congrArg (scal · x) ((Category.comp_id _).trans (zeroGt_pG R I e)))
  rw [← Ideal.Quotient.eq, ← (scal_bijective q).1.eq_iff, ← hp, ← hp]
  have hpre : ∀ {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {U : Y.Opens}, U = ⊤ → ⊤ ≤ g ⁻¹ᵁ U := by
    rintro _ _ g _ rfl
    exact le_rfl
  have key : ∀ S p' j₁ jf jt, (zeroPre R I).expW e p' j₁ S jf jt = ⊤ := fun S p' j₁ jf jt =>
    top_unique (le_inf (le_inf (le_inf (wchart_triv _ _).ge (wchart_triv _ _).ge)
      (hpre _ (wchart_triv _ _))) (Finset.le_inf fun α _ =>
        le_inf (hpre _ (wchart_triv _ _)) (wchart_triv _ _).ge))
  constructor
  · rintro ⟨S, h0, h⟩
    have h1 := h (fun _ => PUnit.unit, fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ _ => PUnit.unit)
      (fun _ _ => PUnit.unit) rfl (fun _ _ _ => @Subsingleton.elim PUnit _ _ _)
    have h2 := ((unit_pow_mul_app _ _ _ rfl (ha _) k).symm.trans h1).trans
      (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _))
    rw [hG, hB, Finset.sum_const, Finset.card_attach] at h2
    by_cases hS : PUnit.unit ∈ S
    · obtain rfl : S = {PUnit.unit} := Finset.eq_singleton_iff_unique_mem.2 ⟨hS, fun _ _ => rfl⟩
      exact resTop_inj (key _ _ _ _ _) (h2.trans (one_nsmul _))
    · obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun _ => hS
      rw [Finset.card_empty, zero_smul] at h2
      have h3 := ((app_resTop _ _ _).symm.trans
        (congrArg _ (hb (fun _ => PUnit.unit)).symm)).trans (h0 PUnit.unit hS _)
      rw [hB] at h3
      exact (resTop_inj (key _ _ _ _ _) (h2.trans (map_zero _).symm)).trans
        (resTop_inj (top_unique (hpre _ (wchart_triv _ _))) (h3.trans (map_zero _).symm)).symm
  · intro H
    refine ⟨{PUnit.unit}, fun α hα => (hα (Finset.mem_singleton_self _)).elim, ?_⟩
    intro p' j₁ jf jt _ _
    refine (unit_pow_mul_app _ _ _ rfl (ha _) k).trans
      (Eq.trans ?_ (Finset.sum_congr rfl fun α _ => app_mul_unit _ _ _ (gv_one _) (hb _)).symm)
    rw [hG, hB, Finset.sum_const, Finset.card_attach, H]
    exact (one_nsmul _).symm
end GlobalTheory.UnifZero
