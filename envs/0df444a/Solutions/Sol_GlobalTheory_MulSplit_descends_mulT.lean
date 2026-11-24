-- Prove2me | solution 1 for GlobalTheory.MulSplit.descends_mulT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:53.08024+00:00
-- url     : https://prove2.me/submissions/eb3fc97e-4176-45ec-aedc-35830a4431f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_Descends_of_iso
import Theorems.Thm_GlobalTheory_MulSplit_translPt_eq
import Theorems.Thm_P2M_GlobalTheory_MulSplit_translT_snd__7615715b5518
import Theorems.Thm_GlobalTheory_MulSplit_mulT_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}
namespace GlobalTheory.MulSplit
theorem _root_.solution [IsCommMonObj A] (n : ℕ)
    (H : ∀ (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over S) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤ ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f) :
    Descends (mulT A (baseOver S) n).left
      (fun y : {y : baseOver S ⟶ A // y ^ n = 1} => (translT A y.1).left) := by
  let t : A ⟶ baseOver S := Over.homMk A.hom (Category.comp_id _)
  have inv : ∀ {T' : Over S} (t' : A ⟶ T') (y : T' ⟶ A), y ^ n = 1 →
      ((t' ≫ y) * 𝟙 A).left ≫ (mulA A n).left = (mulA A n).left := fun t' y hy => by
    rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy, MonObj.comp_one,
      _root_.one_mul]
  have H' : Descends (mulA A n).left
      (fun y : {y : baseOver S ⟶ A // y ^ n = 1} => ((t ≫ y.1) * 𝟙 A).left) := by
    refine ⟨fun U a b hab => ?_, fun U f hf => ?_⟩
    · refine (H U _ fun y hy e => fn_ext fun z hz => ?_).unique hab rfl
      refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans ((gs_pull (𝟙 _ ≫ ((toUnit A ≫ y) * 𝟙 A).left) _ z U (e hz) b).trans
        (Eq.trans ?_ (gs_pull (𝟙 _) _ z U hz b).symm))
      rw [Category.assoc, inv _ y hy]
    · refine (H U f fun y hy e => fn_ext fun z hz => ?_).exists
      refine (gs_appLE _ _ _ e (𝟙 _) z hz _).trans (Eq.trans ?_ (hf ⟨toUnit _ ≫ y, by
        rw [← MonObj.comp_pow, hy, MonObj.comp_one]⟩ z hz))
      show _ = gs ((t ≫ toUnit _ ≫ y) * 𝟙 A).left z _ f
      rw [Category.id_comp, ← Category.assoc, comp_toUnit]
  let e : baseOver S ⊗ A ≅ A := ⟨snd _ _, lift t (𝟙 A), by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · simp, lift_snd _ _⟩
  refine H'.of_iso (fun y => inv t y.1 y.2) ((Over.forget S).mapIso e) ?_ fun y => ?_
  · refine congrArg (fun r => r.left)
      (show lift t (𝟙 A) ≫ mulT A (baseOver S) n = mulA A n ≫ lift t (𝟙 A) from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, Category.assoc, mulT_snd, MonObj.comp_pow, lift_snd, Category.comp_id]
  · refine congrArg (fun r => r.left)
      (show lift t (𝟙 A) ≫ translT A y.1 = ((t ≫ y.1) * 𝟙 A) ≫ lift t (𝟙 A) from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.mkIdTerminal.hom_ext _ _
    · rw [Category.assoc, Category.assoc, translT_snd', translPt_eq, MonObj.comp_mul, lift_snd, Category.comp_id,
        lift_fst_assoc]
end GlobalTheory.MulSplit
