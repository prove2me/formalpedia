-- Prove2me | solution 1 for GlobalTheory.torsion_eq_and_weilIs_of_isHolTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:29:29.701252+00:00
-- url     : https://prove2.me/submissions/22a26ab3-410e-4df2-a7da-c2e5f6e98b58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
import Theorems.Thm_GlobalTheory_HolTorsion_isHolTo_comp
import Theorems.Thm_GlobalTheory_HolTorsion_isHolTo_congr
import Theorems.Thm_GlobalTheory_HolTorsion_exists_isHolTo_lift
import Theorems.Thm_P2M_GlobalTheory_HolTorsion_valAt__eq_of_pow_eq_one_6fce98a090c1
import Theorems.Thm_GlobalTheory_HolTorsion_comp_eq_of_unramified
import Theorems.Thm_GlobalTheory_HolTorsion_pow_eq_one_of_weilIs
import Theorems.Thm_GlobalTheory_HolTorsion_val_map_appTop
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open HolTorsion
namespace GlobalTheory
theorem _root_.solution : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (m k : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (x x' : ∀ b, Over.mk (y b) ⟶ P.A) (c : ℂˣ) (b₀ : Fin m → ℂ), 0 < k → IsUnit (k : Γ(X, ⊤)) → IsOpen B → IsPreconnected B → b₀ ∈ B → IsHolTo B (fun b => (x b).left) → IsHolTo B (fun b => (x' b).left) → (∀ b ∈ B, x b ^ k = 1 ∧ x' b ^ k = 1) → ((x b₀ = x' b₀ → ∀ b ∈ B, x b = x' b) ∧ (Out.WeilIs P.A P.L k (x b₀) (x' b₀) (unitOn c) → ∀ b ∈ B, Out.WeilIs P.A P.L k (x b) (x' b) (unitOn c))) := by
  intro hL X _ P m k B y x x' c b₀ hk hku _ hB hb₀ hx hx' htor
  obtain ⟨hfin, -, -, het, -⟩ := hL.mulN X P k hk
  have het := het hku
  let o : X ⟶ P.A.left := (η[P.A] : 𝟙_ (Over X) ⟶ P.A).left
  have ho : o ≫ P.A.hom = 𝟙 X := Over.w (η[P.A] : 𝟙_ (Over X) ⟶ P.A)

  have hkill : ∀ (T : Over X) (u : T ⟶ P.A), u ^ k = 1 ↔ u.left ≫ (Out.mulA P.A k).left = T.hom ≫ o := by
    intro T u
    have e₁ : u.left ≫ (Out.mulA P.A k).left = (u ^ k).left := by
      rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : T.hom ≫ o = (1 : T ⟶ P.A).left := by
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rw [e₁, e₂]
    exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩
  let p := pullback.fst (Out.mulA P.A k).left o
  let q := pullback.snd (Out.mulA P.A k).left o
  have H : IsPullback p q (Out.mulA P.A k).left o := IsPullback.of_hasPullback _ _
  have hpq : p ≫ P.A.hom = q := by
    rw [← Over.w (Out.mulA P.A k), ← Category.assoc, H.w, Category.assoc, ho, Category.comp_id]
  have hy : IsHolTo B y := isHolTo_congr (isHolTo_comp hx P.A.hom) fun b _ => (Over.w (x b)).symm
  obtain ⟨a, ha, hab⟩ := exists_isHolTo_lift H hx hy (fun b hb => (hkill _ _).1 (htor b hb).1) hb₀
  obtain ⟨a', ha', hab'⟩ := exists_isHolTo_lift H hx' hy (fun b hb => (hkill _ _).1 (htor b hb).2) hb₀
  obtain ⟨z, hz, hzb⟩ := exists_isHolTo_lift (IsPullback.of_hasPullback q q) ha ha'
    (fun b hb => (hab b hb).2.trans (hab' b hb).2.symm) hb₀
  refine ⟨fun h₀ b hb => ?_, fun h₀ b hb => ?_⟩
  · have e₀ : a b₀ = a' b₀ := H.hom_ext (by rw [(hab b₀ hb₀).1, (hab' b₀ hb₀).1, h₀])
      (by rw [(hab b₀ hb₀).2, (hab' b₀ hb₀).2])
    have e := comp_eq_of_unramified q hz hB hb₀ hb (by rw [(hzb b₀ hb₀).1, (hzb b₀ hb₀).2, e₀])
    rw [(hzb b hb).1, (hzb b hb).2] at e
    apply Over.OverMorphism.ext
    rw [← (hab b hb).1, ← (hab' b hb).1, e]
  · let T : Over X := Over.mk (pullback.fst q q ≫ q)
    let u : T ⟶ P.A := Over.homMk (pullback.fst q q ≫ p) (by
      show (pullback.fst q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq])
    let v : T ⟶ P.A := Over.homMk (pullback.snd q q ≫ p) (by
      show (pullback.snd q q ≫ p) ≫ P.A.hom = pullback.fst q q ≫ q
      rw [Category.assoc, hpq, pullback.condition])
    have hu : u ^ k = 1 := (hkill T u).2 (by
      show (pullback.fst q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, Category.assoc])
    have hv : v ^ k = 1 := (hkill T v).2 (by
      show (pullback.snd q q ≫ p) ≫ _ = (pullback.fst q q ≫ q) ≫ o
      rw [Category.assoc, H.w, pullback.condition, Category.assoc])
    obtain ⟨e, he, -⟩ := (hL.weil X P k T).1 u v hu hv
    have hek : e.val ^ k = 1 :=
      congrArg Units.val (pow_eq_one_of_weilIs hL.weil P k hu hv he)
    have hpull : ∀ w ∈ B, Out.WeilIs P.A P.L k (x w) (x' w) (Units.map (z w).appTop.hom.toMonoidHom e) := by
      intro w hw
      let h : Over.mk (y w) ⟶ T := Over.homMk (z w) (by
        show z w ≫ pullback.fst q q ≫ q = y w
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).2])
      have e₁ : h ≫ u = x w := Over.OverMorphism.ext (by
        show z w ≫ pullback.fst q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).1, (hab w hw).1])
      have e₂ : h ≫ v = x' w := Over.OverMorphism.ext (by
        show z w ≫ pullback.snd q q ≫ p = _
        rw [← Category.assoc, (hzb w hw).2, (hab' w hw).1])
      have := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h he
      rw [e₁, e₂] at this
      exact this
    have e₀ : Units.map (z b₀).appTop.hom.toMonoidHom e = unitOn c :=
      ((hL.weil X P k _).1 _ _ (htor b₀ hb₀).1 (htor b₀ hb₀).2).unique (hpull b₀ hb₀) h₀
    have e₁ : Units.map (z b).appTop.hom.toMonoidHom e = Units.map (z b₀).appTop.hom.toMonoidHom e :=
      Units.ext ((val_map_appTop (z b) e.val).trans
        ((congrArg _ (valAt'_eq_of_pow_eq_one hz hB hk hek hb₀ hb)).trans (val_map_appTop (z b₀) e.val).symm))
    have := hpull b hb
    rw [e₁, e₀] at this
    exact this
end GlobalTheory
