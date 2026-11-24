-- Prove2me | solution 1 for GlobalTheory.existsUnique_descend_of_torsion_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:46.077203+00:00
-- url     : https://prove2.me/submissions/82888706-04d0-4901-ad72-6fe8709561e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Theorems.Thm_GlobalTheory_exists_local_rational_torsion
import Theorems.Thm_GlobalTheory_existsUnique_appTop_eq_of_flat
import Theorems.Thm_GlobalTheory_resLE_appTop_topIso_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_comp_mOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    [Etale (mulA A n).left] [Surjective (mulA A n).left] [QuasiCompact (mulA A n).left]
    (U : A.left.Opens) (f : Γ(A.left, (mulA A n).left ⁻¹ᵁ U))
    (hf : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, y ^ n = 1 →
      ∀ (e : (mulA A n).left ⁻¹ᵁ U ≤
        ((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ ((mulA A n).left ⁻¹ᵁ U)),
        (((toUnit A ≫ y) * 𝟙 A).left.appLE _ _ e).hom f = f) :
    ∃! g : Γ(A.left, U), ((mulA A n).left.app U).hom g = f := by
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ A), y ≫ mulA A n = y ^ n :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  let m := (mulA A n).left
  have hm : m = (mulA A n).left := rfl
  let V := m ⁻¹ᵁ U
  let f' : Γ(V, ⊤) := V.topIso.inv.hom f
  have key : ∀ {Z : Scheme.{0}} (a b : Z ⟶ V), a ≫ (m ∣_ U) = b ≫ (m ∣_ U) →
      a ≫ TLinPf.mOf f' = b ≫ TLinPf.mOf f' := by
    intro Z a b hab
    have hab' : (a ≫ V.ι) ≫ m = (b ≫ V.ι) ≫ m := by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% hab]
    have hw : (a ≫ V.ι) ≫ A.hom = (b ≫ V.ι) ≫ A.hom := by
      rw [← Over.w (mulA A n), ← hm, ← Category.assoc, hab', Category.assoc _ m]
    let FinalForm : Over (Spec (CommRingCat.of K)) := Over.mk ((b ≫ V.ι) ≫ A.hom)
    let z₁ : FinalForm ⟶ A := Over.homMk (a ≫ V.ι) hw
    let z₂ : FinalForm ⟶ A := Over.homMk (b ≫ V.ι) rfl
    have hz : z₁ ^ n = z₂ ^ n := by
      rw [← hmul, ← hmul]
      exact Over.OverMorphism.ext hab'
    have hd : (z₁ * z₂⁻¹) ^ n = 1 := by
      rw [mul_pow, inv_pow, hz, mul_inv_cancel]
    have hloc := exists_local_rational_torsion A n _ hd
    choose W c hc hp y hy hcy using hloc
    let 𝒰 : Z.OpenCover := Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Z (fun p => (W p).left)
      (fun p => (c p).left) (fun p => ⟨p, hp p⟩) hc
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change (c p).left ≫ a ≫ _ = (c p).left ≫ b ≫ _
    let t : A ⟶ A := (toUnit A ≫ y p) * 𝟙 A
    have htm : t ≫ mulA A n = mulA A n := by
      rw [hmul, mul_pow, ← MonObj.comp_pow, hy p, MonObj.comp_one, _root_.one_mul]
    have htm' : t.left ≫ m = m := by rw [hm, ← Over.comp_left, htm]
    have e : V ≤ t.left ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, htm']
    have h1 : c p ≫ z₁ = c p ≫ z₂ ≫ t := by
      have h2 := hcy p
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul] at h2
      rw [h2, ← Category.assoc _ z₂, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
    have h3 : (c p).left ≫ a = (c p).left ≫ b ≫ t.left.resLE V V e := by
      rw [← cancel_mono V.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
      have := congr(($h1).left)
      simpa [z₁, z₂] using this
    have h4 : t.left.resLE V V e ≫ TLinPf.mOf f' = TLinPf.mOf f' := by
      rw [TLinPf.comp_mOf]
      congr 1
      exact (resLE_appTop_topIso_inv t.left e f).trans (congrArg _ (hf _ (hy p) e))
    rw [← Category.assoc, h3, Category.assoc, Category.assoc, h4]
  have : Surjective (m ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨g, hg, hu⟩ := existsUnique_appTop_eq_of_flat (m ∣_ U) f' key
  have h7 : ∀ g : Γ(A.left, U), (m ∣_ U).appTop.hom (U.topIso.inv.hom g) =
      V.topIso.inv.hom ((m.app U).hom g) := fun g => by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_topIso_inv, Scheme.Hom.appLE_eq_app]
  have hV : Function.Injective V.topIso.inv.hom := V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hU : Function.Bijective U.topIso.inv.hom := U.topIso.symm.commRingCatIsoToRingEquiv.bijective
  obtain ⟨g, rfl⟩ := hU.2 g
  refine ⟨g, hV ((h7 g).symm.trans hg), fun g' hg' => hU.1 (hu _ ?_)⟩
  exact (h7 g').trans (congrArg _ hg')
end GlobalTheory
