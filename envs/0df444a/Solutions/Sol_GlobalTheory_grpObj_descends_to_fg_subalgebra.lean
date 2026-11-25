-- Prove2me | solution 1 for GlobalTheory.grpObj_descends_to_fg_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:01.08004+00:00
-- url     : https://prove2.me/submissions/aa00c5ba-f359-4a93-a9c4-d07b4fe88a0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GrpObjDescendsToFgSubalgebra
import Theorems.Thm_GlobalTheory_GrpSpread_isSquare_sq
import Theorems.Thm_GlobalTheory_GrpSpread_sq_ext
import Theorems.Thm_GlobalTheory_GrpSpread_isPullback_sq
import Theorems.Thm_GlobalTheory_GrpSpread_exists_grpObj
import Theorems.Thm_GlobalTheory_GrpSpread_exists_fg_descent
import Theorems.Thm_GlobalTheory_Spread_isSchemeTheoreticallyDominant_bcMap
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open GrpSpread
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (X : Scheme.{0}) (p : X ⟶ Sp k) (φ : A.left ⟶ X) (F : Finset V), Smooth p → IsSeparated p → QuasiCompact p → IsPullback φ A.hom p (spMap (algebraMap k V)) → ∃ (R : Subalgebra k V) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (ψ : A.left ⟶ A₀.left), (F : Set V) ⊆ R ∧ R.FG ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧ QuasiCompact A₀.hom ∧ IsGrpPullback A A₀ (spMap R.val.toRingHom) ψ := by
  intro k V _ _ _ A _ _ X p φ F hsm hsep hqc hA
  let G : Over (Sp k) := Over.mk p
  have hAG : IsPullback φ A.hom G.hom (spMap (algebraMap k V)) := hA
  have : QuasiCompact (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]
    show QuasiCompact (pullback.fst p p ≫ p)
    infer_instance
  have : QuasiSeparated (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]
    show QuasiSeparated (pullback.fst p p ≫ p)
    infer_instance
  have : LocallyOfFinitePresentation p := inferInstance

  have hf₁ : ((μ[A]).left ≫ φ) ≫ p = sq hAG.w ≫ (G ⊗ G).hom := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (μ[A]), (isPullback_sq hAG).w]
  obtain ⟨R₁, hR₁, H₁⟩ := exists_fg_descent (G ⊗ G).hom p (isPullback_sq hAG) _ hf₁
  have hf₂ : ((ι[A]).left ≫ φ) ≫ p = φ ≫ p := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (ι[A])]
  obtain ⟨R₂, hR₂, H₂⟩ := exists_fg_descent p p hA _ hf₂
  have hf₃ : ((η[A]).left ≫ φ) ≫ p = spMap (algebraMap k V) ≫ 𝟙 (Sp k) := by
    rw [Category.assoc, hA.w, ← Category.assoc, Over.w (η[A]), Category.comp_id]
    exact Category.id_comp _
  obtain ⟨R₃, hR₃, H₃⟩ := exists_fg_descent (𝟙 (Sp k)) p
    (IsPullback.id_vert (spMap (algebraMap k V))) ((η[A]).left ≫ φ) hf₃
  let R : Subalgebra k V := R₁ ⊔ R₂ ⊔ R₃ ⊔ Algebra.adjoin k (F : Set V)
  have hRfg : R.FG := ((hR₁.sup hR₂).sup hR₃).sup (Subalgebra.fg_adjoin_finset F)
  have le₁ : R₁ ≤ R := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have le₂ : R₂ ≤ R := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have le₃ : R₃ ≤ R := le_sup_right.trans le_sup_left
  have hF : (F : Set V) ⊆ R := fun x hx => (le_sup_right : Algebra.adjoin k (F : Set V) ≤ R)
    (Algebra.subset_adjoin hx)

  obtain ⟨A₀, f₀, h₀, hsm₀, hse₀, hqc₀⟩ : ∃ (A₀ : Over (Sp R)) (f₀ : A₀.left ⟶ X),
      IsPullback f₀ A₀.hom p (spMap (algebraMap k R)) ∧ Smooth A₀.hom ∧ IsSeparated A₀.hom ∧
        QuasiCompact A₀.hom :=
    ⟨Over.mk (pullback.snd p _), pullback.fst p _, IsPullback.of_hasPullback _ _,
      by dsimp; infer_instance, by dsimp; infer_instance, by dsimp; infer_instance⟩
  have h₀G : IsPullback f₀ A₀.hom G.hom (spMap (algebraMap k R)) := h₀

  have hP := GlobalTheory.Spread.isPullback_bcMap (𝟙 (Sp k)) R.val
  have : Flat (𝟙 (Sp k)) := by
    have : IsOpenImmersion (𝟙 (Sp k)) := inferInstance
    infer_instance
  have := GlobalTheory.Spread.isSchemeTheoreticallyDominant_bcMap (𝟙 (Sp k)) R.val Subtype.val_injective
  have eJ : spMap R.val.toRingHom = inv (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k V))) ≫
      GlobalTheory.Spread.bcMap (𝟙 (Sp k)) R.val ≫ pullback.snd _ _ := by
    rw [hP.w, IsIso.inv_hom_id_assoc]
  have : IsSchemeTheoreticallyDominant (spMap R.val.toRingHom) := by
    rw [eJ]
    infer_instance
  have : QuasiCompact (spMap R.val.toRingHom) := by
    rw [eJ]
    infer_instance
  have eV : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) :=
    GlobalTheory.Spread.spMap_algHom_comp R.val
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : A.left ⟶ A₀.left, ψ ≫ f₀ = φ ∧ ψ ≫ A₀.hom = A.hom ≫ spMap R.val.toRingHom :=
    ⟨h₀.lift φ (A.hom ≫ spMap R.val.toRingHom) (by rw [hA.w, Category.assoc, eV]),
      h₀.lift_fst _ _ _, h₀.lift_snd _ _ _⟩
  have hψ : IsPullback ψ A.hom A₀.hom (spMap R.val.toRingHom) := by
    refine IsPullback.of_right ?_ hψ₂ h₀
    rw [hψ₁, eV]
    exact hA

  have c₂ : sq hψ.w ≫ sq h₀G.w = sq hAG.w := by
    apply sq_ext
    · rw [Category.assoc, (isSquare_sq h₀G.w).1, ← Category.assoc, (isSquare_sq hψ.w).1, Category.assoc,
        hψ₁, (isSquare_sq hAG.w).1]
    · rw [Category.assoc, (isSquare_sq h₀G.w).2, ← Category.assoc, (isSquare_sq hψ.w).2, Category.assoc,
        hψ₁, (isSquare_sq hAG.w).2]
  obtain ⟨g₁, hg₁, hg₁p⟩ := H₁ R le₁ (A₀ ⊗ A₀).left (A₀ ⊗ A₀).hom (sq h₀G.w) (sq hψ.w)
    (isPullback_sq h₀G).w c₂ (isPullback_sq hψ).w
  let m₀ : A₀ ⊗ A₀ ⟶ A₀ := Over.homMk (h₀.lift g₁ (A₀ ⊗ A₀).hom hg₁p) (h₀.lift_snd _ _ _)
  have hm : sq hψ.w ≫ m₀.left = (μ[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [m₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₁, Category.assoc, hψ₁]
    · simp only [m₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, (isPullback_sq hψ).w, Category.assoc, hψ₂,
        ← Category.assoc, Over.w (μ[A])]

  obtain ⟨g₂, hg₂, hg₂p⟩ := H₂ R le₂ A₀.left A₀.hom f₀ ψ h₀.w hψ₁ hψ₂
  let i₀ : A₀ ⟶ A₀ := Over.homMk (h₀.lift g₂ A₀.hom hg₂p) (h₀.lift_snd _ _ _)
  have hi : ψ ≫ i₀.left = (ι[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [i₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₂, Category.assoc, hψ₁]
    · simp only [i₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, hψ₂, Category.assoc, hψ₂, ← Category.assoc,
        Over.w (ι[A])]

  obtain ⟨g₃, hg₃, hg₃p⟩ := H₃ R le₃ (Sp R) (𝟙 _) (spMap (algebraMap k R)) (spMap R.val.toRingHom)
    (by rw [Category.comp_id, Category.id_comp]) eV (by rw [Category.comp_id, Category.id_comp])
  let e₀ : 𝟙_ (Over (Sp R)) ⟶ A₀ := Over.homMk (h₀.lift g₃ (𝟙 (Sp R)) hg₃p) (h₀.lift_snd _ _ _)
  have he : spMap R.val.toRingHom ≫ e₀.left = (η[A]).left ≫ ψ := by
    apply h₀.hom_ext
    · simp only [e₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_fst, hg₃, Category.assoc, hψ₁]
    · simp only [e₀, Over.homMk_left]
      rw [Category.assoc, h₀.lift_snd, Category.comp_id, Category.assoc, hψ₂,
        ← Category.assoc, Over.w (η[A])]
      exact (Category.id_comp _).symm
  obtain ⟨inst, hcomm, hgp⟩ := exists_grpObj (spMap R.val.toRingHom) hψ m₀ i₀ e₀ hm hi he
  exact ⟨R, A₀, inst, hcomm, ψ, hF, hRfg, hsm₀, hse₀, hqc₀, hgp⟩
end GlobalTheory
