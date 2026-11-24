-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:27:21.490573+00:00
-- url     : https://prove2.me/submissions/2b401780-3ad3-4aca-bc6e-f2c6a30a8690

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pair_map
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_overR_mkT
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pair_mkT
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_exists_factor
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_unique
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_over
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_mem_of_fst
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pair_axis
import Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_exists_split
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (U : (A ⊗ A).left.affineOpens) (ε : Sec (A ⊗ A).hom U.1 →+* B)
    (hε : spMap ε ≫ affPt (A ⊗ A).hom U = (lift (x0 A B) (x0 A B)).left)
    (l : Ω[Sec (A ⊗ A).hom U.1⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω) : l (c.1 (op U)) = 0 := by
  have he : ε.comp (algebraMap R _) = algebraMap R B :=
    factor_over _ U ε _ (by rw [hε]; exact Over.w (lift (x0 A B) (x0 A B)))
  have ht := overR_mkT ε l hl he
  let t := mkT ε l hl
  have hU : ∀ z, (spMap ε ≫ affPt (A ⊗ A).hom U) z ∈ U.1 := fun z ↦ by
    change affPt _ U _ ∈ U.1
    have := U.2.range_fromSpec
    rw [← SetLike.mem_coe, ← this]
    exact ⟨_, rfl⟩
  let y : TT (r1 R B M) ⟶ A ⊗ A := Over.homMk (spMap t ≫ affPt (A ⊗ A).hom U) (by
    change (spMap t ≫ affPt (A ⊗ A).hom U) ≫ (A ⊗ A).hom = spMap (r1 R B M)
    rw [Category.assoc, affPt_w, ← spMap_comp]
    exact congrArg spMap ht)
  have hft : (TrivSqZeroExt.fstHom B B M).toRingHom.comp t = ε := by
    ext a; simp [t, mkT]
  have hy : pt (ρ := r1 R B M) (TrivSqZeroExt.fstHom B B M).toRingHom fst_comp_square_zero_section ≫ y =
      lift (x0 A B) (x0 A B) := by
    apply Over.OverMorphism.ext
    rw [← hε, ← hft, spMap_comp]
    exact (Category.assoc _ _ _).symm
  obtain ⟨Y, hY0, hYs, hY1, hY2⟩ := exists_split A y hy
  have hYU : ∀ z, Y.left z ∈ U.1 := mem_of_fst Y.left U.1 fun z ↦ by
    have e : spMap (TrivSqZeroExt.fstHom B B (M × M)).toRingHom ≫ Y.left = spMap ε ≫ affPt (A ⊗ A).hom U :=
      (congrArg (fun q ↦ q.left) hY0).trans hε.symm
    rw [e]
    exact hU z
  obtain ⟨t₂, et₂⟩ := exists_factor (A ⊗ A).hom U Y.left hYU
  have ht₂ : OverR R t₂ := factor_over _ U t₂ _ (by rw [et₂]; exact Over.w Y)
  have cmpU : ∀ (u : M × M →ₗ[B] M), spMap ((mH u).comp t₂) ≫ affPt (A ⊗ A).hom U =
      (pt (mH u) (module_hom_comp_square_zero_section (R := R) _) ≫ Y).left := fun u ↦ by
    rw [spMap_comp, Category.assoc, et₂]; rfl
  have ovr : ∀ (u : M × M →ₗ[B] M), OverR R ((mH u).comp t₂) := fun u ↦ by
    change ((mH u).comp t₂).comp _ = _
    rw [RingHom.comp_assoc, ht₂]
    exact module_hom_comp_square_zero_section (R := R) u
  have es : (mH (LinearMap.fst B M M + LinearMap.snd B M M)).comp t₂ = t := factor_unique _ U (by
    rw [cmpU, hYs]; rfl)
  have k1 : pair ((mH (LinearMap.fst B M M)).comp t₂) (ovr _) (c.1 (op U)) = 0 :=
    pair_axis (wOver (lift (𝟙 A) (1 : A ⟶ A))) c h1 U _ _ (y ≫ CartesianMonoidalCategory.fst A A).left
      (Over.w (y ≫ CartesianMonoidalCategory.fst A A)) (by
        rw [cmpU, hY1]; rfl)
  have k2 : pair ((mH (LinearMap.snd B M M)).comp t₂) (ovr _) (c.1 (op U)) = 0 :=
    pair_axis (wOver (lift (1 : A ⟶ A) (𝟙 A))) c h2 U _ _ (y ≫ CartesianMonoidalCategory.snd A A).left
      (Over.w (y ≫ CartesianMonoidalCategory.snd A A)) (by
        rw [cmpU, hY2]; rfl)
  rw [pair_map _ t₂ ht₂] at k1 k2
  have k3 := pair_map (LinearMap.fst B M M + LinearMap.snd B M M) t₂ ht₂ (ovr _) (c.1 (op U))
  rw [LinearMap.add_apply, k1, k2, add_zero] at k3
  have k4 : ∀ (t' : _ →+* TrivSqZeroExt B M) (e : t' = t) (h : OverR R t'), pair t' h (c.1 (op U)) = l (c.1 (op U)) := by
    intro t' e h
    subst e
    exact pair_mkT ε l hl _ _
  rw [← k4 _ es (ovr _), k3]
end GlobalTheory.CompanionTheory.AxForm
