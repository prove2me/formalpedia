-- Prove2me | solution 1 for GlobalTheory.dRel_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:12:19.448531+00:00
-- url     : https://prove2.me/submissions/469933d1-de3d-4035-bd60-400b11c3bd87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomologyDerivativeRelationSemilinearPullback
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_FormExt_glue_one_forms
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_restrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_exists_pair_below_two
import Theorems.Thm_GlobalTheory_CechDR_form_eq_zero_of_basis_cover
import Theorems.Thm_GlobalTheory_CechDR_isPullForm_pullForm
import Theorems.Thm_GlobalTheory_CechDR_isPullO_pullHO1
import Theorems.Thm_GlobalTheory_CechDR_pair_cover_affine
import Theorems.Thm_GlobalTheory_CechDR_prodFirstProjection_smul
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_cocycle_one_forms_coboundary_of_restrict
import Theorems.Thm_GlobalTheory_jacAlt_apply
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
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 600000
namespace GlobalTheory
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (y : Fin n → HO1 s) (w : Fin n → GlobForm s), DRel (OAff s) x y w → DRel (OAff s') (pullHO1 h x) (fun k ↦ pullHO1 h (y k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (w k)) := by
  intro R R' _ _ X X' s s' σ φ h x n y w hx
  obtain ⟨f, g, ω, hf, hg, hD⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  choose g' hg' using fun k ↦ H1.mk_surjective (OAff s') (pullHO1 h (y k))
  have ef := (isPullO_pullHO1 h x).symm
  rw [← hf', ← hf, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at ef
  obtain ⟨A, hA⟩ := ef
  have eg : ∀ k, ∃ B : C0 (OPair φ s'), d0 (OPair φ s') B =
      ((pairRes φ s').pullbackOneCocycle (g' k)).1 - ((pairPull h).pullbackOneCocycle (g k)).1 := by
    intro k
    have e := (isPullO_pullHO1 h (y k)).symm
    rw [← hg' k, ← hg k, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e
    exact e
  choose B hB using eg
  have hA' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a + (A t' - mp (OPair φ s') a (A t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hA t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  have hB' : ∀ k ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a =
      ((pairPull h).pullbackOneCocycle (g k)).1 t t' a + (B k t' - mp (OPair φ s') a (B k t)) := by
    intro k t t' a
    have e := congrFun (congrFun (congrFun (hB k) t) t') a
    rw [amitsur_d0_apply, Pi.sub_apply, Pi.sub_apply] at e
    exact sub_eq_iff_eq_add'.1 e.symm
  set w' : Fin n → GlobForm s' := fun k ↦ pullForm h (w k) with hw'def
  let Wm : Fin n → Glob1 (OPair φ s') := fun k ↦ pullGlob1 (pairPull h) (w k)
  have hWm : ∀ k t, (Wm k).1 t = (w' k).1 ((pairFst φ).obj t) := fun k t ↦
    (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) (isPullForm_pullForm h (w k))).trans
      (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _)
  let κ : A1 (OAff s') := fun T T' a ↦ D R' _ (f'.1 T T' a) - ∑ k, (g' k).1 T T' a • (w' k).1 T'
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (b : T' ⟶ T''),
      κ T T'' (a ≫ b) = p1 (OAff s') b (κ T T' a) + κ T' T'' b := by
    intro T T' T'' a b
    have e1 : D R' _ (f'.1 T T'' (a ≫ b)) =
        p1 (OAff s') b (D R' _ (f'.1 T T' a)) + D R' _ (f'.1 T' T'' b) := by
      rw [Z1.comp, Derivation.map_add, p1_D]
    have e2 : ∀ k, (g' k).1 T T'' (a ≫ b) • (w' k).1 T'' =
        p1 (OAff s') b ((g' k).1 T T' a • (w' k).1 T') + (g' k).1 T' T'' b • (w' k).1 T'' := by
      intro k; rw [Z1.comp, add_smul, oneFormsMapOfFunctorMorphism_smul, ← (w' k).2 b]
    simp only [κ]
    rw [e1, Finset.sum_congr rfl fun k _ ↦ e2 k, Finset.sum_add_distrib, map_sub, map_sum]
    abel
  let θP : A0 (OPair φ s') := fun t ↦
    q1 (pairPull h) t (ω ((pairPull h).G.obj t)) + D R' _ (A t) - ∑ k, B k t • (Wm k).1 t
  have key : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      D R' _ (((pairRes φ s').pullbackOneCocycle f').1 t t' a) - ∑ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        θP t' - p1 (OPair φ s') a (θP t) := by
    intro t t' a
    have hW : ∀ k, (Wm k).1 t' = p1 (OPair φ s') a ((Wm k).1 t) := fun k ↦ (Wm k).2 a
    have e1 : D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) =
        ∑ k, ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' +
          (q1 (pairPull h) t' (ω ((pairPull h).G.obj t')) -
            p1 (OPair φ s') a (q1 (pairPull h) t (ω ((pairPull h).G.obj t)))) := by
      rw [CoefMap.pullCocycleOne_apply, ← cechDeRhamCoefMapOneForms_D, hD, map_add, map_sum, map_sub, cechDeRhamCoefMapOneForms_naturality]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ prodFirstProjection_smul _ _ _
    have e2 : ∀ k, ((pairRes φ s').pullbackOneCocycle (g' k)).1 t t' a • (Wm k).1 t' =
        ((pairPull h).pullbackOneCocycle (g k)).1 t t' a • (Wm k).1 t' + B k t' • (Wm k).1 t' -
          p1 (OPair φ s') a (B k t • (Wm k).1 t) := by
      intro k
      rw [hB', oneFormsMapOfFunctorMorphism_smul, ← hW k, add_smul, sub_smul]
      abel
    simp only [θP]
    rw [hA', Derivation.map_add, Derivation.map_sub, ← p1_D, e1, Finset.sum_congr rfl fun k _ ↦ e2 k]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sub, map_add, map_sum]
    abel
  let θ' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] := θP
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'), κ _ _ ((pairFst φ).map a) =
      θ' t' - p1 (OAff s') ((pairFst φ).map a) (θ' t) := by
    intro t t' a
    have k := key a
    simp only [hWm] at k
    exact k
  obtain ⟨θ, hθ⟩ := GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ)
    (_root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s'))
    (_root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) (_root_.GlobalTheory.CechDR.pair_cover_affine φ s')
      (_root_.GlobalTheory.CechDR.exists_pair_below_two φ s')) κ hκ θ' hθ'
  refine ⟨f', g', θ, hf', hg', fun T T' a ↦ ?_⟩
  exact sub_eq_iff_eq_add'.1 (hθ a)
end GlobalTheory
