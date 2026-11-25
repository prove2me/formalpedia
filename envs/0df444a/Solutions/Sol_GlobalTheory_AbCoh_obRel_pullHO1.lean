-- Prove2me | solution 1 for GlobalTheory.AbCoh.obRel_pullHO1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:33.267352+00:00
-- url     : https://prove2.me/submissions/ad3a037c-8e85-4b37-a1fe-5db24645b223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionCurvatureSumWedgeSemilinearPullback
import Theorems.Thm_GlobalTheory_AbCoh_pOm_wsum
import Theorems.Thm_GlobalTheory_AbCoh_qOm_wsum
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
import Theorems.Thm_GlobalTheory_CechDR_qOm_restrict
import Theorems.Thm_GlobalTheory_CechDR_twoForm_sep_of_basis
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
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (u v : Fin n → GlobForm s), ObRel (OAff s) x u v → ObRel (OAff s') (pullHO1 h x) (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) := by
  intro R R' _ _ X X' s s' σ φ h x n u v hx
  obtain ⟨f, ω, hfx, hconn, hcurv⟩ := hx
  obtain ⟨f', hf'⟩ := H1.mk_surjective (OAff s') (pullHO1 h x)
  have e1 := isPullO_pullHO1 h x
  rw [IsPullO, ← hf', ← hfx, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at e1
  obtain ⟨b, hb⟩ := e1
  have hb' : ∀ (t t' : (Pair φ)ᵒᵖ) (a : t ⟶ t'), ((pairRes φ s').pullbackOneCocycle f').1 t t' a =
      ((pairPull h).pullbackOneCocycle f).1 t t' a - (b t' - mp (OPair φ s') a (b t)) := by
    intro t t' a
    have e := congrFun (congrFun (congrFun hb t) t') a
    simp only [Pi.sub_apply, amitsur_d0_apply] at e
    linear_combination e
  let ω'' : ∀ t : (Pair φ)ᵒᵖ, Ω[(OAff s').obj ((pairFst φ).obj t)⁄R'] :=
    fun t ↦ q1 (pairPull h) t (ω _) - D R' _ (b t)
  let κ : A1 (OAff s') := fun T T' ψ ↦ D R' _ (f'.1 T T' ψ)
  have hκ : ∀ ⦃T T' T'' : AffOp X'⦄ (a : T ⟶ T') (c : T' ⟶ T''),
      κ T T'' (a ≫ c) = p1 (OAff s') c (κ T T' a) + κ T' T'' c := by
    intro T T' T'' a c
    simp only [κ]
    rw [Z1.comp f', map_add, p1_D]
  have hθ' : ∀ ⦃t t' : (Pair φ)ᵒᵖ⦄ (a : t ⟶ t'),
      κ _ _ ((pairFst φ).map a) = ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) := by
    intro t t' a
    have e0 := hconn ((pairSnd φ).map a)
    have e : q1 (pairPull h) t' (ω _) = p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) +
        D R' _ ((pairPull h).α t' (f.1 _ _ ((pairSnd φ).map a))) := by
      rw [← cechDeRhamCoefMapOneForms_naturality, ← cechDeRhamCoefMapOneForms_D, ← map_add]; exact congrArg _ e0
    have k1 : κ _ _ ((pairFst φ).map a) = D R' _ (((pairPull h).pullbackOneCocycle f).1 t t' a) -
        (D R' _ (b t') - D R' _ (mp (OPair φ s') a (b t))) := by
      simp only [κ]
      rw [show f'.1 _ _ ((pairFst φ).map a) = ((pairRes φ s').pullbackOneCocycle f').1 t t' a from rfl, hb' t t' a,
        map_sub, map_sub] <;> rfl
    have k3 : p1 (OPair φ s') a (D R' _ (b t)) = D R' _ (mp (OPair φ s') a (b t)) :=
      p1_D _ _ _
    have key : ∀ {M : Type} [AddCommGroup M] (df da db dm q' q pq pd : M), df = da - (db - dm) →
        q' = pq + da → pd = dm → df = (q' - db) - (pq - pd) := by
      intros; subst_vars; abel
    rw [show ω'' t' - p1 (OAff s') ((pairFst φ).map a) (ω'' t) = (q1 (pairPull h) t' (ω _) - D R' _ (b t')) -
      (p1 (OPair φ s') a (q1 (pairPull h) t (ω _)) -
        p1 (OPair φ s') a (D R' _ (b t))) from by simp only [ω'', map_sub] <;> rfl]
    exact key _ _ _ _ _ (0 : Ω[(OAff s').obj ((pairFst φ).obj t')⁄R']) _ _ k1 e k3
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'
  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict (OAff s') (pairFst φ) hs1 hg1
    κ hκ ω'' hθ'
  have key2 : ∀ {M : Type} [AddCommGroup M] (k A PA C PC PAC : M), k = A - PA → k = C - PC →
      PAC = PA - PC → A - C = PAC := by
    intro M _ k A PA C PC PAC h1 h2 h3
    subst h3
    exact sub_eq_sub_iff_sub_eq_sub.1 (h1.symm.trans h2)
  let δ : Glob1 (OPair φ s') := ⟨fun t ↦ θ ((pairFst φ).obj t) - ω'' t, fun t t' a ↦
    key2 _ _ _ _ _ _ (hθ ((pairFst φ).map a)) (hθ' a) (map_sub _ _ _)⟩
  obtain ⟨β, hβ⟩ := (pairRes_bijective φ s').2.1.2 δ
  have hβt : ∀ t, β.1 ((pairFst φ).obj t) = θ ((pairFst φ).obj t) - ω'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff s') (pairFst φ) t _).symm.trans (congrArg (fun z : Glob1 (OPair φ s') ↦ z.1 t) hβ)
  refine ⟨f', fun T ↦ θ T - β.1 T, hf', fun T T' ψ ↦ ?_, fun T ↦ ?_⟩
  · have key3 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB : M), k = A - PA → B = PB →
        A - B = (PA - PB) + k := by
      intros; subst_vars; abel
    rw [map_sub]
    exact key3 _ _ _ _ _ (hθ ψ) (β.2 ψ)
  · refine sub_eq_zero.1 (hs2 T _ fun t w ↦ ?_)
    have key4 : ∀ {M : Type} [AddCommGroup M] (k A PA B PB O : M), k = A - PA → B = PB → B = A - O →
        PA - PB = O - k := by
      intros; subst_vars; abel
    have key5 : ∀ (B : Type) [CommRing B] [Algebra R' B] (y : Ω[B⁄R']) (c : B),
        dOne R' B (y - D R' B c) = dOne R' B y := fun B _ _ y c ↦ by rw [map_sub, dOne_D, sub_zero]
    have c1 : p1 (OAff s') w (θ T - β.1 T) = ω'' t - D R' _ (f'.1 _ _ w) := by
      rw [map_sub]; exact key4 _ _ _ _ _ _ (hθ w) (β.2 w) (hβt t)
    have e1 : ∀ (z : Fin n → GlobForm s) k, pullGlob1 (pairPull h) (z k) =
        pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (z k)) := fun z k ↦ isPullForm_pullForm h (z k)
    have c2 : dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t) = wsum (OAff s')
        (fun k ↦ GlobalTheory.CechDR.pullForm h (u k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t) := by
      calc dOne R' ((OAff s').obj ((pairFst φ).obj t)) (ω'' t)
          = dOne R' ((OPair φ s').obj t) (q1 (pairPull h) t (ω ((pairSnd φ).obj t))) := key5 _ _ _
        _ = qOm (pairPull h) 2 t (dOne R ((OAff s).obj ((pairSnd φ).obj t)) (ω ((pairSnd φ).obj t))) :=
          (qOm_dOne _ _).symm
        _ = qOm (pairPull h) 2 t (wsum (OAff s) u v ((pairSnd φ).obj t)) := by rw [hcurv]
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairPull h) (u k)) (fun k ↦ pullGlob1 (pairPull h) (v k)) t :=
          qOm_wsum _ _ _ _
        _ = wsum (OPair φ s') (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (u k)))
            (fun k ↦ pullGlob1 (pairRes φ s') (GlobalTheory.CechDR.pullForm h (v k))) t := by
          simp only [e1 u, e1 v]
        _ = qOm (pairRes φ s') 2 t (wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
            (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) ((pairFst φ).obj t)) := (qOm_wsum _ _ _ _).symm
        _ = _ := qOm_restrict _ _ _ _
    have c3 := pOm_wsum (OAff s') (fun k ↦ GlobalTheory.CechDR.pullForm h (u k))
      (fun k ↦ GlobalTheory.CechDR.pullForm h (v k)) w
    rw [map_sub, pOm_dOne, c1, c3, key5, c2, sub_self]
end GlobalTheory.AbCoh
