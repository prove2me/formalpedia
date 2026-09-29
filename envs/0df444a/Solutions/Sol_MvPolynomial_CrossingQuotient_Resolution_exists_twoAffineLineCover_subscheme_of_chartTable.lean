-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.exists_twoAffineLineCover_subscheme_of_chartTable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/64b67d9a-270b-5fcf-b32f-aa08af72ace4

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ExcE85
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

section RingLevel
open MvPolynomial.CrossingQuotient
variable {W : Type u} [CommRing W] (t : W)

theorem ringHom_ext_chart' {L : Type*} [Semiring L] {f g : MvPolynomial.CrossingQuotient W t →+* L}
    (hC : ∀ w : W, f (algebraMap W _ w) = g (algebraMap W _ w)) (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    simp only [RingHom.comp_apply]
    have : (Ideal.Quotient.mk (Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C t : MvPolynomial (Fin 2) W)}))
        (MvPolynomial.C w) = algebraMap W (MvPolynomial.CrossingQuotient W t) w := rfl
    rw [this]; exact hC w
  · intro i
    fin_cases i
    · exact hU
    · exact hV

variable (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
  (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t})
include hq hker

noncomputable def quotEquiv : (W ⧸ Ideal.span ({t} : Set W)) ≃ₐ[W] k₀ :=
  (Ideal.quotientEquivAlgOfEq W (show Ideal.span ({t} : Set W) = RingHom.ker (Algebra.ofId W k₀) from hker.symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId W k₀) hq)

theorem algebraMap_k₀_t : algebraMap W k₀ t = 0 := by
  rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t

noncomputable def EU : (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {U t}) ≃ₐ[W] Polynomial k₀ :=
  (exists_algEquiv_quotient_span_U_and_span_V_polynomial t).1.choose.trans
    (Polynomial.mapAlgEquiv (quotEquiv t k₀ hq hker))

theorem EU_mk_V : EU t k₀ hq hker (Ideal.Quotient.mk _ (V t)) = Polynomial.X := by
  rw [EU, AlgEquiv.trans_apply, (exists_algEquiv_quotient_span_U_and_span_V_polynomial t).1.choose_spec]
  simp [Polynomial.mapAlgEquiv]

noncomputable def EV : (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {V t}) ≃ₐ[W] Polynomial k₀ :=
  (exists_algEquiv_quotient_span_U_and_span_V_polynomial t).2.choose.trans
    (Polynomial.mapAlgEquiv (quotEquiv t k₀ hq hker))

theorem EV_mk_U : EV t k₀ hq hker (Ideal.Quotient.mk _ (U t)) = Polynomial.X := by
  rw [EV, AlgEquiv.trans_apply, (exists_algEquiv_quotient_span_U_and_span_V_polynomial t).2.choose_spec]
  simp [Polynomial.mapAlgEquiv]

noncomputable def πU : MvPolynomial.CrossingQuotient W t →ₐ[W] Polynomial k₀ :=
  (EU t k₀ hq hker).toAlgHom.comp (Ideal.Quotient.mkₐ W (Ideal.span {U t}))

noncomputable def πV : MvPolynomial.CrossingQuotient W t →ₐ[W] Polynomial k₀ :=
  (EV t k₀ hq hker).toAlgHom.comp (Ideal.Quotient.mkₐ W (Ideal.span {V t}))

@[scoped simp] theorem πU_U : πU t k₀ hq hker (U t) = 0 := by
  simp [πU, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
@[scoped simp] theorem πU_V : πU t k₀ hq hker (V t) = Polynomial.X := by
  simp [πU, Ideal.Quotient.mkₐ_eq_mk, EU_mk_V]
@[scoped simp] theorem πV_V : πV t k₀ hq hker (V t) = 0 := by
  simp [πV, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
@[scoped simp] theorem πV_U : πV t k₀ hq hker (U t) = Polynomial.X := by
  simp [πV, Ideal.Quotient.mkₐ_eq_mk, EV_mk_U]

theorem πU_algebraMap (w : W) : πU t k₀ hq hker (algebraMap W _ w) = algebraMap W _ w := AlgHom.commutes _ w
theorem πV_algebraMap (w : W) : πV t k₀ hq hker (algebraMap W _ w) = algebraMap W _ w := AlgHom.commutes _ w

noncomputable def ψ : OverlapRing t →+* Localization.Away (Polynomial.X : Polynomial k₀) :=
  Localization.awayLift ((algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀))).comp
    (πU t k₀ hq hker).toRingHom) (V t) (by
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, πU_V]
      exact IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k₀))

theorem ψ_algebraMap (c : MvPolynomial.CrossingQuotient W t) :
    ψ t k₀ hq hker (algebraMap _ (OverlapRing t) c) =
      algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)) (πU t k₀ hq hker c) := by
  rw [ψ, Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  rfl

theorem ψ_comp_transitionUp :
    (ψ t k₀ hq hker).comp (transitionUp t).toRingHom =
      (Polynomial.aeval (R := k₀) (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀))
        (Polynomial.X : Polynomial k₀))).toRingHom.comp (πV t k₀ hq hker).toRingHom := by
  apply ringHom_ext_chart' t
  · intro w
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply W (MvPolynomial.CrossingQuotient W t) (OverlapRing t), ψ_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply W k₀ (Polynomial k₀), Polynomial.algebraMap_apply, Polynomial.aeval_C,
      IsScalarTower.algebraMap_apply k₀ (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)),
      Polynomial.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [transitionUp_U, πV_U, Polynomial.aeval_X]

    have h1 : ψ t k₀ hq hker (algebraMap _ (OverlapRing t) (V t)) * ψ t k₀ hq hker (IsLocalization.Away.invSelf (V t)) = 1 := by
      rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    rw [ψ_algebraMap, πU_V] at h1
    have h2 : algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)) Polynomial.X *
        IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀) = 1 :=
      IsLocalization.Away.mul_invSelf _

    calc ψ t k₀ hq hker (IsLocalization.Away.invSelf (V t))
        = ψ t k₀ hq hker (IsLocalization.Away.invSelf (V t)) * (algebraMap (Polynomial k₀) _ Polynomial.X *
            IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀)) := by
          rw [h2, mul_one]
      _ = IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀) := by
          rw [← mul_assoc, mul_comm (ψ t k₀ hq hker _), h1, one_mul]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [transitionUp_V, map_mul, ψ_algebraMap, πU_V, πV_V, map_zero,
      IsScalarTower.algebraMap_apply W (MvPolynomial.CrossingQuotient W t) (OverlapRing t), ψ_algebraMap, πU_algebraMap,
      IsScalarTower.algebraMap_apply W k₀ (Polynomial k₀), algebraMap_k₀_t t k₀ hq hker, map_zero, map_zero, zero_mul]

end RingLevel

section ChartLift
open MvPolynomial.CrossingQuotient
variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

noncomputable def mkQ (g : MvPolynomial.CrossingQuotient W t) :
    MvPolynomial.CrossingQuotient W t →+* MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g} :=
  Ideal.Quotient.mk (Ideal.span {g})

theorem mkQ_surjective (g : MvPolynomial.CrossingQuotient W t) : Function.Surjective (mkQ t g) :=
  Ideal.Quotient.mk_surjective

theorem ker_mkQ (g : MvPolynomial.CrossingQuotient W t) : RingHom.ker (mkQ t g) = Ideal.span {g} :=
  Ideal.mk_ker

theorem ker_specMap_quotient_mk (g : MvPolynomial.CrossingQuotient W t) :
    (Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g))).ker =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (Ideal.span {g})) := by
  rw [Scheme.ker_of_isAffine]
  congr 1

  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g))

  have happ : (Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom ≫
        CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}))).inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [happ]
  ext x
  simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  constructor
  · intro hx
    have hx' : mkQ t g ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x) = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}))).hom.hom hx
      simpa using this
    have hx'' : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x ∈ Ideal.span {g} := by
      rw [← ker_mkQ t g]; exact hx'
    have : x = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x) := by
      simp
    rw [this]
    exact Ideal.mem_map_of_mem _ hx''
  · intro hx

    have hx' : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x ∈ Ideal.span {g} := by
      have hsub : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom (Ideal.span {g}) ≤
          (Ideal.span {g}).comap (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        simp only [Ideal.mem_comap]
        simpa using hy
      exact hsub hx
    have hx'' : mkQ t g ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x) = 0 := by
      have h3 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).hom.hom x ∈ RingHom.ker (mkQ t g) := by
        rw [ker_mkQ]; exact hx'
      exact h3
    rw [hx'', map_zero]

theorem exists_lift_chart (F : Fin (e + 1) → (Resolution t e).IdealSheafData) (k : Fin (e + 1)) (a : Fin e)
    (g : MvPolynomial.CrossingQuotient W t)
    (hJ : (F k).comap (Resolution.ι t e a) = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom (Ideal.span {g}))) :
    ∃ lam : Spec (CommRingCat.of (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g})) ⟶ (F k).subscheme,
      IsOpenImmersion lam ∧
      lam ≫ (F k).subschemeι = Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g)) ≫ Resolution.ι t e a ∧
      IsPullback (Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g))) lam (Resolution.ι t e a) (F k).subschemeι := by
  set q := Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t) (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {g}) (mkQ t g)) with hq
  haveI : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ (mkQ_surjective t g)
  have hker_q : q.ker = (F k).comap (Resolution.ι t e a) := by rw [hq, ker_specMap_quotient_mk, hJ]
  have H : (F k).subschemeι.ker ≤ (q ≫ Resolution.ι t e a).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.le_map_iff_comap_le,
      hker_q]
  refine ⟨IsClosedImmersion.lift (F k).subschemeι (q ≫ Resolution.ι t e a) H, ?_, IsClosedImmersion.lift_fac _ _ _, ?_⟩
  · have hpb : IsPullback q (IsClosedImmersion.lift (F k).subschemeι (q ≫ Resolution.ι t e a) H) (Resolution.ι t e a)
        (F k).subschemeι :=
      isPullback_of_isClosedImmersion q _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm
        (by rw [Scheme.IdealSheafData.ker_subschemeι, hker_q])
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
  · exact isPullback_of_isClosedImmersion q _ _ _ (IsClosedImmersion.lift_fac _ _ _).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hker_q])

end ChartLift

section LemmaZ
open MvPolynomial.CrossingQuotient

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

theorem le_of_forall_comap_ι {I J : (Resolution t e).IdealSheafData}
    (h : ∀ a : Fin e, I.comap (Resolution.ι t e a) ≤ J.comap (Resolution.ι t e a)) : I ≤ J := by
  apply Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun a : Fin e => (⟨(Resolution.ι t e a).opensRange, isAffineOpen_opensRange (Resolution.ι t e a)⟩ :
      (Resolution t e).affineOpens))
  · exact Resolution.iSup_opensRange_ι t e
  · intro a
    have hI := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I (Resolution.ι t e a) ⟨⊤, isAffineOpen_top _⟩
    have hJ := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (Resolution.ι t e a) ⟨⊤, isAffineOpen_top _⟩
    have hle : (I.comap (Resolution.ι t e a)).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
        (J.comap (Resolution.ι t e a)).ideal ⟨⊤, isAffineOpen_top _⟩ := Scheme.IdealSheafData.ideal_mono (h a) _
    rw [hI, hJ] at hle
    have hV : (⟨(Resolution.ι t e a) ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (Resolution.ι t e a)⟩ :
        (Resolution t e).affineOpens) = ⟨(Resolution.ι t e a).opensRange, isAffineOpen_opensRange (Resolution.ι t e a)⟩ :=
      Subtype.ext (Scheme.Hom.image_top_eq_opensRange _)
    rw [← hV]
    intro s hs
    have h1 : ((Resolution.ι t e a).appIso ⊤).inv.hom (((Resolution.ι t e a).appIso ⊤).hom.hom s) = s := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
    have h2 : ((Resolution.ι t e a).appIso ⊤).hom.hom s ∈
        Ideal.comap ((Resolution.ι t e a).appIso ⊤).inv.hom (I.ideal ⟨(Resolution.ι t e a) ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion (Resolution.ι t e a)⟩) := by
      rw [Ideal.mem_comap, h1]; exact hs
    have h3 := hle h2
    rw [Ideal.mem_comap, h1] at h3
    exact h3

theorem ideal_top_ker_specMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (Spec.map (CommRingCat.ofHom φ)).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (RingHom.ker φ) := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal]
  have hid : (Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤) = 𝟙 _ from Subsingleton.elim _ _, op_id,
      CategoryTheory.Functor.map_id]
  rw [hid]
  change Ideal.map (RingHom.id _) _ = _
  rw [Ideal.map_id]

  have happ : (Spec.map (CommRingCat.ofHom φ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ), Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [happ]
  ext x
  simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  constructor
  · intro hx
    have hx' : φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom hx
      simpa using this
    have : x = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := by simp
    rw [this]
    exact Ideal.mem_map_of_mem _ hx'
  · intro hx
    have hx' : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x ∈ RingHom.ker φ := by
      have hsub : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (RingHom.ker φ) ≤
          (RingHom.ker φ).comap (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        simp only [Ideal.mem_comap]
        simpa using hy
      exact hsub hx
    rw [(RingHom.mem_ker).mp hx', map_zero]

theorem exists_lift_toSpec' (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t}) :
    ∃ z : (F ⟨d, by omega⟩).subscheme ⟶ Spec (CommRingCat.of k₀),
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) =
        (F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e := by
  classical
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap W k₀))) := IsClosedImmersion.spec_of_surjective _ hq
  have H : (Spec.map (CommRingCat.ofHom (algebraMap W k₀))).ker ≤
      ((F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e).ker := by
    rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.le_map_iff_comap_le]
    apply le_of_forall_comap_ι
    intro a
    rw [← Scheme.IdealSheafData.comap_comp, MvPolynomial.CrossingQuotient.Resolution.ι_toSpec, hF a,
      ← Scheme.IdealSheafData.le_map_iff_comap_le]
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [ideal_top_ker_specMap, Scheme.IdealSheafData.ideal_map_of_isAffineHom, Scheme.IdealSheafData.ofIdealTop_ideal,
      Ideal.map_le_iff_le_comap, hker]

    have hid : (Spec (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).presheaf.map
        (homOfLE (le_top : Spec.map (CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of W)).Opens) ≤ ⊤)).op = 𝟙 _ := by
      have : (homOfLE (le_top : Spec.map (CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t))) ⁻¹ᵁ
          (⊤ : (Spec (CommRingCat.of W)).Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
      rw [this]
      exact (Spec (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).presheaf.map_id _
    have hρ : ∀ I : Ideal Γ(Spec (CommRingCat.of (MvPolynomial.CrossingQuotient W t)), ⊤),
        Ideal.map ((Spec (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).presheaf.map
          (homOfLE (le_top : Spec.map (CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t))) ⁻¹ᵁ
            (⊤ : (Spec (CommRingCat.of W)).Opens) ≤ ⊤)).op).hom I = I := by
      intro I; rw [hid]; exact Ideal.map_id I
    rw [hρ]
    intro w hw
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change (Spec.map (CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t)))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom w) ∈ _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    apply Ideal.mem_map_of_mem

    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    change algebraMap W (MvPolynomial.CrossingQuotient W t) (c * t) ∈ _
    rw [map_mul, ← U_mul_V]
    split_ifs with h1 h2
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · exact Submodule.mem_top
  exact ⟨IsClosedImmersion.lift _ _ H, IsClosedImmersion.lift_fac _ _ H⟩

end LemmaZ

section LemmaCovMeet
open MvPolynomial.CrossingQuotient

variable {W : Type u} [CommRing W] (t : W) (e : ℕ)

theorem subschemeι_mem_range_ι' (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e) (x : ↥((F ⟨d, by omega⟩).subscheme)) :
    (F ⟨d, by omega⟩).subschemeι.base x ∈
      Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base ∪
        Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩).base := by
  obtain ⟨a, y, hy⟩ := Resolution.exists_ι_apply_eq t e ((F ⟨d, by omega⟩).subschemeι.base x)

  have hsupp : (F ⟨d, by omega⟩).subschemeι.base x ∈ ((F ⟨d, by omega⟩).support : Set _) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩

  have hy' : y ∈ ((F ⟨d, by omega⟩).comap (Resolution.ι t e a)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change (Resolution.ι t e a).base y ∈ ((F ⟨d, by omega⟩).support : Set _)
    rw [hy]; exact hsupp
  rw [hF a] at hy'
  by_cases h1 : (d : ℕ) = (a : ℕ)
  · right
    have ha : a = ⟨d, hde⟩ := Fin.ext h1.symm
    rw [ha] at hy
    exact ⟨y, hy⟩
  · by_cases h2 : (d : ℕ) = (a : ℕ) + 1
    · left
      have ha : a = ⟨d - 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [ha] at hy
      exact ⟨y, hy⟩
    · exfalso
      have hif : (if ((⟨d, by omega⟩ : Fin (e + 1)) : ℕ) = (a : ℕ) then Ideal.span {V t}
          else if ((⟨d, by omega⟩ : Fin (e + 1)) : ℕ) = (a : ℕ) + 1 then Ideal.span {U t} else (⊤ : Ideal (MvPolynomial.CrossingQuotient W t))) = ⊤ := by
        rw [if_neg h1, if_neg h2]
      rw [hif, Ideal.map_top] at hy'
      have htop : Scheme.IdealSheafData.ofIdealTop (⊤ : Ideal Γ(chartScheme t, ⊤)) = ⊤ :=
        Scheme.IdealSheafData.ext_of_isAffine (by simp)
      rw [htop, Scheme.IdealSheafData.support_top] at hy'
      exact hy'

theorem V_notMem_of_ι_apply_mem_range_succ' (i : Fin e) (hi : (i : ℕ) + 1 < e)
    (P : ↥(MvPolynomial.CrossingQuotient.chartScheme t))
    (h : (MvPolynomial.CrossingQuotient.Resolution.ι t e i).base P ∈
      Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨(i : ℕ) + 1, hi⟩).base) :
    MvPolynomial.CrossingQuotient.V t ∉ P.asIdeal := by
  classical
  obtain ⟨y, hy⟩ := h
  obtain ⟨a, ha, hb, z, hz1, hz2⟩ := (Resolution.ι_apply_eq_iff t e P y).mp hy.symm
  intro hV
  cases a with
  | chart k =>
    have h1 : k = i := (GlueIndex.chart_le_chart _ _).mp ha
    have h2 : k = ⟨(i : ℕ) + 1, hi⟩ := (GlueIndex.chart_le_chart _ _).mp hb
    have := congrArg Fin.val (h1.symm.trans h2)
    simp at this
  | overlap k hk =>
    have h1 := (GlueIndex.overlap_le_chart _ _ _).mp ha
    have h2 := (GlueIndex.overlap_le_chart _ _ _).mp hb
    by_cases hik : (i : ℕ) = (k : ℕ)
    · rw [glueMap_overlap_chart_of_eq t e hk ha hik] at hz1
      have hP : P ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial.CrossingQuotient W t) (OverlapRing t))) :=
        ⟨z, hz1⟩
      rw [PrimeSpectrum.localization_away_comap_range (OverlapRing t) (V t)] at hP
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hP hV
    · exfalso
      rcases h1 with h1 | h1
      · exact hik (congrArg Fin.val h1)
      · rcases h2 with h2 | h2
        · have := congrArg Fin.val h2; simp at this; omega
        · simp at h2; omega
  | torus h0 =>
    rw [glueMap_torus_chart] at hz1
    have hmem : torusChart t (i : ℕ) (V t) ∈ z.asIdeal := by
      have : P.asIdeal = Ideal.comap (torusChart t (i : ℕ)).toRingHom z.asIdeal := by rw [← hz1]; rfl
      rw [this, Ideal.mem_comap] at hV; exact hV
    have hunit : IsUnit (torusChart t (i : ℕ) (V t)) := by
      rw [torusChart_V]
      have hy : IsUnit (yT t) := isUnit_of_mul_isUnit_right (by rw [xT_mul_yT]; exact isUnit_tT t)
      exact hy.mul ((isUnit_tT t).pow _)
    exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

end LemmaCovMeet

section Ws37

theorem exists_lift_toSpec {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t}) :
    ∃ z : (F ⟨d, by omega⟩).subscheme ⟶ Spec (CommRingCat.of k₀),
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) =
        (F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e :=
  exists_lift_toSpec' t e F hF d hd0 hde k₀ hq hker

theorem subschemeι_mem_range_ι {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e) (x : ↥((F ⟨d, by omega⟩).subscheme)) :
    (F ⟨d, by omega⟩).subschemeι.base x ∈
      Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base ∪
        Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩).base :=
  subschemeι_mem_range_ι' t e F hF d hd0 hde x

theorem V_notMem_of_ι_apply_mem_range_succ {W : Type u} [CommRing W] (t : W) (e : ℕ) (i : Fin e) (hi : (i : ℕ) + 1 < e)
    (P : ↥(MvPolynomial.CrossingQuotient.chartScheme t))
    (h : (MvPolynomial.CrossingQuotient.Resolution.ι t e i).base P ∈
      Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨(i : ℕ) + 1, hi⟩).base) :
    MvPolynomial.CrossingQuotient.V t ∉ P.asIdeal :=
  V_notMem_of_ι_apply_mem_range_succ' t e i hi P h

end Ws37

end ExcE85
p2m_reactivate "P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable.ExcE85"

open ExcE85 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t}) :
    ∃ (z : (F ⟨d, by omega⟩).subscheme ⟶ Spec (CommRingCat.of k₀))
      (i₀ i₁ : Spec (CommRingCat.of (Polynomial k₀)) ⟶ (F ⟨d, by omega⟩).subscheme),
      IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) = (F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e ∧
      i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k₀)
          (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀))).toRingHom) ≫ i₁ ∧
      Set.range i₀.base ∩ Set.range i₁.base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀).base ∧
      Set.range (i₀ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base ∧
      Set.range (i₁ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩).base := by
  classical

  have hd1 : d - 1 + 1 = d := by omega

  have hJ₀ : (F ⟨d, by omega⟩).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (Ideal.span {MvPolynomial.CrossingQuotient.U t})) := by
    rw [hF ⟨d - 1, by omega⟩ ⟨d, by omega⟩]
    have h1 : ¬ ((d : ℕ) = d - 1) := by omega
    simp only [h1, if_false, hd1, if_true]
  have hJ₁ : (F ⟨d, by omega⟩).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (Ideal.span {MvPolynomial.CrossingQuotient.V t})) := by
    rw [hF ⟨d, hde⟩ ⟨d, by omega⟩]
    simp only [if_true]

  obtain ⟨lam₀, hlam₀, hfac₀, hpb₀⟩ := exists_lift_chart t e F ⟨d, by omega⟩ ⟨d - 1, by omega⟩ (MvPolynomial.CrossingQuotient.U t) hJ₀
  obtain ⟨lam₁, hlam₁, hfac₁, hpb₁⟩ := exists_lift_chart t e F ⟨d, by omega⟩ ⟨d, hde⟩ (MvPolynomial.CrossingQuotient.V t) hJ₁

  obtain ⟨z, hz⟩ := exists_lift_toSpec t e F hF d hd0 hde k₀ hq hker

  let eU : CommRingCat.of (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) ≅
      CommRingCat.of (Polynomial k₀) := (EU t k₀ hq hker).toRingEquiv.toCommRingCatIso
  let eV : CommRingCat.of (MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) ≅
      CommRingCat.of (Polynomial k₀) := (EV t k₀ hq hker).toRingEquiv.toCommRingCatIso
  set i₀ : Spec (CommRingCat.of (Polynomial k₀)) ⟶ (F ⟨d, by omega⟩).subscheme := Spec.map eU.hom ≫ lam₀ with hi₀def
  set i₁ : Spec (CommRingCat.of (Polynomial k₀)) ⟶ (F ⟨d, by omega⟩).subscheme := Spec.map eV.hom ≫ lam₁ with hi₁def
  haveI : IsOpenImmersion lam₀ := hlam₀
  haveI : IsOpenImmersion lam₁ := hlam₁
  have hI₀ : IsOpenImmersion i₀ := by rw [hi₀def]; infer_instance
  have hI₁ : IsOpenImmersion i₁ := by rw [hi₁def]; infer_instance

  have hqU : lam₀ ≫ (F ⟨d, by omega⟩).subschemeι =
      Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) (mkQ t (MvPolynomial.CrossingQuotient.U t))) ≫
        MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩ := hfac₀
  have hqV : lam₁ ≫ (F ⟨d, by omega⟩).subschemeι =
      Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) (mkQ t (MvPolynomial.CrossingQuotient.V t))) ≫
        MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩ := hfac₁
  haveI hmonoW : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap W k₀))) :=
    IsClosedImmersion.spec_of_surjective _ hq

  have hringU : CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t)) ≫
      CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) (mkQ t (MvPolynomial.CrossingQuotient.U t)) ≫ eU.hom =
      CommRingCat.ofHom (algebraMap W k₀) ≫ CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)) := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro w
    change EU t k₀ hq hker (Ideal.Quotient.mk _ (algebraMap W (MvPolynomial.CrossingQuotient W t) w)) = algebraMap k₀ (Polynomial k₀) (algebraMap W k₀ w)
    rw [Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes, IsScalarTower.algebraMap_apply W k₀ (Polynomial k₀)]
  have hringV : CommRingCat.ofHom (algebraMap W (MvPolynomial.CrossingQuotient W t)) ≫
      CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) (mkQ t (MvPolynomial.CrossingQuotient.V t)) ≫ eV.hom =
      CommRingCat.ofHom (algebraMap W k₀) ≫ CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀)) := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro w
    change EV t k₀ hq hker (Ideal.Quotient.mk _ (algebraMap W (MvPolynomial.CrossingQuotient W t) w)) = algebraMap k₀ (Polynomial k₀) (algebraMap W k₀ w)
    rw [Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes, IsScalarTower.algebraMap_apply W k₀ (Polynomial k₀)]
  refine ⟨z, i₀, i₁, hI₀, hI₁, hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap W k₀))), Category.assoc, hz, hi₀def, Category.assoc,
      reassoc_of% hqU, MvPolynomial.CrossingQuotient.Resolution.ι_toSpec, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      Category.assoc, hringU]
  ·
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap W k₀))), Category.assoc, hz, hi₁def, Category.assoc,
      reassoc_of% hqV, MvPolynomial.CrossingQuotient.Resolution.ι_toSpec, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      Category.assoc, hringV]
  ·
    apply Set.eq_univ_of_forall
    intro x
    rcases subschemeι_mem_range_ι t e F hF d hd0 hde x with ⟨P, hP⟩ | ⟨P, hP⟩
    · left
      obtain ⟨y, -, hy⟩ := Scheme.Pullback.exists_preimage_pullback P x hP
      refine ⟨(Spec.map eU.inv).base (hpb₀.isoPullback.inv.base y), ?_⟩
      rw [hi₀def, ← Scheme.Hom.comp_apply, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp,
        ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hy]
    · right
      obtain ⟨y, -, hy⟩ := Scheme.Pullback.exists_preimage_pullback P x hP
      refine ⟨(Spec.map eV.inv).base (hpb₁.isoPullback.inv.base y), ?_⟩
      rw [hi₁def, ← Scheme.Hom.comp_apply, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp,
        ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hy]
  ·
    rw [← cancel_mono (F ⟨d, by omega⟩).subschemeι, hi₀def, hi₁def]
    simp only [Category.assoc]
    rw [hqU, hqV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]

    have hL : CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
          (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) (mkQ t (MvPolynomial.CrossingQuotient.U t)) ≫
          eU.hom ≫ CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀))) =
        CommRingCat.ofHom (algebraMap (MvPolynomial.CrossingQuotient W t) (MvPolynomial.CrossingQuotient.OverlapRing t)) ≫
          CommRingCat.ofHom (ψ t k₀ hq hker) := by
      apply CommRingCat.hom_ext; apply RingHom.ext; intro c
      change algebraMap (Polynomial k₀) _ (EU t k₀ hq hker (Ideal.Quotient.mk _ c)) = ψ t k₀ hq hker (algebraMap _ _ c)
      rw [ψ_algebraMap]; rfl
    have hR : CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
          (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) (mkQ t (MvPolynomial.CrossingQuotient.V t)) ≫
          eV.hom ≫ CommRingCat.ofHom (Polynomial.aeval (R := k₀)
            (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀))).toRingHom =
        CommRingCat.ofHom (MvPolynomial.CrossingQuotient.transitionUp t).toRingHom ≫ CommRingCat.ofHom (ψ t k₀ hq hker) := by
      apply CommRingCat.hom_ext; apply RingHom.ext; intro c
      have := congrArg (fun φ => φ c) (ψ_comp_transitionUp t k₀ hq hker)
      simp only [RingHom.comp_apply] at this
      change (Polynomial.aeval _).toRingHom (EV t k₀ hq hker (Ideal.Quotient.mk _ c)) = ψ t k₀ hq hker ((MvPolynomial.CrossingQuotient.transitionUp t).toRingHom c)
      rw [this]; rfl
    rw [hL, hR, Spec.map_comp_assoc, Spec.map_comp_assoc]
    have hglue := MvPolynomial.CrossingQuotient.Resolution.glue_condition t e ⟨d - 1, by omega⟩ (by simp only; omega)
    have hfin : (⟨((⟨d - 1, by omega⟩ : Fin e) : ℕ) + 1, by simp only; omega⟩ : Fin e) = ⟨d, hde⟩ := Fin.ext hd1
    rw [hfin] at hglue
    change Spec.map (CommRingCat.ofHom (ψ t k₀ hq hker)) ≫ MvPolynomial.CrossingQuotient.overlapToChartLeft t ≫ _ =
      Spec.map (CommRingCat.ofHom (ψ t k₀ hq hker)) ≫ MvPolynomial.CrossingQuotient.overlapToChartRight t ≫ _
    rw [hglue]
  ·
    rintro x ⟨⟨q₀, hq₀⟩, ⟨q₁, hq₁⟩⟩
    rw [hi₀def] at hq₀
    rw [hi₁def] at hq₁

    set P : ↥(MvPolynomial.CrossingQuotient.chartScheme t) :=
      (Spec.map eU.hom ≫ Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.U t}) (mkQ t (MvPolynomial.CrossingQuotient.U t)))).base q₀ with hPdef
    have hP : (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base P = (F ⟨d, by omega⟩).subschemeι.base x := by
      rw [hPdef, ← Scheme.Hom.comp_apply, Category.assoc, ← hqU, ← Category.assoc, Scheme.Hom.comp_apply]
      exact congrArg _ hq₀
    have hP' : (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base P ∈
        Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨((⟨d - 1, by omega⟩ : Fin e) : ℕ) + 1, by simp only; omega⟩).base := by
      have hfin : (⟨((⟨d - 1, by omega⟩ : Fin e) : ℕ) + 1, by simp only; omega⟩ : Fin e) = ⟨d, hde⟩ := Fin.ext hd1
      rw [hfin, hP]
      refine ⟨(Spec.map eV.hom ≫ Spec.map (CommRingCat.ofHom (R := MvPolynomial.CrossingQuotient W t)
        (S := MvPolynomial.CrossingQuotient W t ⧸ Ideal.span {MvPolynomial.CrossingQuotient.V t}) (mkQ t (MvPolynomial.CrossingQuotient.V t)))).base q₁, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hqV, ← Category.assoc, Scheme.Hom.comp_apply]
      exact congrArg _ hq₁
    have hV := V_notMem_of_ι_apply_mem_range_succ t e ⟨d - 1, by omega⟩ (by simp only; omega) P hP'

    have hX : (Polynomial.X : Polynomial k₀) ∉ q₀.asIdeal := by
      intro hXq
      apply hV
      rw [hPdef, ← Spec.map_comp]
      change MvPolynomial.CrossingQuotient.V t ∈ Ideal.comap _ q₀.asIdeal
      rw [Ideal.mem_comap]
      change EU t k₀ hq hker (Ideal.Quotient.mk _ (MvPolynomial.CrossingQuotient.V t)) ∈ q₀.asIdeal
      rw [EU_mk_V]; exact hXq
    have hq₀' : q₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀)]
      exact SetLike.mem_coe.mpr ((PrimeSpectrum.mem_basicOpen _ _).mpr hX)
    obtain ⟨q', hq'⟩ := hq₀'
    refine ⟨q', ?_⟩
    rw [hi₀def, Scheme.Hom.comp_apply]
    have hq'' : (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀))))) q' = q₀ := hq'
    rw [hq'']; exact hq₀
  ·
    rintro _ ⟨y, rfl⟩
    rw [hi₀def, Category.assoc, hqU, ← Category.assoc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  ·
    rintro _ ⟨y, rfl⟩
    rw [hi₁def, Category.assoc, hqV, ← Category.assoc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

end S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable (solution)
