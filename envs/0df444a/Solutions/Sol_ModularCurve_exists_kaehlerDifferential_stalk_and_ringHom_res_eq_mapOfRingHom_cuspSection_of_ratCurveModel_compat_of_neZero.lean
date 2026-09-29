-- Prove2me | solution 1 for ModularCurve.exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/df8151a2-45f5-5a75-988e-840d7317ceee

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing CuspForm AlgebraicGeometry.Scheme"

namespace GenFF

universe u

section K1
variable {Y X : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h] [IsIntegral Y] [IsIntegral X]

theorem base_genericPoint : h.base (genericPoint Y) = genericPoint X :=
  genericPoint_eq_of_isOpenImmersion h

noncomputable def ffIso : X.functionField ≅ Y.functionField :=
  X.presheaf.stalkCongr (Inseparable.of_eq (base_genericPoint h).symm) ≪≫
    asIso (h.stalkMap (genericPoint Y))

theorem genericPoint_mem_preimage (U : X.Opens) (hU : genericPoint X ∈ U) : genericPoint Y ∈ h ⁻¹ᵁ U := by
  show h.base (genericPoint Y) ∈ U
  rw [base_genericPoint]; exact hU

theorem germ_ffIso_hom (U : X.Opens) (hU : genericPoint X ∈ U) :
    X.presheaf.germ U (genericPoint X) hU ≫ (ffIso h).hom =
      h.app U ≫ Y.presheaf.germ (h ⁻¹ᵁ U) (genericPoint Y) (genericPoint_mem_preimage h U hU) := by
  simp only [ffIso, Iso.trans_hom, asIso_hom, TopCat.Presheaf.stalkCongr_hom]
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact Scheme.Hom.germ_stalkMap h U (genericPoint Y) _

theorem germ_ffIso_hom_top :
    X.presheaf.germ ⊤ (genericPoint X) trivial ≫ (ffIso h).hom =
      h.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) trivial :=
  germ_ffIso_hom h ⊤ trivial

theorem ffIso_germ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    (ffIso h).hom.hom ((X.presheaf.germ U (genericPoint X) hU).hom s) =
      (Y.presheaf.germ (h ⁻¹ᵁ U) (genericPoint Y) (genericPoint_mem_preimage h U hU)).hom ((h.app U).hom s) := by
  have := congrArg (fun φ => φ.hom s) (germ_ffIso_hom h U hU)
  simpa using this

end K1

section K2

theorem isOpenImmersion_specMap_rat (q : ℕ) [Fact q.Prime] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ))) := by
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  exact NeronModelInfra.isOpenImmersion_specGenericFibreInclusion ↥(GaloisRep.ratLocalizedAt q) ℚ
end K2

section Iota

variable (p : ℕ) (q : ℕ) [Fact q.Prime]
  {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))) [IsIntegral X]
  (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
  (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) [IsIso e₀]

noncomputable def hImm : M₀.C ⟶ X :=
  e₀ ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))

omit [IsIntegral X] in
theorem isOpenImmersion_hImm : IsOpenImmersion (hImm p q c M₀ e₀) := by
  haveI := isOpenImmersion_specMap_rat q
  unfold hImm
  infer_instance

noncomputable def iota0 (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(X, U) →+* ↥(modularFunctionFieldFull p) :=
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  M₀.ffEquiv.symm.toRingHom.comp
    ((ffIso (hImm p q c M₀ e₀)).hom.hom.comp (X.presheaf.germ U (genericPoint X) hU).hom)

theorem iota0_apply (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    haveI := isOpenImmersion_hImm p q c M₀ e₀
    iota0 p q c M₀ e₀ U hU s =
      M₀.ffEquiv.symm ((ffIso (hImm p q c M₀ e₀)).hom.hom ((X.presheaf.germ U (genericPoint X) hU).hom s)) := rfl

theorem iota0_apply' (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    haveI := isOpenImmersion_hImm p q c M₀ e₀
    iota0 p q c M₀ e₀ U hU s =
      M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((hImm p q c M₀ e₀) ⁻¹ᵁ U) (genericPoint M₀.C)
        (genericPoint_mem_preimage (hImm p q c M₀ e₀) U hU)).hom (((hImm p q c M₀ e₀).app U).hom s)) := by
  rw [iota0_apply, ffIso_germ]

theorem iota0_res {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) (hle : V ≤ U) (s : Γ(X, U)) :
    iota0 p q c M₀ e₀ V hV ((X.presheaf.map (homOfLE hle).op).hom s) = iota0 p q c M₀ e₀ U hU s := by
  simp only [iota0_apply]
  congr 2
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hle) (genericPoint X) hV s

theorem iota0_injective (U : X.Opens) (hU : genericPoint X ∈ U) : Function.Injective (iota0 p q c M₀ e₀ U hU) := by
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  intro a b hab
  simp only [iota0_apply, EquivLike.apply_eq_iff_eq] at hab
  have hinj : Function.Injective (ffIso (hImm p q c M₀ e₀)).hom.hom :=
    (ffIso (hImm p q c M₀ e₀)).commRingCatIsoToRingEquiv.injective
  exact germ_injective_of_isIntegral X (genericPoint X) hU (hinj hab)

noncomputable def iota (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(X, U) →+* ↥(modularFunctionFieldBar p) :=
  RingHom.codRestrict
    ((coeffEmb (AlgebraicClosure ℚ)).comp
      (((modularFunctionFieldFull p).val : ↥(modularFunctionFieldFull p) →+* LaurentSeries ℚ).comp
        (iota0 p q c M₀ e₀ U hU)))
    (modularFunctionFieldBar p)
    (fun s => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (iota0 p q c M₀ e₀ U hU s).2)

theorem coe_iota_apply (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(X, U)) :
    (iota p q c M₀ e₀ U hU s : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((iota0 p q c M₀ e₀ U hU s : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) :=
  rfl

theorem iota_injective (U : X.Opens) (hU : genericPoint X ∈ U) : Function.Injective (iota p q c M₀ e₀ U hU) := by
  intro a b hab
  have h1 := congrArg (fun z : ↥(modularFunctionFieldBar p) => (z : LaurentSeries (AlgebraicClosure ℚ))) hab
  simp only [coe_iota_apply] at h1
  exact iota0_injective p q c M₀ e₀ U hU (Subtype.ext ((coeffEmb (AlgebraicClosure ℚ)).injective h1))

theorem iota_rat (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U)) :
    ∃ x ∈ modularFunctionFieldFull p,
      coeffEmb (AlgebraicClosure ℚ) x = (iota p q c M₀ e₀ U hU a : LaurentSeries (AlgebraicClosure ℚ)) :=
  ⟨(iota0 p q c M₀ e₀ U hU a : LaurentSeries ℚ), (iota0 p q c M₀ e₀ U hU a).2, rfl⟩

theorem iota_frac (U : X.Opens) (hUaff : IsAffineOpen U) [Nonempty U] (hU : genericPoint X ∈ U)
    (x : LaurentSeries ℚ) (hx : x ∈ modularFunctionFieldFull p) :
    ∃ a b : Γ(X, U), iota p q c M₀ e₀ U hU b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (iota p q c M₀ e₀ U hU b : LaurentSeries (AlgebraicClosure ℚ)) =
        iota p q c M₀ e₀ U hU a := by
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  haveI := functionField_isFractionRing_of_isAffineOpen X U hUaff

  set z : X.functionField := (ffIso (hImm p q c M₀ e₀)).inv.hom (M₀.ffEquiv ⟨x, hx⟩) with hz
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) z

  refine ⟨a, b, ?_, ?_⟩
  · intro hb0
    have hb : (b : Γ(X, U)) ≠ 0 := nonZeroDivisors.ne_zero b.2
    exact hb ((iota_injective p q c M₀ e₀ U hU) (hb0.trans (map_zero _).symm))
  ·
    have hΦ : ∀ s : Γ(X, U), M₀.ffEquiv.symm ((ffIso (hImm p q c M₀ e₀)).hom.hom (algebraMap Γ(X, U) X.functionField s)) =
        iota0 p q c M₀ e₀ U hU s := fun s => rfl
    have hzΦ : M₀.ffEquiv.symm ((ffIso (hImm p q c M₀ e₀)).hom.hom z) = ⟨x, hx⟩ := by
      rw [hz, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, RingEquiv.symm_apply_apply]
    have key : (⟨x, hx⟩ : ↥(modularFunctionFieldFull p)) * iota0 p q c M₀ e₀ U hU b = iota0 p q c M₀ e₀ U hU a := by
      rw [← hzΦ, ← hΦ, ← hΦ, ← map_mul, ← map_mul, hab]
    have key' := congrArg (fun y : ↥(modularFunctionFieldFull p) => coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ)) key
    simpa only [coe_iota_apply, IntermediateField.coe_mul, map_mul] using key'

end Iota

section IotaR

variable (p : ℕ) (q : ℕ) [Fact q.Prime]
  {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))) [IsIntegral X]
  (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
  (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) [IsIso e₀]
  (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

omit [Fact q.Prime] [IsIntegral X] [IsIso e₀] in
include he₀ in
theorem hImm_comp : hImm p q c M₀ e₀ ≫ c =
    M₀.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)) := by
  unfold hImm
  rw [Category.assoc, pullback.condition, ← Category.assoc, he₀]

include he₀ in

theorem germ_ffIso_appLE (U : X.Opens) (hU : genericPoint X ∈ U) :
    haveI := isOpenImmersion_hImm p q c M₀ e₀
    (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))).inv ≫ c.appLE ⊤ U le_top ≫
        X.presheaf.germ U (genericPoint X) hU ≫ (ffIso (hImm p q c M₀ e₀)).hom =
      CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫
        M₀.toBase.appTop ≫ M₀.C.presheaf.germ ⊤ (genericPoint M₀.C) trivial := by
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  have h1 : c.appLE ⊤ U le_top ≫ X.presheaf.germ U (genericPoint X) hU =
      c.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  rw [reassoc_of% h1, germ_ffIso_hom_top (hImm p q c M₀ e₀)]
  have h2 : c.appTop ≫ (hImm p q c M₀ e₀).appTop = (hImm p q c M₀ e₀ ≫ c).appTop := rfl
  rw [reassoc_of% h2, hImm_comp p q c M₀ e₀ he₀, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]

include he₀ in
theorem iota0_algebraMap (U : X.Opens) (hU : genericPoint X ∈ U) (r : ↥(GaloisRep.ratLocalizedAt q)) :
    iota0 p q c M₀ e₀ U hU ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))).inv.hom r)) =
      algebraMap ℚ ↥(modularFunctionFieldFull p) (r : ℚ) := by
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  rw [iota0_apply, RingEquiv.symm_apply_eq, M₀.ffEquiv_algebraMap]
  have := congrArg (fun φ => φ.hom r) (germ_ffIso_appLE p q c M₀ e₀ he₀ U hU)
  exact this

include he₀ in

theorem iota_algebraMap (U : X.Opens) (hU : genericPoint X ∈ U) (r : ↥(GaloisRep.ratLocalizedAt q)) :
    iota p q c M₀ e₀ U hU ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))).inv.hom r)) =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)
        (algebraMap ↥(GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ) r) := by
  apply Subtype.ext
  rw [coe_iota_apply, iota0_algebraMap p q c M₀ e₀ he₀ U hU r]
  have e1 : ((algebraMap ℚ ↥(modularFunctionFieldFull p) (r : ℚ) : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) :=
    (eq_ratCast ((((modularFunctionFieldFull p).val : ↥(modularFunctionFieldFull p) →+* LaurentSeries ℚ)).comp
      (algebraMap ℚ ↥(modularFunctionFieldFull p))) (r : ℚ)).trans (eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) (r : ℚ)).symm
  have e2 : ∀ y : AlgebraicClosure ℚ, ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) y :
      ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) y := fun y => rfl
  rw [e1, e2, algebraMap_apply_eq_single, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]
  rfl

end IotaR

end GenFF

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0)

    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιdef : ∀ a : (𝒱.cover c).A0, ((ι a : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((M₀.ffEquiv.symm ((M₀.C.presheaf.germ ((e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) (genericPoint M₀.C) hgen0).hom (((e₀ ≫ pullback.fst c _).app (𝒱.U0)).hom a))) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) c)
    (x₀ : closedPoints M₀.C)
    (y : Spec (CommRingCat.of ℚ) ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
    (hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull N)
    (hy : y ≫ pullback.snd c _ = 𝟙 _)
    (hyε : y ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)) ≫ εinf.1)
    (hyx₀ : (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)

    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • Mη.pointEquivPlace x)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N),
        IsPlaceReductionModL A N r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) (hs : IsClosed ({s} : Set (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))))
    (hspec : (e₀ ≫ pullback.fst c _).base x₀.1 ⤳ εinf.1.base s)
    (ω : ↥((𝒱.kaehlerSections c).H0)) :
    letI : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).toAlgebra
    ∃ (ω_s : Ω[(X.presheaf.stalk (εinf.1.base s))⁄↥(GaloisRep.ratLocalizedAt p)]) (Exp : X.presheaf.stalk (εinf.1.base s) →+* ↥(modularFunctionFieldBar N))
      (hExpR : Exp.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s))) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))),

      (∀ z : X.presheaf.stalk (εinf.1.base s), ((Exp z : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField (((X.presheaf.stalkSpecializes hspec) ≫ Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom z)) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧

      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) Exp hExpR ω_s  := by
  classical
  haveI := GenFF.isOpenImmersion_hImm N p c M₀ e₀
  letI instRS : Algebra ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s)) := ((X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom.comp
        (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom)).toAlgebra

  let route : X.presheaf.stalk (εinf.1.base s) →+* M₀.C.presheaf.stalk x₀.1 :=
    ((X.presheaf.stalkSpecializes hspec) ≫ Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom
  let Exp0 : X.presheaf.stalk (εinf.1.base s) →+* ↥(modularFunctionFieldFull N) :=
    M₀.ffEquiv.symm.toRingHom.comp ((algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField).comp route)
  let Exp : X.presheaf.stalk (εinf.1.base s) →+* ↥(modularFunctionFieldBar N) :=
    RingHom.codRestrict
      ((coeffEmb (AlgebraicClosure ℚ)).comp
        (((modularFunctionFieldFull N).val : ↥(modularFunctionFieldFull N) →+* LaurentSeries ℚ).comp Exp0))
      (modularFunctionFieldBar N)
      (fun z => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (Exp0 z).2)
  have hExp_coe : ∀ z, ((Exp z : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((Exp0 z : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) := fun z => rfl

  have ha : ∀ z : X.presheaf.stalk (εinf.1.base s), ((Exp z : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((M₀.ffEquiv.symm (algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField (((X.presheaf.stalkSpecializes hspec) ≫ Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom z)) : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) := fun z => rfl

  have hgX : ∀ (U : X.Opens) (x : X), x ∈ U → genericPoint X ∈ U := fun U x hx =>
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

  have KEY : ∀ (U : X.Opens) (hU : εinf.1.base s ∈ U),
      Exp.comp (X.presheaf.germ U (εinf.1.base s) hU).hom = GenFF.iota N p c M₀ e₀ U (hgX U _ hU) := by
    intro U hU
    refine RingHom.ext fun a => Subtype.ext ?_
    rw [RingHom.comp_apply, hExp_coe, GenFF.coe_iota_apply, GenFF.iota0_apply']
    congr 2

    show M₀.ffEquiv.symm ((algebraMap (M₀.C.presheaf.stalk x₀.1) M₀.C.functionField)
      ((Scheme.Hom.stalkMap (e₀ ≫ pullback.fst c _) x₀.1).hom
        ((X.presheaf.stalkSpecializes hspec).hom ((X.presheaf.germ U (εinf.1.base s) hU).hom a)))) = _
    congr 1
    have hx₀U : (e₀ ≫ pullback.fst c _).base x₀.1 ∈ U := hspec.mem_open U.2 hU
    have s1 : (X.presheaf.stalkSpecializes hspec).hom ((X.presheaf.germ U (εinf.1.base s) hU).hom a) =
        (X.presheaf.germ U ((e₀ ≫ pullback.fst c _).base x₀.1) hx₀U).hom a := by
      rw [← CategoryTheory.ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [s1, Scheme.Hom.germ_stalkMap_apply, RingHom.algebraMap_toAlgebra, ← CategoryTheory.ConcreteCategory.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
    rfl

  have happ : c.appLE ⊤ ⊤ le_top = c.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  have hExpR : Exp.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s))) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
      ← RingHom.comp_apply Exp, KEY ⊤ trivial, ← happ]
    exact GenFF.iota_algebraMap N p c M₀ e₀ he₀ ⊤ _ r

  have hU0 : genericPoint X ∈ 𝒱.U0 := by
    have h := hgen0
    change (GenFF.hImm N p c M₀ e₀).base (genericPoint M₀.C) ∈ 𝒱.U0 at h
    rwa [GenFF.base_genericPoint] at h
  have hιι : ι = (GenFF.iota N p c M₀ e₀ 𝒱.U0 hU0) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    rw [hιdef a]
    exact (congrArg (coeffEmb (AlgebraicClosure ℚ)) (congrArg Subtype.val (GenFF.iota0_apply' N p c M₀ e₀ _ hU0 a))).symm

  have hgerm_aux : ∀ (U : X.Opens) (hU : εinf.1.base s ∈ U) (r : ↥(GaloisRep.ratLocalizedAt p)),
      (X.presheaf.germ U (εinf.1.base s) hU).hom ((c.appLE ⊤ U le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r)) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s))) r := by
    intro U hU r
    rw [RingHom.algebraMap_toAlgebra]
    show (c.appLE ⊤ U le_top ≫ X.presheaf.germ U (εinf.1.base s) hU).hom _ =
      (X.presheaf.germ ⊤ (εinf.1.base s) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))).inv.hom r))
    have h1 : c.appLE ⊤ U le_top ≫ X.presheaf.germ U (εinf.1.base s) hU =
        c.appTop ≫ X.presheaf.germ ⊤ (εinf.1.base s) trivial := by
      simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
      rfl
    rw [h1]
    rfl

  have hcov : εinf.1.base s ∈ 𝒱.U0 ⊔ 𝒱.U1 := by rw [𝒱.sup_eq_top]; trivial
  rcases (TopologicalSpace.Opens.mem_sup.mp hcov) with h0 | h1
  ·
    let g0 : ((𝒱.cover c).A0) →+* X.presheaf.stalk (εinf.1.base s) := (X.presheaf.germ 𝒱.U0 (εinf.1.base s) h0).hom
    have hgermR0 : g0.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0)) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s))).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) :=
      RingHom.ext fun r => hgerm_aux 𝒱.U0 h0 r
    have KEY0 : Exp.comp g0 = ι := (KEY 𝒱.U0 h0).trans hιι.symm
    refine ⟨KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) g0 hgermR0 ω.val.1, Exp, hExpR, ha, ?_⟩
    have h₃ : ((Exp.comp g0).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0))) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp
          ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [RingHom.comp_assoc, hgermR0, ← RingHom.comp_assoc, hExpR, RingHom.comp_assoc]
    rw [KaehlerDifferential.mapOfRingHom_comp_apply (h₃ := h₃), hres]
    exact (KaehlerDifferential.mapOfRingHom_congr KEY0 h₃ hιR ω.val.1).symm
  ·
    have hU1 : genericPoint X ∈ 𝒱.U1 := hgX 𝒱.U1 _ h1
    have hU01 : genericPoint X ∈ 𝒱.U0 ⊓ 𝒱.U1 := by

      obtain ⟨z, hz0, hz1⟩ := nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen ⟨_, hU0⟩ ⟨_, h1⟩
      exact hgX (𝒱.U0 ⊓ 𝒱.U1) z ⟨hz0, hz1⟩
    let i01 : ((𝒱.cover c).A01) →+* ↥(modularFunctionFieldBar N) := (GenFF.iota N p c M₀ e₀ (𝒱.U0 ⊓ 𝒱.U1) hU01)
    let i1 : ((𝒱.cover c).A1) →+* ↥(modularFunctionFieldBar N) := (GenFF.iota N p c M₀ e₀ 𝒱.U1 hU1)
    let i0 : ((𝒱.cover c).A0) →+* ↥(modularFunctionFieldBar N) := (GenFF.iota N p c M₀ e₀ 𝒱.U0 hU0)
    let g1 : ((𝒱.cover c).A1) →+* X.presheaf.stalk (εinf.1.base s) := (X.presheaf.germ 𝒱.U1 (εinf.1.base s) h1).hom
    have hgermR1 : g1.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A1)) = (algebraMap ↥(GaloisRep.ratLocalizedAt p) (X.presheaf.stalk (εinf.1.base s))).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) :=
      RingHom.ext fun r => hgerm_aux 𝒱.U1 h1 r
    have KEY1 : Exp.comp g1 = i1 := KEY 𝒱.U1 h1
    refine ⟨KaehlerDifferential.mapOfRingHom (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) g1 hgermR1 ω.val.2, Exp, hExpR, ha, ?_⟩
    have h₃ : ((Exp.comp g1).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A1))) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp
          ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      rw [RingHom.comp_assoc, hgermR1, ← RingHom.comp_assoc, hExpR, RingHom.comp_assoc]
    have hi1R' : i1.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A1)) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp
          ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by rw [← KEY1]; exact h₃
    rw [KaehlerDifferential.mapOfRingHom_comp_apply (h₃ := h₃), hres,
      KaehlerDifferential.mapOfRingHom_congr KEY1 h₃ hi1R' ω.val.2]

    have hres0 : i01.comp (𝒱.cover c).ρ0.toRingHom = (GenFF.iota N p c M₀ e₀ 𝒱.U0 hU0) :=
      RingHom.ext fun a => Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (congrArg Subtype.val
        (GenFF.iota0_res N p c M₀ e₀ hU0 hU01 inf_le_left a)))
    have hres1 : i01.comp (𝒱.cover c).ρ1.toRingHom = i1 :=
      RingHom.ext fun a => Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (congrArg Subtype.val
        (GenFF.iota0_res N p c M₀ e₀ hU1 hU01 inf_le_right a)))
    have hi01R : i01.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A01)) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :=
      RingHom.ext fun r => GenFF.iota_algebraMap N p c M₀ e₀ he₀ (𝒱.U0 ⊓ 𝒱.U1) hU01 r
    have hi1R : i1.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A1)) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :=
      RingHom.ext fun r => GenFF.iota_algebraMap N p c M₀ e₀ he₀ 𝒱.U1 hU1 r

    have hcoc : (𝒱.kaehlerSections c).r0 ω.val.1 = (𝒱.kaehlerSections c).r1 ω.val.2 := by
      have hk := LinearMap.mem_ker.mp ω.2
      rw [TwoChartCech.Sections.cechDiff_apply, sub_eq_zero] at hk
      exact hk.symm
    have h3a : ((i01.comp (𝒱.cover c).ρ0.toRingHom).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A0))) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      refine RingHom.ext fun r => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
      exact GenFF.iota_algebraMap N p c M₀ e₀ he₀ (𝒱.U0 ⊓ 𝒱.U1) hU01 r
    have h3b : ((i01.comp (𝒱.cover c).ρ1.toRingHom).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ((𝒱.cover c).A1))) =
        (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) := by
      refine RingHom.ext fun r => ?_
      simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
      exact GenFF.iota_algebraMap N p c M₀ e₀ he₀ (𝒱.U0 ⊓ 𝒱.U1) hU01 r
    calc KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1
        = KaehlerDifferential.mapOfRingHom ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))
            (i01.comp (𝒱.cover c).ρ0.toRingHom) h3a ω.val.1 :=
          KaehlerDifferential.mapOfRingHom_congr (hιι.trans hres0.symm) hιR h3a ω.val.1
      _ = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) i01 hi01R
            ((𝒱.kaehlerSections c).r0 ω.val.1) :=
          (KaehlerDifferential.mapOfRingHom_comp_apply (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (𝒱.cover c).ρ0.toRingHom
            (𝒱.cover c).ρ0_comp_algebraMap_eq_comp_id (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) i01 hi01R h3a ω.val.1).symm
      _ = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) i01 hi01R
            ((𝒱.kaehlerSections c).r1 ω.val.2) := by rw [hcoc]
      _ = KaehlerDifferential.mapOfRingHom ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p)))
            (i01.comp (𝒱.cover c).ρ1.toRingHom) h3b ω.val.2 :=
          KaehlerDifferential.mapOfRingHom_comp_apply (RingHom.id ↥(GaloisRep.ratLocalizedAt p)) (𝒱.cover c).ρ1.toRingHom
            (𝒱.cover c).ρ1_comp_algebraMap_eq_comp_id (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) i01 hi01R h3b ω.val.2
      _ = KaehlerDifferential.mapOfRingHom ((algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)).comp (RingHom.id ↥(GaloisRep.ratLocalizedAt p))) i1 hi1R' ω.val.2 :=
          KaehlerDifferential.mapOfRingHom_congr hres1 h3b hi1R' ω.val.2

end S_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero
end P2MW
export P2MW.S_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero (solution)
