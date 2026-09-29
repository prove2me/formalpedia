-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d714a1c0-15c2-5945-89e0-ad463dd07bfe

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme AlgebraicCurve.CurveModel

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace SPISO

structure GlueDatum (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (K : Type) [Field K]
    [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] {L : Type} [Field L] [Algebra K L] (t : L) where
  θFin : ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K →+* ↥(chartRing K ({t} : Set L))
  θInf : ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K →+* ↥(chartRing K ({t⁻¹} : Set L))
  ρMid : ↥(chartAlgMid N ℓ) →+* ↥(chartRing K ({t, t⁻¹} : Set L))
  θFin_right : θFin.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)) =
    algebraMap K ↥(chartRing K ({t} : Set L))
  θInf_right : θInf.comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L))
  sq_fin : (incl₀ K t).toRingHom.comp (θFin.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom
  sq_inf : (inclInf K t).toRingHom.comp (θInf.comp Algebra.TensorProduct.includeLeftRingHom) =
    ρMid.comp (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom
  ρInf_jInv : (θInf.comp Algebra.TensorProduct.includeLeftRingHom) (jInvChartInf N ℓ) = tInvChart K t
  bijFin : Function.Bijective θFin
  bijInf : Function.Bijective θInf

abbrev baseMap (ℓ : ℕ) (K : Type) [Field K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K))

section Igusa

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem ig_ιFin_eq_ιInf_iff (x₀ : ModularCurve.IgusaScheme.XFin N ℓ) (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ↔
      ∃ w : ModularCurve.IgusaScheme.XMid N ℓ,
        (ModularCurve.IgusaScheme.fFin N ℓ).base w = x₀ ∧ (ModularCurve.IgusaScheme.fInf N ℓ).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (ModularCurve.IgusaScheme.fFin N ℓ) (ModularCurve.IgusaScheme.fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base w =
      (ModularCurve.IgusaScheme.fInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base w
    rw [ModularCurve.IgusaScheme.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ig_range_fInf : Set.range (ModularCurve.IgusaScheme.fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf N ℓ))) : Set (PrimeSpectrum ↥(chartAlgInf N ℓ))) := by
  letI := (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid N ℓ) (jInvChartInf N ℓ)

private theorem ig_ιInf_mem_range_ιFin_iff (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔
      jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(ModularCurve.IgusaScheme.fFin N ℓ).base w, (ig_ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨w, rfl, rfl⟩⟩

end Igusa

section Schemes

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K]
  [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] {L : Type} [Field L] [Algebra K L] {t : L} [Fact (t ≠ 0)]
  (D : GlueDatum N ℓ K t)

abbrev GlueDatum.ρFin : ↥(chartAlgFin N ℓ) →+* ↥(chartRing K ({t} : Set L)) :=
  D.θFin.comp Algebra.TensorProduct.includeLeftRingHom

abbrev GlueDatum.ρInf : ↥(chartAlgInf N ℓ) →+* ↥(chartRing K ({t⁻¹} : Set L)) :=
  D.θInf.comp Algebra.TensorProduct.includeLeftRingHom

private theorem ρFin_comp_algebraMap :
    D.ρFin.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)) =
      (algebraMap K ↥(chartRing K ({t} : Set L))).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) q) :
      ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K) =
      (1 : ↥(chartAlgFin N ℓ)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θFin_right (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q)
  show D.θFin (Algebra.TensorProduct.includeLeftRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) q)) =
    algebraMap K ↥(chartRing K ({t} : Set L)) (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q)
  rw [h1, ← h2]
  rfl

private theorem ρInf_comp_algebraMap :
    D.ρInf.comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)) =
      (algebraMap K ↥(chartRing K ({t⁻¹} : Set L))).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K) := by
  refine RingHom.ext fun q => ?_
  have h1 : (Algebra.TensorProduct.includeLeftRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) q) :
      ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K) =
      (1 : ↥(chartAlgInf N ℓ)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h2 := RingHom.congr_fun D.θInf_right (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q)
  show D.θInf (Algebra.TensorProduct.includeLeftRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) q)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L)) (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K q)
  rw [h1, ← h2]
  rfl

private abbrev uFin : X₀ K t ⟶ ModularCurve.IgusaScheme.XFin N ℓ := Spec.map (CommRingCat.ofHom D.ρFin)

private abbrev uInf : CurveModel.XInf K t ⟶ ModularCurve.IgusaScheme.XInf N ℓ :=
  Spec.map (CommRingCat.ofHom D.ρInf)

private abbrev uMid : XOverlap K t ⟶ ModularCurve.IgusaScheme.XMid N ℓ := Spec.map (CommRingCat.ofHom D.ρMid)

private theorem f₀_uFin : f₀ K t ≫ uFin D = uMid D ≫ ModularCurve.IgusaScheme.fFin N ℓ := by
  simp only [f₀, uFin, uMid, ModularCurve.IgusaScheme.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_fin

private theorem fInf_uInf : CurveModel.fInf K t ≫ uInf D = uMid D ≫ ModularCurve.IgusaScheme.fInf N ℓ := by
  simp only [CurveModel.fInf, uInf, uMid, ModularCurve.IgusaScheme.fInf, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) D.sq_inf

private theorem glue_compat :
    f₀ K t ≫ (uFin D ≫ ModularCurve.IgusaScheme.ιFin N ℓ) =
      CurveModel.fInf K t ≫ (uInf D ≫ ModularCurve.IgusaScheme.ιInf N ℓ) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    ModularCurve.IgusaScheme.glue_condition]

private def u : glued K t ⟶ ModularCurve.IgusaScheme N ℓ :=
  pushout.desc (uFin D ≫ ModularCurve.IgusaScheme.ιFin N ℓ) (uInf D ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (glue_compat D)

@[reassoc]
private theorem ι₀_u : ι₀ K t ≫ u D = uFin D ≫ ModularCurve.IgusaScheme.ιFin N ℓ :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u : CurveModel.ιInf K t ≫ u D = uInf D ≫ ModularCurve.IgusaScheme.ιInf N ℓ :=
  pushout.inr_desc _ _ _

private theorem uFin_base :
    uFin D ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap K ↥(chartRing K ({t} : Set L)))) ≫ baseMap ℓ K := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρFin_comp_algebraMap D)

private theorem uInf_base :
    uInf D ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap K ↥(chartRing K ({t⁻¹} : Set L)))) ≫ baseMap ℓ K := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρInf_comp_algebraMap D)

private theorem u_igusaTo : u D ≫ igusaTo N ℓ = gluedToBase K t ≫ baseMap ℓ K := by
  refine pushout.hom_ext (f := f₀ K t) (g := CurveModel.fInf K t) ?_ ?_
  · change ι₀ K t ≫ u D ≫ igusaTo N ℓ = ι₀ K t ≫ gluedToBase K t ≫ baseMap ℓ K
    rw [ι₀_u_assoc, ModularCurve.IgusaScheme.ιFin_igusaTo, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf K t ≫ u D ≫ igusaTo N ℓ =
      CurveModel.ιInf K t ≫ gluedToBase K t ≫ baseMap ℓ K
    rw [ιInf_u_assoc, ModularCurve.IgusaScheme.ιInf_igusaTo, uInf_base, ιInf_gluedToBase_assoc]

def es : glued K t ⟶ pullback (igusaTo N ℓ) (baseMap ℓ K) :=
  pullback.lift (u D) (gluedToBase K t) (u_igusaTo D)

@[reassoc (attr := simp)]
private theorem es_fst : es D ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ K) = u D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem es_snd : es D ≫ pullback.snd (igusaTo N ℓ) (baseMap ℓ K) = gluedToBase K t :=
  pullback.lift_snd _ _ _

theorem ι₀_es_fst :
    ι₀ K t ≫ es D ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ K) =
      uFin D ≫ ModularCurve.IgusaScheme.ιFin N ℓ := by
  rw [es_fst, ι₀_u]

theorem ιInf_es_fst :
    CurveModel.ιInf K t ≫ es D ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ K) =
      uInf D ≫ ModularCurve.IgusaScheme.ιInf N ℓ := by
  rw [es_fst, ιInf_u]

private theorem uInf_asIdeal (z : CurveModel.XInf K t) :
    ((uInf D).base z).asIdeal = z.asIdeal.comap D.ρInf := rfl

private theorem u_mem_range_ιFin_iff (y : glued K t) :
    (u D).base y ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔ y ∈ Set.range (ι₀ K t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf K t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin D).base x₀, ?_⟩⟩
    change (uFin D ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ι₀ K t ≫ u D).base x₀
    rw [ι₀_u]
  · have hz : (u D).base ((CurveModel.ιInf K t).base z) =
        (ModularCurve.IgusaScheme.ιInf N ℓ).base ((uInf D).base z) := by
      change (CurveModel.ιInf K t ≫ u D).base z = (uInf D ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base z
      rw [ιInf_u]
    rw [hz, ig_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap]
    exact not_congr (iff_of_eq (congrArg (· ∈ z.asIdeal) D.ρInf_jInv))

theorem es_fst_mem_range_ιFin_iff (y : glued K t) :
    (es D ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ K)).base y ∈
        Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔ y ∈ Set.range (ι₀ K t).base := by
  rw [es_fst]; exact u_mem_range_ιFin_iff D y

private abbrev PFin (_D : GlueDatum N ℓ K t) := pullback (ModularCurve.IgusaScheme.ιFin N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ K))

private abbrev PInf (_D : GlueDatum N ℓ K t) := pullback (ModularCurve.IgusaScheme.ιInf N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ K))

private def φFin : X₀ K t ⟶ PFin D :=
  pullback.lift (uFin D) (ι₀ K t ≫ es D) (by rw [Category.assoc, ι₀_es_fst])

private def φInf : CurveModel.XInf K t ⟶ PInf D :=
  pullback.lift (uInf D) (CurveModel.ιInf K t ≫ es D) (by rw [Category.assoc, ιInf_es_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin D ≫ pullback.fst _ _ = uFin D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin D ≫ pullback.snd _ _ = ι₀ K t ≫ es D := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf D ≫ pullback.fst _ _ = uInf D := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf D ≫ pullback.snd _ _ = CurveModel.ιInf K t ≫ es D := pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom D.θFin) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) K).inv =
      φFin D ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θFin_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, es_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom D.θInf) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) K).inv =
      φInf D ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [D.θInf_right]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, es_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin : IsIso (φFin D) := by
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)
      (S := ↥(chartRing K ({t} : Set L))) D.θFin) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using D.bijFin)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)
      (S := ↥(chartRing K ({t} : Set L))) D.θFin)) := inferInstance
  haveI : IsIso (φFin D ≫
      (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom) := by
    rw [← SpecMap_θFin_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φFin D)
    ((pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
      (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φInf : IsIso (φInf D) := by
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)
      (S := ↥(chartRing K ({t⁻¹} : Set L))) D.θInf) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using D.bijInf)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)
      (S := ↥(chartRing K ({t⁻¹} : Set L))) D.θInf)) := inferInstance
  haveI : IsIso (φInf D ≫
      (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom) := by
    rw [← SpecMap_θInf_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φInf D)
    ((pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ K) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
      (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ι₀_es : IsOpenImmersion (ι₀ K t ≫ es D) := by
  haveI := isIso_φFin D
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_es : IsOpenImmersion (CurveModel.ιInf K t ≫ es D) := by
  haveI := isIso_φInf D
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_es_eq {y y' : glued K t} (h : es D y = es D y') : u D y = u D y' := by
  have h1 := congrArg (pullback.fst (igusaTo N ℓ) (baseMap ℓ K)) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, es_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_es : Function.Injective (es D) := by
  intro y y' h
  have hu := u_eq_of_es_eq D h
  have hu' : (u D).base y = (u D).base y' := hu
  have hsame : y ∈ Set.range (ι₀ K t).base ↔ y' ∈ Set.range (ι₀ K t).base := by
    rw [← u_mem_range_ιFin_iff D y, ← u_mem_range_ιFin_iff D y', hu']
  by_cases hy : y ∈ Set.range (ι₀ K t).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_es D
    have : (ι₀ K t ≫ es D) a = (ι₀ K t ≫ es D) a' := h
    rw [(ι₀ K t ≫ es D).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ K t).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf K t y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf K t y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_es D
    have : (CurveModel.ιInf K t ≫ es D) a = (CurveModel.ιInf K t ≫ es D) a' := h
    rw [(CurveModel.ιInf K t ≫ es D).isOpenEmbedding.injective this]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem surjective_es : Function.Surjective (es D) := by
  intro p
  rcases mem_range_ιFin_or_mem_range_ιInf N ℓ (pullback.fst (igusaTo N ℓ) (baseMap ℓ K) p) with hp | hp
  · have hp' : p ∈ Set.range (pullback.snd (ModularCurve.IgusaScheme.ιFin N ℓ)
        (pullback.fst (igusaTo N ℓ) (baseMap ℓ K))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φFin D
    obtain ⟨a, rfl⟩ := (φFin D).homeomorph.surjective r
    exact ⟨ι₀ K t a, by
      show (ι₀ K t ≫ es D) a = (φFin D ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : p ∈ Set.range (pullback.snd (ModularCurve.IgusaScheme.ιInf N ℓ)
        (pullback.fst (igusaTo N ℓ) (baseMap ℓ K))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf D
    obtain ⟨a, rfl⟩ := (φInf D).homeomorph.surjective r
    exact ⟨CurveModel.ιInf K t a, by
      show (CurveModel.ιInf K t ≫ es D) a = (φInf D ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

theorem isIso_es : IsIso (es D) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_es D⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_es D) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf K t y with hy | hy
  · exact ⟨_, ι₀ K t, inferInstance, hy, isOpenImmersion_ι₀_es D⟩
  · exact ⟨_, CurveModel.ιInf K t, inferInstance, hy, isOpenImmersion_ιInf_es D⟩

end Schemes

section Datum

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] {K : Type} [Field K]
  [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K] {L : Type} [Field L] [Algebra K L] {t : L}

variable
  (eFin : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[K] ↥(chartRing K ({t} : Set L)))
  (eInf : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[K] ↥(chartRing K ({t⁻¹} : Set L)))

private def θF : ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K →+* ↥(chartRing K ({t} : Set L)) :=
  (eFin : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) →+* ↥(chartRing K ({t} : Set L))).comp
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) K))

private def θI : ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K →+* ↥(chartRing K ({t⁻¹} : Set L)) :=
  (eInf : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) →+* ↥(chartRing K ({t⁻¹} : Set L))).comp
    (RingHomClass.toRingHom
      (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) K))

private theorem θF_tmul (b : ↥(chartAlgFin N ℓ)) (x : K) :
    θF eFin (b ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] x) = eFin (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := by
  show eFin (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) K (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

private theorem θI_tmul (b : ↥(chartAlgInf N ℓ)) (x : K) :
    θI eInf (b ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] x) = eInf (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := by
  show eInf (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) K (b ⊗ₜ x)) = _
  rw [Algebra.TensorProduct.comm_tmul]

private theorem θF_right :
    (θF eFin).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)) =
    algebraMap K ↥(chartRing K ({t} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θF eFin ((1 : ↥(chartAlgFin N ℓ)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] x) = _
  rw [θF_tmul]
  have hx : (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] (1 : ↥(chartAlgFin N ℓ)) :
      K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)) = algebraMap K _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgEquiv.commutes]

private theorem θI_right :
    (θI eInf).comp (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
      K →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] K)) =
    algebraMap K ↥(chartRing K ({t⁻¹} : Set L)) := by
  refine RingHom.ext fun x => ?_
  show θI eInf ((1 : ↥(chartAlgInf N ℓ)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] x) = _
  rw [θI_tmul]
  have hx : (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] (1 : ↥(chartAlgInf N ℓ)) :
      K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)) = algebraMap K _ x := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [hx, AlgEquiv.commutes]

private theorem θF_includeLeft (b : ↥(chartAlgFin N ℓ)) :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b = eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θF_tmul]

private theorem θI_includeLeft (b : ↥(chartAlgInf N ℓ)) :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b = eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) := by
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θI_tmul]

private def gMid : ↥(chartAlgFin N ℓ) →+* ↥(chartRing K ({t, t⁻¹} : Set L)) :=
  (incl₀ K t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)

private theorem coe_gMid (b : ↥(chartAlgFin N ℓ)) :
    (gMid (t := t) eFin b : L) = (eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) := by
  show ((incl₀ K t) ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom b) : L) = _
  rw [CurveModel.coe_chartIncl, θF_includeLeft]

private theorem isUnit_gMid_j [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t) : IsUnit (gMid (t := t) eFin (jChartFin N ℓ)) := by
  have h : gMid (t := t) eFin (jChartFin N ℓ) = incl₀ K t (tChart K t) := by
    apply Subtype.ext
    rw [coe_gMid, hj, CurveModel.coe_chartIncl, coe_tChart]
  rw [h]
  exact isUnit_incl₀_tChart K t Fact.out

private def ρM [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t) : ↥(chartAlgMid N ℓ) →+* ↥(chartRing K ({t, t⁻¹} : Set L)) :=
  letI := (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  IsLocalization.Away.lift (jChartFin N ℓ) (g := gMid (t := t) eFin) (isUnit_gMid_j eFin hj)

private theorem ρM_inclFin [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t) (b : ↥(chartAlgFin N ℓ)) :
    ρM eFin hj (ModularCurve.IgusaScheme.inclFin N ℓ b) = gMid (t := t) eFin b := by
  letI := (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact IsLocalization.Away.lift_eq (jChartFin N ℓ) (isUnit_gMid_j eFin hj) b

private theorem _root_.SPISO.sq_fin [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t) :
    (incl₀ K t).toRingHom.comp ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom :=
  RingHom.ext fun b => (ρM_inclFin eFin hj b).symm

p2m_export "SPISO" "sq_fin"

private theorem _root_.SPISO.sq_inf [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n)) :
    (inclInf K t).toRingHom.comp ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom) =
      (ρM eFin hj).comp (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom := by
  letI := (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  refine RingHom.ext fun b' => Subtype.ext ?_

  obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, h⟩ :=
    IsLocalization.surj (Submonoid.powers (jChartFin N ℓ)) (ModularCurve.IgusaScheme.inclInf N ℓ b')
  have h' : (ModularCurve.IgusaScheme.inclInf N ℓ b') * (ModularCurve.IgusaScheme.inclFin N ℓ (jChartFin N ℓ)) ^ n =
      ModularCurve.IgusaScheme.inclFin N ℓ b := by
    simpa only [RingHom.algebraMap_toAlgebra, map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h
  have hF : (b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n := by
    have := congrArg (fun z : ↥(chartAlgMid N ℓ) => (z : ↥(modularFunctionFieldFull N))) h'
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, ModularCurve.IgusaScheme.coe_chartIncl, coe_jChartFin]
      using this.symm
  have hc := hcompat b b' n hF

  have hρ := congrArg (fun z : ↥(chartAlgMid N ℓ) => ((ρM eFin hj z : ↥(chartRing K ({t, t⁻¹} : Set L))) : L)) h'
  simp only [map_mul, map_pow, Subalgebra.coe_mul, Subalgebra.coe_pow] at hρ
  rw [ρM_inclFin, ρM_inclFin, coe_gMid, coe_gMid, hj, hc] at hρ
  have htn : t ^ n ≠ 0 := pow_ne_zero n Fact.out
  have hmain : ((ρM eFin hj (ModularCurve.IgusaScheme.inclInf N ℓ b') : ↥(chartRing K ({t, t⁻¹} : Set L))) : L) =
      (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) :=
    mul_right_cancel₀ htn hρ
  show ((inclInf K t) ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom b') : L) =
    ((ρM eFin hj (ModularCurve.IgusaScheme.inclInf N ℓ b') : ↥(chartRing K ({t, t⁻¹} : Set L))) : L)
  rw [CurveModel.coe_chartIncl, θI_includeLeft, hmain]

p2m_export "SPISO" "sq_inf"

private def datum [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n))
    (hjInv : ((eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)) : L) = t⁻¹) : GlueDatum N ℓ K t where
  θFin := θF eFin
  θInf := θI eInf
  ρMid := ρM eFin hj
  θFin_right := θF_right eFin
  θInf_right := θI_right eInf
  sq_fin := sq_fin eFin hj
  sq_inf := sq_inf eFin eInf hj hcompat
  ρInf_jInv := Subtype.ext (by rw [θI_includeLeft, hjInv, coe_tInvChart])
  bijFin := eFin.bijective.comp
    (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) K).bijective
  bijInf := eInf.bijective.comp
    (Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) K).bijective

private theorem ρFin_eq :
    (θF eFin).comp Algebra.TensorProduct.includeLeftRingHom =
      eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgFin N ℓ))).toRingHom :=
  RingHom.ext fun b => θF_includeLeft eFin b

private theorem ρInf_eq :
    (θI eInf).comp Algebra.TensorProduct.includeLeftRingHom =
      eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgInf N ℓ))).toRingHom :=
  RingHom.ext fun b => θI_includeLeft eInf b

theorem main [Fact (t ≠ 0)] (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n))
    (hjInv : ((eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)) : L) = t⁻¹) :
    ∃ (es : glued K t ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) (_ : IsIso es),
      es ≫ pullback.snd (igusaTo N ℓ) _ = gluedToBase K t ∧
      (AlgebraicCurve.CurveModel.ι₀ K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) := by
  let D := datum eFin eInf hj hcompat hjInv
  refine ⟨es D, isIso_es D, es_snd D, ?_, ?_⟩
  · rw [ι₀_es_fst]
    show Spec.map (CommRingCat.ofHom ((θF eFin).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [ρFin_eq]
  · rw [ιInf_es_fst]
    show Spec.map (CommRingCat.ofHom ((θI eInf).comp Algebra.TensorProduct.includeLeftRingHom)) ≫ _ = _
    rw [ρInf_eq]

end Datum

end SPISO

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme in
open scoped TensorProduct in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K]
    {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (eFin : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t} : Set L)))
    (eInf : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hjInv : ((eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)) : L) = t⁻¹)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n)) :
    ∃ (es : AlgebraicCurve.CurveModel.glued K t ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) (_ : IsIso es),
      es ≫ pullback.snd (igusaTo N ℓ) _ = AlgebraicCurve.CurveModel.gluedToBase K t ∧
      (AlgebraicCurve.CurveModel.ι₀ K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) :=
  SPISO.main eFin eInf hj hcompat hjInv

end S_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing (solution)
