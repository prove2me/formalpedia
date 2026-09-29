-- Prove2me | solution 1 for ModularCurve.DRLevel.mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b00356ea-6999-52d5-aea7-597bd323b31b

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme ModularCurve.DRLevel"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase0 DRLevel.fibre0 IgusaScheme.chartAlgFin IgusaScheme.jChartFin IgusaScheme IgusaScheme.ιFin IgusaScheme.mem_range_ιFin_or_mem_range_ιInf qExpand jq modularFunctionFieldFull jGeomGen jNGeomGen modularFunctionFieldC"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull_ne_zero coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition mem_range_ιFin_or_mem_range_ιInf chartFinOpen chartInfOpen"
namespace Charts
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "X₀" => ModularCurve.IgusaScheme N ℓ

theorem ιFin_eq_ιInf_iff (x₀ : XFin N ℓ) (xi : XInf N ℓ) :
    (ιFin N ℓ).base x₀ = (ιInf N ℓ).base xi ↔
      ∃ u : XMid N ℓ, (fFin N ℓ).base u = x₀ ∧ (fInf N ℓ).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin N ℓ) (fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      exact ⟨u, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · rcases fj with ⟨⟩
    · rcases fi with ⟨⟩
  · rintro ⟨u, rfl, rfl⟩
    change (fFin N ℓ ≫ ιFin N ℓ).base u = (fInf N ℓ ≫ ιInf N ℓ).base u
    rw [glue_condition]

theorem range_fFin : Set.range (fFin N ℓ).base =
    ((PrimeSpectrum.basicOpen (jChartFin N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin N ℓ))) :
      Set (PrimeSpectrum (chartAlgFin N ℓ))) := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jChartFin N ℓ)

theorem range_fInf : Set.range (fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf N ℓ))) :
      Set (PrimeSpectrum (chartAlgInf N ℓ))) := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid N ℓ) (jInvChartInf N ℓ)

abbrev ιMid : XMid N ℓ ⟶ X₀ := fFin N ℓ ≫ ιFin N ℓ

scoped instance isOpenImmersion_ιMid : IsOpenImmersion (ιMid N ℓ) := IsOpenImmersion.comp _ _

theorem ιMid_eq' : ιMid N ℓ = fInf N ℓ ≫ ιInf N ℓ := glue_condition N ℓ

theorem inclFin_j_mul_inclInf_jInv :
    inclFin N ℓ (jChartFin N ℓ) * inclInf N ℓ (jInvChartInf N ℓ) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ (jFull_ne_zero N)])

abbrev U : (X₀).Opens := (ιFin N ℓ) ''ᵁ ⊤

abbrev V : (X₀).Opens := (ιInf N ℓ) ''ᵁ ⊤

theorem U_eq : U N ℓ = chartFinOpen N ℓ := (ιFin N ℓ).image_top_eq_opensRange
theorem V_eq : V N ℓ = chartInfOpen N ℓ := (ιInf N ℓ).image_top_eq_opensRange

def sF : Γ(XFin N ℓ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin N ℓ))).inv (jChartFin N ℓ)

def sI : Γ(XInf N ℓ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf N ℓ))).inv (jInvChartInf N ℓ)

def f : Γ(X₀, U N ℓ) := ((ιFin N ℓ).appIso ⊤).inv (sF N ℓ)

def g : Γ(X₀, V N ℓ) := ((ιInf N ℓ).appIso ⊤).inv (sI N ℓ)

theorem basicOpen_sF : (XFin N ℓ).basicOpen (sF N ℓ) = (fFin N ℓ).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sF, basicOpen_eq_of_affine]
  exact (range_fFin N ℓ).symm

theorem basicOpen_sI : (XInf N ℓ).basicOpen (sI N ℓ) = (fInf N ℓ).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sI, basicOpen_eq_of_affine]
  exact (range_fInf N ℓ).symm

theorem image_opensRange {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a]
    [IsOpenImmersion b] :
    b ''ᵁ a.opensRange = (a ≫ b).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (Scheme.Hom.comp_apply a b u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a.base u, ⟨u, rfl⟩, (Scheme.Hom.comp_apply a b u).symm⟩

theorem basicOpen_f : (X₀).basicOpen (f N ℓ) = (ιMid N ℓ).opensRange := by
  rw [f, ← Scheme.image_basicOpen, basicOpen_sF, image_opensRange]

theorem opensRange_ιMid' : (fInf N ℓ ≫ ιInf N ℓ).opensRange = (ιMid N ℓ).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_opensRange]
  rw [← ιMid_eq']

theorem basicOpen_g : (X₀).basicOpen (g N ℓ) = (ιMid N ℓ).opensRange := by
  rw [g, ← Scheme.image_basicOpen, basicOpen_sI, image_opensRange, opensRange_ιMid']

theorem U_inf_V : U N ℓ ⊓ V N ℓ = (ιMid N ℓ).opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨x₀, -, hx₀⟩, ⟨xi, -, hxi⟩⟩ := hx
    obtain ⟨u, rfl, rfl⟩ := (ιFin_eq_ιInf_iff N ℓ x₀ xi).mp (hx₀.trans hxi.symm)
    exact ⟨u, hx₀⟩
  · rintro x ⟨u, rfl⟩
    refine ⟨⟨(fFin N ℓ).base u, trivial, rfl⟩, ⟨(fInf N ℓ).base u, trivial, ?_⟩⟩
    change (fInf N ℓ ≫ ιInf N ℓ).base u = (fFin N ℓ ≫ ιFin N ℓ).base u
    rw [glue_condition]

theorem presheaf_map_map_apply {Y : Scheme.{0}} {A B C : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(Y, A)) :
    Y.presheaf.map i' (Y.presheaf.map i t) = Y.presheaf.map i'' t := by
  rw [Subsingleton.elim i'' (i ≫ i'), Functor.map_comp, CommRingCat.comp_apply]

theorem presheaf_map_map_map_apply {Y : Scheme.{0}} {A B C D : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op C ⟶ op D) (k : op A ⟶ op D) (t : Γ(Y, A)) :
    Y.presheaf.map i'' (Y.presheaf.map i' (Y.presheaf.map i t)) = Y.presheaf.map k t := by
  rw [presheaf_map_map_apply i i' (i ≫ i'), presheaf_map_map_apply (i ≫ i') i'' k]

theorem app_res_f (W : (X₀).Opens) (hWU : W ≤ U N ℓ) :
    (ιMid N ℓ).app W ((X₀).presheaf.map (homOfLE hWU).op (f N ℓ)) =
      (XMid N ℓ).presheaf.map (homOfLE le_top).op ((fFin N ℓ).appTop (sF N ℓ)) := by
  have step1 : (ιMid N ℓ).app W ((X₀).presheaf.map (homOfLE hWU).op (f N ℓ)) =
      (XMid N ℓ).presheaf.map ((TopologicalSpace.Opens.map (ιMid N ℓ).base).map (homOfLE hWU)).op
        ((ιMid N ℓ).app (U N ℓ) (f N ℓ)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (ιMid N ℓ).app (U N ℓ) (f N ℓ) =
      (fFin N ℓ).app _ ((ιFin N ℓ).app (U N ℓ) (f N ℓ)) := rfl
  have step4 : ∀ {V' : (XFin N ℓ).Opens} (k : op ⊤ ⟶ op V'),
      (fFin N ℓ).app V' ((XFin N ℓ).presheaf.map k (sF N ℓ)) =
        (XMid N ℓ).presheaf.map ((TopologicalSpace.Opens.map (fFin N ℓ).base).map k.unop).op
          ((fFin N ℓ).appTop (sF N ℓ)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, f, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_apply _ _ _ _

theorem app_res_g (W : (X₀).Opens) (hWV : W ≤ V N ℓ) :
    (ιMid N ℓ).app W ((X₀).presheaf.map (homOfLE hWV).op (g N ℓ)) =
      (XMid N ℓ).presheaf.map (homOfLE le_top).op ((fInf N ℓ).appTop (sI N ℓ)) := by
  rw [Scheme.Hom.congr_app (ιMid_eq' N ℓ) W, CommRingCat.comp_apply]
  have step1 : (fInf N ℓ ≫ ιInf N ℓ).app W ((X₀).presheaf.map (homOfLE hWV).op (g N ℓ)) =
      (XMid N ℓ).presheaf.map ((TopologicalSpace.Opens.map (fInf N ℓ ≫ ιInf N ℓ).base).map (homOfLE hWV)).op
        ((fInf N ℓ ≫ ιInf N ℓ).app (V N ℓ) (g N ℓ)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (fInf N ℓ ≫ ιInf N ℓ).app (V N ℓ) (g N ℓ) =
      (fInf N ℓ).app _ ((ιInf N ℓ).app (V N ℓ) (g N ℓ)) := rfl
  have step4 : ∀ {V' : (XInf N ℓ).Opens} (k : op ⊤ ⟶ op V'),
      (fInf N ℓ).app V' ((XInf N ℓ).presheaf.map k (sI N ℓ)) =
        (XMid N ℓ).presheaf.map ((TopologicalSpace.Opens.map (fInf N ℓ).base).map k.unop).op
          ((fInf N ℓ).appTop (sI N ℓ)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, g, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_map_apply _ _ _ _ _

theorem appTop_sF : (fFin N ℓ).appTop (sF N ℓ) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid N ℓ))).inv (inclFin N ℓ (jChartFin N ℓ)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclFin N ℓ).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jChartFin N ℓ)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

theorem appTop_sI : (fInf N ℓ).appTop (sI N ℓ) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid N ℓ))).inv (inclInf N ℓ (jInvChartInf N ℓ)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf N ℓ).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jInvChartInf N ℓ)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

theorem res_f_mul_res_g :
    ((X₀).presheaf.map (homOfLE (inf_le_left : U N ℓ ⊓ V N ℓ ≤ U N ℓ)).op).hom (f N ℓ) *
      ((X₀).presheaf.map (homOfLE (inf_le_right : U N ℓ ⊓ V N ℓ ≤ V N ℓ)).op).hom (g N ℓ) = 1 := by
  have hWle : U N ℓ ⊓ V N ℓ ≤ (ιMid N ℓ).opensRange := (U_inf_V N ℓ).le

  haveI : IsIso ((ιMid N ℓ).app (U N ℓ ⊓ V N ℓ)) := Scheme.Hom.isIso_app _ _ hWle
  have hinj : Function.Injective ((ιMid N ℓ).app (U N ℓ ⊓ V N ℓ)) :=
    (ConcreteCategory.bijective_of_isIso ((ιMid N ℓ).app (U N ℓ ⊓ V N ℓ))).1
  apply hinj
  rw [map_mul, map_one, app_res_f, app_res_g, appTop_sF, appTop_sI, ← map_mul, ← map_mul,
    inclFin_j_mul_inclInf_jInv, map_one, map_one]

theorem charts_aux :
    ∃ (f' : Γ(X₀, U N ℓ)) (g' : Γ(X₀, V N ℓ)),
      U N ℓ ⊓ V N ℓ = (X₀).basicOpen f' ∧ U N ℓ ⊓ V N ℓ = (X₀).basicOpen g' ∧
      ((X₀).presheaf.map (homOfLE (inf_le_left : U N ℓ ⊓ V N ℓ ≤ U N ℓ)).op).hom f' *
        ((X₀).presheaf.map (homOfLE (inf_le_right : U N ℓ ⊓ V N ℓ ≤ V N ℓ)).op).hom g' = 1 :=
  ⟨f N ℓ, g N ℓ, (U_inf_V N ℓ).trans (basicOpen_f N ℓ).symm, (U_inf_V N ℓ).trans (basicOpen_g N ℓ).symm,
    res_f_mul_res_g N ℓ⟩

end ModularCurve.IgusaScheme.Charts
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme.Charts"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ)
    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))
    (x : closedPoints M.C) (hj : jGeomGen κ N₀ ∈ (M.placeOfPoint x).toValuationSubring) :
    (e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base x.1 ∈
      Set.range (IgusaScheme.ιFin N₀ q).base := by
  classical
  set F : M.C ⟶ ModularCurve.IgusaScheme N₀ q :=
    e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)) with hF
  by_contra hxU

  have hUV := ModularCurve.IgusaScheme.Charts.U_inf_V N₀ q
  have hbg := ModularCurve.IgusaScheme.Charts.basicOpen_g N₀ q

  have hxV : F.base x.1 ∈ ModularCurve.IgusaScheme.Charts.V N₀ q := by
    rcases ModularCurve.IgusaScheme.mem_range_ιFin_or_mem_range_ιInf N₀ q (F.base x.1) with h | h
    · exact absurd h hxU
    · rw [ModularCurve.IgusaScheme.Charts.V_eq]; exact h

  set t : Γ(M.C, F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.V N₀ q) :=
    (F.app (ModularCurve.IgusaScheme.Charts.V N₀ q)).hom (ModularCurve.IgusaScheme.Charts.g N₀ q) with ht
  have hnot : ¬ IsUnit ((M.C.presheaf.germ (F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.V N₀ q) x.1 hxV).hom t) := by
    intro hunit
    have hmem : x.1 ∈ M.C.basicOpen t := (Scheme.mem_basicOpen M.C t x.1 hxV).mpr hunit
    rw [ht, ← Scheme.preimage_basicOpen, hbg] at hmem

    apply hxU
    have h2 : F.base x.1 ∈ ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q := by
      rw [hUV]; exact hmem
    have h3 : F.base x.1 ∈ ModularCurve.IgusaScheme.Charts.U N₀ q := h2.1
    rw [ModularCurve.IgusaScheme.Charts.U_eq] at h3
    exact h3

  have hηU : genericPoint M.C ∈ F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.U N₀ q := by
    obtain ⟨⟨y, hy⟩⟩ := hMne
    exact (genericPoint_specializes y).mem_open (F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.U N₀ q).2 hy
  have hηV : genericPoint M.C ∈ F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.V N₀ q :=
    (genericPoint_specializes x.1).mem_open (F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.V N₀ q).2 hxV

  set s : Γ(M.C, F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.U N₀ q) :=
    (F.app (ModularCurve.IgusaScheme.Charts.U N₀ q)).hom (ModularCurve.IgusaScheme.Charts.f N₀ q) with hs

  have hηW : genericPoint M.C ∈ F ⁻¹ᵁ (ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q) := ⟨hηU, hηV⟩
  have hprod : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s *
      (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t = 1 := by
    have key := ModularCurve.IgusaScheme.Charts.res_f_mul_res_g N₀ q

    have e1 : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s =
        (M.C.presheaf.germ _ (genericPoint M.C) hηW).hom
          ((F.app (ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q)).hom
            (((ModularCurve.IgusaScheme N₀ q).presheaf.map (homOfLE (inf_le_left : ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q ≤ ModularCurve.IgusaScheme.Charts.U N₀ q)).op).hom
              (ModularCurve.IgusaScheme.Charts.f N₀ q))) := by
      have nat := congrArg (fun φ => φ.hom (ModularCurve.IgusaScheme.Charts.f N₀ q))
        (F.naturality (homOfLE (inf_le_left : ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q ≤ ModularCurve.IgusaScheme.Charts.U N₀ q)).op)
      simp only [CommRingCat.comp_apply] at nat
      rw [nat, TopCat.Presheaf.germ_res_apply, hs]
    have e2 : (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t =
        (M.C.presheaf.germ _ (genericPoint M.C) hηW).hom
          ((F.app (ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q)).hom
            (((ModularCurve.IgusaScheme N₀ q).presheaf.map (homOfLE (inf_le_right : ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q ≤ ModularCurve.IgusaScheme.Charts.V N₀ q)).op).hom
              (ModularCurve.IgusaScheme.Charts.g N₀ q))) := by
      have nat := congrArg (fun φ => φ.hom (ModularCurve.IgusaScheme.Charts.g N₀ q))
        (F.naturality (homOfLE (inf_le_right : ModularCurve.IgusaScheme.Charts.U N₀ q ⊓ ModularCurve.IgusaScheme.Charts.V N₀ q ≤ ModularCurve.IgusaScheme.Charts.V N₀ q)).op)
      simp only [CommRingCat.comp_apply] at nat
      rw [nat, TopCat.Presheaf.germ_res_apply, ht]
    rw [e1, e2, ← map_mul, ← map_mul, key, map_one, map_one]

  have hpin : (M.C.presheaf.germ _ (genericPoint M.C) hηU).hom s = M.ffEquiv (jGeomGen κ N₀) := by
    have h := (hMpin (ModularCurve.IgusaScheme.jChartFin N₀ q)).1 rfl
    rw [RingEquiv.symm_apply_eq] at h
    exact h

  obtain ⟨r, hr⟩ : ∃ r : M.C.presheaf.stalk x.1,
      algebraMap (M.C.presheaf.stalk x.1) M.C.functionField r = M.ffEquiv (jGeomGen κ N₀) := by
    have hj' : jGeomGen κ N₀ ∈ (M.placeOfPoint x).toValuationSubring.toSubring := hj
    rw [← M.range_stalk_eq x] at hj'
    obtain ⟨r, hr⟩ := RingHom.mem_range.mp hj'
    refine ⟨r, ?_⟩
    rw [← RingEquiv.symm_apply_eq]
    exact hr

  have htη : algebraMap (M.C.presheaf.stalk x.1) M.C.functionField
      ((M.C.presheaf.germ (F ⁻¹ᵁ ModularCurve.IgusaScheme.Charts.V N₀ q) x.1 hxV).hom t) =
      (M.C.presheaf.germ _ (genericPoint M.C) hηV).hom t := by
    show (M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

  have hinj : Function.Injective (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField) :=
    IsFractionRing.injective (M.C.presheaf.stalk x.1) M.C.functionField
  apply hnot
  refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
  apply hinj
  rw [map_mul, map_one, htη, hr, ← hpin, mul_comm]
  exact hprod

end
p2m_reactivate "P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint.ModularCurve.IgusaScheme.Charts"

end S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint
end P2MW
export P2MW.S_ModularCurve_DRLevel_mem_range_iotaFin_of_isAffineGeomPlace_placeOfPoint (solution)
