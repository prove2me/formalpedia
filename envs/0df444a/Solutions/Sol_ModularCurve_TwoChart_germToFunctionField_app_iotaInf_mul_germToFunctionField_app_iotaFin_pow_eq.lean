-- Prove2me | solution 1 for ModularCurve.TwoChart.germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4f80a6cb-2e92-5de5-abf7-0da5e5ab62ea

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace K6card
namespace M

section TwoChartM

open ModularCurve.TwoChart

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem span_overlap_aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (y : Y) (z : Z)
    (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
    (w : (span f g).obj k) (h₁ : (span f g).map fi w = y) (h₂ : (span f g).map fj w = z) :
    ∃ x : X, f.base x = y ∧ g.base x = z := by
  match k, fi, fj, w, h₁, h₂ with
  | none, WidePushoutShape.Hom.init _, WidePushoutShape.Hom.init _, w, h₁, h₂ => exact ⟨w, h₁, h₂⟩

theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    exact span_overlap_aux _ _ _ _ k fi fj w h₁ h₂
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

theorem range_fInf : Set.range (fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R F j))) :
      Set (PrimeSpectrum (chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

theorem range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R F j))) :
      Set (PrimeSpectrum (chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem ιInf_mem_range_ιFin_iff (xi : XInf R F j) :
    (ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔ jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (ιInf R F j).base ↔ jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fInf R F j).base w, ((ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

variable {R F j}

theorem exists_eq_specMap_comp_ιFin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base) :
    ∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιFin R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιFin R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιFin R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιFin R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_eq_specMap_comp_ιInf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base) :
    ∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιInf R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιInf R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιInf R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιInf R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_chart_factorisation_fin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j ∧
        β (jInvChartInf R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιFin g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιInf g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_left h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιInf_mem_range_ιFin_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation_inf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel R F j) :
    (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) ∨
      (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j ∧
        β (jChartFin R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιInf g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιFin g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_right h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιFin_mem_range_ιInf_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) := by
  rcases exists_chart_factorisation_fin g with h | ⟨β, hβ, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨β, hβ⟩

end TwoChartM
end M

section InfRead

open ModularCurve.TwoChart

theorem stalkMap_germ_congr {X Y : Scheme.{u}} (F₁ F₂ : X ⟶ Y) (hF : F₁ = F₂) (x : X) (U : Y.Opens) (s : Γ(Y, U))
    (h₁ : F₁.base x ∈ U) (h₂ : F₂.base x ∈ U) :
    (F₁.stalkMap x).hom ((Y.presheaf.germ U (F₁.base x) h₁).hom s) = (F₂.stalkMap x).hom ((Y.presheaf.germ U (F₂.base x) h₂).hom s) := by
  subst hF; rfl

theorem stalkMap_germ_sec {B : CommRingCat.{u}} {Y : Scheme.{u}} (ι : Spec B ⟶ Y) [IsOpenImmersion ι] (x : Spec B) (b : B)
    (hx : ι.base x ∈ ι ''ᵁ ⊤) :
    (ι.stalkMap x).hom ((Y.presheaf.germ (ι ''ᵁ ⊤) (ι.base x) hx).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b))) =
      ((Spec B).presheaf.germ ⊤ x trivial).hom ((Scheme.ΓSpecIso B).inv b) := by
  rw [Scheme.Hom.germ_stalkMap_apply ι (ι ''ᵁ ⊤) x hx, ← CommRingCat.comp_apply (ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_app,
    TopCat.Presheaf.germ_res_apply']

theorem stalkMap_germ_top_spec {B C : CommRingCat.{u}} (φ : B ⟶ C) (x : Spec C) (b : B) :
    ((Spec.map φ).stalkMap x).hom (((Spec B).presheaf.germ ⊤ ((Spec.map φ).base x) trivial).hom ((Scheme.ΓSpecIso B).inv b)) =
      ((Spec C).presheaf.germ ⊤ x trivial).hom ((Scheme.ΓSpecIso C).inv (φ b)) := by
  rw [Scheme.Hom.germ_stalkMap_apply (Spec.map φ) ⊤ x trivial]
  congr 1
  change ((Scheme.ΓSpecIso B).inv ≫ (Spec.map φ).appTop) b = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]

abbrev ιMid : XMid A K j ⟶ ModularCurve.TwoChartModel A K j := fFin A K j ≫ ιFin A K j

theorem germ_secInf_mul_germ_secFin_pow_eq (q : XMid A K j)
    (b' : ↥(chartAlgInf A K j)) (a : ↥(chartAlgFin A K j)) (n : ℕ) (hab : (b' : K) * j ^ n = (a : K))
    (p : ModularCurve.TwoChartModel A K j) (hp : (ιMid A K j).base q = p)
    (hpF : p ∈ (ιFin A K j) ''ᵁ ⊤) (hpI : p ∈ (ιInf A K j) ''ᵁ ⊤) :
    ((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιInf A K j) ''ᵁ ⊤) p hpI).hom
        (((ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf A K j))).inv b')) *
      (((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιFin A K j) ''ᵁ ⊤) p hpF).hom
        (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv (jChartFin A K j)))) ^ n =
      ((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιFin A K j) ''ᵁ ⊤) p hpF).hom
        (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv a)) := by
  subst hp

  haveI : IsIso ((ιMid A K j).stalkMap q) := inferInstance
  apply ((ConcreteCategory.bijective_of_isIso ((ιMid A K j).stalkMap q)).1)
  rw [map_mul, map_pow]

  have hF : ∀ (c : ↥(chartAlgFin A K j)) (hc : (ιMid A K j).base q ∈ (ιFin A K j) ''ᵁ ⊤),
      ((ιMid A K j).stalkMap q).hom (((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιFin A K j) ''ᵁ ⊤) ((ιMid A K j).base q) hc).hom
        (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv c))) =
      ((XMid A K j).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid A K j))).inv (inclFin A K j c)) := by
    intro c hc
    rw [Scheme.Hom.stalkMap_comp]
    show ((fFin A K j).stalkMap q).hom (((ιFin A K j).stalkMap ((fFin A K j).base q)).hom
      ((((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιFin A K j) ''ᵁ ⊤) ((ιFin A K j).base ((fFin A K j).base q)) hc).hom
        (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv c))))) = _
    rw [stalkMap_germ_sec (ιFin A K j) ((fFin A K j).base q) c]
    exact stalkMap_germ_top_spec (CommRingCat.ofHom (inclFin A K j).toRingHom) q c
  have hI : ∀ (c : ↥(chartAlgInf A K j)) (hc : (ιMid A K j).base q ∈ (ιInf A K j) ''ᵁ ⊤),
      ((ιMid A K j).stalkMap q).hom (((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιInf A K j) ''ᵁ ⊤) ((ιMid A K j).base q) hc).hom
        (((ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf A K j))).inv c))) =
      ((XMid A K j).presheaf.germ ⊤ q trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgMid A K j))).inv (inclInf A K j c)) := by
    intro c hc
    have hc' : (fInf A K j ≫ ιInf A K j).base q ∈ (ιInf A K j) ''ᵁ ⊤ := by rw [← glue_condition]; exact hc
    rw [stalkMap_germ_congr (ιMid A K j) (fInf A K j ≫ ιInf A K j) (glue_condition A K j) q _ _ hc hc', Scheme.Hom.stalkMap_comp]
    show ((fInf A K j).stalkMap q).hom (((ιInf A K j).stalkMap ((fInf A K j).base q)).hom
      ((((ModularCurve.TwoChartModel A K j).presheaf.germ ((ιInf A K j) ''ᵁ ⊤) ((ιInf A K j).base ((fInf A K j).base q)) hc').hom
        (((ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf A K j))).inv c))))) = _
    rw [stalkMap_germ_sec (ιInf A K j) ((fInf A K j).base q) c]
    exact stalkMap_germ_top_spec (CommRingCat.ofHom (inclInf A K j).toRingHom) q c
  rw [hF, hF, hI, ← map_pow, ← map_mul, ← map_pow, ← map_mul]
  congr 2
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_jChartFin]
  exact hab

theorem germToFunctionField_secInf_mul_pow_eq {Z : Scheme.{u}} [IsIntegral Z] (h : Z ⟶ ModularCurve.TwoChartModel A K j)
    [hUF : Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ιFin A K j) ''ᵁ ⊤)))]
    [hUI : Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ιInf A K j) ''ᵁ ⊤)))]
    (b' : ↥(chartAlgInf A K j)) (a : ↥(chartAlgFin A K j)) (n : ℕ) (hab : (b' : K) * j ^ n = (a : K)) :
    (Z.germToFunctionField (h ⁻¹ᵁ ((ιInf A K j) ''ᵁ ⊤)))
        ((h.app ((ιInf A K j) ''ᵁ ⊤)).hom (((ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf A K j))).inv b'))) *
      ((Z.germToFunctionField (h ⁻¹ᵁ ((ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ιFin A K j) ''ᵁ ⊤)).hom (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv (jChartFin A K j))))) ^ n =
      (Z.germToFunctionField (h ⁻¹ᵁ ((ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ιFin A K j) ''ᵁ ⊤)).hom (((ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin A K j))).inv a))) := by

  have hξF : genericPoint Z ∈ h ⁻¹ᵁ ((ιFin A K j) ''ᵁ ⊤) :=
    (genericPoint_spec Z).mem_open_set_iff (h ⁻¹ᵁ ((ιFin A K j) ''ᵁ ⊤)).2 |>.mpr (by
      obtain ⟨⟨z, hz⟩⟩ := hUF; exact ⟨z, Set.mem_univ _, hz⟩)
  have hξI : genericPoint Z ∈ h ⁻¹ᵁ ((ιInf A K j) ''ᵁ ⊤) :=
    (genericPoint_spec Z).mem_open_set_iff (h ⁻¹ᵁ ((ιInf A K j) ''ᵁ ⊤)).2 |>.mpr (by
      obtain ⟨⟨z, hz⟩⟩ := hUI; exact ⟨z, Set.mem_univ _, hz⟩)

  have hread : ∀ (U : (ModularCurve.TwoChartModel A K j).Opens) [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ U))] (hξ : genericPoint Z ∈ h ⁻¹ᵁ U) (s : (ModularCurve.TwoChartModel A K j).presheaf.obj (Opposite.op U)),
      (Z.germToFunctionField (h ⁻¹ᵁ U)) ((h.app U).hom s) =
        (h.stalkMap (genericPoint Z)).hom (((ModularCurve.TwoChartModel A K j).presheaf.germ U (h.base (genericPoint Z)) hξ).hom s) := by
    intro U _ hξ s
    rw [Scheme.Hom.germ_stalkMap_apply h U (genericPoint Z) hξ]
  rw [hread _ hξI, hread _ hξF, hread _ hξF, ← map_pow, ← map_mul]
  congr 1

  obtain ⟨x₀, -, hx₀⟩ := hξF
  obtain ⟨xi, -, hxi⟩ := hξI
  obtain ⟨q, hq₀, hqi⟩ := (K6card.M.ιFin_eq_ιInf_iff A K j x₀ xi).mp (hx₀.trans hxi.symm)
  have hp : (ιMid A K j).base q = h.base (genericPoint Z) := by
    rw [← hx₀, ← hq₀]; rfl
  exact germ_secInf_mul_germ_secFin_pow_eq A K j q b' a n hab _ hp _ _

end InfRead

end K6card
end

open CategoryTheory AlgebraicGeometry in
theorem solution
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    {Z : Scheme.{u}} [AlgebraicGeometry.IsIntegral Z] (h : Z ⟶ ModularCurve.TwoChartModel A K j)
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))]
    (b' : ↥(ModularCurve.TwoChart.chartAlgInf A K j)) (a : ↥(ModularCurve.TwoChart.chartAlgFin A K j)) (n : ℕ) (hab : (b' : K) * j ^ n = (a : K)) :
    (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιInf A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιInf A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgInf A K j))).inv b'))) *
      ((Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv (ModularCurve.TwoChart.jChartFin A K j))))) ^ n =
      (Z.germToFunctionField (h ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)))
        ((h.app ((ModularCurve.TwoChart.ιFin A K j) ''ᵁ ⊤)).hom (((ModularCurve.TwoChart.ιFin A K j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A K j))).inv a))) :=
  K6card.germToFunctionField_secInf_mul_pow_eq A K j h b' a n hab

end S_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq
end P2MW
export P2MW.S_ModularCurve_TwoChart_germToFunctionField_app_iotaInf_mul_germToFunctionField_app_iotaFin_pow_eq (solution)
