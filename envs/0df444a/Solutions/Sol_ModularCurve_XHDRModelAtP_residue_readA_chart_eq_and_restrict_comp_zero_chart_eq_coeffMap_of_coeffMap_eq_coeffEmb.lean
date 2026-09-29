-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a664dffd-0276-5b70-8abf-bd094989e367

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PistarResidue

section Read

variable {X : Scheme.{u}} {Z : Scheme.{u}} [IrreducibleSpace Z]

theorem genericPoint_mem_of_nonempty (V : Z.Opens) [h : Nonempty V] : genericPoint Z ∈ V :=
  ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using h)

noncomputable def readHom (g : Z ⟶ X) {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] : CommRingCat.of B ⟶ Z.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ g.app (ι ''ᵁ ⊤) ≫ Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))

theorem readHom_apply (g : Z ⟶ X) {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] (b : B) :
    (readHom g ι).hom b =
      Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤)) ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) :=
  rfl

theorem readHom_apply' (g : Z ⟶ X) {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] (hη : genericPoint Z ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤)) (b : B) :
    (readHom g ι).hom b =
      Z.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) (genericPoint Z) hη
        ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) :=
  rfl

theorem readHom_congr {g g' : Z ⟶ X} (h : g = g') {B : Type u} [CommRing B] (ι : Spec (CommRingCat.of B) ⟶ X)
    [IsOpenImmersion ι] [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    [Nonempty (Scheme.Opens.toScheme (g' ⁻¹ᵁ (ι ''ᵁ ⊤)))] :
    readHom g ι = readHom g' ι := by
  subst h; rfl

theorem appIso_inv_appLE_of_eq {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion ι]
    (φ : B →+* B') (κ : Spec (CommRingCat.of B') ⟶ X)
    (hκ : κ = Spec.map (CommRingCat.ofHom φ) ≫ ι) (e : (⊤ : (Spec (CommRingCat.of B')).Opens) ≤ κ ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv ≫ κ.appLE (ι ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).inv := by
  subst hκ
  have h2 : (Spec.map (CommRingCat.ofHom φ) ≫ ι).appLE (ι ''ᵁ ⊤) ⊤ e =
      ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) ≫ (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appLE_comp_appLE]
  have h3 : (ι.appIso ⊤).inv ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    convert (Spec (CommRingCat.of B)).presheaf.map_id _
    rfl
  have h4 : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom φ)).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [h2, ← Category.assoc (ι.appIso ⊤).inv, h3, Category.id_comp, h4, ← Scheme.ΓSpecIso_inv_naturality]

theorem image_top_le_preimage_image_top {X' : Scheme.{u}} (π : X ⟶ X') {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ X) (ι' : Spec (CommRingCat.of B') ⟶ X') [IsOpenImmersion ι] [IsOpenImmersion ι']
    (φ : B' →+* B) (hsq : ι ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ ι') :
    ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι' ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨s, rfl⟩
  show (ι ≫ π).base s ∈ ι'.opensRange
  rw [hsq]
  exact ⟨_, rfl⟩

theorem readHom_comp {X' : Scheme.{u}} (g : Z ⟶ X) (π : X ⟶ X') (g₀ : Z ⟶ X') (hg : g ≫ π = g₀)
    {B B' : Type u} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B) ⟶ X) (ι' : Spec (CommRingCat.of B') ⟶ X') [IsOpenImmersion ι] [IsOpenImmersion ι']
    (φ : B' →+* B) (hsq : ι ≫ π = Spec.map (CommRingCat.ofHom φ) ≫ ι')
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))] [Nonempty (Scheme.Opens.toScheme (g₀ ⁻¹ᵁ (ι' ''ᵁ ⊤)))] :
    readHom g₀ ι' = CommRingCat.ofHom φ ≫ readHom g ι := by
  subst hg
  have hle : ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι' ''ᵁ ⊤) := image_top_le_preimage_image_top π ι ι' φ hsq
  have hle' : g ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ (g ≫ π) ⁻¹ᵁ (ι' ''ᵁ ⊤) := fun x hx => hle hx

  have h1 : (g ≫ π).app (ι' ''ᵁ ⊤) ≫ Z.germToFunctionField ((g ≫ π) ⁻¹ᵁ (ι' ''ᵁ ⊤)) =
      (g ≫ π).appLE (ι' ''ᵁ ⊤) (g ⁻¹ᵁ (ι ''ᵁ ⊤)) hle' ≫ Z.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
    simp only [Scheme.germToFunctionField, Scheme.Hom.appLE, Category.assoc]
    rw [TopCat.Presheaf.germ_res]

  have h2 : (g ≫ π).appLE (ι' ''ᵁ ⊤) (g ⁻¹ᵁ (ι ''ᵁ ⊤)) hle' =
      π.appLE (ι' ''ᵁ ⊤) (ι ''ᵁ ⊤) hle ≫ g.appLE (ι ''ᵁ ⊤) (g ⁻¹ᵁ (ι ''ᵁ ⊤)) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE]

  have h3 : (Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (ι'.appIso ⊤).inv ≫ π.appLE (ι' ''ᵁ ⊤) (ι ''ᵁ ⊤) hle =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (ι.appIso ⊤).inv := by
    have H := appIso_inv_appLE_of_eq ι' φ (ι ≫ π) hsq
      (by rintro s -; exact hle (by rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨s, rfl⟩))
    have hsplit : (ι ≫ π).appLE (ι' ''ᵁ ⊤) ⊤
        (by rintro s -; exact hle (by rw [Scheme.Hom.image_top_eq_opensRange]; exact ⟨s, rfl⟩)) =
        π.appLE (ι' ''ᵁ ⊤) (ι ''ᵁ ⊤) hle ≫ ι.appLE (ι ''ᵁ ⊤) ⊤ (by rw [Scheme.Hom.preimage_image_eq]) := by
      rw [Scheme.Hom.appLE_comp_appLE]
    rw [hsplit, ← Scheme.Hom.appIso_hom'] at H
    rw [← cancel_mono (ι.appIso ⊤).hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H
  simp only [readHom]
  rw [h1, h2]
  simp only [Category.assoc]
  rw [reassoc_of% h3, Scheme.Hom.appLE_eq_app]

end Read

section TwoChart

open AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem ιInf_preimage_chartFinOpen :
    ιInf R F j ⁻¹ᵁ chartFinOpen R F j = PrimeSpectrum.basicOpen (jInvChartInf R F j) := by
  apply TopologicalSpace.Opens.ext
  ext y
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨u, rfl, rfl⟩ := (TwoChartsAux.ιFin_eq_ιInf_iff R F j x y).mp hx
    have : (fInf R F j).base u ∈ Set.range (fInf R F j).base := ⟨u, rfl⟩
    rw [TwoChartsAux.range_fInf] at this
    exact this
  · intro hy
    have hy' : y ∈ Set.range (fInf R F j).base := by rw [TwoChartsAux.range_fInf]; exact hy
    obtain ⟨u, rfl⟩ := hy'
    refine ⟨(fFin R F j).base u, ?_⟩
    change (fFin R F j ≫ ιFin R F j).base u = (fInf R F j ≫ ιInf R F j).base u
    rw [glue_condition]

end TwoChart

section Frame

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve
open scoped MatrixGroups

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

theorem iotaInf_jInvChartInf :
    𝔛.iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) =
      TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) := by
  apply Subtype.ext; apply Subtype.ext
  rw [𝔛.iotaInf_spec, TwoChartIntegralModel.coe_jInvChartInf, TwoChartIntegralModel.coe_jInvChartInf,
    IntermediateField.coe_inv, IntermediateField.coe_inv, coe_jAt, coe_jAt]

set_option maxHeartbeats 1600000 in

theorem mem_range_ιFin_of_pi_mem (x : ↥(X p (ΓM M H) hj))
    (hx : 𝔛.π.1.base x ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base) :
    x ∈ Set.range (ιFin p (ΓM M H) hj).base := by
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf _ _ _ x with h | ⟨y, rfl⟩
  · exact h
  · have e : 𝔛.π.1.base ((ιInf p (ΓM M H) hj).base y) =
        (ιInf p (ΓN p M H hpM) hj).base ((Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y) := by
      rw [← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]
    have hx' : (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)).base y ∈
        ιInf p (ΓN p M H hpM) hj ⁻¹ᵁ TwoChartIntegralModel.chartFinOpen _ _ _ := by
      show (ιInf p (ΓN p M H hpM) hj).base _ ∈ Set.range _
      rw [← e]; exact hx
    rw [ιInf_preimage_chartFinOpen] at hx'
    have h1 : TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) ∉ y.asIdeal := by
      rw [← iotaInf_jInvChartInf 𝔛]
      exact fun hmem => (PrimeSpectrum.mem_basicOpen _ _).mp hx' (Ideal.mem_comap.mpr hmem)
    have h2 : y ∈ ιInf p (ΓM M H) hj ⁻¹ᵁ TwoChartIntegralModel.chartFinOpen _ _ _ := by
      rw [ιInf_preimage_chartFinOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).mpr h1
    exact h2

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

abbrev XQ (𝔛 : XHDRModelAtP p M H hpM hj) : Scheme.{0} :=
  pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))

abbrev prA : XQ 𝔛 ⟶ XO (ΓM M H) hj ρ :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])

abbrev bcA (𝔛 : XHDRModelAtP p M H hpM hj) : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ XO (ΓM M H) hj ρ :=
  bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

abbrev WM (𝔛 : XHDRModelAtP p M H hpM hj) : (X p (ΓM M H) hj).Opens := (ιFin p (ΓM M H) hj) ''ᵁ ⊤

theorem prA_fst :
    prA 𝔛 A ρ hρ ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) =
      pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
  rw [pullback.lift_fst, Category.comp_id]

theorem comp_zero_fst_pi :
    𝔛.comp A hA ρ hρ 0 ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ≫ 𝔛.π.1 =
      pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) := by
  have h1 : fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.π.1 := by
    rw [fibreMap, pullback.lift_fst]
  rw [← h1, ← Category.assoc, 𝔛.comp_pi, Category.id_comp]

abbrev gInf : (𝔛.Mfib A hA ρ hρ).C ⟶ X p (ΓM M H) hj :=
  (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA A ρ 𝔛) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))

abbrev gN : (𝔛.Mfib A hA ρ hρ).C ⟶ X p (ΓN p M H hpM) hj :=
  𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))

theorem gInf_pi : gInf 𝔛 A hA ρ hρ ≫ 𝔛.π.1 = gN 𝔛 A hA ρ hρ := by
  simp only [gInf, gN, Category.assoc, bcMap_fst_assoc, comp_zero_fst_pi]

abbrev gGen : (𝔛.Meta).C ⟶ X p (ΓM M H) hj :=
  (𝔛.eeta ≫ prA 𝔛 A ρ hρ) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))

abbrev gGen₀ : (𝔛.Meta).C ⟶ X p (ΓM M H) hj :=
  𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))

theorem gGen_eq : gGen 𝔛 A ρ hρ = gGen₀ 𝔛 := by
  simp only [gGen, gGen₀, Category.assoc, prA_fst]

theorem genericPoint_mem_gInf :
    genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ gInf 𝔛 A hA ρ hρ ⁻¹ᵁ WM 𝔛 := by
  have h0 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ gN 𝔛 A hA ρ hρ ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) :=
    genericPoint_mem_of_nonempty _
  rw [← gInf_pi] at h0
  have h1 : 𝔛.π.1.base ((gInf 𝔛 A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C)) ∈
      Set.range (ιFin p (ΓN p M H hpM) hj).base := by
    rw [← Scheme.Hom.comp_apply]
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.image_top_eq_opensRange] at h0
    exact h0
  show (gInf 𝔛 A hA ρ hρ).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) ∈ (ιFin p (ΓM M H) hj) ''ᵁ ⊤
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact mem_range_ιFin_of_pi_mem 𝔛 _ h1

scoped instance nonempty_gInf : Nonempty (Scheme.Opens.toScheme (gInf 𝔛 A hA ρ hρ ⁻¹ᵁ WM 𝔛)) :=
  ⟨⟨_, genericPoint_mem_gInf 𝔛 A hA ρ hρ⟩⟩

theorem genericPoint_mem_gGen :
    genericPoint (𝔛.Meta).C ∈ gGen 𝔛 A ρ hρ ⁻¹ᵁ WM 𝔛 := by
  rw [gGen_eq]
  exact genericPoint_mem_of_nonempty _

scoped instance nonempty_gGen : Nonempty (Scheme.Opens.toScheme (gGen 𝔛 A ρ hρ ⁻¹ᵁ WM 𝔛)) :=
  ⟨⟨_, genericPoint_mem_gGen 𝔛 A ρ hρ⟩⟩

theorem coe_read_gInf_iota0 (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((readHom (gInf 𝔛 A hA ρ hρ) (ιFin p (ΓM M H) hj)).hom (𝔛.iota0 b))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y := by
  have H := readHom_comp (gInf 𝔛 A hA ρ hρ) 𝔛.π.1 (gN 𝔛 A hA ρ hρ) (gInf_pi 𝔛 A hA ρ hρ)
    (ιFin p (ΓM M H) hj) (ιFin p (ΓN p M H hpM) hj) 𝔛.iota0.toRingHom 𝔛.pi_chart
  have H' := congrArg (fun f => f.hom b) H
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at H'
  rw [← H']
  exact 𝔛.Mfib_pin A hA ρ hρ b y hy

theorem coe_read_gGen_iota0 (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
    (((𝔛.Meta).ffEquiv.symm ((readHom (gGen 𝔛 A ρ hρ) (ιFin p (ΓM M H) hj)).hom (𝔛.iota0 b)) : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) := by
  rw [readHom_congr (gGen_eq 𝔛 A ρ hρ), ← 𝔛.iota0_spec b]
  exact 𝔛.Meta_pin (𝔛.iota0 b)

variable [NeZero (M / p)]
  (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

theorem exists_residue_read_gGen_iota0 (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    ∃ h : (𝔛.Meta).ffEquiv.symm ((readHom (gGen 𝔛 A ρ hρ) (ιFin p (ΓM M H) hj)).hom (𝔛.iota0 b)) ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y := by
  have hyM : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by
    rw [hy, ← coe_read_gGen_iota0 𝔛 A ρ hρ b]
    exact SetLike.coe_mem _
  have e : (𝔛.Meta).ffEquiv.symm ((readHom (gGen 𝔛 A ρ hρ) (ιFin p (ΓM M H) hj)).hom (𝔛.iota0 b)) =
      ⟨coeffMap A.subtype y, hyM⟩ :=
    Subtype.ext (by rw [coe_read_gGen_iota0]; exact hy.symm)
  rw [e]
  exact Rpd.residue₁_coeffMap y hyM

theorem exists_coe_germ_gInf_iota0 (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ gInf 𝔛 A hA ρ hρ ⁻¹ᵁ WM 𝔛,
      ((((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ (gInf 𝔛 A hA ρ hρ ⁻¹ᵁ WM 𝔛) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
            (((gInf 𝔛 A hA ρ hρ).app (WM 𝔛)).hom
              (((ιFin p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b)))))) :
            JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y :=
  ⟨genericPoint_mem_gInf 𝔛 A hA ρ hρ, coe_read_gInf_iota0 𝔛 A hA ρ hρ b y hy⟩

end Frame

end PistarResidue
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb.PistarResidue"

set_option maxHeartbeats 6400000 in
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial PistarResidue in
open scoped MatrixGroups in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ))) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    letI V : (XO (ΓM M H) hj ρ).Opens :=
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
    letI gb : Γ(XO (ΓM M H) hj ρ, V) :=
      ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b)))
    ∃ (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V)
      (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    (∃ h : readA gb ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨readA gb, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y) ∧
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    (∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
      (((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom gb)) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y) :=
  ⟨genericPoint_mem_gInf 𝔛 A hA ρ hρ, genericPoint_mem_gGen 𝔛 A ρ hρ,
    exists_residue_read_gGen_iota0 𝔛 A ρ hρ θ Psp Rpd b y hy, exists_coe_germ_gInf_iota0 𝔛 A hA ρ hρ b y hy⟩

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb.PistarResidue"

end S_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb (solution)
