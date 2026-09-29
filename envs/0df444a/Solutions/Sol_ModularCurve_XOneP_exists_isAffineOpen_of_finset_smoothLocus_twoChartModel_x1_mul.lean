-- Prove2me | solution 1 for ModularCurve.XOneP.exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6e40226c-f9ef-5fa6-8b34-71b294417c04

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_finset_of_twoCharts
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian"

open Opposite

noncomputable section

namespace E9Cov

open ModularCurve.TwoChart

variable (R₀ : Type) [CommRing R₀] (F : Type) [Field F] [Algebra R₀ F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X₀" => ModularCurve.TwoChartModel R₀ F j

private theorem ιFin_eq_ιInf_iff (x₀ : XFin R₀ F j) (xi : XInf R₀ F j) :
    (ιFin R₀ F j).base x₀ = (ιInf R₀ F j).base xi ↔
      ∃ u : XMid R₀ F j, (fFin R₀ F j).base u = x₀ ∧ (fInf R₀ F j).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R₀ F j) (fInf R₀ F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      exact ⟨u, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · rcases fj with ⟨⟩
    · rcases fi with ⟨⟩
  · rintro ⟨u, rfl, rfl⟩
    change (fFin R₀ F j ≫ ιFin R₀ F j).base u = (fInf R₀ F j ≫ ιInf R₀ F j).base u
    rw [glue_condition]

private theorem range_fFin : Set.range (fFin R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R₀ F j))) :
      Set (PrimeSpectrum (chartAlgFin R₀ F j))) := by
  letI := (inclFin R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jChartFin R₀ F j)

private theorem range_fInf : Set.range (fInf R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R₀ F j))) :
      Set (PrimeSpectrum (chartAlgInf R₀ F j))) := by
  letI := (inclInf R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jInvChartInf R₀ F j)

private abbrev ιMid : XMid R₀ F j ⟶ X₀ := fFin R₀ F j ≫ ιFin R₀ F j

private scoped instance isOpenImmersion_ιMid : IsOpenImmersion (ιMid R₀ F j) := IsOpenImmersion.comp _ _

private theorem ιMid_eq' : ιMid R₀ F j = fInf R₀ F j ≫ ιInf R₀ F j := glue_condition R₀ F j

private theorem inclFin_j_mul_inclInf_jInv :
    inclFin R₀ F j (jChartFin R₀ F j) * inclInf R₀ F j (jInvChartInf R₀ F j) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ ((Fact.out : j ≠ 0))])

private abbrev U : (X₀).Opens := (ιFin R₀ F j) ''ᵁ ⊤

private abbrev V : (X₀).Opens := (ιInf R₀ F j) ''ᵁ ⊤

private theorem U_eq : U R₀ F j = chartFinOpen R₀ F j := (ιFin R₀ F j).image_top_eq_opensRange
private theorem V_eq : V R₀ F j = chartInfOpen R₀ F j := (ιInf R₀ F j).image_top_eq_opensRange

private def sF : Γ(XFin R₀ F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgFin R₀ F j))).inv (jChartFin R₀ F j)

private def sI : Γ(XInf R₀ F j, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (chartAlgInf R₀ F j))).inv (jInvChartInf R₀ F j)

private def f : Γ(X₀, U R₀ F j) := ((ιFin R₀ F j).appIso ⊤).inv (sF R₀ F j)

private def g : Γ(X₀, V R₀ F j) := ((ιInf R₀ F j).appIso ⊤).inv (sI R₀ F j)

private theorem basicOpen_sF : (XFin R₀ F j).basicOpen (sF R₀ F j) = (fFin R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sF, basicOpen_eq_of_affine]
  exact (range_fFin R₀ F j).symm

private theorem basicOpen_sI : (XInf R₀ F j).basicOpen (sI R₀ F j) = (fInf R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [sI, basicOpen_eq_of_affine]
  exact (range_fInf R₀ F j).symm

private theorem image_opensRange {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a]
    [IsOpenImmersion b] :
    b ''ᵁ a.opensRange = (a ≫ b).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, (Scheme.Hom.comp_apply a b u).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨a.base u, ⟨u, rfl⟩, (Scheme.Hom.comp_apply a b u).symm⟩

private theorem basicOpen_f : (X₀).basicOpen (f R₀ F j) = (ιMid R₀ F j).opensRange := by
  rw [f, ← Scheme.image_basicOpen, basicOpen_sF, image_opensRange]

private theorem opensRange_ιMid' : (fInf R₀ F j ≫ ιInf R₀ F j).opensRange = (ιMid R₀ F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_opensRange]
  rw [← ιMid_eq']

private theorem basicOpen_g : (X₀).basicOpen (g R₀ F j) = (ιMid R₀ F j).opensRange := by
  rw [g, ← Scheme.image_basicOpen, basicOpen_sI, image_opensRange, opensRange_ιMid']

private theorem U_inf_V : U R₀ F j ⊓ V R₀ F j = (ιMid R₀ F j).opensRange := by
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨x₀, -, hx₀⟩, ⟨xi, -, hxi⟩⟩ := hx
    obtain ⟨u, rfl, rfl⟩ := (ιFin_eq_ιInf_iff R₀ F j x₀ xi).mp (hx₀.trans hxi.symm)
    exact ⟨u, hx₀⟩
  · rintro x ⟨u, rfl⟩
    refine ⟨⟨(fFin R₀ F j).base u, trivial, rfl⟩, ⟨(fInf R₀ F j).base u, trivial, ?_⟩⟩
    change (fInf R₀ F j ≫ ιInf R₀ F j).base u = (fFin R₀ F j ≫ ιFin R₀ F j).base u
    rw [glue_condition]

private theorem presheaf_map_map_apply {Y : Scheme.{0}} {A B C : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op A ⟶ op C) (t : Γ(Y, A)) :
    Y.presheaf.map i' (Y.presheaf.map i t) = Y.presheaf.map i'' t := by
  rw [Subsingleton.elim i'' (i ≫ i'), Functor.map_comp, CommRingCat.comp_apply]

private theorem presheaf_map_map_map_apply {Y : Scheme.{0}} {A B C D : Y.Opens} (i : op A ⟶ op B) (i' : op B ⟶ op C)
    (i'' : op C ⟶ op D) (k : op A ⟶ op D) (t : Γ(Y, A)) :
    Y.presheaf.map i'' (Y.presheaf.map i' (Y.presheaf.map i t)) = Y.presheaf.map k t := by
  rw [presheaf_map_map_apply i i' (i ≫ i'), presheaf_map_map_apply (i ≫ i') i'' k]

private theorem app_res_f (W : (X₀).Opens) (hWU : W ≤ U R₀ F j) :
    (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R₀ F j)) =
      (XMid R₀ F j).presheaf.map (homOfLE le_top).op ((fFin R₀ F j).appTop (sF R₀ F j)) := by
  have step1 : (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWU).op (f R₀ F j)) =
      (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (ιMid R₀ F j).base).map (homOfLE hWU)).op
        ((ιMid R₀ F j).app (U R₀ F j) (f R₀ F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (ιMid R₀ F j).app (U R₀ F j) (f R₀ F j) =
      (fFin R₀ F j).app _ ((ιFin R₀ F j).app (U R₀ F j) (f R₀ F j)) := rfl
  have step4 : ∀ {V' : (XFin R₀ F j).Opens} (k : op ⊤ ⟶ op V'),
      (fFin R₀ F j).app V' ((XFin R₀ F j).presheaf.map k (sF R₀ F j)) =
        (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fFin R₀ F j).base).map k.unop).op
          ((fFin R₀ F j).appTop (sF R₀ F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, f, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_apply _ _ _ _

private theorem app_res_g (W : (X₀).Opens) (hWV : W ≤ V R₀ F j) :
    (ιMid R₀ F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R₀ F j)) =
      (XMid R₀ F j).presheaf.map (homOfLE le_top).op ((fInf R₀ F j).appTop (sI R₀ F j)) := by
  rw [Scheme.Hom.congr_app (ιMid_eq' R₀ F j) W, CommRingCat.comp_apply]
  have step1 : (fInf R₀ F j ≫ ιInf R₀ F j).app W ((X₀).presheaf.map (homOfLE hWV).op (g R₀ F j)) =
      (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R₀ F j ≫ ιInf R₀ F j).base).map (homOfLE hWV)).op
        ((fInf R₀ F j ≫ ιInf R₀ F j).app (V R₀ F j) (g R₀ F j)) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have step2 : (fInf R₀ F j ≫ ιInf R₀ F j).app (V R₀ F j) (g R₀ F j) =
      (fInf R₀ F j).app _ ((ιInf R₀ F j).app (V R₀ F j) (g R₀ F j)) := rfl
  have step4 : ∀ {V' : (XInf R₀ F j).Opens} (k : op ⊤ ⟶ op V'),
      (fInf R₀ F j).app V' ((XInf R₀ F j).presheaf.map k (sI R₀ F j)) =
        (XMid R₀ F j).presheaf.map ((TopologicalSpace.Opens.map (fInf R₀ F j).base).map k.unop).op
          ((fInf R₀ F j).appTop (sI R₀ F j)) := fun k => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  rw [step1, step2, g, Scheme.Hom.appIso_inv_app_apply, step4]
  exact presheaf_map_map_map_apply _ _ _ _ _

omit [Fact (j ≠ 0)] in
private theorem appTop_sF : (fFin R₀ F j).appTop (sF R₀ F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R₀ F j))).inv (inclFin R₀ F j (jChartFin R₀ F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclFin R₀ F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jChartFin R₀ F j)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

omit [Fact (j ≠ 0)] in
private theorem appTop_sI : (fInf R₀ F j).appTop (sI R₀ F j) =
    (Scheme.ΓSpecIso (CommRingCat.of (chartAlgMid R₀ F j))).inv (inclInf R₀ F j (jInvChartInf R₀ F j)) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (inclInf R₀ F j).toRingHom)
  have h' := congrArg (fun φ => φ.hom (jInvChartInf R₀ F j)) h
  simp only [CommRingCat.comp_apply] at h'
  exact h'.symm

private theorem res_f_mul_res_g :
    ((X₀).presheaf.map (homOfLE (inf_le_left : U R₀ F j ⊓ V R₀ F j ≤ U R₀ F j)).op).hom (f R₀ F j) *
      ((X₀).presheaf.map (homOfLE (inf_le_right : U R₀ F j ⊓ V R₀ F j ≤ V R₀ F j)).op).hom (g R₀ F j) = 1 := by
  have hWle : U R₀ F j ⊓ V R₀ F j ≤ (ιMid R₀ F j).opensRange := (U_inf_V R₀ F j).le

  haveI : IsIso ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j)) := Scheme.Hom.isIso_app _ _ hWle
  have hinj : Function.Injective ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j)) :=
    (ConcreteCategory.bijective_of_isIso ((ιMid R₀ F j).app (U R₀ F j ⊓ V R₀ F j))).1
  apply hinj
  rw [map_mul, map_one, app_res_f, app_res_g, appTop_sF, appTop_sI, ← map_mul, ← map_mul,
    inclFin_j_mul_inclInf_jInv, map_one, map_one]

private theorem exists_isAffineOpen_forall_mem (S : Finset ↥(X₀)) :
    ∃ W : (X₀).Opens, IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by
  have hU : IsAffineOpen (U R₀ F j) := by rw [U_eq]; exact isAffineOpen_chartFinOpen R₀ F j
  have hV : IsAffineOpen (V R₀ F j) := by rw [V_eq]; exact isAffineOpen_chartInfOpen R₀ F j
  have hUV : U R₀ F j ⊔ V R₀ F j = ⊤ := by rw [U_eq, V_eq]; exact twoChartCover R₀ F j
  exact AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_finset_of_twoCharts (modelTo R₀ F j)
    (U R₀ F j) (V R₀ F j) hU hV hUV (f R₀ F j) (g R₀ F j)
    ((U_inf_V R₀ F j).trans (basicOpen_f R₀ F j).symm) ((U_inf_V R₀ F j).trans (basicOpen_g R₀ F j).symm)
    (res_f_mul_res_g R₀ F j) S

end E9Cov
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul.E9Cov"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul.E9Cov"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)
    :
    ∀ (V : (Spec (CommRingCat.of A)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)).base x ∈ (V : (Spec (CommRingCat.of A)).Opens)) →
      ∃ W : (U : Scheme.{0}).Opens, IsAffineOpen W ∧
        W ≤ (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) ⁻¹ᵁ (V : (Spec (CommRingCat.of A)).Opens) ∧ ∀ x ∈ F, x ∈ W := by
  intro V F hF
  exact AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    (E9Cov.exists_isAffineOpen_forall_mem A (↥K) j) U
    ((ModularCurve.TwoChart.modelTo A (↥K) j) ⁻¹ᵁ (V : (Spec (CommRingCat.of A)).Opens)) F hF

end S_ModularCurve_XOneP_exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_isAffineOpen_of_finset_smoothLocus_twoChartModel_x1_mul (solution)
