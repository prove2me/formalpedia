-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8412919c-b9a6-52a7-9795-4ecde86fbb67

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_normModule_unit_iso
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsLocallyNoetherian Surjective Scheme.Modules.pullback Scheme.Hom IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme Flat Scheme.Hom.finrank_of_isPullback isLocallyNoetherian_of_isOpenImmersion Scheme.Modules.pullbackCongr Scheme.isBasis_affineOpens IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.resLE_eq_morphismRestrict LocallyOfFinitePresentation Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Modules.normModule Scheme.Modules.normModuleFunctor Scheme.Modules.nonempty_normModule_unit_iso"
namespace ZeroSectionTriv
p2m_open "AlgebraicGeometry"

section Squares

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {c' : C' ⟶ Spec (CommRingCat.of R)} (f : C' ⟶ C) (hf : f ≫ c = c')

theorem isPullback_curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (curveChange f hf t) (pullback.fst c' t) (pullback.fst c t) f := by
  have big : IsPullback (curveChange f hf t ≫ pullback.snd c t) (pullback.fst c' t) t (f ≫ c) := by
    rw [curveChange_snd, hf]
    exact (IsPullback.of_hasPullback c' t).flip
  have hcomm : curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
    simp only [curveChange, pullback.lift_fst]
  exact IsPullback.of_right big hcomm (IsPullback.of_hasPullback c t).flip

noncomputable def sliceAt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T) (hσ : σ ≫ t = 𝟙 _) :
    C ⟶ pullback c t :=
  pullback.lift (𝟙 C) (c ≫ σ) (by rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

@[scoped simp] theorem sliceAt_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c) t σ hσ ≫ pullback.fst c t = 𝟙 C :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem sliceAt_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c) t σ hσ ≫ pullback.snd c t = c ≫ σ :=
  pullback.lift_snd _ _ _

theorem sliceAt_curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) : sliceAt (c := c') t σ hσ ≫ curveChange f hf t = f ≫ sliceAt (c := c) t σ hσ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, sliceAt_fst, Category.comp_id]
    rw [show curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f by simp only [curveChange, pullback.lift_fst],
      ← Category.assoc, sliceAt_fst, Category.id_comp]
  · rw [Category.assoc, Category.assoc, curveChange_snd, sliceAt_snd, sliceAt_snd, ← Category.assoc, hf]

theorem isPullback_sliceAt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (σ : Spec (CommRingCat.of R) ⟶ T)
    (hσ : σ ≫ t = 𝟙 _) :
    IsPullback (sliceAt (c := c') t σ hσ) f (curveChange f hf t) (sliceAt (c := c) t σ hσ) := by
  refine IsPullback.of_right ?_ (sliceAt_curveChange f hf t σ hσ) (isPullback_curveChange_fst f hf t).flip
  rw [sliceAt_fst, sliceAt_fst]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

end Squares

section Restrict

variable {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X)
  (sq : IsPullback g' π' π g)

include sq in
theorem preimage_le (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) : π' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  intro x hx
  show (g' ≫ π).base x ∈ V
  rw [sq.w]
  exact hV' hx

include sq in

theorem isPullback_resLE (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') (preimage_le π g π' g' sq V V' hV'))
      (π'.resLE V' (π' ⁻¹ᵁ V') le_rfl) (π.resLE V (π ⁻¹ᵁ V) le_rfl) (g.resLE V V' hV') := by
  have big : IsPullback ((π' ⁻¹ᵁ V').ι ≫ g') (π' ∣_ V') π (V'.ι ≫ g) :=
    (isPullback_morphismRestrict π' V').flip.paste_horiz sq
  rw [← Scheme.Hom.resLE_comp_ι g' (preimage_le π g π' g' sq V V' hV'), ← Scheme.Hom.resLE_comp_ι g hV',
    ← Scheme.Hom.resLE_eq_morphismRestrict] at big
  have right : IsPullback (π ⁻¹ᵁ V).ι (π.resLE V (π ⁻¹ᵁ V) le_rfl) π V.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict π V).flip
  refine IsPullback.of_right big ?_ right
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, sq.w]

end Restrict

theorem isDomain_and_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    (hnorm : ∀ U : X.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(X, U)) (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) (show x ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsIntegrallyClosed Γ(X, U) := hnorm U hU
  obtain ⟨y, rfl⟩ : ∃ y : U, (y : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  haveI := hU.isLocalization_stalk y
  have hle : (hU.primeIdealOf y).asIdeal.primeCompl ≤ nonZeroDivisors Γ(X, U) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  have h1 : IsDomain (X.presheaf.stalk (y : X)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := (hU.primeIdealOf y).asIdeal.primeCompl) _ hle
  have h2 : IsIntegrallyClosed (X.presheaf.stalk (y : X)) :=
    isIntegrallyClosed_of_isLocalization (X.presheaf.stalk (y : X)) _ hle
  exact ⟨h1, h2⟩

theorem isLocalization_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] :
    IsLocalization ((Ideal.span {(p : ℤ)}).primeCompl) (GaloisRep.ratLocalizedAt p) := by
  have hcomp : ∀ s : ℤ, s ∈ (Ideal.span {(p : ℤ)}).primeCompl ↔ s.natAbs.Coprime p := by
    intro s
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out,
      Int.natCast_dvd]
  have hcoe : ∀ z : ℤ, ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) z : GaloisRep.ratLocalizedAt p) : ℚ) = z := fun z => by
    simp
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨s, hs⟩
    rw [hcomp] at hs
    have hs0 : (s : ℚ) ≠ 0 := by
      intro h
      have : s = 0 := by exact_mod_cast h
      subst this
      simp [Nat.coprime_zero_left, hp.out.ne_one] at hs
    have hmem : ((s : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt p := by
      show ((s : ℚ)⁻¹).den.Coprime p
      rw [Rat.inv_intCast_den, if_neg (by exact_mod_cast hs0)]
      exact hs
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) s : GaloisRep.ratLocalizedAt p) : ℚ) * (s : ℚ)⁻¹ = 1
    rw [hcoe, mul_inv_cancel₀ hs0]
  ·
    intro z
    have hz : (z : ℚ).den.Coprime p := z.2
    refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), (hcomp _).mpr (by simpa using hz)⟩⟩, Subtype.ext ?_⟩
    show (z : ℚ) * ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) ((z : ℚ).den : ℤ) : GaloisRep.ratLocalizedAt p) : ℚ) =
      ((algebraMap ℤ (GaloisRep.ratLocalizedAt p) (z : ℚ).num : GaloisRep.ratLocalizedAt p) : ℚ)
    rw [hcoe, hcoe, Int.cast_natCast, Rat.mul_den_eq_num]
  ·
    intro x y h
    refine ⟨1, ?_⟩
    have h' := congrArg (fun w : GaloisRep.ratLocalizedAt p => (w : ℚ)) h
    simp only [hcoe, Int.cast_inj] at h'
    rw [h']

theorem isNoetherianRing_R (p : ℕ) [Fact p.Prime] : IsNoetherianRing (R p) := by
  haveI := isLocalization_ratLocalizedAt p
  exact IsLocalization.isNoetherianRing (Ideal.span {(p : ℤ)}).primeCompl _ inferInstance

end AlgebraicGeometry.ZeroSectionTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry.ZeroSectionTriv"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι IsLocallyNoetherian Surjective Scheme.Modules.pullback Scheme.Hom IsFinite isPullback_morphismRestrict LocallyOfFiniteType Spec IsIntegral Scheme Flat Scheme.Hom.finrank_of_isPullback isLocallyNoetherian_of_isOpenImmersion Scheme.Modules.pullbackCongr Scheme.isBasis_affineOpens IsAffineOpen Scheme.Modules Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.resLE_eq_morphismRestrict LocallyOfFinitePresentation Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit Scheme.Modules.nonempty_pullback_normModule_iso Scheme.Modules.normModule Scheme.Modules.normModuleFunctor Scheme.Modules.nonempty_normModule_unit_iso"
namespace ZeroSectionTriv
p2m_open "AlgebraicGeometry"

open ModularCurve ModularCurve.DRLevel AlgebraicGeometry.RelPicard

noncomputable def pbComp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅ (Scheme.Modules.pullback (f ≫ g)).obj N :=
  (Scheme.Modules.pullbackComp f g).app N

noncomputable def pbCongr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (N : Y.Modules) :
    (Scheme.Modules.pullback f).obj N ≅ (Scheme.Modules.pullback g).obj N :=
  (Scheme.Modules.pullbackCongr h).app N

set_option maxHeartbeats 3200000 in

theorem nonempty_iso_unit_of_slice
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (π₁ π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (h0 : ∀ L : (pullback (toBase (N₀ * ℓ) p) D.toBase).Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm (curveChange π₂.1 π₂.2 D.toBase) L))
    (he : ∀ (W : (pullback (toBase N₀ p) D.toBase).Opens) (d : ℕ), Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) → LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) →
          (∀ y : W, ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W).finrank y = d) →
          ∀ L : (pullback (toBase (N₀ * ℓ) p) D.toBase).Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback W.ι).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) L) ≅
              Scheme.Modules.normModule ((curveChange π₂.1 π₂.2 D.toBase) ∣_ W) d ((Scheme.Modules.pullback ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ W).ι).obj L)))
    (V : (X N₀ p).Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : X N₀ p, ringKrullDim ((X N₀ p).presheaf.stalk x) ≤ 1 → x ∈ V) :
    Nonempty ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase)).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅ 𝟙_ (X N₀ p).Modules) := by
  haveI := 𝔓.isIntegral
  haveI := 𝔓.lfp
  have hP : Scheme.Modules.IsInvertible hD.poincare.L := hD.poincare.isInvertible
  have hL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L) := hP.pullback _
  have hM : Scheme.Modules.IsInvertible (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) := h0 _ hL

  have hPz : Nonempty ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase)).obj hD.poincare.L ≅ 𝟙_ (X N₀ p).Modules) := by
    let j : X N₀ p ⟶ pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p)))) := pullback.lift (𝟙 _) (toBase N₀ p) (by simp)
    have hj : j ≫ baseChangeSnd (toBase N₀ p) (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase) = (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) := by
      apply pullback.hom_ext
      · rw [Category.assoc, sliceAt_fst, baseChangeSnd, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
          Category.id_comp]
      · rw [Category.assoc, sliceAt_snd, baseChangeSnd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
    exact ⟨pbCongr hj.symm _ ≪≫ (pbComp j _ _).symm ≪≫ (Scheme.Modules.pullback j).mapIso hD.zero.some ≪≫
      Scheme.Modules.pullbackUnitIso j⟩

  have sqF : IsPullback (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst (toBase N₀ p) D.toBase) := (isPullback_curveChange_fst π₂.1 π₂.2 D.toBase).flip
  have sqZ : IsPullback (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) := isPullback_sliceAt π₂.1 π₂.2 D.toBase D.zeroSection D.zeroSection_toBase
  haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance

  have sqFV := isPullback_resLE π₂.1 (pullback.fst (toBase N₀ p) D.toBase) (curveChange π₂.1 π₂.2 D.toBase) (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) sqF V ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) le_rfl
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at sqFV
  haveI : Flat ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @Flat) sqFV inferInstance
  haveI : LocallyOfFinitePresentation ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sqFV inferInstance
  haveI : IsFinite (π₂.1 ∣_ V) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict π₂.1 V).flip inferInstance
  haveI : IsFinite ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict (curveChange π₂.1 π₂.2 D.toBase) ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).flip inferInstance
  have hrkD : ∀ y : ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V), ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).finrank y = d := fun y => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sqFV y]
    exact hrk _

  obtain ⟨e₁⟩ := he ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) d inferInstance inferInstance hrkD _ hL

  have hVz : V ≤ (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) := by
    intro x hx
    show ((ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) ≫ (pullback.fst (toBase N₀ p) D.toBase)).base x ∈ V
    rw [sliceAt_fst]
    exact hx
  have sqZV := isPullback_resLE (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at sqZV

  obtain ⟨e₂⟩ := Scheme.Modules.nonempty_pullback_normModule_iso ((curveChange π₂.1 π₂.2 D.toBase) ∣_ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) d hrkD
    ((ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz) (π₂.1 ∣_ V)
    ((ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V) (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz))
    sqZV (hL.pullback _)

  have hcomm : (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V)
      (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz) ≫ ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).ι ≫ (curveChange π₁.1 π₁.2 D.toBase) =
      ((π₂.1 ⁻¹ᵁ V).ι ≫ π₁.1) ≫ (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) := by
    rw [Scheme.Hom.resLE_comp_ι_assoc, Category.assoc, sliceAt_curveChange π₁.1 π₁.2]
  obtain ⟨u⟩ := hPz
  let e₃ : (Scheme.Modules.pullback ((ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)) (π₂.1 ⁻¹ᵁ V)
      (preimage_le (curveChange π₂.1 π₂.2 D.toBase) (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) π₂.1 (ZeroSectionTriv.sliceAt (c := (toBase (N₀ * ℓ) p)) D.toBase D.zeroSection D.zeroSection_toBase) sqZ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz))).obj
      ((Scheme.Modules.pullback ((curveChange π₂.1 π₂.2 D.toBase) ⁻¹ᵁ ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).ι).obj ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      𝟙_ _ :=
    (Scheme.Modules.pullback _).mapIso (pbComp _ _ _) ≪≫ pbComp _ _ _ ≪≫ pbCongr hcomm _ ≪≫ (pbComp _ _ _).symm ≪≫
      (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackUnitIso _

  obtain ⟨e₄⟩ := Scheme.Modules.nonempty_normModule_unit_iso (π₂.1 ∣_ V) d hrk
  let e₅ := (Scheme.Modules.normModuleFunctor (π₂.1 ∣_ V) d).mapIso e₃ ≪≫ e₄

  have hcomm' : (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase).resLE ((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V) V hVz ≫ (((pullback.fst (toBase N₀ p) D.toBase) ⁻¹ᵁ V)).ι = V.ι ≫ (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) := Scheme.Hom.resLE_comp_ι _ _
  have φV : Nonempty ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase)).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L))) ≅
      (Scheme.Modules.pullback V.ι).obj (𝟙_ (X N₀ p).Modules)) :=
    ⟨pbComp _ _ _ ≪≫ pbCongr hcomm'.symm _ ≪≫ (pbComp _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e₁ ≪≫ e₂ ≪≫
      (by exact e₅) ≪≫ (Scheme.Modules.pullbackUnitIso V.ι).symm⟩

  haveI : IsLocallyNoetherian (X N₀ p) := by
    haveI := isNoetherianRing_R p
    haveI : IsLocallyNoetherian (pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))) := inferInstance
    let jj : X N₀ p ⟶ pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p)))) := pullback.lift (𝟙 (X N₀ p)) (toBase N₀ p) (by simp)
    haveI : IsIso jj := ⟨⟨pullback.fst _ _, pullback.lift_fst _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, Category.comp_id]⟩⟩
    exact isLocallyNoetherian_of_isOpenImmersion jj
  have hst := isDomain_and_isIntegrallyClosed_stalk (X := X N₀ p) 𝔓.normal
  obtain ⟨φ⟩ := φV
  obtain ⟨⟨ψ, hψ, -⟩, hiso⟩ :=
    Scheme.Modules.IsInvertible.existsUnique_pullback_map_eq_of_isIntegrallyClosed_stalk hst V hVcodim
      (hM.pullback _) (Scheme.Modules.isInvertible_unit _) φ.hom
  exact ⟨@asIso _ _ _ _ ψ (hiso ψ hψ inferInstance)⟩

end AlgebraicGeometry.ZeroSectionTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry.ZeroSectionTriv"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit.AlgebraicGeometry.ZeroSectionTriv"

open AlgebraicGeometry.ZeroSectionTriv in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]

    (π₁ π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] [IsIntegral ↑(pullback (toBase N₀ p) D.toBase)]
    (hnorm : ∀ U : (pullback (toBase N₀ p) D.toBase).Opens, IsAffineOpen U →
      IsIntegrallyClosed Γ(pullback (toBase N₀ p) D.toBase, U))
    [LocallyOfFiniteType D.toBase]

    (Nm : ∀ ⦃X Y : Scheme.{0}⦄, (X ⟶ Y) → X.Modules → Y.Modules)
    (hNm :
      ∀ ⦃X Y : Scheme.{0}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧

        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧

        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧

        (∀ ⦃X' Y' : Scheme.{0}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧

        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))))
    (hinv : Scheme.Modules.IsInvertible
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)))

    (V : (X N₀ p).Opens) (d : ℕ) [Flat (π₂.1 ∣_ V)] [LocallyOfFinitePresentation (π₂.1 ∣_ V)]
    (hrk : ∀ y : V, (π₂.1 ∣_ V).finrank y = d)
    (hVcodim : ∀ x : X N₀ p, ringKrullDim ((X N₀ p).presheaf.stalk x) ≤ 1 → x ∈ V) :

    Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p)
        (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase))).obj
      (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))).ringCatSheaf) ∧

    Nonempty (((RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf)
        (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) hinv).pullbackAlong
        ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
      (RigidifiedLineBundle.unit (c := toBase N₀ p) (ε := 𝔓.εinf) (𝟙 _)).L) := by
  haveI := 𝔓.isIntegral

  have sqF : IsPullback (pullback.fst (toBase (N₀ * ℓ) p) D.toBase) (curveChange π₂.1 π₂.2 D.toBase) π₂.1 (pullback.fst (toBase N₀ p) D.toBase) := (isPullback_curveChange_fst π₂.1 π₂.2 D.toBase).flip
  haveI : IsFinite (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @IsFinite) sqF inferInstance
  haveI : Surjective (curveChange π₂.1 π₂.2 D.toBase) := MorphismProperty.of_isPullback (P := @Surjective) sqF inferInstance
  obtain ⟨h0, -, -, -, -, he⟩ := hNm (curveChange π₂.1 π₂.2 D.toBase) hnorm

  obtain ⟨u⟩ := nonempty_iso_unit_of_slice N₀ p hpN₀ 𝔓 ℓ π₁ π₂ D hD Nm h0 he V d hrk hVcodim

  have hs : (pullback.fst (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))) ≫ (ZeroSectionTriv.sliceAt (c := (toBase N₀ p)) D.toBase D.zeroSection D.zeroSection_toBase) = (baseChangeSnd (toBase N₀ p) (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, sliceAt_fst, Category.comp_id, baseChangeSnd, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, sliceAt_snd, baseChangeSnd, pullback.lift_snd, ← Category.assoc, pullback.condition,
        Category.comp_id]
  have h1 : Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase))).obj (Nm (curveChange π₂.1 π₂.2 D.toBase) ((Scheme.Modules.pullback (curveChange π₁.1 π₁.2 D.toBase)).obj hD.poincare.L)) ≅
      SheafOfModules.unit (pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))).ringCatSheaf) :=
    ⟨pbCongr hs.symm _ ≪≫ (pbComp _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso u ≪≫ Scheme.Modules.pullbackUnitIso _⟩
  refine ⟨h1, ?_⟩

  obtain ⟨α⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := 𝔓.εinf) (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase) hinv
  obtain ⟨β⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := 𝔓.εinf) (hinv.pullback _)
    (Scheme.Modules.isInvertible_unit _) h1.some
  obtain ⟨γ⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (RigidifiedLineBundle.unit (c := (toBase N₀ p)) (ε := 𝔓.εinf) (𝟙 (Spec (CommRingCat.of (R p)))))
  exact ⟨α ≪≫ β ≪≫ γ⟩

end S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackAlong_zeroSection_ofInvertible_norm_pullback_poincare_iso_unit (solution)
