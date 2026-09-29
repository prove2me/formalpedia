-- Prove2me | solution 1 for ModularCurve.XOneP.exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/75d48f00-52aa-5bdd-a62c-f03d0cb7665c

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

import Theorems.Thm_AlgebraicGeometry_exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

namespace DomExt

universe u

section ValOI

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (V : ValuationSubring Ω) (Fi : IntermediateField k Ω)

abbrev OI : Subring Ω := V.toSubring ⊓ Fi.toSubring

def inclOI : ↥(OI V Fi) →+* ↥Fi.toSubfield where
  toFun x := ⟨x.1, x.2.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inclOI_apply (x : ↥(OI V Fi)) : ((inclOI V Fi x : ↥Fi.toSubfield) : Ω) = (x : Ω) := rfl

theorem inclOI_injective : Function.Injective (inclOI V Fi) := fun a b h =>
  Subtype.ext (congrArg (fun z : ↥Fi.toSubfield => (z : Ω)) h)

theorem valuationRing_OI : ValuationRing ↥(OI V Fi) := by
  classical
  suffices hpre : PreValuationRing ↥(OI V Fi) from @ValuationRing.mk _ _ _ hpre
  refine ⟨fun a b => ?_⟩
  by_cases hb : (b : Ω) = 0
  · refine ⟨0, Or.inl (Subtype.ext ?_)⟩
    change (a : Ω) * 0 = b
    rw [mul_zero, hb]
  by_cases ha : (a : Ω) = 0
  · refine ⟨0, Or.inr (Subtype.ext ?_)⟩
    change (b : Ω) * 0 = a
    rw [mul_zero, ha]
  have haF : (a : Ω) ∈ Fi := a.2.2
  have hbF : (b : Ω) ∈ Fi := b.2.2
  rcases V.mem_or_inv_mem ((b : Ω) / a) with h | h
  · refine ⟨⟨(b : Ω) / a, h, Fi.div_mem hbF haF⟩, Or.inl (Subtype.ext ?_)⟩
    change (a : Ω) * ((b : Ω) / a) = b
    field_simp
  · refine ⟨⟨((b : Ω) / a)⁻¹, h, Fi.inv_mem (Fi.div_mem hbF haF)⟩, Or.inr (Subtype.ext ?_)⟩
    change (b : Ω) * ((b : Ω) / a)⁻¹ = a
    field_simp

theorem isFractionRing_OI :
    letI := (inclOI V Fi).toAlgebra
    IsFractionRing ↥(OI V Fi) ↥Fi.toSubfield := by
  letI := (inclOI V Fi).toAlgebra
  have halg : ∀ x : ↥(OI V Fi), algebraMap ↥(OI V Fi) ↥Fi.toSubfield x = inclOI V Fi x := fun _ => rfl
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
  ·
    have hy0 : ((y : ↥(OI V Fi)) : Ω) ≠ 0 := fun h0 =>
      nonZeroDivisors.coe_ne_zero y (Subtype.ext h0)
    refine isUnit_iff_ne_zero.2 fun h0 => hy0 ?_
    have := congrArg (fun z : ↥Fi.toSubfield => (z : Ω)) h0
    exact this
  · by_cases hzV : (z : Ω) ∈ V
    · refine ⟨(⟨z, hzV, z.2⟩, 1), ?_⟩
      change z * algebraMap ↥(OI V Fi) ↥Fi.toSubfield 1 = algebraMap ↥(OI V Fi) ↥Fi.toSubfield ⟨z, hzV, z.2⟩
      rw [map_one, mul_one, halg]
      exact Subtype.ext rfl
    · have hz0 : (z : Ω) ≠ 0 := fun h0 => hzV (h0 ▸ V.zero_mem)
      have hinv : ((z : Ω))⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left hzV
      have hinvF : ((z : Ω))⁻¹ ∈ Fi := Fi.inv_mem z.2
      refine ⟨(1, ⟨⟨((z : Ω))⁻¹, hinv, hinvF⟩,
        mem_nonZeroDivisors_of_ne_zero fun h0 => inv_ne_zero hz0 (congrArg Subtype.val h0)⟩), ?_⟩
      change z * algebraMap ↥(OI V Fi) ↥Fi.toSubfield ⟨((z : Ω))⁻¹, hinv, hinvF⟩ = algebraMap ↥(OI V Fi) ↥Fi.toSubfield 1
      rw [map_one, halg]
      apply Subtype.ext
      change (z : Ω) * ((z : Ω))⁻¹ = 1
      exact mul_inv_cancel₀ hz0
  · exact ⟨1, by rw [inclOI_injective V Fi h]⟩

end ValOI

theorem apply_algebraMap_eq_of_forall_pow_eq_one (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ') (l : L) :
    σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l := by
  let φ₀ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure ℚ)
  let φ₁ : L →ₐ[ℚ] AlgebraicClosure ℚ := (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).comp φ₀
  have hle : Algebra.adjoin ℚ {b : L | ∃ n : ℕ, n ∈ ({p} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} ≤
      AlgHom.equalizer φ₁ φ₀ := by
    refine Algebra.adjoin_le ?_
    rintro b ⟨n, hn, -, hb⟩
    rw [Set.mem_singleton_iff] at hn
    subst hn
    rw [SetLike.mem_coe, AlgHom.mem_equalizer]
    change σ (algebraMap L (AlgebraicClosure ℚ) b) = algebraMap L (AlgebraicClosure ℚ) b
    apply hσ
    rw [← map_pow, hb, map_one]
  have hl := hle (IsCyclotomicExtension.adjoin_roots (S := ({p} : Set ℕ)) (A := ℚ) (B := L) l)
  rw [AlgHom.mem_equalizer] at hl
  exact hl

open CategoryTheory AlgebraicGeometry in
theorem eq_of_spec_map_comp_eq {F Ω : Type} [Field F] [Field Ω] (i : F →+* Ω) {A : CommRingCat.{0}}
    (f₁ f₂ : Spec (CommRingCat.of F) ⟶ Spec A)
    (h : Spec.map (CommRingCat.ofHom i) ≫ f₁ = Spec.map (CommRingCat.ofHom i) ≫ f₂) : f₁ = f₂ := by
  obtain ⟨φ₁, rfl⟩ := Spec.map_surjective f₁
  obtain ⟨φ₂, rfl⟩ := Spec.map_surjective f₂
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  haveI : Mono (CommRingCat.ofHom i) :=
    ConcreteCategory.mono_of_injective (CommRingCat.ofHom i) (fun a b hab => i.injective hab)
  rw [cancel_mono] at h
  rw [h]

end DomExt

open DomExt in
theorem DomExt.main
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)) :
    ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
      (ρI : A →+* ↥(Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring))
      (hρI : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype.comp ρI =
        algebraMap A (AlgebraicClosure ℚ)),
      ∀ y ∈ ModularCurve.normFreePartAt (M * p) p, (∀ σ ∈ I, σ • y = y) →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 := by
  intro I hI hIμ ρI hρI y hy hfix

  obtain ⟨ybar, hybar⟩ := (h𝒜gen y).1 hy

  have hLfix : ∀ σ ∈ I, ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) =
      algebraMap L (AlgebraicClosure ℚ) ((1 : L ≃ₐ[ℚ] L) l) := fun σ hσ l => by
    rw [AlgEquiv.one_apply]
    exact apply_algebraMap_eq_of_forall_pow_eq_one p L σ (hIμ σ hσ) l

  have hinvD : ∀ σ ∈ I,
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ (gpts y).1 = (gpts y).1 := by
    intro σ hσ
    have h := hτpts σ 1 (hLfix σ hσ) y
    rw [hfix σ hσ, inv_one, hτ1, Category.comp_id] at h
    exact h.symm
  haveI : Mono ι.1 := ((IsClosedImmersion.iff_isFinite_and_mono ι.1).1 h𝒜cl).2
  have hinvA : ∀ σ ∈ I, Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ybar.1 = ybar.1 := by
    intro σ hσ
    rw [← cancel_mono ι.1, Category.assoc, hybar, hinvD σ hσ]

  obtain ⟨yF, hyF⟩ :=
    AlgebraicGeometry.exists_spec_map_comp_eq_of_forall_spec_map_comp_eq_of_forall_mem_iff
      (AlgebraicClosure ℚ) 𝒜 ybar.1
      ((fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => σ.toRingEquiv) ''
        ((I : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))))
      (by
        rintro _ ⟨σ, hσ, rfl⟩
        exact hinvA σ hσ)
      (IntermediateField.fixedField I).toSubfield
      (fun x => by
        change x ∈ IntermediateField.fixedField I ↔ _
        rw [IntermediateField.mem_fixedField_iff]
        constructor
        · rintro h _ ⟨σ, hσ, rfl⟩
          exact h σ hσ
        · intro h σ hσ
          exact h σ.toRingEquiv ⟨σ, hσ, rfl⟩)

  letI : ValuationRing ↥(OI Pl (IntermediateField.fixedField I)) := valuationRing_OI Pl _
  letI : Algebra ↥(OI Pl (IntermediateField.fixedField I)) ↥(IntermediateField.fixedField I).toSubfield :=
    (inclOI Pl (IntermediateField.fixedField I)).toAlgebra
  haveI : IsFractionRing ↥(OI Pl (IntermediateField.fixedField I)) ↥(IntermediateField.fixedField I).toSubfield :=
    isFractionRing_OI Pl _
  have hcomp : (IntermediateField.fixedField I).toSubfield.subtype.comp
      (algebraMap ↥(OI Pl (IntermediateField.fixedField I)) ↥(IntermediateField.fixedField I).toSubfield) =
      (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype :=
    RingHom.ext fun _ => rfl
  have hsq : CommSq yF
      (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(OI Pl (IntermediateField.fixedField I)) ↥(IntermediateField.fixedField I).toSubfield)))
      a (Spec.map (CommRingCat.ofHom ρI)) := by
    constructor
    apply eq_of_spec_map_comp_eq (IntermediateField.fixedField I).toSubfield.subtype
    rw [← Category.assoc, hyF, ybar.2, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hcomp, hρI]

  have hval : ValuativeCriterion a := by
    have h := h𝒜pr
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨⟨lift⟩⟩ := hval
    { R := ↥(OI Pl (IntermediateField.fixedField I))
      K := ↥(IntermediateField.fixedField I).toSubfield
      i₁ := yF
      i₂ := Spec.map (CommRingCat.ofHom ρI)
      commSq := hsq }
  have hfl : Spec.map (CommRingCat.ofHom
      (algebraMap ↥(OI Pl (IntermediateField.fixedField I)) ↥(IntermediateField.fixedField I).toSubfield)) ≫
        lift.default.l = yF := lift.default.fac_left
  have hfr : lift.default.l ≫ a = Spec.map (CommRingCat.ofHom ρI) := lift.default.fac_right

  refine ⟨⟨lift.default.l ≫ ι.1, by rw [Category.assoc, ι.2, hfr]⟩, ?_⟩
  change (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫
    lift.default.l ≫ ι.1
  rw [← hcomp, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, reassoc_of% hfl, reassoc_of% hyF, hybar]

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
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (φ : ModularCurve.HeckeAlgOne → SchemeHomOver D.toBase D.toBase)
    (τ : ∀ s : L ≃ₐ[ℚ] L,
      SchemeHomOver (D.toBase ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) D.toBase)
    (hφmul : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s x y) (φ t) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
          (NeronModelInfra.schemeHomOverComp x (φ t)) (NeronModelInfra.schemeHomOverComp y (φ t)))
    (hφpts : letI := ModularCurve.heckeModuleOneBar (M * p)
      ∀ (t : ModularCurve.HeckeAlgOne) (x : ModularCurve.JOne (M * p)), (gpts (t • x)).1 = (gpts x).1 ≫ (φ t).1)
    (hτ1 : (τ 1).1 = 𝟙 D.P) (hτmul : ∀ s s' : L ≃ₐ[ℚ] L, (τ (s * s')).1 = (τ s).1 ≫ (τ s').1)
    (hτφ : ∀ (t : ModularCurve.HeckeAlgOne) (s : L ≃ₐ[ℚ] L), (τ s).1 ≫ (φ t).1 = (φ t).1 ≫ (τ s).1)

    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hτpts : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (s : L ≃ₐ[ℚ] L),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ (τ s⁻¹).1)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))

    (𝒜 : Scheme.{0}) (a : 𝒜 ⟶ Spec (CommRingCat.of A)) (ι : SchemeHomOver a D.toBase)

    (h𝒜cl : IsClosedImmersion ι.1)

    (h𝒜pr : IsProper a) (h𝒜sm : Smooth a)
    (h𝒜conn : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
        ConnectedSpace ↥(pullback a s))

    (h𝒜grp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)),
        (∃ o : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp o ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one s) ∧
        (∀ x y : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul s
            (NeronModelInfra.schemeHomOverComp x ι) (NeronModelInfra.schemeHomOverComp y ι)) ∧
        (∀ x : SchemeHomOver s a, ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).inv s
            (NeronModelInfra.schemeHomOverComp x ι)))

    (h𝒜gen : ∀ x : ModularCurve.JOne (M * p),
        x ∈ ModularCurve.normFreePartAt (M * p) p ↔
          ∃ y : SchemeHomOver (specMap A (AlgebraicClosure ℚ)) a, y.1 ≫ ι.1 = (gpts x).1)

    (h𝒜hecke : ∀ (t : ModularCurve.HeckeAlgOne) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of A)) (x : SchemeHomOver s a),
        ∃ z : SchemeHomOver s a, NeronModelInfra.schemeHomOverComp z ι =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp x ι) (φ t)) :
    ∀ (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hI : I ≤ Pl.inertiaSubgroupIn ℚ)
      (hIμ : ∀ σ ∈ I, ∀ ζ' : AlgebraicClosure ℚ, ζ' ^ p = 1 → σ ζ' = ζ')
      (ρI : A →+* ↥(Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring))
      (hρI : (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype.comp ρI =
        algebraMap A (AlgebraicClosure ℚ)),
      ∀ y ∈ ModularCurve.normFreePartAt (M * p) p, (∀ σ ∈ I, σ • y = y) →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρI)) D.toBase,
          (gpts y).1 = Spec.map (CommRingCat.ofHom (Pl.toSubring ⊓ (IntermediateField.fixedField I).toSubring).subtype) ≫ z.1 :=
  DomExt.main p M hM hpM L ζ hζ K hK A hAp hζA j hj ε D hrep hsm hsep hin hcomm hΓA gpts φ τ hφmul hφpts hτ1 hτmul hτφ
    hgadd hτpts Pl hPl ρ hρ 𝒜 a ι h𝒜cl h𝒜pr h𝒜sm h𝒜conn h𝒜grp h𝒜gen h𝒜hecke

end S_ModularCurve_XOneP_exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_points_fixedValuationSubring_of_smul_eq_self_of_mem_normFreePart_twoChartModel_x1_mul (solution)
