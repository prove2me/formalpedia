-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/38f70a48-63b2-5739-ba16-21d4318615f5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

namespace CentreH

universe u

theorem exists_lift {X : Scheme.{u}} {B : CommRingCat.{u}} (f : X ⟶ Spec B) [UniversallyClosed f]
    {K : Type u} [Field K] (O : ValuationSubring K)
    (i₁ : Spec (CommRingCat.of K) ⟶ X) (i₂ : Spec (CommRingCat.of ↥O) ⟶ Spec B)
    (hsq : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ↥O K)) ≫ i₂) :
    ∃ ℓ : Spec (CommRingCat.of ↥O) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap ↥O K)) ≫ ℓ = i₁ ∧ ℓ ≫ f = i₂ := by
  let S : ValuativeCommSq f := { R := ↥O, K := K, i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }
  have hE : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  haveI : S.commSq.HasLift := hE S
  exact ⟨S.commSq.lift, S.commSq.fac_left, S.commSq.fac_right⟩

theorem SpecMap_app_top {X : Scheme.{u}} {R S : CommRingCat.{u}} (ψ : R ⟶ S) (ℓ : Spec R ⟶ X) (V : X.Opens)
    (e₁ : ℓ ⁻¹ᵁ V = ⊤) (e₂ : (Spec.map ψ ≫ ℓ) ⁻¹ᵁ V = ⊤) :
    (Spec.map ψ).app (ℓ ⁻¹ᵁ V) ≫ (Spec S).presheaf.map (eqToHom e₂.symm).op ≫ (Scheme.ΓSpecIso S).hom =
      (Spec R).presheaf.map (eqToHom e₁.symm).op ≫ (Scheme.ΓSpecIso R).hom ≫ ψ := by
  rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  show _ = _ ≫ (Spec.map ψ).app ⊤ ≫ _
  rw [Scheme.Hom.app_eq_appLE (Spec.map ψ) (U := ⊤), Scheme.Hom.map_appLE_assoc]
  rfl

theorem stalkClosedPointTo_SpecMap_comp_apply {X : Scheme.{u}} {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (ψ : R ⟶ S) (ℓ : Spec R ⟶ X) (V : X.Opens)
    (hR : ℓ.base (closedPoint R) ∈ V) (hS : (Spec.map ψ ≫ ℓ).base (closedPoint S) ∈ V) (g : Γ(X, V)) :
    Scheme.stalkClosedPointTo (Spec.map ψ ≫ ℓ) (X.presheaf.germ V _ hS g) =
      ψ (Scheme.stalkClosedPointTo ℓ (X.presheaf.germ V _ hR g)) := by
  have e₁ := Scheme.preimage_eq_top_of_closedPoint_mem ℓ hR
  have e₂ := Scheme.preimage_eq_top_of_closedPoint_mem (Spec.map ψ ≫ ℓ) hS
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.germ_stalkClosedPointTo (Spec.map ψ ≫ ℓ) V hS, Scheme.germ_stalkClosedPointTo_assoc ℓ V hR]
  suffices H : (Spec.map ψ ≫ ℓ).app V ≫ ((Spec S).presheaf.mapIso (eqToIso e₂.symm).op ≪≫ Scheme.ΓSpecIso S).hom =
      ℓ.app V ≫ ((Spec R).presheaf.mapIso (eqToIso e₁.symm).op ≪≫ Scheme.ΓSpecIso R).hom ≫ ψ by
    exact congrArg (fun k => (k : Γ(X, V) ⟶ S) g) H
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Iso.op_hom, Iso.op_hom,
    eqToIso.hom, eqToIso.hom, Category.assoc, ← SpecMap_app_top ψ ℓ V e₁ e₂]
  erw [Scheme.Hom.comp_app]
  erw [Category.assoc]

theorem stalkClosedPointTo_fromSpecStalk_comp_apply {X Y : Scheme.{u}} {S : CommRingCat.{u}} [IsLocalRing S]
    {x : X} (φ : X.presheaf.stalk x ⟶ S) [IsLocalHom φ.hom] (e : X ⟶ Y) (V : Y.Opens)
    (h : ((Spec.map φ ≫ X.fromSpecStalk x) ≫ e).base (closedPoint S) ∈ V) (hx : x ∈ e ⁻¹ᵁ V) (g : Γ(Y, V)) :
    Scheme.stalkClosedPointTo ((Spec.map φ ≫ X.fromSpecStalk x) ≫ e) (Y.presheaf.germ V _ h g) =
      φ (X.presheaf.germ (e ⁻¹ᵁ V) x hx (e.app V g)) := by
  show (Y.presheaf.germ V _ h ≫ Scheme.stalkClosedPointTo _) g = _
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc e V ((Spec.map φ ≫ X.fromSpecStalk x).base (closedPoint S)) h]
  erw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk φ (e ⁻¹ᵁ V) h]
  rfl

theorem isLocalHom_codRestrict {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar] (R₁ : RegularProlongation A F Fbar)
    (hAO : ∀ a : ↥A, ((algebraMap L F).comp A.subtype) a ∈ R₁.integers) :
    IsLocalHom (((algebraMap L F).comp A.subtype).codRestrict R₁.integers hAO) := by
  set ι := ((algebraMap L F).comp A.subtype).codRestrict R₁.integers hAO
  have hι : ∀ a : ↥A, ((ι a : ↥R₁.integers) : F) = algebraMap L F (a : L) := fun a => rfl
  constructor
  intro a ha
  have ha0 : (a : L) ≠ 0 := by
    intro h0
    apply not_isUnit_zero (M₀ := ↥R₁.integers)
    have : ι a = 0 := Subtype.ext (by rw [hι, h0, map_zero]; rfl)
    rwa [this] at ha
  obtain ⟨w, hw⟩ := ha.exists_right_inv
  have hwF : ((w : ↥R₁.integers) : F) = (algebraMap L F (a : L))⁻¹ := by
    have h1 : ((ι a : ↥R₁.integers) : F) * ((w : ↥R₁.integers) : F) = 1 := by
      rw [← Subring.coe_mul R₁.integers.toSubring]
      exact congrArg (fun z : ↥R₁.integers => (z : F)) hw
    rw [hι] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hinvA : (a : L)⁻¹ ∈ A := by
    rw [← R₁.algebraMap_mem_iff, map_inv₀, ← hwF]
    exact w.2
  exact IsUnit.of_mul_eq_one ⟨_, hinvA⟩ (Subtype.ext (mul_inv_cancel₀ ha0))

theorem isLocalHom_ofHom_symm {K L : Type u} [CommRing K] [CommRing L] (e : K ≃+* L) :
    IsLocalHom (CommRingCat.ofHom e.symm.toRingHom).hom := by
  constructor
  intro a ha
  have ha' : IsUnit (e.symm a) := by simpa using ha
  simpa using ha'.map e

theorem SpecMap_ffEquiv_fromSpecStalk_toBase {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L]
    (𝓜 : CurveModel K L) :
    Spec.map (CommRingCat.ofHom 𝓜.ffEquiv.symm.toRingHom) ≫ 𝓜.C.fromSpecStalk (genericPoint 𝓜.C) ≫ 𝓜.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  refine RingHom.ext fun a => ?_
  change 𝓜.ffEquiv.symm ((𝓜.toBase.stalkMap (genericPoint 𝓜.C))
    (((Spec (CommRingCat.of K)).presheaf.germ ⊤ _ trivial)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))) = algebraMap K L a
  rw [RingEquiv.symm_apply_eq, 𝓜.ffEquiv_algebraMap]
  erw [Scheme.Hom.germ_stalkMap_apply]
  rfl

end CentreH

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    ∃ c : ↥(XO (ΓM M H) hj ρ), (XO.toBase (ΓM M H) hj ρ).base c = IsLocalRing.closedPoint ↥A ∧
      ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
        (g : Γ(XO (ΓM M H) hj ρ, V)) (hc : c ∈ V),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      ∃ h : readA g ∈ Rpd.R₁.integers,
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V c hc g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0) := by
  classical

  let F : Type := ↥(xHFunctionFieldBar M H)
  let O : ValuationSubring F := Rpd.R₁.integers
  haveI := 𝔛.isProper
  let XA : Scheme.{0} := XO (ΓM M H) hj ρ
  let f : XA ⟶ Spec (CommRingCat.of ↥A) := XO.toBase (ΓM M H) hj ρ
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XA :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])

  have hAO : ∀ a : ↥A, ((algebraMap (AlgebraicClosure ℚ) F).comp A.subtype) a ∈ O :=
    fun a => (Rpd.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  let ιAO : ↥A →+* ↥O := ((algebraMap (AlgebraicClosure ℚ) F).comp A.subtype).codRestrict O hAO
  haveI hloc : IsLocalHom ιAO := CentreH.isLocalHom_codRestrict A Rpd.R₁ hAO
  let i₂ : Spec (CommRingCat.of ↥O) ⟶ Spec (CommRingCat.of ↥A) := Spec.map (CommRingCat.ofHom ιAO)
  let ψ : CommRingCat.of ↥O ⟶ CommRingCat.of F := CommRingCat.ofHom (algebraMap ↥O F)

  let ξ : ↥(𝔛.Meta).C := genericPoint (𝔛.Meta).C
  let φ : (𝔛.Meta).C.functionField ⟶ CommRingCat.of F := CommRingCat.ofHom (𝔛.Meta).ffEquiv.symm.toRingHom
  haveI hφloc : IsLocalHom φ.hom := CentreH.isLocalHom_ofHom_symm (𝔛.Meta).ffEquiv
  let j : Spec (CommRingCat.of F) ⟶ (𝔛.Meta).C := Spec.map φ ≫ (𝔛.Meta).C.fromSpecStalk ξ
  let e : (𝔛.Meta).C ⟶ XA := 𝔛.eeta ≫ prA
  let i₁ : Spec (CommRingCat.of F) ⟶ XA := j ≫ e
  have hjcp : j.base (closedPoint F) = ξ := by
    show ((𝔛.Meta).C.fromSpecStalk ξ).base ((Spec.map φ).base (closedPoint F)) = ξ
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hsq : i₁ ≫ f = Spec.map ψ ≫ i₂ := by

    have h1 : i₁ ≫ f = j ≫ (𝔛.Meta).toBase ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
      show (j ≫ 𝔛.eeta ≫ prA) ≫ pullback.snd _ _ = _
      simp only [Category.assoc, prA, pullback.lift_snd]
      rw [← Category.assoc 𝔛.eeta, 𝔛.heeta]
    have h2 : j ≫ (𝔛.Meta).toBase = Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) F)) := by
      show (Spec.map φ ≫ (𝔛.Meta).C.fromSpecStalk ξ) ≫ (𝔛.Meta).toBase = _
      rw [Category.assoc]
      exact CentreH.SpecMap_ffEquiv_fromSpecStalk_toBase (𝔛.Meta)
    have h3 : Spec.map ψ ≫ i₂ = Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) F)) ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [h1, ← Category.assoc, h2, h3]

  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ := CentreH.exists_lift f O i₁ i₂ hsq
  refine ⟨ℓ.base (closedPoint ↥O), ?_, ?_⟩
  · show (ℓ ≫ f).base (closedPoint ↥O) = closedPoint ↥A
    rw [hℓ₂]
    haveI : IsLocalHom (CommRingCat.ofHom ιAO).hom := hloc
    exact Spec_closedPoint
  · intro V hgenV g hcV

    let u : ↥O := (Scheme.stalkClosedPointTo ℓ) (XA.presheaf.germ V _ hcV g)
    have hy : (Spec.map ψ ≫ ℓ).base (closedPoint F) ∈ V := by
      rw [hℓ₁]
      show e.base (j.base (closedPoint F)) ∈ V
      rw [hjcp]
      exact hgenV
    have T2 := CentreH.stalkClosedPointTo_SpecMap_comp_apply ψ ℓ V hcV hy g
    have T1 : ∀ (m : Spec (CommRingCat.of F) ⟶ XA) (hm : m = j ≫ e) (hy : m.base (closedPoint F) ∈ V),
        (Scheme.stalkClosedPointTo m (XA.presheaf.germ V _ hy g) : F) = (𝔛.Meta).ffEquiv.symm
          ((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) ξ hgenV ((𝔛.eeta.app (prA ⁻¹ᵁ V)) ((prA.app V) g))) := by
      rintro m rfl hy'
      exact CentreH.stalkClosedPointTo_fromSpecStalk_comp_apply φ e V hy' hgenV g
    have hu := T1 _ hℓ₁ hy
    rw [T2] at hu

    have hunit : IsUnit (XA.presheaf.germ V _ hcV g) ↔ IsUnit u :=
      (isUnit_map_iff (Scheme.stalkClosedPointTo ℓ).hom _).symm
    suffices hfin : ∀ (r : F), r = (u : F) →
        ∃ h : r ∈ Rpd.R₁.integers, (IsUnit (XA.presheaf.germ V _ hcV g) ↔ Rpd.R₁.residue ⟨r, h⟩ ≠ 0) from
      hfin _ hu.symm
    rintro r rfl
    refine ⟨u.2, ?_⟩
    rw [hunit]
    exact ⟨fun h => Rpd.R₁.residue_ne_zero_of_isUnit h, fun h => Rpd.R₁.isUnit_of_residue_ne_zero h⟩

end S_ModularCurve_XHDRModelAtP_exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_base_eq_closedPoint_and_forall_readA_mem_integers_and_isUnit_germ_iff (solution)
