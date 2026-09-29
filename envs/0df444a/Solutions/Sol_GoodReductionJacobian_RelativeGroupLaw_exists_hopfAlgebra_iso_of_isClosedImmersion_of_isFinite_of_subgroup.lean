-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2ed72305-29a8-56b8-8605-02f0893896df

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace SubgrpHopf

variable {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}

def OneMem (L : RelativeGroupLaw k f) {C : Scheme.{u}} (ι : C ⟶ A) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)), ∃ P₀ : T ⟶ C, P₀ ≫ ι = (L.one t).1

def MulMem (L : RelativeGroupLaw k f) {C : Scheme.{u}} (ι : C ⟶ A) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      (∃ P₀ : T ⟶ C, P₀ ≫ ι = P.1) → (∃ Q₀ : T ⟶ C, Q₀ ≫ ι = Q.1) →
        (∃ R₀ : T ⟶ C, R₀ ≫ ι = (L.mul t P Q).1) ∧ (∃ S₀ : T ⟶ C, S₀ ≫ ι = (L.inv t P).1)

variable (L : RelativeGroupLaw k f) {C : Scheme.{u}} (ι : C ⟶ A) [IsClosedImmersion ι]

def toA {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (ι ≫ f)) : SchemeHomOver t f :=
  ⟨x.1 ≫ ι, by rw [Category.assoc]; exact x.2⟩

@[scoped simp] theorem toA_val {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (ι ≫ f)) :
    (toA ι x).1 = x.1 ≫ ι := rfl

theorem toA_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} :
    Function.Injective (toA (f := f) ι (T := T) (t := t)) := by
  intro x y h
  apply Subtype.ext
  have := congrArg Subtype.val h
  simpa [cancel_mono] using this

theorem toA_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t (ι ≫ f)) :
    toA ι (schemeHomOverComp ψ hψ x) = schemeHomOverComp ψ hψ (toA ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem toA_mem {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t (ι ≫ f)) :
    ∃ P₀ : T ⟶ C, P₀ ≫ ι = (toA ι x).1 :=
  ⟨x.1, rfl⟩

section ops

variable (hone : OneMem L ι) (hmul : MulMem L ι)

noncomputable def mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)) :
    SchemeHomOver t (ι ≫ f) :=
  ⟨(hmul t (toA ι x) (toA ι y) (toA_mem ι x) (toA_mem ι y)).1.choose, by
    rw [← Category.assoc, (hmul t (toA ι x) (toA ι y) (toA_mem ι x) (toA_mem ι y)).1.choose_spec]
    exact (L.mul t (toA ι x) (toA ι y)).2⟩

theorem toA_mulPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)) :
    toA ι (mulPt L ι hmul t x y) = L.mul t (toA ι x) (toA ι y) :=
  Subtype.ext (hmul t (toA ι x) (toA ι y) (toA_mem ι x) (toA_mem ι y)).1.choose_spec

noncomputable def onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) : SchemeHomOver t (ι ≫ f) :=
  ⟨(hone t).choose, by
    rw [← Category.assoc, (hone t).choose_spec]
    exact (L.one t).2⟩

theorem toA_onePt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toA ι (onePt L ι hone t) = L.one t :=
  Subtype.ext (hone t).choose_spec

noncomputable def invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (ι ≫ f)) :
    SchemeHomOver t (ι ≫ f) :=
  ⟨(hmul t (toA ι x) (toA ι x) (toA_mem ι x) (toA_mem ι x)).2.choose, by
    rw [← Category.assoc, (hmul t (toA ι x) (toA ι x) (toA_mem ι x) (toA_mem ι x)).2.choose_spec]
    exact (L.inv t (toA ι x)).2⟩

theorem toA_invPt {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (ι ≫ f)) :
    toA ι (invPt L ι hmul t x) = L.inv t (toA ι x) :=
  Subtype.ext (hmul t (toA ι x) (toA ι x) (toA_mem ι x) (toA_mem ι x)).2.choose_spec

end ops

noncomputable def restrict (hone : OneMem L ι) (hmul : MulMem L ι) : RelativeGroupLaw k (ι ≫ f) where
  mul t x y := mulPt L ι hmul t x y
  one t := onePt L ι hone t
  inv t x := invPt L ι hmul t x
  mul_assoc t x y z := toA_injective ι (by
    rw [toA_mulPt, toA_mulPt, toA_mulPt, toA_mulPt, L.mul_assoc])
  one_mul t x := toA_injective ι (by rw [toA_mulPt, toA_onePt, L.one_mul])
  mul_one t x := toA_injective ι (by rw [toA_mulPt, toA_onePt, L.mul_one])
  inv_mul_cancel t x := toA_injective ι (by rw [toA_mulPt, toA_invPt, L.inv_mul_cancel, toA_onePt])
  mul_natural t t' ψ hψ x y := toA_injective ι (by
    rw [toA_comp, toA_mulPt, L.mul_natural, toA_mulPt, toA_comp, toA_comp])

variable (hone : OneMem L ι) (hmul : MulMem L ι)

theorem toA_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)) :
    toA ι ((restrict L ι hone hmul).mul t x y) = L.mul t (toA ι x) (toA ι y) :=
  toA_mulPt L ι hmul t x y

theorem toA_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    toA ι ((restrict L ι hone hmul).one t) = L.one t :=
  toA_onePt L ι hone t

theorem toA_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (ι ≫ f)) :
    toA ι ((restrict L ι hone hmul).inv t x) = L.inv t (toA ι x) :=
  toA_invPt L ι hmul t x

theorem restrict_comm
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)) :
    (restrict L ι hone hmul).mul t x y = (restrict L ι hone hmul).mul t y x :=
  toA_injective ι (by rw [toA_mul, toA_mul, hcomm])

theorem schemeNsmul_zero : (restrict L ι hone hmul).schemeNsmul 0 =
    (ι ≫ f) ≫ ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 := by
  show ((restrict L ι hone hmul).nsmul (ι ≫ f) 0 RelativeGroupLaw.idPoint).1 = _
  rw [RelativeGroupLaw.nsmul_zero]
  exact (congrArg Subtype.val ((restrict L ι hone hmul).one_natural (𝟙 (Spec (CommRingCat.of k))) (ι ≫ f) (ι ≫ f)
    (Category.comp_id _))).symm

theorem pullback_fst_comp_eq_schemeKerStr (n : ℕ) :
    pullback.fst ((restrict L ι hone hmul).schemeNsmul n)
        ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ (ι ≫ f) =
      (restrict L ι hone hmul).schemeKerStr n := by
  have he : ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ (ι ≫ f) = 𝟙 _ :=
    ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).2
  calc pullback.fst ((restrict L ι hone hmul).schemeNsmul n)
          ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ (ι ≫ f)
      = pullback.fst ((restrict L ι hone hmul).schemeNsmul n)
          ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 ≫
            ((restrict L ι hone hmul).schemeNsmul n ≫ (ι ≫ f)) := by
        rw [RelativeGroupLaw.schemeNsmul_over]
    _ = (pullback.snd ((restrict L ι hone hmul).schemeNsmul n)
          ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 ≫
            ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1) ≫ (ι ≫ f) := by
        rw [← Category.assoc, pullback.condition]
    _ = (restrict L ι hone hmul).schemeKerStr n := by
        rw [Category.assoc, he, Category.comp_id]

theorem isIso_pullback_fst_zero :
    IsIso (pullback.fst ((restrict L ι hone hmul).schemeNsmul 0)
      ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1) := by
  have h0 := schemeNsmul_zero L ι hone hmul
  refine ⟨⟨pullback.lift (𝟙 C) (ι ≫ f) (by rw [Category.id_comp, h0]), ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact pullback_fst_comp_eq_schemeKerStr L ι hone hmul 0
  · rw [pullback.lift_fst]

variable [IsFinite (ι ≫ f)]

theorem isFinite_schemeKerStr (n : ℕ) : IsFinite ((restrict L ι hone hmul).schemeKerStr n) := by
  rw [← pullback_fst_comp_eq_schemeKerStr L ι hone hmul n]
  haveI : IsClosedImmersion ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).1 :=
    isClosedImmersion_of_comp_eq_id (ι ≫ f) _ ((restrict L ι hone hmul).one (𝟙 (Spec (CommRingCat.of k)))).2
  infer_instance

theorem flat_schemeKerStr (n : ℕ) : Flat ((restrict L ι hone hmul).schemeKerStr n) := by
  infer_instance

section Main

variable {k : Type u} [Field k]

theorem exists_algHom_of_over {H T : Type u} [CommRing H] [Algebra k H] [CommRing T] [Algebra k T]
    (y : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of H))
    (hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap k H)) = Spec.map (CommRingCat.ofHom (algebraMap k T))) :
    ∃ φ : H →ₐ[k] T, Spec.map (CommRingCat.ofHom φ.toRingHom) = y := by
  let ψ : CommRingCat.of H ⟶ CommRingCat.of T := Spec.preimage y
  have hψ : Spec.map ψ = y := Spec.map_preimage y
  have hcomp : CommRingCat.ofHom (algebraMap k H) ≫ ψ = CommRingCat.ofHom (algebraMap k T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hy]
  refine ⟨{ toRingHom := ψ.hom, commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => (CommRingCat.Hom.hom g) c) hcomp
    simpa using this
  · change Spec.map (CommRingCat.ofHom ψ.hom) = y
    simpa using hψ

theorem main {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    {C : Scheme.{u}} (ι : C ⟶ A) [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    (hone : OneMem L ι) (hmul : MulMem L ι) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H),
      Module.Finite k H ∧ Coalgebra.IsCocomm k H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ C)
        (e : ∀ (T : Type u) [CommRing T] [Algebra k T],
          WithConv (H →ₐ[k] T) →
            {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T))) f // ∃ P₀ : _ ⟶ C, P₀ ≫ ι = P.1}),
        IsIso j ∧
        j ≫ ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ : WithConv (H →ₐ[k] T)),
          ((e T φ).val : SchemeHomOver _ f).1 = Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫ ι) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T], Function.Bijective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
            (g : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) := by
  classical
  set LC := restrict L ι hone hmul with hLC

  haveI : IsAffineHom (ι ≫ f) := inferInstance
  haveI : IsSeparated (ι ≫ f) := inferInstance
  haveI : LocallyOfFiniteType (ι ≫ f) := inferInstance
  haveI hfinK : IsFinite (LC.schemeKerStr 0) := isFinite_schemeKerStr L ι hone hmul 0
  haveI : LocallyQuasiFinite (LC.schemeKerStr 0) := inferInstance
  haveI : QuasiCompact (LC.schemeKerStr 0) := inferInstance
  haveI : Flat (LC.schemeKerStr 0) := flat_schemeKerStr L ι hone hmul 0
  obtain ⟨H, instCR, instHopf, hfin, hflat, hcoc, j, e, hj, hopen, hclosed, hcover, hpts, hinj, hsurj, hmulE, hnat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
      LC (fun t x y => restrict_comm L ι hone hmul hcomm t x y) 0

  have hjsurj : Function.Surjective j.base := by
    intro x
    obtain ⟨y, hy⟩ := hcover x (Subsingleton.elim _ _)
    exact ⟨y, hy⟩
  haveI : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext x
    simp only [Scheme.Hom.opensRange, TopologicalSpace.Opens.coe_mk, Set.mem_range, TopologicalSpace.Opens.coe_top,
      Set.mem_univ, iff_true]
    exact hjsurj x
  haveI hfst : IsIso (pullback.fst (LC.schemeNsmul 0) (LC.one (𝟙 (Spec (CommRingCat.of k)))).1) :=
    isIso_pullback_fst_zero L ι hone hmul
  set p₁ := pullback.fst (LC.schemeNsmul 0) (LC.one (𝟙 (Spec (CommRingCat.of k)))).1 with hp₁
  have hp₁str : p₁ ≫ (ι ≫ f) = LC.schemeKerStr 0 := pullback_fst_comp_eq_schemeKerStr L ι hone hmul 0

  let jC : Spec (CommRingCat.of H) ⟶ C := j ≫ p₁
  have hjC : jC ≫ ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H)) := by
    simp only [jC, Category.assoc]
    rw [hp₁str, hj]

  let e' : ∀ (T : Type u) [CommRing T] [Algebra k T], WithConv (H →ₐ[k] T) →
      {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T))) f // ∃ P₀ : _ ⟶ C, P₀ ≫ ι = P.1} :=
    fun T _ _ φ => ⟨toA ι (e T φ).val, (e T φ).val.1, rfl⟩
  refine ⟨H, instCR, instHopf, hfin, hcoc, jC, e', inferInstance, hjC, ?_, ?_, ?_, ?_⟩
  ·
    intro T _ _ φ
    show ((e T φ).val).1 ≫ ι = _
    rw [hpts T φ]
    simp only [jC, Category.assoc]
  ·
    intro T _ _
    constructor
    · intro φ ψ h
      apply hinj T
      apply Subtype.ext
      apply toA_injective ι
      exact congrArg Subtype.val h
    · rintro ⟨P, P₀, hP₀⟩

      have hP₀t : P₀ ≫ (ι ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
        rw [← Category.assoc, hP₀]; exact P.2
      let y : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of H) := P₀ ≫ inv p₁ ≫ inv j
      have hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap k H)) = Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
        rw [← hjC]
        simp only [y, jC, Category.assoc, IsIso.inv_hom_id_assoc]
        exact hP₀t
      obtain ⟨φ, hφ⟩ := exists_algHom_of_over y hy
      refine ⟨WithConv.toConv φ, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show ((e T (WithConv.toConv φ)).val).1 ≫ ι = P.1
      rw [hpts T, ← hP₀]
      simp only [hφ, y, Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  ·
    intro T _ _ φ ψ
    show toA ι (e T (φ * ψ)).val = L.mul _ (toA ι (e T φ).val) (toA ι (e T ψ).val)
    rw [hmulE T φ ψ, toA_mul]
  ·
    intro T T' _ _ _ _ g φ
    show ((e T' (.toConv (g.comp φ.ofConv))).val).1 ≫ ι = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ ((e T φ).val.1 ≫ ι)
    rw [hnat T T' g φ, Category.assoc]

end Main

end SubgrpHopf
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup.SubgrpHopf"

theorem solution
    {k : Type u} [Field k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {C : Scheme.{u}} (ι : C ⟶ A) [IsClosedImmersion ι] [IsFinite (ι ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)), ∃ P₀ : T ⟶ C, P₀ ≫ ι = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      (∃ P₀ : T ⟶ C, P₀ ≫ ι = P.1) → (∃ Q₀ : T ⟶ C, Q₀ ≫ ι = Q.1) →
        (∃ R₀ : T ⟶ C, R₀ ≫ ι = (L.mul t P Q).1) ∧ (∃ S₀ : T ⟶ C, S₀ ≫ ι = (L.inv t P).1)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H),
      Module.Finite k H ∧ Coalgebra.IsCocomm k H ∧
      ∃ (j : Spec (CommRingCat.of H) ⟶ C)
        (e : ∀ (T : Type u) [CommRing T] [Algebra k T],
          WithConv (H →ₐ[k] T) →
            {P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k T))) f // ∃ P₀ : _ ⟶ C, P₀ ≫ ι = P.1}),
        IsIso j ∧
        j ≫ ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k H)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ : WithConv (H →ₐ[k] T)),
          ((e T φ).val : SchemeHomOver _ f).1 = Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫ ι) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T], Function.Bijective (e T)) ∧
        (∀ (T : Type u) [CommRing T] [Algebra k T] (φ ψ : WithConv (H →ₐ[k] T)),
          ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra k T] [CommRing T'] [Algebra k T']
            (g : T →ₐ[k] T') (φ : WithConv (H →ₐ[k] T)),
          ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1) :=
  SubgrpHopf.main L hcomm ι hone hmul

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_iso_of_isClosedImmersion_of_isFinite_of_subgroup (solution)
