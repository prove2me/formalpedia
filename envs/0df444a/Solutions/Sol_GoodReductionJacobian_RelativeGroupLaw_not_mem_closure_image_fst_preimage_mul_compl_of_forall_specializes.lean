-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6bcd3216-fc7f-5f46-9a3b-5661a91d7049

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Topology

universe u

namespace P2mBadClosureSol

variable {R : Type u} [CommRing R]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    schemeHomOverComp ψ hψ (LB.inv t x) = LB.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := LB.pointGroup t'
  have h1 : LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x)) (schemeHomOverComp ψ hψ x) = LB.one t' := by
    rw [← LB.mul_natural, LB.inv_mul_cancel, LB.one_natural]

  have h2 : LB.mul t' (LB.inv t' (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) = LB.one t' :=
    LB.inv_mul_cancel t' _
  calc schemeHomOverComp ψ hψ (LB.inv t x)
      = LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x)) (LB.one t') := (LB.mul_one t' _).symm
    _ = LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x))
          (LB.mul t' (schemeHomOverComp ψ hψ x) (LB.inv t' (schemeHomOverComp ψ hψ x))) := by
          rw [LB.mul_inv_cancel]
    _ = LB.mul t' (LB.mul t' (schemeHomOverComp ψ hψ (LB.inv t x)) (schemeHomOverComp ψ hψ x))
          (LB.inv t' (schemeHomOverComp ψ hψ x)) := by rw [LB.mul_assoc]
    _ = LB.inv t' (schemeHomOverComp ψ hψ x) := by rw [h1, LB.one_mul]

noncomputable def rightMul {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ B :=
  (LB.mul (pullback.snd g t₀ ≫ t₀) ⟨pullback.fst g t₀, pullback.condition⟩
      (schemeHomOverComp (pullback.snd g t₀) rfl σ)).1

theorem rightMul_comp {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightMul LB t₀ σ ≫ g = pullback.snd g t₀ ≫ t₀ :=
  (LB.mul _ _ _).2

noncomputable def rightTrans {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : pullback g t₀ ⟶ pullback g t₀ :=
  pullback.lift (rightMul LB t₀ σ) (pullback.snd g t₀) (rightMul_comp LB t₀ σ)

@[scoped simp] theorem rightTrans_fst {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightTrans LB t₀ σ ≫ pullback.fst g t₀ = rightMul LB t₀ σ :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem rightTrans_snd {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : rightTrans LB t₀ σ ≫ pullback.snd g t₀ = pullback.snd g t₀ :=
  pullback.lift_snd _ _ _

theorem comp_rightMul {T₀ T : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) (ψ : T ⟶ pullback g t₀) (t' : T ⟶ Spec (CommRingCat.of R))
    (hψ : ψ ≫ (pullback.snd g t₀ ≫ t₀) = t') :
    ψ ≫ rightMul LB t₀ σ =
      (LB.mul t' ⟨ψ ≫ pullback.fst g t₀, by rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ, Category.assoc]⟩
        ⟨ψ ≫ pullback.snd g t₀ ≫ σ.1, by rw [Category.assoc, Category.assoc, σ.2, ← Category.assoc, ← hψ, Category.assoc]⟩).1 := by
  have h := LB.mul_natural (pullback.snd g t₀ ≫ t₀) t' ψ hψ
    ⟨pullback.fst g t₀, pullback.condition⟩ (schemeHomOverComp (pullback.snd g t₀) rfl σ)
  have h1 := congrArg Subtype.val h
  simp only [schemeHomOverComp_coe] at h1
  unfold rightMul
  rw [h1]
  congr 2

theorem rightTrans_comp_rightTrans_inv {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) :
    rightTrans LB t₀ σ ≫ rightTrans LB t₀ (LB.inv t₀ σ) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, rightTrans_fst, Category.id_comp,
      comp_rightMul LB t₀ (LB.inv t₀ σ) (rightTrans LB t₀ σ) (pullback.snd g t₀ ≫ t₀)
        (by rw [← Category.assoc, rightTrans_snd])]

    have e1 : (⟨rightTrans LB t₀ σ ≫ pullback.fst g t₀, by
          rw [Category.assoc, pullback.condition, ← Category.assoc, rightTrans_snd]⟩ :
          SchemeHomOver (pullback.snd g t₀ ≫ t₀) g) =
        LB.mul (pullback.snd g t₀ ≫ t₀) ⟨pullback.fst g t₀, pullback.condition⟩
          (schemeHomOverComp (pullback.snd g t₀) rfl σ) := by
      apply Subtype.ext; simp only [rightTrans_fst]; rfl
    have e2 : (⟨rightTrans LB t₀ σ ≫ pullback.snd g t₀ ≫ (LB.inv t₀ σ).1, by
          rw [Category.assoc, Category.assoc, (LB.inv t₀ σ).2, ← Category.assoc, rightTrans_snd]⟩ :
          SchemeHomOver (pullback.snd g t₀ ≫ t₀) g) =
        LB.inv (pullback.snd g t₀ ≫ t₀) (schemeHomOverComp (pullback.snd g t₀) rfl σ) := by
      rw [← inv_natural LB t₀ (pullback.snd g t₀ ≫ t₀) (pullback.snd g t₀) rfl σ]
      apply Subtype.ext; simp only [schemeHomOverComp_coe]; rw [← Category.assoc, rightTrans_snd]
    rw [e1, e2, LB.mul_assoc, LB.mul_inv_cancel, LB.mul_one]
  · rw [Category.assoc, rightTrans_snd, rightTrans_snd, Category.id_comp]

theorem isIso_rightTrans {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R))
    (σ : SchemeHomOver t₀ g) : IsIso (rightTrans LB t₀ σ) := by
  refine ⟨⟨rightTrans LB t₀ (LB.inv t₀ σ), rightTrans_comp_rightTrans_inv LB t₀ σ, ?_⟩⟩
  have h := rightTrans_comp_rightTrans_inv LB t₀ (LB.inv t₀ σ)

  have hii : LB.inv t₀ (LB.inv t₀ σ) = σ := by
    letI := LB.pointGroup t₀
    exact inv_inv σ
  rwa [hii] at h

section Top

variable [IsDomain R] [IsDiscreteValuationRing R] [Smooth g] [IsSeparated g] [QuasiCompact g]

theorem base_fst_eq (s₀ : B) (x : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) :
    g.base ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base x) = g.base s₀ := by
  show (pullback.fst g (B.fromSpecResidueField s₀ ≫ g) ≫ g) x = g.base s₀
  rw [pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem exists_specializes_fst_eq (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (e : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (y : B) (hy : g.base y = g.base s₀)
    (hye : y ⤳ (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e) :
    ∃ w : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)),
      w ⤳ e ∧ (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base w = y := by

  let t : ↑(Spec (CommRingCat.of R)) := g.base s₀
  let ιt := (Spec (CommRingCat.of R)).fromSpecResidueField t
  let σb : Spec (B.residueField s₀) ⟶ Spec ((Spec (CommRingCat.of R)).residueField t) :=
    Spec.map (g.residueFieldMap s₀)
  have hστ : σb ≫ ιt = B.fromSpecResidueField s₀ ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g s₀
  let fT := pullback.snd g ιt
  let fι := pullback.fst g ιt
  let p' := pullback.fst fT σb
  let E : pullback fT σb ≅ pullback g (B.fromSpecResidueField s₀ ≫ g) :=
    pullbackLeftPullbackSndIso g ιt σb ≪≫ pullback.congrHom rfl hστ
  have hE : E.hom ≫ pullback.fst g (B.fromSpecResidueField s₀ ≫ g) = p' ≫ fι := by
    simp only [E, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.lift_fst,
      Category.comp_id]
    exact pullbackLeftPullbackSndIso_hom_fst g ιt σb

  haveI : Flat σb := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  haveI : Flat p' := inferInstance
  have hgen : GeneralizingMap p'.base := Flat.generalizingMap p'

  set e' := E.inv.base e with he'
  have hEe : E.hom.base e' = e := by
    rw [he', ← TopCat.comp_app, ← Scheme.Hom.comp_base, Iso.inv_hom_id]; rfl
  have hpe : (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e = fι.base (p'.base e') := by
    rw [← hEe, ← TopCat.comp_app, ← Scheme.Hom.comp_base, hE, Scheme.Hom.comp_base, TopCat.comp_app]
  obtain ⟨yF, hyF⟩ : y ∈ Set.range (g.fiberι t) := by
    rw [Scheme.Hom.range_fiberι]; exact hy
  have hyF' : yF ⤳ p'.base e' := by
    rw [hpe, ← hyF] at hye
    exact (g.fiberι t).isEmbedding.isInducing.specializes_iff.mp hye
  obtain ⟨w', hw'e', hpw'⟩ := hgen hyF'
  refine ⟨E.hom.base w', ?_, ?_⟩
  · rw [← hEe]; exact hw'e'.map E.hom.continuous
  · rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, hE, Scheme.Hom.comp_base, TopCat.comp_app, hpw']
    exact hyF

omit LB in

theorem eq_of_ne_closedPoint (a b : ↑(Spec (CommRingCat.of R)))
    (ha : a ≠ IsLocalRing.closedPoint R) (hb : b ≠ IsLocalRing.closedPoint R) : a = b := by
  have key : ∀ c : ↑(Spec (CommRingCat.of R)), c ≠ IsLocalRing.closedPoint R → c.asIdeal = ⊥ := by
    intro c hc
    by_contra h
    apply hc
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := c.2) h)
  exact PrimeSpectrum.ext ((key a ha).trans (key b hb).symm)

omit LB in

theorem locallyOfFiniteType_fromSpecResidueField (s₀ : B)
    (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀) :
    LocallyOfFiniteType (B.fromSpecResidueField s₀) := by
  by_cases ht : g.base s₀ = IsLocalRing.closedPoint R
  ·
    have hcl : IsClosed ({s₀} : Set B) := by
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hsy : s₀ ⤳ y := specializes_iff_mem_closure.mpr hy
      have : g.base y = g.base s₀ := by
        have h1 : g.base s₀ ⤳ g.base y := hsy.map g.continuous
        rw [ht] at h1 ⊢
        have := h1.mem_closed (IsLocalRing.isClosed_singleton_closedPoint R) rfl
        exact this
      exact hs₀ y hsy this
    have := isClosed_singleton_iff_isClosedImmersion.mp hcl
    infer_instance
  ·
    let V : B.Opens := g ⁻¹ᵁ ⟨{IsLocalRing.closedPoint R}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint R).isOpen_compl⟩
    have hs₀V : s₀ ∈ V := ht
    let x : ↑(V : Scheme.{u}) := ⟨s₀, hs₀V⟩
    have hcl : IsClosed ({x} : Set ↑(V : Scheme.{u})) := by
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have hsy : s₀ ⤳ y.1 := hxy.map continuous_subtype_val
      have hyV : g.base y.1 ≠ IsLocalRing.closedPoint R := y.2
      have : g.base y.1 = g.base s₀ := eq_of_ne_closedPoint (R := R) _ _ hyV ht
      have := hs₀ y.1 hsy this
      exact Set.mem_singleton_iff.mpr (Subtype.ext this)
    have hci := isClosed_singleton_iff_isClosedImmersion.mp hcl
    have heq : Spec.map (V.ι.residueFieldMap x) ≫ B.fromSpecResidueField s₀ =
        (V : Scheme.{u}).fromSpecResidueField x ≫ V.ι :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField V.ι x
    have hlft : LocallyOfFiniteType ((V : Scheme.{u}).fromSpecResidueField x ≫ V.ι) := inferInstance
    rw [← heq] at hlft
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType
      (Spec.map (V.ι.residueFieldMap x)) (B.fromSpecResidueField s₀)).mp hlft

theorem eq_of_specializes_of_fst_eq (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (w e : ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (hwe : w ⤳ e)
    (hp : (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base w =
      (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e) : w = e := by
  haveI := locallyOfFiniteType_fromSpecResidueField (g := g) s₀ hs₀
  haveI : LocallyOfFiniteType (B.fromSpecResidueField s₀ ≫ g) := inferInstance
  haveI : LocallyQuasiFinite (B.fromSpecResidueField s₀ ≫ g) :=
    .of_injective (fun a b _ => Subsingleton.elim a b)
  haveI : LocallyQuasiFinite (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hdisc := (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).isDiscrete_preimage_singleton
    ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e)
  rw [isDiscrete_iff_discreteTopology] at hdisc

  let w' : ↥((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)) ⁻¹' {(pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e}) := ⟨w, hp⟩
  let e' : ↥((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)) ⁻¹' {(pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e}) := ⟨e, rfl⟩
  have hwe' : w' ⤳ e' := (Topology.IsInducing.subtypeVal.specializes_iff (x := w') (y := e')).mp hwe
  have : w' = e' := (specializes_iff_eq.mp hwe')
  exact congrArg Subtype.val this

theorem exists_mem_specializes_of_mem_closure_image (s₀ : B)
    (E : Set ↑(pullback g (B.fromSpecResidueField s₀ ≫ g))) (hE : IsClosed E) (η : B)
    (hη : η ∈ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base '' E)) :
    ∃ e ∈ E, (pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base e ⤳ η := by
  let p := pullback.fst g (B.fromSpecResidueField s₀ ≫ g)

  haveI : IsNoetherian ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) :=
    (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  haveI : TopologicalSpace.NoetherianSpace ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) := inferInstance

  obtain ⟨S, hSfin, hScl, hSirr, hSE⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hE

  let γ : ↑S → ↑(pullback g (B.fromSpecResidueField s₀ ≫ g)) := fun t => (hSirr t.1 t.2).genericPoint
  have hγ : ∀ t : ↑S, IsGenericPoint (γ t) (t.1 : Set _) := fun t =>
    (hSirr t.1 t.2).isGenericPoint_genericPoint (hScl t.1 t.2)
  haveI : Finite ↑S := hSfin.to_subtype
  have hsub : p.base '' E ⊆ ⋃ t : ↑S, closure {p.base (γ t)} := by
    rintro b ⟨e, he, rfl⟩
    rw [hSE] at he
    obtain ⟨t, htS, het⟩ := Set.mem_sUnion.mp he
    refine Set.mem_iUnion.mpr ⟨⟨t, htS⟩, ?_⟩
    have hsp : γ ⟨t, htS⟩ ⤳ e := (hγ ⟨t, htS⟩).specializes het
    exact specializes_iff_mem_closure.mp (hsp.map p.continuous)
  have hcl : IsClosed (⋃ t : ↑S, closure {p.base (γ t)}) :=
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hη' := (closure_minimal hsub hcl) hη
  obtain ⟨t, hηt⟩ := Set.mem_iUnion.mp hη'
  refine ⟨γ t, ?_, specializes_iff_mem_closure.mpr hηt⟩
  rw [hSE]
  exact Set.mem_sUnion.mpr ⟨t.1, t.2, (hγ t).mem⟩

omit LB in

theorem forall_specializes_eq_of_specializes_of_ne (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η)
    (d : B) (hd : d ⤳ η) (hdk : g.base d ≠ IsLocalRing.closedPoint R) :
    ∀ y : B, y ⤳ d → y = d := by
  classical

  obtain ⟨_, hdvr⟩ := AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R g η hηk hηmax

  have hrange : Set.range (B.fromSpecStalk η) = {y | y ⤳ η} := Scheme.range_fromSpecStalk

  have hprime : ∀ 𝔭 : PrimeSpectrum (B.presheaf.stalk η),
      𝔭.asIdeal = ⊥ ∨ 𝔭 = IsLocalRing.closedPoint (B.presheaf.stalk η) := by
    intro 𝔭
    by_cases h : 𝔭.asIdeal = ⊥
    · exact Or.inl h
    · right
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (hpi := 𝔭.2) h)

  have hclosed : (B.fromSpecStalk η).base (IsLocalRing.closedPoint (B.presheaf.stalk η)) = η :=
    Scheme.fromSpecStalk_closedPoint
  have hdη : d ≠ η := fun h => hdk (h ▸ hηk)

  obtain ⟨𝔭, h𝔭⟩ : d ∈ Set.range (B.fromSpecStalk η) := by rw [hrange]; exact hd
  intro y hy
  obtain ⟨𝔮, h𝔮⟩ : y ∈ Set.range (B.fromSpecStalk η) := by rw [hrange]; exact hy.trans hd
  have hyη : y ≠ η := by
    intro hyη
    apply hdη
    rw [hyη] at hy
    exact (hd.antisymm hy).eq
  have h𝔭gen : 𝔭.asIdeal = ⊥ := by
    rcases hprime 𝔭 with h | h
    · exact h
    · exact absurd (h𝔭.symm.trans (by rw [h]; exact hclosed)) hdη
  have h𝔮gen : 𝔮.asIdeal = ⊥ := by
    rcases hprime 𝔮 with h | h
    · exact h
    · exact absurd (h𝔮.symm.trans (by rw [h]; exact hclosed)) hyη
  have : 𝔮 = 𝔭 := PrimeSpectrum.ext (h𝔮gen.trans h𝔭gen.symm)
  rw [← h𝔮, ← h𝔭, this]

theorem main (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((rightMul LB (B.fromSpecResidueField s₀ ≫ g) ⟨B.fromSpecResidueField s₀, rfl⟩).base ⁻¹' ((U : Set B)ᶜ))) := by
  classical
  set t₀ := B.fromSpecResidueField s₀ ≫ g with ht₀
  set σ : SchemeHomOver t₀ g := ⟨B.fromSpecResidueField s₀, rfl⟩ with hσ
  set p := pullback.fst g t₀ with hp
  set ρ := rightMul LB t₀ σ with hρ
  intro hη
  have hE : IsClosed (ρ.base ⁻¹' ((U : Set B)ᶜ)) := U.isOpen.isClosed_compl.preimage ρ.continuous
  obtain ⟨e, heE, hde⟩ := exists_mem_specializes_of_mem_closure_image (g := g) s₀ _ hE η hη

  have hdmax : ∀ y : B, y ⤳ p.base e → g.base y = g.base (p.base e) → y = p.base e := by
    by_cases hdk : g.base (p.base e) = IsLocalRing.closedPoint R
    · have hde' : p.base e = η := hηmax _ hde hdk
      intro y hy hyk
      rw [hde'] at hy hyk ⊢
      exact hηmax y hy (hyk.trans hηk)
    · intro y hy _
      exact forall_specializes_eq_of_specializes_of_ne (g := g) η hηk hηmax (p.base e) hde hdk y hy

  have hiso := isIso_rightTrans LB t₀ σ
  set T := rightTrans LB t₀ σ with hT
  have hTfst : T ≫ p = ρ := rightTrans_fst LB t₀ σ
  have hρe : ρ.base e = p.base (T.base e) := by
    rw [← hTfst, Scheme.Hom.comp_base, TopCat.comp_app]
  have hρmax : ∀ y : B, y ⤳ ρ.base e → g.base y = g.base (ρ.base e) → y = ρ.base e := by
    intro y hy hyk
    rw [hρe] at hy hyk ⊢
    have hy' : g.base y = g.base s₀ := by rw [hyk, base_fst_eq]
    obtain ⟨w, hwe', hpw⟩ := exists_specializes_fst_eq (g := g) s₀ hs₀ (T.base e) y hy' hy

    let Tinv := inv T
    have h1 : Tinv.base (T.base e) = e := by
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, IsIso.hom_inv_id]; rfl
    have hw₀e : Tinv.base w ⤳ e := by rw [← h1]; exact hwe'.map Tinv.continuous
    have hpw₀ : p.base (Tinv.base w) ⤳ p.base e := hw₀e.map p.continuous
    have hfib : g.base (p.base (Tinv.base w)) = g.base (p.base e) := by
      rw [base_fst_eq, base_fst_eq]
    have hw₀ : p.base (Tinv.base w) = p.base e := hdmax _ hpw₀ hfib
    have : Tinv.base w = e := eq_of_specializes_of_fst_eq (g := g) s₀ hs₀ _ _ hw₀e hw₀
    have : w = T.base e := by
      rw [← this, ← TopCat.comp_app, ← Scheme.Hom.comp_base, IsIso.inv_hom_id]; rfl
    rw [← hpw, this]
  have hρU : ρ.base e ∈ (U : Set B) := hU _ hρmax
  exact heE hρU

end Top

end P2mBadClosureSol
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes.P2mBadClosureSol"

open P2mBadClosureSol in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens)
    (hU : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (s₀ : B) (hs₀ : ∀ y : B, s₀ ⤳ y → g.base y = g.base s₀ → y = s₀)
    (η : B) (hηk : g.base η = IsLocalRing.closedPoint R)
    (hηmax : ∀ y : B, y ⤳ η → g.base y = IsLocalRing.closedPoint R → y = η) :
    η ∉ closure ((pullback.fst g (B.fromSpecResidueField s₀ ≫ g)).base ''
      ((LB.mul (pullback.snd g (B.fromSpecResidueField s₀ ≫ g) ≫ (B.fromSpecResidueField s₀ ≫ g))
          ⟨pullback.fst g (B.fromSpecResidueField s₀ ≫ g), pullback.condition⟩
          (schemeHomOverComp (pullback.snd g (B.fromSpecResidueField s₀ ≫ g)) rfl
            (⟨B.fromSpecResidueField s₀, rfl⟩ :
              SchemeHomOver (B.fromSpecResidueField s₀ ≫ g) g))).1.base ⁻¹' ((U : Set B)ᶜ))) :=
  P2mBadClosureSol.main LB U hU s₀ hs₀ η hηk hηmax

end S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_not_mem_closure_image_fst_preimage_mul_compl_of_forall_specializes (solution)
