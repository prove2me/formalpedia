-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8654efc6-174d-53bb-b098-224df0a8fa9c

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

namespace BCFormalAux

theorem one_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') : (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem mul_val_congr {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f)
    (hx : x.1 = x'.1) (hy : y.1 = y'.1) : (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst h
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

theorem specOver_comp_specMap {B' B C : Type} [CommRing B'] [CommRing B] [CommRing C] [Algebra B C] [Algebra B' C] (φ : B' →+* B)
    (h : algebraMap B' C = (algebraMap B C).comp φ) :
    Scheme.specOver (𝒪 := B) C ≫ Spec.map (CommRingCat.ofHom φ) = Scheme.specOver (𝒪 := B') C := by
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← h]

theorem nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] {B B₁ C : Type} [CommRing B] [CommRing B₁] [CommRing C]
    [Algebra B B₁] [Algebra B₁ C] [Algebra B C] [IsScalarTower B B₁ C] (n : ℕ) (φ : MvPowerSeries σ B) (s : σ → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap B B₁) φ) s = MvFormalGroup.nilEval n φ s := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_map_algebraMap]

theorem isComm_map {g : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (F : MvFormalGroup g R) [hF : F.IsComm] :
    (F.map f).IsComm := by
  constructor
  intro i
  have hz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => MvPowerSeries.X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> simp [MvPowerSeries.constantCoeff_X]
  have key := congrArg (MvPowerSeries.map f) (hF.comm i)
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hz)] at key
  have hfam : (fun s => MvPowerSeries.map f ((Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => MvPowerSeries.X (Sum.inl j)) s)) =
      Sum.elim (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) S)) fun j => MvPowerSeries.X (Sum.inl j) := by
    funext s; rcases s with j | j <;> simp [MvPowerSeries.map_X]
  rw [hfam] at key
  exact key

theorem map_map {g : ℕ} {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (h : S →+* T) (F : MvFormalGroup g R) :
    (F.map f).map h = F.map (h.comp f) := by
  ext i n
  simp [MvFormalGroup.map, MvPowerSeries.coeff_map]

theorem nilMul_map {g : ℕ} {B' B C : Type} [CommRing B'] [CommRing B] [CommRing C] [Algebra B' B] [Algebra B C] [Algebra B' C]
    [IsScalarTower B' B C] (F : MvFormalGroup g B') (n : ℕ) (s t : Fin g → C) :
    (F.map (algebraMap B' B)).nilMul n s t = F.nilMul n s t := by
  funext i
  unfold MvFormalGroup.nilMul
  exact nilEval_map n (F.toPowerSeries i) (Sum.elim s t)

end BCFormalAux

open BCFormalAux

theorem solution
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    {d : ℕ} (Ĝ₁ : MvFormalGroup d B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ d)
    (P : BareDeformation f₁ L₁ B')
    (GP : MvFormalGroup.Deformation Ĝ₁ B') (θP : RelativeGroupLaw.FormalCoordinates P.f d)
    (hθP : P.L.IsFormalCoordinates GP.F θP) (hlP : P.LiftsCoordinates θ₁ θP) :
    ∃ (D : BareDeformation f₁ L₁ B) (h : D.A ⟶ P.A)
      (hc : IsPullback h D.f P.f (Spec.map (CommRingCat.ofHom φ))),
      D.g ≫ h = P.g ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (x y : SchemeHomOver t D.f),
        (D.L.mul t x y).1 ≫ h =
          (P.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨x.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ h, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      ∃ (G : MvFormalGroup.Deformation Ĝ₁ B) (θ : RelativeGroupLaw.FormalCoordinates D.f d),
        G.F = GP.F.map φ ∧
        (GP.F.IsComm → G.F.IsComm) ∧
        D.L.IsFormalCoordinates G.F θ ∧ D.LiftsCoordinates θ₁ θ ∧
        ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (s : Fin d → B''), (∀ i, IsNilpotent (s i)) →
          letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
          (θ B'' s).1 ≫ h = (θP B'' s).1 := by
  classical

  let ι : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B') := Spec.map (CommRingCat.ofHom φ)
  have hιB₁ : Spec.map (CommRingCat.ofHom (algebraMap B B₁)) ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap B' B₁)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have hsq : IsPullback (pullback.fst P.f ι) (pullback.snd P.f ι) P.f ι := IsPullback.of_hasPullback P.f ι
  have wg : P.g ≫ P.f = (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) ≫ ι := by
    rw [P.cart.w, Category.assoc, hιB₁]
  let gD : A₁ ⟶ pullback P.f ι := pullback.lift P.g (f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) wg
  have hgD1 : gD ≫ pullback.fst P.f ι = P.g := pullback.lift_fst _ _ _
  have hgD2 : gD ≫ pullback.snd P.f ι = f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) := pullback.lift_snd _ _ _
  have hcartD : IsPullback gD f₁ (pullback.snd P.f ι) (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst P.f ι) (v₁₃ := P.f) (h₂₂ := ι) ?_ hgD2 hsq
    rw [hgD1, hιB₁]; exact P.cart

  let D : BareDeformation f₁ L₁ B :=
    { A := pullback P.f ι
      f := pullback.snd P.f ι
      L := P.L.baseChange ι
      comm := RelativeGroupLaw.IsCommutative.baseChange ι P.comm
      bundle := P.bundle.of_isPullback hsq
      g := gD
      cart := hcartD
      hom := by
        intro T t Q R
        apply pullback.hom_ext
        · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
          simp only [Category.assoc, hgD1]
          rw [P.hom]
          exact mul_val_congr P.L (by rw [Category.assoc, hιB₁]) _ _ _ _
            (by show Q.1 ≫ P.g = (Q.1 ≫ gD) ≫ pullback.fst P.f ι; rw [Category.assoc, hgD1])
            (by show R.1 ≫ P.g = (R.1 ≫ gD) ≫ pullback.fst P.f ι; rw [Category.assoc, hgD1])
        · rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
          simp only [Category.assoc, hgD2]
          rw [← Category.assoc, (L₁.mul t Q R).2] }
  refine ⟨D, pullback.fst P.f ι, hsq, hgD1, ?_, ?_⟩
  ·
    intro T t x y
    change ((P.L.baseChange ι).mul t x y).1 ≫ pullback.fst P.f ι = _
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    rfl

  let G : MvFormalGroup.Deformation Ĝ₁ B := ⟨GP.F.map φ, by rw [map_map, hφ]; exact GP.map_eq⟩

  have hbase : ∀ (B'' : Type) [CommRing B''] [Algebra B B''],
      letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
      Scheme.specOver (𝒪 := B) B'' ≫ ι = Scheme.specOver (𝒪 := B') B'' := fun B'' _ _ => by
    letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
    exact specOver_comp_specMap φ rfl
  let θ : RelativeGroupLaw.FormalCoordinates D.f d := fun B'' _ _ s =>
    letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
    ⟨pullback.lift (θP B'' s).1 (Scheme.specOver (𝒪 := B) B'') (by rw [(θP B'' s).2, hbase]), pullback.lift_snd _ _ _⟩
  have hθ1 : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (s : Fin d → B''),
      letI : Algebra B' B'' := ((algebraMap B B'').comp φ).toAlgebra
      (θ B'' s).1 ≫ pullback.fst P.f ι = (θP B'' s).1 := fun B'' _ _ s => pullback.lift_fst _ _ _
  have hθ2 : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (s : Fin d → B''),
      (θ B'' s).1 ≫ pullback.snd P.f ι = Scheme.specOver (𝒪 := B) B'' := fun B'' _ _ s => pullback.lift_snd _ _ _
  refine ⟨G, θ, rfl, fun hcomm => ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    haveI := hcomm
    exact isComm_map φ GP.F
  ·
    intro C _ _ C' _ _ ψ s hs
    letI iC : Algebra B' C := ((algebraMap B C).comp φ).toAlgebra
    letI iC' : Algebra B' C' := ((algebraMap B C').comp φ).toAlgebra
    let ψ' : C →ₐ[B'] C' := ⟨ψ.toRingHom, fun b => by
      change ψ (algebraMap B C (φ b)) = algebraMap B C' (φ b)
      exact ψ.commutes (φ b)⟩
    have hnat := hθP.1 C C' ψ' s hs
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [hθ1, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, hθ1]
      have := congrArg Subtype.val hnat
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
      exact this
    · rw [hθ2, GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, hθ2]
      exact (Scheme.specMap_algHom_comp_specOver ψ).symm
  ·
    intro C _ _ J n hJ
    letI iC : Algebra B' C := ((algebraMap B C).comp φ).toAlgebra
    obtain ⟨hinf, hinj, hsurj, hmul⟩ := hθP.2 C J n hJ
    have hbaseJ : Scheme.specOver (𝒪 := B) (C ⧸ J) ≫ ι = Scheme.specOver (𝒪 := B') (C ⧸ J) := specOver_comp_specMap φ rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro s hsJ
      have h1 := congrArg Subtype.val (hinf s hsJ)
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at h1
      unfold RelativeGroupLaw.IsInfinitesimal
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      change _ = ((P.L.baseChange ι).one _).1
      rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
      apply pullback.hom_ext
      · rw [Category.assoc, hθ1, pullback.lift_fst, one_val_congr P.L hbaseJ]
        exact h1
      · rw [Category.assoc, hθ2, pullback.lift_snd]
        exact Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)
    ·
      intro s t hsJ htJ hst
      apply hinj s t hsJ htJ
      apply Subtype.ext
      rw [← hθ1, ← hθ1]

      exact congrArg (fun w => w ≫ pullback.fst P.f ι) (congrArg Subtype.val hst)
    ·
      intro Q hQ
      let Q' : SchemeHomOver (Scheme.specOver (𝒪 := B') C) P.f :=
        ⟨Q.1 ≫ pullback.fst P.f ι, by rw [Category.assoc, hsq.w, ← Category.assoc, Q.2, hbase]⟩
      have hQ1 := congrArg Subtype.val hQ
      rw [GoodReductionJacobian.schemeHomOverComp_coe] at hQ1
      change _ = ((P.L.baseChange ι).one _).1 at hQ1
      rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe] at hQ1
      have hQ' : P.L.IsInfinitesimal J Q' := by
        unfold RelativeGroupLaw.IsInfinitesimal
        apply Subtype.ext
        rw [GoodReductionJacobian.schemeHomOverComp_coe]
        change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B' J).toRingHom) ≫ Q.1 ≫ pullback.fst P.f ι = _
        have : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B' J).toRingHom) =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom) := rfl
        rw [this, ← Category.assoc, hQ1, pullback.lift_fst, one_val_congr P.L hbaseJ]
      obtain ⟨s, hsJ, hs⟩ := hsurj Q' hQ'
      refine ⟨s, hsJ, ?_⟩
      apply Subtype.ext
      apply pullback.hom_ext
      · rw [hθ1, hs]
      · rw [hθ2, Q.2]
    ·
      intro s t hsJ htJ
      letI : Algebra B' B := φ.toAlgebra
      haveI : IsScalarTower B' B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hnm : (GP.F.map φ).nilMul n s t = GP.F.nilMul n s t := nilMul_map GP.F n s t
      apply Subtype.ext
      change (θ C ((GP.F.map φ).nilMul n s t)).1 = ((P.L.baseChange ι).mul _ (θ C s) (θ C t)).1
      rw [hnm, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe]
      apply pullback.hom_ext
      · rw [hθ1, pullback.lift_fst, congrArg Subtype.val (hmul s t hsJ htJ)]
        exact mul_val_congr P.L (hbase C).symm _ _ _ _ (hθ1 C s).symm (hθ1 C t).symm
      · rw [hθ2, pullback.lift_snd]
  ·
    intro C _ _ _ _ s hs
    letI iC : Algebra B' C := ((algebraMap B C).comp φ).toAlgebra
    haveI : IsScalarTower B' B₁ C := IsScalarTower.of_algebraMap_eq (fun b => by
      change algebraMap B C (φ b) = algebraMap B₁ C (algebraMap B' B₁ b)
      rw [← hφ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B B₁ C])
    change (θ₁ C s).1 ≫ gD = (θ C s).1
    apply pullback.hom_ext
    · rw [Category.assoc, hgD1, hθ1]
      exact hlP C s hs
    · rw [Category.assoc, hgD2, hθ2, ← Category.assoc, (θ₁ C s).2, Scheme.specOver, Scheme.specOver, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  ·
    intro C _ _ s hs
    exact hθ1 C s

end S_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isPullback_isFormalCoordinates_map_of_ringHom_comp_eq (solution)
