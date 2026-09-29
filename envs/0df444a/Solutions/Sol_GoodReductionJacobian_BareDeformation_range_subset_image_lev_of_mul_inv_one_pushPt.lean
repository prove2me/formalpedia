-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.range_subset_image_lev_of_mul_inv_one_pushPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d9e1d4bb-75f8-5f07-9ec5-0382158a3aed

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing

open scoped Quaternion TensorProduct NumberField

universe u

namespace E159LVd2Kit

theorem ker_le_ker_of_range_subset {Y C X : Scheme.{u}} [IsReduced Y] (i : C ⟶ X) [IsClosedImmersion i]
    (g : Y ⟶ X) (hg : Set.range g.base ⊆ Set.range i.base) : i.ker ≤ g.ker := by
  have h1 : (i.ker.comap g).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_top, Set.eq_univ_iff_forall]
    intro y
    exact i.range_subset_ker_support (hg ⟨y, rfl⟩)
  have h2 : i.ker.comap g = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp h1
  have h3 : i.ker ≤ Scheme.IdealSheafData.map ⊥ g :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr h2.le
  rwa [Scheme.IdealSheafData.map_bot] at h3

theorem exists_comp_eq_of_isNilpotent_ker {B B₀ k : Type} [CommRing B] [CommRing B₀] [Field k]
    (π : B →+* B₀) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (sk : B →+* k) :
    ∃ sk₀ : B₀ →+* k, sk = sk₀.comp π := by
  have hle : ∀ x ∈ RingHom.ker π, sk x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := hker
    have hxn : x ^ n ∈ (RingHom.ker π) ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at hxn
    have hx0 : x ^ n = 0 := by simpa using hxn
    have : IsNilpotent (sk x) := ⟨n, by rw [← map_pow, hx0, map_zero]⟩
    exact this.eq_zero
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) sk hle).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
  ext x
  simp

section Theta

variable {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
  {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of B₀)} {Lₛ : RelativeGroupLaw B₀ fₛ}
  (D : BareDeformation fₛ Lₛ B) {T : Scheme.{0}} (t₀ : T ⟶ Spec (CommRingCat.of B₀))

noncomputable def theta (P : SchemeHomOver t₀ fₛ) :
    SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f :=
  ⟨P.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, P.2]⟩

noncomputable def thetaInv (P : SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f) : SchemeHomOver t₀ fₛ :=
  ⟨D.cart.lift P.1 t₀ P.2, D.cart.lift_snd _ _ _⟩

noncomputable def thetaEquiv : SchemeHomOver t₀ fₛ ≃ SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f where
  toFun := theta D t₀
  invFun := thetaInv D t₀
  left_inv P := Subtype.ext (D.cart.hom_ext
    (by rw [thetaInv, theta, IsPullback.lift_fst])
    (by rw [thetaInv, IsPullback.lift_snd, P.2]))
  right_inv P := Subtype.ext (D.cart.lift_fst _ _ _)

theorem thetaEquiv_val (P : SchemeHomOver t₀ fₛ) : (thetaEquiv D t₀ P).1 = P.1 ≫ D.g := rfl

theorem thetaEquiv_mul (P Q : SchemeHomOver t₀ fₛ) :
    thetaEquiv D t₀ (Lₛ.mul t₀ P Q) = D.L.mul _ (thetaEquiv D t₀ P) (thetaEquiv D t₀ Q) :=
  Subtype.ext (D.hom t₀ P Q)

theorem thetaEquiv_one : thetaEquiv D t₀ (Lₛ.one t₀) = D.L.one _ := by
  have h := thetaEquiv_mul D t₀ (Lₛ.one t₀) (Lₛ.one t₀)
  rw [Lₛ.one_mul] at h
  calc thetaEquiv D t₀ (Lₛ.one t₀)
      = D.L.mul _ (D.L.one _) (thetaEquiv D t₀ (Lₛ.one t₀)) := (D.L.one_mul _ _).symm
    _ = D.L.mul _ (D.L.mul _ (D.L.inv _ (thetaEquiv D t₀ (Lₛ.one t₀))) (thetaEquiv D t₀ (Lₛ.one t₀)))
          (thetaEquiv D t₀ (Lₛ.one t₀)) := by rw [D.L.inv_mul_cancel]
    _ = D.L.mul _ (D.L.inv _ (thetaEquiv D t₀ (Lₛ.one t₀)))
          (D.L.mul _ (thetaEquiv D t₀ (Lₛ.one t₀)) (thetaEquiv D t₀ (Lₛ.one t₀))) := D.L.mul_assoc _ _ _ _
    _ = D.L.mul _ (D.L.inv _ (thetaEquiv D t₀ (Lₛ.one t₀))) (thetaEquiv D t₀ (Lₛ.one t₀)) := by rw [← h]
    _ = D.L.one _ := D.L.inv_mul_cancel _ _

theorem thetaEquiv_nsmulPt (n : ℕ) (P : SchemeHomOver t₀ fₛ) :
    thetaEquiv D t₀ (nsmulPt Lₛ t₀ n P) = nsmulPt D.L _ n (thetaEquiv D t₀ P) := by
  induction n with
  | zero => exact thetaEquiv_one D t₀
  | succ n ih => simp only [nsmulPt]; rw [thetaEquiv_mul, ih]

theorem isClosedImmersion_g (hπ : Function.Surjective (algebraMap B B₀)) : IsClosedImmersion D.g :=
  have hs : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) D.cart.flip hs

theorem thetaEquiv_symm_mul (P Q : SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f) :
    (thetaEquiv D t₀).symm (D.L.mul _ P Q) = Lₛ.mul t₀ ((thetaEquiv D t₀).symm P) ((thetaEquiv D t₀).symm Q) := by
  rw [Equiv.symm_apply_eq, thetaEquiv_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem thetaEquiv_symm_one : (thetaEquiv D t₀).symm (D.L.one _) = Lₛ.one t₀ := by
  rw [Equiv.symm_apply_eq, thetaEquiv_one]

theorem thetaEquiv_inv (P : SchemeHomOver t₀ fₛ) :
    thetaEquiv D t₀ (Lₛ.inv t₀ P) = D.L.inv _ (thetaEquiv D t₀ P) := by
  letI := Lₛ.pointGroup t₀
  letI := D.L.pointGroup (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
  let F : SchemeHomOver t₀ fₛ →* SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f :=
    MonoidHom.mk' (fun P => thetaEquiv D t₀ P) (fun a b => thetaEquiv_mul D t₀ a b)
  exact map_inv F P

theorem thetaEquiv_symm_inv (P : SchemeHomOver (t₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) D.f) :
    (thetaEquiv D t₀).symm (D.L.inv _ P) = Lₛ.inv t₀ ((thetaEquiv D t₀).symm P) := by
  rw [Equiv.symm_apply_eq, thetaEquiv_inv, Equiv.apply_symm_apply]

end Theta

end E159LVd2Kit

open E159LVd2Kit in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (φ₀ : ι → (E₀.A ⟶ E₀.A)) (hφ₀ : ∀ i, φ₀ i ≫ E₀.f = E₀.f) (hφg : ∀ i, φ₀ i ≫ D.g = D.g ≫ φ i)
    (hφ₀_stable : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t E₀.f),
      FactorsThrough E₀.lev P → FactorsThrough E₀.lev (pushPt (φ₀ i) (hφ₀ i) P)) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base → Set.range Q.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (D.L.mul t P Q).1.base ⊆ D.g.base '' Set.range E₀.lev.base ∧
            Set.range (D.L.inv t P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)),
        Set.range (D.L.one t).1.base ⊆ D.g.base '' Set.range E₀.lev.base) ∧
    (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        Set.range P.1.base ⊆ D.g.base '' Set.range E₀.lev.base →
          Set.range (pushPt (φ i) (hφ i) P).1.base ⊆ D.g.base '' Set.range E₀.lev.base) := by
  classical
  haveI := E₀.lev_closed
  haveI hgci : IsClosedImmersion D.g := isClosedImmersion_g D hπ
  have hginj : Function.Injective D.g.base := D.g.isClosedEmbedding.injective

  have crit : ∀ {S : Scheme.{0}} [IsReduced S] (s₀ : S ⟶ Spec (CommRingCat.of B₀))
      (P' : SchemeHomOver (s₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) D.f),
      Set.range P'.1.base ⊆ D.g.base '' Set.range E₀.lev.base ↔
        FactorsThrough E₀.lev ((thetaEquiv D s₀).symm P') := by
    intro S _ s₀ P'
    have hval : P'.1 = ((thetaEquiv D s₀).symm P').1 ≫ D.g := by
      conv_lhs => rw [← (thetaEquiv D s₀).apply_symm_apply P']
      rfl
    constructor
    · intro hsub
      have hr : Set.range ((thetaEquiv D s₀).symm P').1.base ⊆ Set.range E₀.lev.base := by
        rintro _ ⟨p, rfl⟩
        obtain ⟨a, ⟨c, rfl⟩, ha⟩ := hsub ⟨p, rfl⟩
        refine ⟨c, hginj ?_⟩
        rw [ha, hval]
        rfl
      exact ⟨IsClosedImmersion.lift E₀.lev _ (ker_le_ker_of_range_subset E₀.lev _ hr),
        IsClosedImmersion.lift_fac _ _ _⟩
    · rintro ⟨z, hz⟩ _ ⟨p, rfl⟩
      refine ⟨E₀.lev.base (z.base p), ⟨_, rfl⟩, ?_⟩
      rw [hval]
      change ((z ≫ E₀.lev) ≫ D.g).base p = _
      rw [hz]

  have factor : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (x : ↥T),
      ∃ s₀ : Spec (T.residueField x) ⟶ Spec (CommRingCat.of B₀),
        T.fromSpecResidueField x ≫ t = s₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
    intro T t x
    obtain ⟨χ₀, hχ₀⟩ := exists_comp_eq_of_isNilpotent_ker (algebraMap B B₀) hπ hker
      (Spec.preimage (T.fromSpecResidueField x ≫ t)).hom
    refine ⟨Spec.map (CommRingCat.ofHom χ₀), ?_⟩
    rw [← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom (χ₀.comp (algebraMap B B₀)))
    rw [← hχ₀]
    exact (Spec.map_preimage _).symm

  have range_iff : ∀ {T : Scheme.{0}} (u : T ⟶ D.A),
      Set.range u.base ⊆ D.g.base '' Set.range E₀.lev.base ↔
        ∀ x : ↥T, Set.range (T.fromSpecResidueField x ≫ u).base ⊆ D.g.base '' Set.range E₀.lev.base := by
    intro T u
    constructor
    · rintro hu x _ ⟨p, rfl⟩
      exact hu ⟨_, rfl⟩
    · rintro hu _ ⟨x, rfl⟩
      have := hu x ⟨closedPoint _, rfl⟩
      rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Scheme.fromSpecResidueField_apply] at this
  refine ⟨?_, ?_, ?_⟩
  ·
    intro T t P Q hP hQ
    rw [range_iff] at hP hQ
    constructor
    · rw [range_iff]
      intro x
      obtain ⟨s₀, hs⟩ := factor t x
      have hnat := congrArg Subtype.val (D.L.mul_natural t _ (T.fromSpecResidueField x) hs P Q)
      rw [schemeHomOverComp_coe] at hnat
      rw [hnat, crit s₀, thetaEquiv_symm_mul]
      exact (E₀.lev_sub s₀ _ _
        ((crit s₀ (schemeHomOverComp (T.fromSpecResidueField x) hs P)).mp (hP x))
        ((crit s₀ (schemeHomOverComp (T.fromSpecResidueField x) hs Q)).mp (hQ x))).1
    · rw [range_iff]
      intro x
      obtain ⟨s₀, hs⟩ := factor t x

      have hnat : T.fromSpecResidueField x ≫ (D.L.inv t P).1
          = (D.L.inv _ (schemeHomOverComp (T.fromSpecResidueField x) hs P)).1 := by
        letI := D.L.pointGroup t
        letI := D.L.pointGroup (s₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
        let F : SchemeHomOver t D.f →* SchemeHomOver (s₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) D.f :=
          MonoidHom.mk' (fun R => schemeHomOverComp (T.fromSpecResidueField x) hs R)
            (fun a b => D.L.mul_natural t _ (T.fromSpecResidueField x) hs a b)
        exact congrArg Subtype.val (map_inv F P)
      rw [hnat, crit s₀, thetaEquiv_symm_inv]
      exact (E₀.lev_sub s₀ _ _
        ((crit s₀ (schemeHomOverComp (T.fromSpecResidueField x) hs P)).mp (hP x))
        ((crit s₀ (schemeHomOverComp (T.fromSpecResidueField x) hs P)).mp (hP x))).2
  ·
    intro T t
    rw [range_iff]
    intro x
    obtain ⟨s₀, hs⟩ := factor t x
    have hnat := congrArg Subtype.val (D.L.one_natural t _ (T.fromSpecResidueField x) hs)
    rw [schemeHomOverComp_coe] at hnat
    rw [hnat, crit s₀, thetaEquiv_symm_one]
    exact E₀.lev_one s₀
  ·
    intro i T t P hP
    rw [range_iff] at hP ⊢
    intro x
    obtain ⟨s₀, hs⟩ := factor t x
    have hx := (crit s₀ (schemeHomOverComp (T.fromSpecResidueField x) hs P)).mp (hP x)
    have hst := hφ₀_stable i s₀ _ hx

    have hpush : (thetaEquiv D s₀).symm (pushPt (φ i) (hφ i) (schemeHomOverComp (T.fromSpecResidueField x) hs P))
        = pushPt (φ₀ i) (hφ₀ i) ((thetaEquiv D s₀).symm (schemeHomOverComp (T.fromSpecResidueField x) hs P)) := by
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      change (schemeHomOverComp (T.fromSpecResidueField x) hs P).1 ≫ φ i
        = (((thetaEquiv D s₀).symm (schemeHomOverComp (T.fromSpecResidueField x) hs P)).1 ≫ φ₀ i) ≫ D.g
      rw [Category.assoc, hφg, ← Category.assoc]
      congr 1
      exact (congrArg Subtype.val ((thetaEquiv D s₀).apply_symm_apply
        (schemeHomOverComp (T.fromSpecResidueField x) hs P))).symm
    have hcoe : T.fromSpecResidueField x ≫ (pushPt (φ i) (hφ i) P).1
        = (pushPt (φ i) (hφ i) (schemeHomOverComp (T.fromSpecResidueField x) hs P)).1 := by
      change T.fromSpecResidueField x ≫ P.1 ≫ φ i = (T.fromSpecResidueField x ≫ P.1) ≫ φ i
      rw [Category.assoc]
    rw [hcoe, crit s₀, hpush]
    exact hst

end S_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_range_subset_image_lev_of_mul_inv_one_pushPt (solution)
