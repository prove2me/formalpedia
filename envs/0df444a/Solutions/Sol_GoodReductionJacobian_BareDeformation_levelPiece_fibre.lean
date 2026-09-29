-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.levelPiece_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e34f6f4e-b848-5a80-8d22-dcc0d75e4dea

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_fibre

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing

open scoped Quaternion TensorProduct NumberField

universe u

namespace E163LVf

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

theorem base_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    (f ≫ g).base x = g.base (f.base x) := rfl

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

section Points

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmul_eq_nsmulPt (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : L.nsmul t n P = nsmulPt L t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih]; simp only [nsmulPt]

theorem comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : P.1 ≫ L.schemeNsmul n = (nsmulPt L t n P).1 := by
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (Category.comp_id _)
  have h := congrArg Subtype.val (L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint)
  rw [hP] at h
  rw [← nsmul_eq_nsmulPt]
  exact h

theorem one_val_eq (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm

end Points

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

end Theta

theorem main {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))
    (k : Type) [Field k] [IsAlgClosed k] (sk₀ : B₀ →+* k) (hNk : (N : k) ≠ 0)
    (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of B))
    (ht : geomPoint k sk₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))) = t) :
    ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver t D.f // FactorsThrough (W.ι ≫ (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1)) P},
      ∀ x y : ZMod N × ZMod N, (e (x + y) : SchemeHomOver t D.f) = D.L.mul t (e x) (e y) := by
  subst ht
  haveI : IsClosedImmersion E₀.lev := E₀.lev_closed
  haveI : IsClosedImmersion D.g := isClosedImmersion_g D hπ
  obtain ⟨e, he⟩ := E₀.lev_fibre k sk₀ hNk
  have hiff : ∀ P₀ : SchemeHomOver (geomPoint k sk₀) E₀.f,
      FactorsThrough E₀.lev P₀ ↔
        FactorsThrough (W.ι ≫ (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1)) (thetaEquiv D (geomPoint k sk₀) P₀) := by
    intro P₀
    constructor
    · rintro ⟨c, hc⟩
      have htor : nsmulPt E₀.L (geomPoint k sk₀) N P₀ = E₀.L.one _ := E₀.lev_torsion _ P₀ ⟨c, hc⟩
      have hw : (thetaEquiv D (geomPoint k sk₀) P₀).1 ≫ D.L.schemeNsmul N =
          (geomPoint k sk₀ ≫ (Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) ≫ (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
        rw [comp_schemeNsmul, ← thetaEquiv_nsmulPt, htor, thetaEquiv_one, one_val_eq]
      have hκ := pullback.lift_fst _ _ hw
      refine ⟨IsOpenImmersion.lift W.ι (pullback.lift _ _ hw) ?_, ?_⟩
      · rw [Scheme.Opens.range_ι, hW]
        rintro _ ⟨p, rfl⟩
        refine ⟨E₀.lev.base (c.base p), ⟨c.base p, rfl⟩, ?_⟩
        show D.g.base (E₀.lev.base (c.base p)) = (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ((pullback.lift _ _ hw).base p)
        rw [← base_comp_apply (pullback.lift _ _ hw), hκ, thetaEquiv_val, ← hc, base_comp_apply, base_comp_apply]
      · rw [← Category.assoc, IsOpenImmersion.lift_fac, hκ]
    · rintro ⟨w, hw⟩
      have hrange : Set.range P₀.1.base ⊆ Set.range E₀.lev.base := by
        rintro _ ⟨p, rfl⟩
        have hmem : (W.ι.base (w.base p)) ∈ (W : Set ↥(D.L.schemeKer N)) :=
          (Scheme.Opens.range_ι W).le ⟨w.base p, rfl⟩
        rw [hW, Set.mem_preimage, ← base_comp_apply, ← base_comp_apply, hw, thetaEquiv_val,
          base_comp_apply] at hmem
        obtain ⟨y, hy, hyeq⟩ := hmem
        exact (D.g.isClosedEmbedding.injective hyeq) ▸ hy
      exact ⟨IsClosedImmersion.lift E₀.lev P₀.1 (ker_le_ker_of_range_subset E₀.lev P₀.1 hrange),
        IsClosedImmersion.lift_fac _ _ _⟩
  refine ⟨e.trans ((thetaEquiv D (geomPoint k sk₀)).subtypeEquiv hiff), fun x y => ?_⟩
  simp only [Equiv.trans_apply, Equiv.subtypeEquiv_apply, he]
  exact thetaEquiv_mul D _ _ _

end E163LVf

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))) :
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k), (N : k) ≠ 0 →
        ∃ e : ZMod N × ZMod N ≃ {P : SchemeHomOver (geomPoint k sk) D.f // FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P},
          ∀ x y : ZMod N × ZMod N,
            (e (x + y) : SchemeHomOver (geomPoint k sk) D.f) = D.L.mul (geomPoint k sk) (e x) (e y)) := by
  intro k _ _ sk hNk
  obtain ⟨sk₀, hsk⟩ := E163LVf.exists_comp_eq_of_isNilpotent_ker (algebraMap B B₀) hπ hker sk
  exact E163LVf.main B B₀ hπ E₀ D W hW k sk₀ hNk (geomPoint k sk) (by
    rw [hsk, geomPoint, geomPoint, CommRingCat.ofHom_comp, Spec.map_comp])

#print axioms solution

end S_GoodReductionJacobian_BareDeformation_levelPiece_fibre
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_fibre (solution)
