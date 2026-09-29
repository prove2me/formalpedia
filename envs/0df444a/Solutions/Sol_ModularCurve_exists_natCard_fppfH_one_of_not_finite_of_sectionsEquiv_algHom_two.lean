-- Prove2me | solution 1 for ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/f83b8834-faaa-5c57-8ed7-1df2161f0e1d

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import Mathlib.CategoryTheory.Sites.EpiMono
import Definitions.Def_AlgebraicGeometry_FppfKummerCalculus
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgebraicGeometry_fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
import Theorems.Thm_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
import Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
import Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
import Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime
import Theorems.Thm_AlgebraicGeometry_natCard_fppfH1_Gm_specZ_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two
p2m_attr_erase "simp" "Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

p2m_open "CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits"

namespace P2mPuncturedH1

section IntAlgHom

def intAlgHom {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (g : R →+* S) :
    R →ₐ[ℤ] S :=
  { g with
    commutes' := fun r => by
      rw [Subsingleton.elim (algebraMap ℤ R) (Int.castRingHom R),
        Subsingleton.elim (algebraMap ℤ S) (Int.castRingHom S)]
      simp }

@[scoped simp] theorem intAlgHom_apply {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S]
    (g : R →+* S) (x : R) : intAlgHom g x = g x := rfl

@[scoped simp] theorem coe_intAlgHom {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S]
    (g : R →+* S) : (intAlgHom g : R →+* S) = g := rfl

end IntAlgHom

section Points

variable {K₀ K : Type} [CommRing K₀] [CommRing K] [HopfAlgebra ℤ K₀] [HopfAlgebra ℤ K]
  (ψ : K₀ →ₐc[ℤ] K)

noncomputable def precomp (A : Type) [CommRing A] :
    WithConv (K →ₐ[ℤ] A) →* WithConv (K₀ →ₐ[ℤ] A) where
  toFun w := WithConv.toConv (w.ofConv.comp (ψ : K₀ →ₐ[ℤ] K))
  map_one' := by
    rw [AlgHom.convOne_def, AlgHom.convOne_def]
    congr 1
    rw [AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    apply WithConv.ofConv_injective
    change AlgHom.comp (f * g).ofConv (ψ : K₀ →ₐ[ℤ] K) = _
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[scoped simp] theorem precomp_apply (A : Type) [CommRing A] (w : WithConv (K →ₐ[ℤ] A)) (x : K₀) :
    precomp ψ A w x = w (ψ x) := rfl

theorem precomp_ofConv (A : Type) [CommRing A] (w : WithConv (K →ₐ[ℤ] A)) :
    (precomp ψ A w).ofConv = w.ofConv.comp (ψ : K₀ →ₐ[ℤ] K) := rfl

variable [Algebra K₀ K] (f : K₀) (hf : IsLocalization.Away f K)
include hf

theorem algHom_ext_of_comp_eq (hψ : ∀ x, algebraMap K₀ K x = ψ x) {A : Type} [CommRing A]
    (φ₁ φ₂ : K →ₐ[ℤ] A)
    (h : φ₁.comp (ψ : K₀ →ₐ[ℤ] K) = φ₂.comp (ψ : K₀ →ₐ[ℤ] K)) : φ₁ = φ₂ := by
  apply AlgHom.coe_ringHom_injective
  haveI := hf
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, hψ]
  exact congrArg (fun χ : K₀ →ₐ[ℤ] A => χ x) h

theorem precomp_injective (hψ : ∀ x, algebraMap K₀ K x = ψ x) (A : Type) [CommRing A] :
    Function.Injective (precomp ψ A) := by
  intro w₁ w₂ h
  apply WithConv.ofConv_injective
  exact algHom_ext_of_comp_eq ψ f hf hψ _ _ (congrArg WithConv.ofConv h)

theorem exists_comp_eq_of_isUnit (hψ : ∀ x, algebraMap K₀ K x = ψ x) {A : Type} [CommRing A]
    (φ₀ : K₀ →ₐ[ℤ] A) (hu : IsUnit (φ₀ f)) :
    ∃ φ : K →ₐ[ℤ] A, φ.comp (ψ : K₀ →ₐ[ℤ] K) = φ₀ := by
  haveI := hf
  have hu' : IsUnit ((φ₀ : K₀ →+* A) f) := hu
  refine ⟨intAlgHom (IsLocalization.Away.lift f hu'), ?_⟩
  apply AlgHom.coe_ringHom_injective
  ext x
  change IsLocalization.Away.lift f hu' (ψ x) = φ₀ x
  rw [← hψ]
  exact IsLocalization.Away.lift_eq f hu' x

theorem isUnit_apply (hψ : ∀ x, algebraMap K₀ K x = ψ x) (A : Type) [CommRing A]
    (φ : K →ₐ[ℤ] A) : IsUnit (φ (ψ f)) := by
  haveI := hf
  rw [← hψ]
  exact (IsLocalization.Away.algebraMap_isUnit f).map φ

end Points

section Engine

variable {K₀ K : Type} [CommRing K₀] [CommRing K] [HopfAlgebra ℤ K₀] [HopfAlgebra ℤ K]
  (ψ : K₀ →ₐc[ℤ] K)
  (X C : Sheaf Scheme.fppfTopology.{0} Ab.{1})
  (eb : ∀ T : Scheme.{0}, X.obj.obj (op T) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))))
  (eC : ∀ T : Scheme.{0}, C.obj.obj (op T) ≃+ Additive (WithConv (K₀ →ₐ[ℤ] Γ(T, ⊤))))

noncomputable def iotaApp (T : Scheme.{0}) : X.obj.obj (op T) →+ C.obj.obj (op T) :=
  (eC T).symm.toAddMonoidHom.comp
    ((MonoidHom.toAdditive (precomp ψ Γ(T, ⊤))).comp (eb T).toAddMonoidHom)

theorem eC_iotaApp (T : Scheme.{0}) (s : X.obj.obj (op T)) :
    eC T (iotaApp ψ X C eb eC T s) =
      Additive.ofMul (precomp ψ Γ(T, ⊤) (Additive.toMul (eb T s))) := by
  simp [iotaApp]

theorem toMul_eC_iotaApp_apply (T : Scheme.{0}) (s : X.obj.obj (op T)) (k : K₀) :
    Additive.toMul (eC T (iotaApp ψ X C eb eC T s)) k = Additive.toMul (eb T s) (ψ k) := by
  rw [eC_iotaApp]; rfl

variable
  (enatb : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : X.obj.obj (op T')) (k : K),
      (Additive.toMul (eb T (X.obj.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (eb T' s)) k))
  (eCnat : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : C.obj.obj (op T')) (k : K₀),
      (Additive.toMul (eC T (C.obj.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (eC T' s)) k))

theorem eC_ext {T : Scheme.{0}} {s₁ s₂ : C.obj.obj (op T)}
    (h : ∀ k : K₀, Additive.toMul (eC T s₁) k = Additive.toMul (eC T s₂) k) : s₁ = s₂ := by
  apply (eC T).injective
  apply Additive.toMul.injective
  apply WithConv.ofConv_injective
  exact AlgHom.ext h

include enatb eCnat in

noncomputable def iota : X ⟶ C :=
  ObjectProperty.homMk
    { app := fun T => AddCommGrpCat.ofHom (iotaApp ψ X C eb eC T.unop)
      naturality := fun T T' g => by
        ext s
        change iotaApp ψ X C eb eC T'.unop (X.obj.map g s) =
          C.obj.map g (iotaApp ψ X C eb eC T.unop s)
        apply eC_ext C eC
        intro k
        rw [toMul_eC_iotaApp_apply, show g = g.unop.op from rfl, enatb, eCnat,
          toMul_eC_iotaApp_apply] }

@[scoped simp] theorem iota_app_apply (T : Scheme.{0}) (s : X.obj.obj (op T)) :
    (iota ψ X C eb eC enatb eCnat).hom.app (op T) s = iotaApp ψ X C eb eC T s := rfl

end Engine

section EngineTwo

variable {K₀ K : Type} [CommRing K₀] [CommRing K] [HopfAlgebra ℤ K₀] [HopfAlgebra ℤ K]
  (ψ : K₀ →ₐc[ℤ] K)
  (X C : Sheaf Scheme.fppfTopology.{0} Ab.{1})
  (eb : ∀ T : Scheme.{0}, X.obj.obj (op T) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))))
  (eC : ∀ T : Scheme.{0}, C.obj.obj (op T) ≃+ Additive (WithConv (K₀ →ₐ[ℤ] Γ(T, ⊤))))
  (enatb : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : X.obj.obj (op T')) (k : K),
      (Additive.toMul (eb T (X.obj.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (eb T' s)) k))
  (eCnat : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : C.obj.obj (op T')) (k : K₀),
      (Additive.toMul (eC T (C.obj.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (eC T' s)) k))
  [Algebra K₀ K] (f : K₀) (hf : IsLocalization.Away f K) (hψ : ∀ x, algebraMap K₀ K x = ψ x)

include hf hψ in
theorem iotaApp_injective (T : Scheme.{0}) : Function.Injective (iotaApp ψ X C eb eC T) := by
  intro s₁ s₂ h
  have h' := congrArg (eC T) h
  rw [eC_iotaApp, eC_iotaApp] at h'
  have h2 := precomp_injective ψ f hf hψ _ (Additive.ofMul.injective h')
  exact (eb T).injective (Additive.toMul.injective h2)

include hf hψ in
theorem mono_iota : Mono (iota ψ X C eb eC enatb eCnat) := by
  haveI : ∀ T, Mono ((iota ψ X C eb eC enatb eCnat).hom.app T) := fun T =>
    ConcreteCategory.mono_of_injective _ (iotaApp_injective ψ X C eb eC f hf hψ T.unop)
  haveI : Mono (iota ψ X C eb eC enatb eCnat).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

noncomputable def ses : ShortComplex (Sheaf Scheme.fppfTopology.{0} Ab.{1}) :=
  ShortComplex.mk (iota ψ X C eb eC enatb eCnat) (cokernel.π (iota ψ X C eb eC enatb eCnat))
    (cokernel.condition _)

include hf hψ in
theorem ses_shortExact : (ses ψ X C eb eC enatb eCnat).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := mono_iota ψ X C eb eC enatb eCnat f hf hψ
  epi_g := (inferInstance : Epi (cokernel.π (iota ψ X C eb eC enatb eCnat)))

theorem natCast_eq_zero_of_hom {A : CommRingCat.{0}} {p : ℕ} (hp : (p : A) = 0) {Y : Scheme.{0}}
    (g : Y ⟶ Spec A) : (p : Γ(Y, ⊤)) = 0 := by
  have := congrArg ((Scheme.ΓSpecIso A).inv ≫ g.appTop).hom hp
  simpa using this

include hf hψ in

theorem cohomologyMap_iota_injective (p : ℕ)
    (h3' : ∀ (R : Type) [CommRing R], (p : R) = 0 → ∀ φ₀ : K₀ →ₐ[ℤ] R, IsUnit (φ₀ f) →
        ∀ x, φ₀ x = algebraMap ℤ R (Bialgebra.counitAlgHom ℤ K₀ x))
    (h4' : ∀ (R : Type) [CommRing R] [Module.Flat ℤ R] (φ₀ : K₀ →ₐ[ℤ] R),
        (∀ x, Ideal.Quotient.mk (Ideal.span {(p : R)}) (φ₀ x) =
          algebraMap ℤ _ (Bialgebra.counitAlgHom ℤ K₀ x)) → IsUnit (φ₀ f))
    (h5' : ∀ χ : K₀ →ₐ[ℤ] ZMod p, ∃ χ' : K₀ →ₐ[ℤ] ℤ, ∀ x, (χ' x : ZMod p) = χ x) :
    Function.Injective
      (FppfCohomologyLES.cohomologyMap (iota ψ X C eb eC enatb eCnat) 1) := by
  set Z₀ : Scheme.{0} := Spec (CommRingCat.of (ZMod p)) with hZ₀
  refine (AlgebraicGeometry.fppfCohomologyMap_one_injective_of_shortExact_of_subsingleton_over
    Z₀ (ses_shortExact ψ X C eb eC enatb eCnat f hf hψ) ?_ ?_ ?_).2
  ·
    intro Y g
    have hp0 : (p : Γ(Y, ⊤)) = 0 :=
      natCast_eq_zero_of_hom (A := CommRingCat.of (ZMod p)) (ZMod.natCast_self p) g
    refine ⟨fun s₁ s₂ => (eb Y).injective (Additive.toMul.injective
      (WithConv.ofConv_injective (algHom_ext_of_comp_eq ψ f hf hψ _ _ ?_)))⟩
    ext x
    have e1 := h3' _ hp0 ((Additive.toMul (eb Y s₁)).ofConv.comp (ψ : K₀ →ₐ[ℤ] K))
        (isUnit_apply ψ f hf hψ _ _) x
    have e2 := h3' _ hp0 ((Additive.toMul (eb Y s₂)).ofConv.comp (ψ : K₀ →ₐ[ℤ] K))
        (isUnit_apply ψ f hf hψ _ _) x
    rw [AlgHom.comp_apply] at e1 e2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, e1, e2]
  ·
    intro R _ _ s hs0

    let I : Ideal R := Ideal.span {(p : R)}
    let q : R →+* R ⧸ I := Ideal.Quotient.mk I
    let k : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom q)
    have hpq : (p : R ⧸ I) = 0 := by
      rw [← map_natCast q]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    let r₀ : ZMod p →+* R ⧸ I :=
      (Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom (R ⧸ I)) (by
        intro a ha
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
        simp [hpq])).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom
    have hk : C.obj.map k.op s = 0 := hs0 _ k (Spec.map (CommRingCat.ofHom r₀))

    let w : WithConv (K₀ →ₐ[ℤ] Γ(Spec (CommRingCat.of R), ⊤)) := Additive.toMul (eC _ s)
    let eR := Scheme.ΓSpecIso (CommRingCat.of R)
    let φ₀ : K₀ →ₐ[ℤ] R := intAlgHom (eR.hom.hom.comp (w.ofConv : K₀ →+* _))

    have hφ₀ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : R)}) (φ₀ x) =
        algebraMap ℤ _ (Bialgebra.counitAlgHom ℤ K₀ x) := by
      intro x
      have h1 : Additive.toMul (eC _ (C.obj.map k.op s)) x =
          (1 : WithConv (K₀ →ₐ[ℤ] Γ(Spec (CommRingCat.of (R ⧸ I)), ⊤))) x := by
        rw [hk, map_zero]; rfl
      rw [eCnat, AlgHom.convOne_apply, Scheme.Γ_map_op] at h1
      have h1' : (Spec.map (CommRingCat.ofHom q)).appTop.hom (w.ofConv x) =
          algebraMap ℤ _ (Bialgebra.counitAlgHom ℤ K₀ x) := h1
      have hnat := congrArg (fun φ => φ.hom (w.ofConv x))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
      rw [h1'] at hnat
      change q (eR.hom.hom (w.ofConv x)) = _
      rw [← hnat, Subsingleton.elim (algebraMap ℤ (Γ(Spec (CommRingCat.of (R ⧸ I)), ⊤) : Type))
          (Int.castRingHom _), Subsingleton.elim (algebraMap ℤ (R ⧸ I)) (Int.castRingHom _)]
      simp
    have hu : IsUnit (φ₀ f) := h4' R φ₀ hφ₀
    have hu' : IsUnit (w f) := by
      have := hu.map eR.inv.hom
      change IsUnit (eR.inv (eR.hom (w f))) at this
      rwa [← CommRingCat.comp_apply, Iso.hom_inv_id] at this
    obtain ⟨φ, hφ⟩ := exists_comp_eq_of_isUnit ψ f hf hψ w.ofConv hu'
    refine ⟨(eb _).symm (Additive.ofMul (WithConv.toConv φ)), ?_⟩
    change (iota ψ X C eb eC enatb eCnat).hom.app _ _ = s
    rw [iota_app_apply]
    apply eC_ext C eC
    intro x
    rw [toMul_eC_iotaApp_apply, AddEquiv.apply_symm_apply, toMul_ofMul]
    exact congrArg (fun χ : K₀ →ₐ[ℤ] _ => χ x) hφ
  ·
    intro cbar
    set π : Z₀ ⟶ Spec (CommRingCat.of ℤ) := specZIsTerminal.from Z₀ with hπ
    have hπ' : π = Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p))) :=
      specZIsTerminal.hom_ext _ _
    let w : WithConv (K₀ →ₐ[ℤ] Γ(Z₀, ⊤)) := Additive.toMul (eC Z₀ cbar)
    let χ : K₀ →ₐ[ℤ] ZMod p :=
      intAlgHom ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).hom.hom.comp (w.ofConv : K₀ →+* _))
    obtain ⟨χ', hχ'⟩ := h5' χ
    let w' : WithConv (K₀ →ₐ[ℤ] Γ(Spec (CommRingCat.of ℤ), ⊤)) :=
      WithConv.toConv (intAlgHom
        ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.comp (χ' : K₀ →+* ℤ)))
    refine ⟨(eC _).symm (Additive.ofMul w'), ?_⟩
    apply eC_ext C eC
    intro k
    change Additive.toMul (eC Z₀ (C.obj.map π.op ((eC _).symm (Additive.ofMul w')))) k = _
    rw [eCnat, AddEquiv.apply_symm_apply, toMul_ofMul]
    change (Scheme.Γ.map π.op) ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv (χ' k)) = w k
    rw [hπ', Scheme.Γ_map_op]
    have hnat := congrArg (fun φ => φ.hom (χ' k))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Int.castRingHom (ZMod p))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
    change (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod p)))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom (χ' k)) = w.ofConv k
    rw [← hnat]
    change (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv.hom ((χ' k : ℤ) : ZMod p) = w.ofConv k
    rw [hχ' k]
    change (Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).hom.hom (w.ofConv k)) = w.ofConv k
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]

end EngineTwo

section SplitModel

theorem pi_two_eq (v : Fin 2 → ℤ) :
    v = v 0 • (Pi.single 0 1 : Fin 2 → ℤ) + v 1 • (Pi.single 1 1 : Fin 2 → ℤ) := by
  ext i; fin_cases i <;> simp

theorem pi_two_single_zero_eq : (Pi.single 0 1 : Fin 2 → ℤ) = 1 - Pi.single 1 1 := by
  ext i; fin_cases i <;> simp

variable {R : Type} [CommRing R]

theorem ringHom_pi_two_apply (χ : (Fin 2 → ℤ) →+* R) (v : Fin 2 → ℤ) :
    χ v = (v 0 : R) * (1 - χ (Pi.single 1 1)) + (v 1 : R) * χ (Pi.single 1 1) := by
  conv_lhs => rw [pi_two_eq v]
  rw [map_add, map_zsmul, map_zsmul, pi_two_single_zero_eq, map_sub, map_one, zsmul_eq_mul,
    zsmul_eq_mul]

theorem isIdempotentElem_ringHom_pi_two (χ : (Fin 2 → ℤ) →+* R) :
    IsIdempotentElem (χ (Pi.single 1 1)) := by
  rw [IsIdempotentElem, ← map_mul]
  congr 1
  ext i; fin_cases i <;> simp

variable {K₀ : Type} [CommRing K₀] [HopfAlgebra ℤ K₀] (e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ))
  {p : ℕ} {f : K₀} (hef : e f = ![1, (p : ℤ)])
  (hcounit : ∀ x : K₀, Bialgebra.counitAlgHom ℤ K₀ x = e x 0)

def splitChar (φ₀ : K₀ →ₐ[ℤ] R) : (Fin 2 → ℤ) →+* R :=
  (φ₀ : K₀ →+* R).comp (e.symm : (Fin 2 → ℤ) →+* K₀)

theorem splitChar_apply (φ₀ : K₀ →ₐ[ℤ] R) (x : K₀) : φ₀ x = splitChar e φ₀ (e x) := by
  simp [splitChar]

include hef in
theorem splitChar_f (φ₀ : K₀ →ₐ[ℤ] R) :
    φ₀ f = (1 - splitChar e φ₀ (Pi.single 1 1)) + (p : R) * splitChar e φ₀ (Pi.single 1 1) := by
  rw [splitChar_apply e φ₀ f, hef, ringHom_pi_two_apply]
  simp

include hef hcounit in

theorem split_h3 (hp : (p : R) = 0) (φ₀ : K₀ →ₐ[ℤ] R) (hu : IsUnit (φ₀ f)) (x : K₀) :
    φ₀ x = algebraMap ℤ R (Bialgebra.counitAlgHom ℤ K₀ x) := by
  set ε := splitChar e φ₀ (Pi.single 1 1) with hε
  have hid : IsIdempotentElem ε := isIdempotentElem_ringHom_pi_two _
  rw [splitChar_f e hef, hp, zero_mul, add_zero] at hu

  have h1 : 1 - ε = 1 := by
    obtain ⟨u, hu⟩ := hu
    have hid' : IsIdempotentElem (1 - ε) := hid.one_sub
    have : (u : R) * u = u := by rw [hu]; exact hid'
    have h := congrArg (fun z => (↑u⁻¹ : R) * z) this
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h
    rw [← hu, h]
  have hε0 : ε = 0 := by
    have := congrArg (fun z => 1 - z) h1
    simpa using this
  rw [hcounit, splitChar_apply e φ₀ x, ringHom_pi_two_apply, ← hε, hε0]
  simp

include hef hcounit in

theorem split_h4 (φ₀ : K₀ →ₐ[ℤ] R)
    (hφ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : R)}) (φ₀ x) =
      algebraMap ℤ _ (Bialgebra.counitAlgHom ℤ K₀ x)) : IsUnit (φ₀ f) := by
  set ε := splitChar e φ₀ (Pi.single 1 1) with hε
  have hid : IsIdempotentElem ε := isIdempotentElem_ringHom_pi_two _

  have hεp : ε ∈ Ideal.span {(p : R)} := by
    have h := hφ (e.symm (Pi.single 1 1))
    rw [hcounit, splitChar_apply e φ₀, AlgEquiv.apply_symm_apply] at h
    simp at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hεp
  rw [splitChar_f e hef, ← hε]
  refine IsUnit.of_mul_eq_one ((1 - ε) + t * ε) ?_
  linear_combination (2 - t - (p : R) + ε) * hid.eq + ε ^ 2 * ht

end SplitModel

section SplitModelTwo

variable {K₀ : Type} [CommRing K₀] [HopfAlgebra ℤ K₀] (e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ))

theorem split_ext {R : Type} [CommRing R] (φ₁ φ₂ : K₀ →ₐ[ℤ] R)
    (h : splitChar e φ₁ (Pi.single 1 1) = splitChar e φ₂ (Pi.single 1 1)) : φ₁ = φ₂ := by
  ext x
  rw [splitChar_apply e φ₁, splitChar_apply e φ₂, ringHom_pi_two_apply (splitChar e φ₁) (e x),
    ringHom_pi_two_apply (splitChar e φ₂) (e x), h]

theorem splitChar_eq_zero_or_one {R : Type} [CommRing R] [NoZeroDivisors R] (φ : K₀ →ₐ[ℤ] R) :
    splitChar e φ (Pi.single 1 1) = 0 ∨ splitChar e φ (Pi.single 1 1) = 1 := by
  have hid := isIdempotentElem_ringHom_pi_two (splitChar e φ)
  rcases mul_eq_zero.mp (show splitChar e φ (Pi.single 1 1) *
      (splitChar e φ (Pi.single 1 1) - 1) = 0 by rw [mul_sub, mul_one, hid.eq, sub_self])
    with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

noncomputable def splitBool {R : Type} [CommRing R] (φ : K₀ →ₐ[ℤ] R) : Bool := by
  classical exact decide (splitChar e φ (Pi.single 1 1) = 1)

theorem splitBool_injective {R : Type} [CommRing R] [NoZeroDivisors R] [Nontrivial R] :
    Function.Injective (splitBool (R := R) e) := by
  classical
  intro φ₁ φ₂ h
  apply split_ext e
  simp only [splitBool, decide_eq_decide] at h
  rcases splitChar_eq_zero_or_one e φ₁ with h1 | h1 <;>
    rcases splitChar_eq_zero_or_one e φ₂ with h2 | h2 <;> simp_all

theorem split_finite (e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ)) {L : Type} [Field L] : Finite (K₀ →ₐ[ℤ] L) :=
  Finite.of_injective _ (splitBool_injective (R := L) e)

theorem split_natCard_le (e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ)) {L : Type} [Field L] :
    Nat.card (K₀ →ₐ[ℤ] L) ≤ 2 :=
  calc Nat.card (K₀ →ₐ[ℤ] L) ≤ Nat.card Bool :=
        Nat.card_le_card_of_injective _ (splitBool_injective (R := L) e)
    _ = 2 := by simp

theorem split_h5 (e : K₀ ≃ₐ[ℤ] (Fin 2 → ℤ)) {p : ℕ} [Fact p.Prime] (χ : K₀ →ₐ[ℤ] ZMod p) :
    ∃ χ' : K₀ →ₐ[ℤ] ℤ, ∀ x, (χ' x : ZMod p) = χ x := by
  rcases splitChar_eq_zero_or_one e χ with h0 | h1
  · refine ⟨(Pi.evalAlgHom ℤ (fun _ : Fin 2 => ℤ) 0).comp (e : K₀ →ₐ[ℤ] (Fin 2 → ℤ)),
      fun x => ?_⟩
    rw [splitChar_apply e χ x, ringHom_pi_two_apply, h0]
    simp
  · refine ⟨(Pi.evalAlgHom ℤ (fun _ : Fin 2 => ℤ) 1).comp (e : K₀ →ₐ[ℤ] (Fin 2 → ℤ)),
      fun x => ?_⟩
    rw [splitChar_apply e χ x, ringHom_pi_two_apply, h1]
    simp

end SplitModelTwo

section MuModel

abbrev GrpAlgTwo : Type := MonoidAlgebra ℤ (Multiplicative (ZMod 2))

abbrev gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem gen_mul_gen : gen * gen = 1 := by decide

theorem eq_one_or_eq_gen (a : Multiplicative (ZMod 2)) : a = 1 ∨ a = gen := by
  revert a; decide

variable {R : Type} [CommRing R]

theorem ringHom_grpAlg_sq (χ : GrpAlgTwo →+* R) :
    χ (MonoidAlgebra.single gen 1) * χ (MonoidAlgebra.single gen 1) = 1 := by
  rw [← map_mul, MonoidAlgebra.single_mul_single, gen_mul_gen, mul_one, ← MonoidAlgebra.one_def,
    map_one]

theorem ringHom_grpAlg_single (χ : GrpAlgTwo →+* R) (a : Multiplicative (ZMod 2)) (c : ℤ) :
    χ (MonoidAlgebra.single a c) = (c : R) * χ (MonoidAlgebra.single a 1) := by
  have : MonoidAlgebra.single a c = (c : GrpAlgTwo) * MonoidAlgebra.single a (1 : ℤ) := by
    rw [MonoidAlgebra.intCast_def, MonoidAlgebra.single_mul_single, one_mul, Int.cast_id, mul_one]
  rw [this, map_mul, map_intCast]

theorem ringHom_grpAlg_f (χ : GrpAlgTwo →+* R) (α β : ℤ) :
    χ (MonoidAlgebra.single 1 α + MonoidAlgebra.single gen β) =
      (α : R) + (β : R) * χ (MonoidAlgebra.single gen 1) := by
  rw [map_add, ringHom_grpAlg_single χ 1 α, ringHom_grpAlg_single χ gen β, ← MonoidAlgebra.one_def,
    map_one, mul_one]

theorem ringHom_grpAlg_ext (χ₁ χ₂ : GrpAlgTwo →+* R)
    (h : χ₁ (MonoidAlgebra.single gen 1) = χ₂ (MonoidAlgebra.single gen 1)) : χ₁ = χ₂ := by
  refine MonoidAlgebra.ringHom_ext (fun b => ?_) (fun a => ?_)
  · rw [ringHom_grpAlg_single χ₁, ringHom_grpAlg_single χ₂, ← MonoidAlgebra.one_def, map_one,
      map_one]
  · rcases eq_one_or_eq_gen a with rfl | rfl
    · rw [← MonoidAlgebra.one_def, map_one, map_one]
    · exact h

theorem counit_grpAlg_single_gen :
    Bialgebra.counitAlgHom ℤ GrpAlgTwo (MonoidAlgebra.single gen 1) = 1 := by
  simp

variable {K₀ : Type} [CommRing K₀] [HopfAlgebra ℤ K₀] (e : K₀ ≃ₐc[ℤ] GrpAlgTwo)

noncomputable def muChar (φ₀ : K₀ →ₐ[ℤ] R) : GrpAlgTwo →+* R :=
  (φ₀ : K₀ →+* R).comp ((e.symm : GrpAlgTwo ≃ₐc[ℤ] K₀) : GrpAlgTwo →+* K₀)

theorem muChar_apply (φ₀ : K₀ →ₐ[ℤ] R) (x : K₀) : φ₀ x = muChar e φ₀ (e x) := by
  simp [muChar]

theorem counit_eq_counit_grpAlg (x : K₀) :
    (Bialgebra.counitAlgHom ℤ K₀ x : ℤ) = Bialgebra.counitAlgHom ℤ GrpAlgTwo (e x) := by
  have h := BialgHom.counitAlgHom_comp (e : K₀ →ₐc[ℤ] GrpAlgTwo)
  exact (congrArg (fun χ : K₀ →ₐ[ℤ] ℤ => χ x) h).symm

theorem mu_ext (φ₁ φ₂ : K₀ →ₐ[ℤ] R)
    (h : muChar e φ₁ (MonoidAlgebra.single gen 1) = muChar e φ₂ (MonoidAlgebra.single gen 1)) :
    φ₁ = φ₂ := by
  ext x
  rw [muChar_apply e φ₁, muChar_apply e φ₂, ringHom_grpAlg_ext _ _ h]

theorem mu_eq_counit_of_eq_one (φ₀ : K₀ →ₐ[ℤ] R)
    (h : muChar e φ₀ (MonoidAlgebra.single gen 1) = 1) (x : K₀) :
    φ₀ x = algebraMap ℤ R (Bialgebra.counitAlgHom ℤ K₀ x) := by
  rw [counit_eq_counit_grpAlg e, muChar_apply e φ₀ x]
  have : muChar e φ₀ =
      (algebraMap ℤ R).comp (Bialgebra.counitAlgHom ℤ GrpAlgTwo : GrpAlgTwo →+* ℤ) := by
    apply ringHom_grpAlg_ext
    rw [h, RingHom.comp_apply]
    change (1 : R) =
      algebraMap ℤ R (Bialgebra.counitAlgHom ℤ GrpAlgTwo (MonoidAlgebra.single gen 1))
    rw [counit_grpAlg_single_gen, map_one]
  rw [this]
  rfl

theorem muChar_counit_single_gen :
    muChar e ((Bialgebra.counitAlgHom ℤ K₀ : K₀ →ₐ[ℤ] ℤ)) (MonoidAlgebra.single gen 1) = 1 := by
  have := muChar_apply e (Bialgebra.counitAlgHom ℤ K₀ : K₀ →ₐ[ℤ] ℤ)
    (e.symm (MonoidAlgebra.single gen 1))
  rw [BialgEquiv.apply_symm_apply] at this
  rw [← this, counit_eq_counit_grpAlg e, BialgEquiv.apply_symm_apply, counit_grpAlg_single_gen]

variable {p : ℕ} {f : K₀}
  (hef : e f = MonoidAlgebra.single 1 (((p : ℤ) + 1) / 2) +
    MonoidAlgebra.single (Multiplicative.ofAdd 1) ((1 - (p : ℤ)) / 2))

include hef in
theorem mu_two_mul_f (hp : Odd p) (φ₀ : K₀ →ₐ[ℤ] R) :
    2 * φ₀ f = ((p : R) + 1) + (1 - (p : R)) * muChar e φ₀ (MonoidAlgebra.single gen 1) := by
  rw [muChar_apply e φ₀ f, hef]
  change 2 * muChar e φ₀ (MonoidAlgebra.single 1 _ + MonoidAlgebra.single gen _) = _
  rw [ringHom_grpAlg_f, mul_add, ← mul_assoc]
  have h2 : (2 : ℤ) ∣ (p : ℤ) + 1 := by
    obtain ⟨m, rfl⟩ := hp; exact ⟨m + 1, by push_cast; ring⟩
  have h2' : (2 : ℤ) ∣ 1 - (p : ℤ) := by
    obtain ⟨m, rfl⟩ := hp; exact ⟨-m, by push_cast; ring⟩
  have hα : (2 : R) * ((((p : ℤ) + 1) / 2 : ℤ) : R) = (p : R) + 1 := by
    rw [← Int.cast_two (R := R), ← Int.cast_mul, Int.mul_ediv_cancel' h2]; push_cast; ring
  have hβ : (2 : R) * (((1 - (p : ℤ)) / 2 : ℤ) : R) = 1 - (p : R) := by
    rw [← Int.cast_two (R := R), ← Int.cast_mul, Int.mul_ediv_cancel' h2']; push_cast; ring
  rw [hα, hβ]

include hef in

theorem mu_h3 (hp : Odd p) (hpR : (p : R) = 0) (φ₀ : K₀ →ₐ[ℤ] R) (hu : IsUnit (φ₀ f))
    (x : K₀) : φ₀ x = algebraMap ℤ R (Bialgebra.counitAlgHom ℤ K₀ x) := by
  apply mu_eq_counit_of_eq_one e
  set r := muChar e φ₀ (MonoidAlgebra.single gen 1) with hr
  have hsq : r * r = 1 := ringHom_grpAlg_sq _
  have h2f := mu_two_mul_f e hef hp φ₀
  rw [hpR, zero_add, sub_zero, one_mul, ← hr] at h2f

  have hu' : IsUnit (1 + r) := by
    rw [← h2f]
    refine (IsUnit.mul ?_ hu)

    obtain ⟨m, hm⟩ := hp
    refine IsUnit.of_mul_eq_one (-(m : R)) ?_
    have : ((2 * m + 1 : ℕ) : R) = 0 := by rw [← hm]; exact hpR
    push_cast at this
    linear_combination -this
  have h0 : (1 + r) * (1 - r) = 0 := by linear_combination -hsq
  obtain ⟨u, hu''⟩ := hu'
  have : (1 - r) = 0 := by
    have := congrArg (fun z => (↑u⁻¹ : R) * z) h0
    simp only [mul_zero] at this
    rwa [← hu'', ← mul_assoc, Units.inv_mul, one_mul] at this
  linear_combination -this

theorem eq_zero_of_natCast_mul_eq_zero [Module.Flat ℤ R] (hp0 : p ≠ 0) {t : R}
    (h : (p : R) * t = 0) : t = 0 := by
  have hreg : IsSMulRegular R ((p : ℤ)) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp0))
  apply hreg
  change ((p : ℤ)) • t = ((p : ℤ)) • (0 : R)
  rw [smul_zero, zsmul_eq_mul, Int.cast_natCast, h]

include hef in

theorem mu_h4 (hp : Odd p) [Module.Flat ℤ R] (φ₀ : K₀ →ₐ[ℤ] R)
    (hφ : ∀ x, Ideal.Quotient.mk (Ideal.span {(p : R)}) (φ₀ x) =
      algebraMap ℤ _ (Bialgebra.counitAlgHom ℤ K₀ x)) : IsUnit (φ₀ f) := by
  have hp0 : p ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hp).elim
  set r := muChar e φ₀ (MonoidAlgebra.single gen 1) with hr
  have hsq : r * r = 1 := ringHom_grpAlg_sq _

  have hr1 : r - 1 ∈ Ideal.span {(p : R)} := by
    have h := hφ (e.symm (MonoidAlgebra.single gen 1))
    rw [muChar_apply e φ₀, BialgEquiv.apply_symm_apply, ← hr, counit_eq_counit_grpAlg e,
      BialgEquiv.apply_symm_apply, counit_grpAlg_single_gen, map_one] at h
    rw [← Ideal.Quotient.eq, h, map_one]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hr1

  have hpt : (p : R) * (2 * t + (p : R) * t ^ 2) = 0 := by
    have : r = 1 + t * p := by linear_combination -ht
    rw [this] at hsq
    linear_combination hsq
  have ht0 : 2 * t + (p : R) * t ^ 2 = 0 := eq_zero_of_natCast_mul_eq_zero hp0 hpt

  have h2f := mu_two_mul_f e hef hp φ₀
  set β : R := (((1 - (p : ℤ)) / 2 : ℤ) : R) with hβ
  have h2' : (2 : ℤ) ∣ 1 - (p : ℤ) := by
    obtain ⟨m, rfl⟩ := hp; exact ⟨-m, by push_cast; ring⟩
  have hβ2 : (2 : R) * β = 1 - (p : R) := by
    rw [hβ, ← Int.cast_two (R := R), ← Int.cast_mul, Int.mul_ediv_cancel' h2']; push_cast; ring
  have hval : φ₀ f = 1 + β * (p : R) * t := by

    rw [muChar_apply e φ₀ f, hef]
    change muChar e φ₀ (MonoidAlgebra.single 1 _ + MonoidAlgebra.single gen _) = _
    rw [ringHom_grpAlg_f, ← hr, ← hβ]
    have h2 : (2 : ℤ) ∣ (p : ℤ) + 1 := by
      obtain ⟨m, rfl⟩ := hp; exact ⟨m + 1, by push_cast; ring⟩
    have hαβ : ((((p : ℤ) + 1) / 2 : ℤ) : R) + β = 1 := by
      rw [hβ, ← Int.cast_add, ← Int.add_ediv_of_dvd_left h2]
      have : (p : ℤ) + 1 + (1 - (p : ℤ)) = 2 := by ring
      rw [this]; simp
    have hr' : r = 1 + t * (p : R) := by linear_combination -ht
    rw [hr']
    linear_combination hαβ
  rw [hval]
  refine IsUnit.of_mul_eq_one (1 - β * t) ?_
  linear_combination (β * t) * hβ2 + (-β ^ 2) * ht0

omit [CommRing R] in

theorem mu_h5 (e : K₀ ≃ₐc[ℤ] GrpAlgTwo) {p : ℕ} [Fact p.Prime] (χ : K₀ →ₐ[ℤ] ZMod p) :
    ∃ χ' : K₀ →ₐ[ℤ] ℤ, ∀ x, (χ' x : ZMod p) = χ x := by
  set r := muChar e χ (MonoidAlgebra.single gen 1) with hr
  have hsq : r * r = 1 := ringHom_grpAlg_sq _
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · refine ⟨(Bialgebra.counitAlgHom ℤ K₀ : K₀ →ₐ[ℤ] ℤ), fun x => ?_⟩
    rw [mu_eq_counit_of_eq_one e χ h1 x]
    simp
  ·
    let σ : Multiplicative (ZMod 2) →* ℤ :=
      { toFun := fun a => if a = 1 then 1 else -1
        map_one' := by simp
        map_mul' := by decide }
    let χneg : GrpAlgTwo →ₐ[ℤ] ℤ := MonoidAlgebra.lift ℤ ℤ (Multiplicative (ZMod 2)) σ
    refine ⟨χneg.comp (e : K₀ →ₐ[ℤ] GrpAlgTwo), fun x => ?_⟩

    have key : (Int.castRingHom (ZMod p)).comp (χneg : GrpAlgTwo →+* ℤ) = muChar e χ := by
      apply ringHom_grpAlg_ext
      rw [← hr, h1, RingHom.comp_apply]
      change (Int.castRingHom (ZMod p)) (MonoidAlgebra.lift ℤ ℤ _ σ (MonoidAlgebra.single gen 1)) = -1
      rw [MonoidAlgebra.lift_single]
      simp [σ]
    have := congrArg (fun χ' : GrpAlgTwo →+* ZMod p => χ' (e x)) key
    simp only [RingHom.comp_apply] at this
    rw [muChar_apply e χ x, ← this]
    rfl

omit [CommRing R] in

theorem mu_subsingleton (e : K₀ ≃ₐc[ℤ] GrpAlgTwo) {L : Type} [Field L] [CharP L 2] :
    Subsingleton (K₀ →ₐ[ℤ] L) := by
  refine ⟨fun φ₁ φ₂ => mu_ext e φ₁ φ₂ ?_⟩
  have h : ∀ φ : K₀ →ₐ[ℤ] L, muChar e φ (MonoidAlgebra.single gen 1) = 1 := by
    intro φ
    have hsq := ringHom_grpAlg_sq (muChar e φ)
    set r := muChar e φ (MonoidAlgebra.single gen 1)
    have h2 : (2 : L) = 0 := by
      have := CharP.cast_eq_zero L 2; exact_mod_cast this
    have : (r - 1) ^ 2 = 0 := by linear_combination hsq + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  rw [h φ₁, h φ₂]

end MuModel

end P2mPuncturedH1
p2m_reactivate "P2MW.S_ModularCurve_exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two.P2mPuncturedH1"

open P2mPuncturedH1 AlgebraicGeometry.Scheme in
theorem solution
    (p : ℕ)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (eb : ∀ T : Scheme.{0},
      X.obj.obj (Opposite.op T) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))))
    (enatb : ∀ {T T' : Scheme.{0}} (g : T ⟶ T') (s : X.obj.obj (Opposite.op T')) (k : K),
      (Additive.toMul (eb T (X.obj.map g.op s))) k
        = (Scheme.Γ.map g.op) ((Additive.toMul (eb T' s)) k))
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (a : ℕ) (ha : Nat.card (K →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a)
    (hK : ¬ Module.Finite ℤ K) :
    ∃ l1 : ℕ, Nat.card (FppfCohomologyLES.FppfH X 1) = 2 ^ l1 ∧ l1 + a ≤ 1 := by
  obtain ⟨hp, K₀, _, _, ψ, f, hloc, hcases⟩ :=
    HopfAlgebra.prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
      p K hff hgen hK
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra K₀ K := (ψ : K₀ →+* K).toAlgebra
  have hψ : ∀ x, algebraMap K₀ K x = ψ x := fun x => rfl

  have hKK₀ : ∀ (L : Type) [Field L], Function.Injective
      (fun φ : K →ₐ[ℤ] L => φ.comp (ψ : K₀ →ₐ[ℤ] K)) := fun L _ φ₁ φ₂ h =>
    algHom_ext_of_comp_eq ψ f hloc hψ φ₁ φ₂ h
  rcases hcases with ⟨e, hef, hcounit⟩ | ⟨hp2, e, hef⟩
  ·
    obtain ⟨eC, eCnat⟩ :=
      AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two K₀ e
    have hinj := cohomologyMap_iota_injective ψ X _ eb eC (fun g s k => enatb g s k)
      (fun g s k => eCnat g s k) f hloc hψ p
      (fun R _ hpR φ₀ hu x => split_h3 e hef hcounit hpR φ₀ hu x)
      (fun R _ _ φ₀ hφ => split_h4 e hef hcounit φ₀ hφ)
      (fun χ => split_h5 e χ)

    haveI := AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime 2
    have hsub : Subsingleton (FppfCohomologyLES.FppfH X 1) :=
      ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    have h1 : Nat.card (FppfCohomologyLES.FppfH X 1) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    refine ⟨0, by rw [h1, pow_zero], ?_⟩

    haveI := split_finite e (L := AlgebraicClosure (ZMod 2))
    have hle : 2 ^ a ≤ 2 ^ 1 := by
      rw [← ha, pow_one]
      exact (Nat.card_le_card_of_injective _ (hKK₀ _)).trans (split_natCard_le e)
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    omega
  ·
    obtain ⟨eC, eCnat⟩ :=
      AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two K₀ e
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have hinj := cohomologyMap_iota_injective ψ X _ eb eC (fun g s k => enatb g s k)
      (fun g s k => eCnat g s k) f hloc hψ p
      (fun R _ hpR φ₀ hu x => mu_h3 e hef hodd hpR φ₀ hu x)
      (fun R _ _ φ₀ hφ => mu_h4 e hef hodd φ₀ hφ)
      (fun χ => mu_h5 e χ)

    have hC2 : Nat.card (FppfCohomologyLES.FppfH (FppfKummerSES.muPAbelianSheafLifted.{0} 2) 1) = 2 := by
      rw [FppfBigSiteH0Gm.kummer_h1_card_value_of_pic_trivial 2 Nat.prime_two
        AlgebraicGeometry.natCard_fppfH1_Gm_specZ_eq_one]
      simp
    have hdvd : Nat.card (FppfCohomologyLES.FppfH X 1) ∣ 2 := by
      rw [← hC2]
      exact AddSubgroup.card_dvd_of_injective _ hinj

    haveI : CharP (AlgebraicClosure (ZMod 2)) 2 :=
      charP_of_injective_algebraMap (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2))).injective 2
    haveI := mu_subsingleton e (L := AlgebraicClosure (ZMod 2))
    have ha0 : a = 0 := by
      have hle : 2 ^ a ≤ 1 := by
        rw [← ha]
        exact (Nat.card_le_card_of_injective _ (hKK₀ _)).trans
          (Finite.card_le_one_iff_subsingleton.mpr inferInstance)
      have := Nat.one_le_two_pow (n := a)
      exact Nat.pow_eq_one.mp (le_antisymm hle this) |>.resolve_left (by norm_num)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact ⟨0, by rw [h1, pow_zero], by omega⟩
    · exact ⟨1, by rw [h2, pow_one], by omega⟩

end S_ModularCurve_exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two
end P2MW
export P2MW.S_ModularCurve_exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two (solution)
