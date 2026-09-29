-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f72e3b64-b915-52d4-a6a6-c0146aef396c

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_Algebra_isReduced_tensorProduct_of_perfectField
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

set_option maxHeartbeats 1600000

p2m_open "Topology TopologicalSpace CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory"
open scoped TensorProduct

namespace H2ALocal

open IsLocalRing

theorem injective_of_surjective_of_isArtinianRing {B : Type*} [CommRing B] [IsArtinianRing B]
    (ψ : B →+* B) (hψ : Function.Surjective ψ) : Function.Injective ψ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hK
  set K : Ideal B := RingHom.ker ψ with hKdef
  let e : B ⧸ K ≃+* B := RingHom.quotientKerEquivOfSurjective hψ
  have h1 : Module.length B (B ⧸ K) < Module.length B B :=
    Submodule.length_quotient_lt (R := B) (M := B) K hK
  have h2 : Module.length B (B ⧸ K) = Module.length (B ⧸ K) (B ⧸ K) :=
    Module.length_eq_of_surjective (S := B) (R := B ⧸ K) (M := B ⧸ K) Ideal.Quotient.mk_surjective
  have h3 : Module.length (B ⧸ K) (B ⧸ K) = Module.length B B := by
    rw [Module.length_eq_height, Module.length_eq_height]
    have := Order.height_orderIso e.idealComapOrderIso (⊤ : Ideal B)
    rw [map_top] at this
    exact this
  rw [h2, h3] at h1
  exact lt_irrefl _ h1

variable {C A : Type*} [CommRing C] [CommRing A] [IsLocalRing A]

theorem exists_sub_map_mem_pow
    (ι₀ : C →+* A) (φ : A →+* A) (hfix : ∀ c, φ (ι₀ c) = ι₀ c)
    (hres : ∀ a : A, ∃ c : C, a - ι₀ c ∈ maximalIdeal A)
    (hφ : (maximalIdeal A).map φ = maximalIdeal A) (n : ℕ) (x : A) :
    ∃ y : A, x - φ y ∈ maximalIdeal A ^ n := by
  have hpow : ∀ m : ℕ, (maximalIdeal A ^ m).map φ = maximalIdeal A ^ m := fun m => by
    rw [Ideal.map_pow, hφ]
  induction n generalizing x with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨y₀, hy₀⟩ := ih x

    have hr : x - φ y₀ ∈ (maximalIdeal A ^ n).map φ := by rw [hpow]; exact hy₀

    suffices H : ∀ s ∈ (maximalIdeal A ^ n).map φ,
        ∃ y ∈ maximalIdeal A ^ n, s - φ y ∈ maximalIdeal A ^ (n + 1) by
      obtain ⟨y, -, hy⟩ := H _ hr
      exact ⟨y₀ + y, by rw [map_add]; convert hy using 1; ring⟩
    intro s hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, by simp⟩
    · rintro s t - - ⟨y, hy, hsy⟩ ⟨z, hz, htz⟩
      exact ⟨y + z, add_mem hy hz, by rw [map_add]; convert add_mem hsy htz using 1; ring⟩
    · rintro a s hs' ⟨y, hy, hsy⟩

      have hsn : s ∈ maximalIdeal A ^ n := by
        have : s = (s - φ y) + φ y := by ring
        rw [this]
        refine add_mem (Ideal.pow_le_pow_right n.le_succ hsy) ?_
        have : φ y ∈ (maximalIdeal A ^ n).map φ := Ideal.mem_map_of_mem _ hy
        rwa [hpow] at this

      obtain ⟨c, hb⟩ := hres a
      refine ⟨ι₀ c * y, Ideal.mul_mem_left _ _ hy, ?_⟩
      have : a • s - φ (ι₀ c * y)
          = ι₀ c * (s - φ y) + (a - ι₀ c) * s := by
        rw [map_mul, hfix, smul_eq_mul]; ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ hsy) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hb hsn

theorem injective_of_map_maximalIdeal_eq [IsNoetherianRing A]
    (ι₀ : C →+* A) (φ : A →+* A) (hfix : ∀ c, φ (ι₀ c) = ι₀ c)
    (hres : ∀ a : A, ∃ c : C, a - ι₀ c ∈ maximalIdeal A)
    (hφ : (maximalIdeal A).map φ = maximalIdeal A) :
    Function.Injective φ := by
  have hpow : ∀ m : ℕ, (maximalIdeal A ^ m).map φ = maximalIdeal A ^ m := fun m => by
    rw [Ideal.map_pow, hφ]
  have hle : ∀ m : ℕ, maximalIdeal A ^ m ≤ (maximalIdeal A ^ m).comap φ := fun m => by
    rw [← Ideal.map_le_iff_le_comap]; exact (hpow m).le

  have hinj : ∀ m : ℕ, 0 < m → ∀ a : A, φ a ∈ maximalIdeal A ^ m → a ∈ maximalIdeal A ^ m := by
    intro m hm a ha
    let ψ : A ⧸ maximalIdeal A ^ m →+* A ⧸ maximalIdeal A ^ m :=
      Ideal.quotientMap (maximalIdeal A ^ m) φ (hle m)
    have hψs : Function.Surjective ψ := by
      intro q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨y, hy⟩ := exists_sub_map_mem_pow ι₀ φ hfix hres hφ m x
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have : (φ y - x) = -(x - φ y) := by simp
      rw [this]
      exact Submodule.neg_mem _ hy
    haveI : IsArtinianRing (A ⧸ maximalIdeal A ^ m) := by
      refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ?_
      refine ⟨⟨inferInstance, Ideal.pow_le_self hm.ne'⟩, ?_⟩
      rintro p ⟨hp, hpm⟩ -
      exact (hp.pow_le_iff hm.ne' |>.mp hpm)
    have hψi := injective_of_surjective_of_isArtinianRing ψ hψs
    have : ψ (Ideal.Quotient.mk _ a) = 0 := by
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]; exact ha
    have := hψi (this.trans (map_zero ψ).symm)
    exact (Ideal.Quotient.eq_zero_iff_mem).mp this
  intro a b hab
  rw [← sub_eq_zero]
  have h0 : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem : ∀ m : ℕ, a - b ∈ maximalIdeal A ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · exact hinj m hm _ (by rw [h0]; exact Submodule.zero_mem _)
  have hKrull := Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have : a - b ∈ (⨅ m : ℕ, maximalIdeal A ^ m) := Ideal.mem_iInf.mpr hmem
  rwa [hKrull, Ideal.mem_bot] at this

theorem isReduced_of_map_maximalIdeal_eq_of_factors [IsNoetherianRing A]
    (ι₀ : C →+* A) (φ : A →+* A) (hfix : ∀ c, φ (ι₀ c) = ι₀ c)
    (hres : ∀ a : A, ∃ c : C, a - ι₀ c ∈ maximalIdeal A)
    (hφ : (maximalIdeal A).map φ = maximalIdeal A)
    {D : Type*} [CommRing D] [IsReduced D] (ι : A →+* D) (h : D →+* A)
    (hfac : ∀ a, φ a = h (ι a)) : IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  apply injective_of_map_maximalIdeal_eq ι₀ φ hfix hres hφ
  rw [map_zero, hfac, (ha.map ι).eq_zero, map_zero]

end H2ALocal

namespace H2AF2

theorem isReduced_stalk_of_fixed
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (φ : X ⟶ X) (hφf : φ ≫ f = f) [FormallyUnramified φ]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (x : X) (hsx : s.base (IsLocalRing.closedPoint K) = x) (hx : φ.base x = x)
    {Z : Scheme.{u}} [IsReduced Z] (h : X ⟶ Z) (ι : Z ⟶ X) (hfac : h ≫ ι = φ) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  classical
  haveI : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ f) := by rw [hφf]; infer_instance
    exact locallyOfFiniteType_of_comp φ f
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

  let e : X.presheaf.stalk (φ.base x) ≅ X.presheaf.stalk x := X.presheaf.stalkCongr (.of_eq hx)
  let φ' : X.presheaf.stalk x →+* X.presheaf.stalk x := (φ.stalkMap x).hom.comp e.inv.hom

  have hmapψ : (IsLocalRing.maximalIdeal _).map (φ.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    algebraize [(φ.stalkMap x).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (φ.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs <| IsLocalHom (φ.stalkMap x).hom
    have : Algebra.EssFiniteType (X.presheaf.stalk (φ.base x)) (X.presheaf.stalk x) := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap φ x
    have : Algebra.FormallyUnramified (X.presheaf.stalk (φ.base x)) (X.presheaf.stalk x) := by
      rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
      exact FormallyUnramified.stalkMap φ x
    exact Algebra.FormallyUnramified.map_maximalIdeal
  have heinv_surj : Function.Surjective e.inv.hom := (ConcreteCategory.bijective_of_isIso e.inv).2
  have hφ' : (IsLocalRing.maximalIdeal _).map φ' = IsLocalRing.maximalIdeal _ := by
    rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e.inv.hom heinv_surj]
    exact hmapψ

  let ι₀ : Γ(Spec (CommRingCat.of K), ⊤) →+* X.presheaf.stalk x :=
    (f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom
  have hgerm_e : ∀ t, e.inv.hom (X.presheaf.germ ⊤ x trivial t) =
      X.presheaf.germ ⊤ (φ.base x) trivial t := by
    intro t
    change (X.presheaf.germ ⊤ x trivial ≫ e.inv) t = _
    rw [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.germ_stalkSpecializes]
  have hgerm_ψ : ∀ t, (φ.stalkMap x).hom (X.presheaf.germ ⊤ (φ.base x) trivial t) =
      X.presheaf.germ ⊤ x trivial (φ.appTop t) := by
    intro t
    change (X.presheaf.germ ⊤ (φ.base x) trivial ≫ φ.stalkMap x) t = _
    rw [Scheme.Hom.germ_stalkMap]
    rfl
  have happ : ∀ c, φ.appTop (f.appTop c) = f.appTop c := by
    intro c
    change (f.appTop ≫ φ.appTop) c = _
    rw [← Scheme.Hom.comp_appTop, hφf]
  have hfix : ∀ c, φ' (ι₀ c) = ι₀ c := by
    intro c
    change (φ.stalkMap x).hom (e.inv.hom (X.presheaf.germ ⊤ x trivial (f.appTop c))) =
      X.presheaf.germ ⊤ x trivial (f.appTop c)
    rw [hgerm_e, hgerm_ψ, happ]

  have hres : ∀ a : X.presheaf.stalk x, ∃ c, a - ι₀ c ∈ IsLocalRing.maximalIdeal _ := by
    intro a
    let e₂ : X.presheaf.stalk (s.base (IsLocalRing.closedPoint K)) ≅ X.presheaf.stalk x :=
      X.presheaf.stalkCongr (.of_eq hsx)
    let r : X.presheaf.stalk x →+* (Spec (CommRingCat.of K)).presheaf.stalk (IsLocalRing.closedPoint K) :=
      (s.stalkMap (IsLocalRing.closedPoint K)).hom.comp e₂.inv.hom
    haveI : IsLocalHom e₂.inv.hom := isLocalHom_of_isIso e₂.inv
    haveI : IsLocalHom r := RingHom.isLocalHom_comp _ _
    have hsurj : Function.Surjective
        ((Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial) := by
      rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
      exact (ConcreteCategory.bijective_of_isIso _).2
    obtain ⟨c, hc⟩ := hsurj (r a)
    refine ⟨c, ?_⟩
    have hrι : r (ι₀ c) = (Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial c := by
      have h1 : e₂.inv.hom (X.presheaf.germ ⊤ x trivial (f.appTop c)) =
          X.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint K)) trivial (f.appTop c) := by
        change (X.presheaf.germ ⊤ x trivial ≫ e₂.inv) (f.appTop c) = _
        rw [TopCat.Presheaf.stalkCongr_inv, TopCat.Presheaf.germ_stalkSpecializes]
      have h2 : (s.stalkMap (IsLocalRing.closedPoint K)).hom
          (X.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint K)) trivial (f.appTop c)) =
          (Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial (s.appTop (f.appTop c)) := by
        change (X.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint K)) trivial ≫ s.stalkMap _) (f.appTop c) = _
        rw [Scheme.Hom.germ_stalkMap]
        rfl
      have h3 : s.appTop (f.appTop c) = c := by
        change (f.appTop ≫ s.appTop) c = c
        rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
        rfl
      change (s.stalkMap (IsLocalRing.closedPoint K)).hom (e₂.inv.hom (X.presheaf.germ ⊤ x trivial (f.appTop c))) = _
      rw [h1, h2, h3]
    by_contra hmem
    have hu : IsUnit (a - ι₀ c) := by
      by_contra hnu
      exact hmem ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have hu' := hu.map r
    rw [map_sub, hrι, hc, sub_self] at hu'
    exact not_isUnit_zero hu'

  have hpt : φ.base x = (h ≫ ι).base x := by rw [hfac]
  let c₂ : X.presheaf.stalk (φ.base x) ≅ X.presheaf.stalk ((h ≫ ι).base x) :=
    X.presheaf.stalkCongr (.of_eq hpt)
  have hcomp : φ.stalkMap x = c₂.hom ≫ ι.stalkMap (h.base x) ≫ h.stalkMap x := by
    have := Scheme.Hom.stalkMap_congr_hom φ (h ≫ ι) hfac.symm x
    rw [Scheme.Hom.stalkMap_comp] at this
    exact this
  let ιD : X.presheaf.stalk x →+* Z.presheaf.stalk (h.base x) :=
    (ι.stalkMap (h.base x)).hom.comp (c₂.hom.hom.comp e.inv.hom)
  have hfac' : ∀ a, φ' a = (h.stalkMap x).hom (ιD a) := by
    intro a
    change (φ.stalkMap x).hom (e.inv.hom a) = (h.stalkMap x).hom ((ι.stalkMap (h.base x)).hom (c₂.hom.hom (e.inv.hom a)))
    rw [hcomp]
    rfl
  exact H2ALocal.isReduced_of_map_maximalIdeal_eq_of_factors ι₀ φ' hfix hres hφ' ιD (h.stalkMap x).hom hfac'

end H2AF2

namespace H2AF4

theorem isReduced_pullback_Spec_of_perfectField
    {k : Type u} [Field k] [PerfectField k] (R : CommRingCat.{u}) [_root_.IsReduced R]
    (F : Spec R ⟶ Spec (CommRingCat.of k)) (Ω : Type u) [Field Ω] [Algebra k Ω] :
    IsReduced (pullback F (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of k ⟶ R, Spec.map φ = F := ⟨Spec.preimage F, Spec.map_preimage F⟩
  subst hφ
  algebraize [φ.hom]
  haveI : _root_.IsReduced (R ⊗[k] Ω) := by
    haveI := Algebra.isReduced_tensorProduct_of_perfectField k R Ω
    exact isReduced_of_injective (Algebra.TensorProduct.comm k R Ω).toRingHom
      (Algebra.TensorProduct.comm k R Ω).injective
  let e : pullback (Spec.map φ) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≅
      Spec (CommRingCat.of (R ⊗[k] Ω)) :=
    pullbackSpecIso k R Ω
  haveI : IsReduced (Spec (CommRingCat.of (R ⊗[k] Ω))) := inferInstance
  exact isReduced_of_isOpenImmersion e.hom

theorem isReduced_pullback_of_perfectField
    {k : Type u} [Field k] [PerfectField k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k)) [IsReduced Z]
    (Ω : Type u) [Field Ω] [Algebra k Ω] :
    IsReduced (pullback q (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) := by
  let 𝒰 := Scheme.Pullback.openCoverOfLeft Z.affineOpenCover.openCover q
    (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
  haveI : ∀ i, IsReduced (𝒰.X i) := by
    intro i
    haveI : IsReduced (Spec (Z.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (Z.affineOpenCover.f i)
    haveI : _root_.IsReduced (Z.affineOpenCover.X i) := (affine_isReduced_iff _).mp inferInstance
    exact isReduced_pullback_Spec_of_perfectField (Z.affineOpenCover.X i)
      (Z.affineOpenCover.f i ≫ q) Ω
  exact IsReduced.of_openCover _ 𝒰

end H2AF4

namespace H2AF3

theorem isReduced_sections_of_isAffineOpen {X : Scheme.{u}} [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) : _root_.IsReduced Γ(X, U) := by
  apply isReduced_ofLocalizationMaximal
  intro m hm
  let y : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
  have hyU : hU.fromSpec y ∈ U := hU.range_fromSpec.subset ⟨y, rfl⟩

  have hcl : IsClosed ({hU.fromSpec y} : Set X) := by
    have h1 : IsClosed ({y} : Set (PrimeSpectrum Γ(X, U))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
    have h2 := hU.fromSpec.isOpenEmbedding.preimage_closedPoints (Y := X)
    have h3 : y ∈ hU.fromSpec ⁻¹' closedPoints X := by
      rw [h2]
      exact h1
    exact h3
  have hred : _root_.IsReduced (X.presheaf.stalk (hU.fromSpec y)) := h _ hcl

  letI : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hyU⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  let e : Localization.AtPrime m ≃ₐ[Γ(X, U)] X.presheaf.stalk (hU.fromSpec y) :=
    IsLocalization.algEquiv m.primeCompl _ _
  exact isReduced_of_injective e.toRingEquiv.toRingHom e.toRingEquiv.injective

theorem isReduced_of_forall_isClosed_isReduced_stalk
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsClosed ({x} : Set X) → _root_.IsReduced (X.presheaf.stalk x)) :
    IsReduced X := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (Set.mem_univ x)
    haveI : _root_.IsReduced Γ(X, U) := isReduced_sections_of_isAffineOpen h hU
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    exact isReduced_localizationPreserves (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl _
      inferInstance
  exact isReduced_of_isReduced_stalk X

end H2AF3

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {k : Type u} [Field k] [PerfectField k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    (m : ℕ) (hm : IsUnit (m : k))
    {Z : Scheme.{u}} [IsReduced Z] (h : G ⟶ Z) (ι : Z ⟶ G)
    (hfac : h ≫ ι = L.schemeNsmul m) :
    IsReduced G ∧ Smooth g := by
  classical

  haveI hFU : FormallyUnramified (L.schemeNsmul m) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing L hcomm m hm

  let γ : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let gΩ := pullback.snd g γ
  letI : GrpObj (Over.mk g) := L.grpObjOverMk
  letI : GrpObj (Over.mk gΩ) := Over.grpObjMkPullbackSnd
  have hnover : L.schemeNsmul m ≫ g = g := L.schemeNsmul_over m
  let nΩ : pullback g γ ⟶ pullback g γ :=
    pullback.map g γ g γ (L.schemeNsmul m) (𝟙 _) (𝟙 _) (by rw [hnover, Category.comp_id]) (by simp)
  have hnΩ_over : nΩ ≫ gΩ = gΩ := by simp [nΩ, gΩ]
  haveI : FormallyUnramified nΩ :=
    MorphismProperty.pullbackMap (P := @FormallyUnramified) hFU
      (inferInstance : FormallyUnramified (𝟙 _)) hnover.symm (Category.id_comp _).symm

  haveI : IsReduced (pullback (ι ≫ g) γ) := H2AF4.isReduced_pullback_of_perfectField (ι ≫ g) (AlgebraicClosure k)
  let hΩ : pullback g γ ⟶ pullback (ι ≫ g) γ :=
    pullback.map g γ (ι ≫ g) γ h (𝟙 _) (𝟙 _)
      (by rw [← Category.assoc, hfac, hnover, Category.comp_id]) (by simp)
  let iZ : pullback (ι ≫ g) γ ⟶ pullback g γ :=
    pullback.map (ι ≫ g) γ g γ ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hfacΩ : hΩ ≫ iZ = nΩ := by
    apply pullback.hom_ext <;> simp [hΩ, iZ, nΩ, ← hfac]

  haveI : JacobsonSpace ↥(pullback g γ) := LocallyOfFiniteType.jacobsonSpace gΩ
  have hstalk : ∀ x : ↥(pullback g γ), IsClosed ({x} : Set ↥(pullback g γ)) →
      _root_.IsReduced ((pullback g γ).presheaf.stalk x) := by
    intro x hxc
    let p := (pointEquivClosedPoint gΩ).symm ⟨x, hxc⟩
    have hpx : p.1.base (IsLocalRing.closedPoint (AlgebraicClosure k)) = x := by simp [p]
    let x' : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ Over.mk gΩ := Over.homMk p.1 p.2
    let z' : 𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ Over.mk gΩ := x' ≫ Over.homMk nΩ hnΩ_over
    let α : Over.mk gΩ ≅ Over.mk gΩ :=
      (GrpObj.mulRight (A := Over.mk gΩ) z').symm ≪≫ GrpObj.mulRight (A := Over.mk gΩ) x'
    have hα : z' ≫ α.hom = x' := by
      dsimp only [Iso.trans_hom, Iso.symm_hom, α]
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      simp [comp_lift_assoc]
    have hα' : α.hom.left.base (nΩ.base x) = x := by
      have := congr(($hα).left.base (IsLocalRing.closedPoint (AlgebraicClosure k)))
      simpa [x', z', hpx] using this
    let φx : pullback g γ ⟶ pullback g γ := nΩ ≫ α.hom.left
    have hφx_over : φx ≫ gΩ = gΩ := by
      simp only [φx, Category.assoc]
      rw [show α.hom.left ≫ gΩ = gΩ from Over.w α.hom, hnΩ_over]
    haveI : IsIso α.hom.left := inferInstance
    haveI : FormallyUnramified α.hom.left := MorphismProperty.of_isIso @FormallyUnramified _
    haveI : FormallyUnramified φx := MorphismProperty.comp_mem @FormallyUnramified nΩ α.hom.left ‹_› ‹_›
    have hfix : φx.base x = x := by
      show (nΩ ≫ α.hom.left).base x = x
      simpa [Scheme.Hom.comp_base] using hα'
    exact H2AF2.isReduced_stalk_of_fixed gΩ φx hφx_over p.1 p.2 x hpx hfix hΩ (iZ ≫ α.hom.left)
      (by rw [← Category.assoc, hfacΩ])

  haveI : IsReduced (pullback g γ) := H2AF3.isReduced_of_forall_isClosed_isReduced_stalk gΩ hstalk
  haveI : GeometricallyReduced gΩ := GeometricallyReduced.of_isReduced_of_perfectField gΩ
  have hsmΩ : Smooth gΩ := smooth_of_grpObj gΩ
  have hsm : Smooth g :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := γ)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsmΩ

  haveI : IsSchemeTheoreticallyDominant γ := by
    rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine]
    have hinj : Function.Injective γ.appTop.hom := by
      have e : γ.appTop = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv := by
        rw [← Iso.inv_comp_eq]
        exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).symm
      have i1 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv.hom :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure k))).inv).1
      have i2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom :=
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
      rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_comp]
      exact (i1.comp (algebraMap k (AlgebraicClosure k)).injective).comp i2
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [Scheme.IdealSheafData.ideal_bot]
  haveI : IsReduced G := IsSchemeTheoreticallyDominant.isReduced (pullback.fst g γ)
  exact ⟨inferInstance, hsm⟩

end S_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit (solution)
