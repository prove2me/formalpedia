-- Prove2me | solution 1 for NeronModelInfra.exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a1de3bda-882e-5643-a832-f134cfa74b95

import Mathlib
import Definitions.Def_RingTheory_AffineDilatation
import Theorems.Thm_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular
import Theorems.Thm_AffineDilatation_exists_algHom_isLocalization_map
import Theorems.Thm_AffineDilatation_finiteType_of_fg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace P2mDilatation

section RingLevel

variable {A : Type u} [CommRing A]

open AffineDilatation

theorem isSMulRegular_ring (I : Ideal A) (a : A) : IsSMulRegular (Ring I a) a := by
  intro x y h
  apply Subtype.ext
  have h' : ((a • x : Ring I a) : Localization.Away a) = ((a • y : Ring I a) : Localization.Away a) :=
    congrArg Subtype.val h
  simp only [Algebra.smul_def] at h'
  change algebraMap A (Localization.Away a) a * (x : Localization.Away a) =
    algebraMap A (Localization.Away a) a * (y : Localization.Away a) at h'
  exact (IsLocalization.Away.algebraMap_isUnit a).mul_left_cancel h'

theorem mul_left_cancel_algebraMap (I : Ideal A) (a : A) {x y : Ring I a}
    (h : algebraMap A (Ring I a) a * x = algebraMap A (Ring I a) a * y) : x = y := by
  refine isSMulRegular_ring I a (?_ : a • x = a • y)
  rwa [Algebra.smul_def, Algebra.smul_def]

theorem ringHom_ext {C : Type*} [CommRing C] (I : Ideal A) (a : A) (φ ψ : Ring I a →+* C)
    (hA : ∀ r : A, φ (algebraMap A (Ring I a) r) = ψ (algebraMap A (Ring I a) r))
    (hreg : ∀ c c' : C, φ (algebraMap A (Ring I a) a) * c = φ (algebraMap A (Ring I a) a) * c' → c = c') :
    φ = ψ := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change φ (divElem I a g hg) = ψ (divElem I a g hg)
      have h := congrArg φ (algebraMap_mul_divElem I a g hg)
      have h' := congrArg ψ (algebraMap_mul_divElem I a g hg)
      rw [map_mul] at h h'
      apply hreg
      rw [h, hA g, ← h', hA a]
  | algebraMap r => exact hA r
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

theorem exists_ringHom {C : Type u} [CommRing C] (I : Ideal A) (a : A) (v : A →+* C)
    (hreg : ∀ c c' : C, v a * c = v a * c' → c = c')
    (hI : ∀ g ∈ I, ∃ c : C, v g = v a * c) :
    ∃ φ : Ring I a →+* C, φ.comp (algebraMap A (Ring I a)) = v := by
  letI : Algebra A C := v.toAlgebra
  have hreg' : IsSMulRegular C a := by
    intro c c' h
    exact hreg c c' (by simpa [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h)
  have hI' : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a} := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    obtain ⟨c, hc⟩ := hI g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨c, by rw [mul_comm, RingHom.algebraMap_toAlgebra]; exact hc.symm⟩
  obtain ⟨⟨φ⟩, -⟩ := AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular I a hreg' hI'
  exact ⟨φ.toRingHom, RingHom.ext fun r => φ.commutes r⟩

theorem algebraMap_bijective_of_isUnit (I : Ideal A) {a : A} (ha : IsUnit a) :
    Function.Bijective (algebraMap A (Ring I a)) := by
  have hle : Submonoid.powers a ≤ IsUnit.submonoid A := by
    rw [Submonoid.powers_le]; exact ha
  let e : A ≃ₐ[A] Localization.Away a := IsLocalization.atUnits A (Submonoid.powers a) hle
  have he : ∀ r : A, e r = algebraMap A (Localization.Away a) r := fun r => e.commutes r
  constructor
  · intro r s h
    have h' : (algebraMap A (Localization.Away a) r) = algebraMap A (Localization.Away a) s :=
      congrArg Subtype.val h
    rw [← he, ← he] at h'
    exact e.injective h'
  · rintro ⟨x, hx⟩
    refine ⟨e.symm x, Subtype.ext ?_⟩
    change algebraMap A (Localization.Away a) (e.symm x) = x
    rw [← he, AlgEquiv.apply_symm_apply]

theorem exists_ringEquiv_of_eq_unit_mul (I : Ideal A) (a b : A) (u : Aˣ) (hb : b = u * a)
    (ha : a ∈ I) :
    ∃ e : Ring I a ≃+* Ring I b,
      e.toRingHom.comp (algebraMap A (Ring I a)) = algebraMap A (Ring I b) := by
  have hb' : a = (u⁻¹ : Aˣ) * b := by rw [hb, ← mul_assoc, Units.inv_mul, one_mul]
  have hbI : b ∈ I := by rw [hb]; exact I.mul_mem_left _ ha

  have reg : ∀ (c d : A) (w : Aˣ), d = w * c → ∀ x y : Ring I c,
      algebraMap A (Ring I c) d * x = algebraMap A (Ring I c) d * y → x = y := by
    intro c d w hd x y h
    rw [hd, map_mul, mul_assoc, mul_assoc] at h
    have h2 := (((Units.map (algebraMap A (Ring I c)).toMonoidHom w).isUnit).mul_left_cancel h)
    exact mul_left_cancel_algebraMap I c h2
  have dvd : ∀ (c d : A) (w : Aˣ), d = w * c → ∀ g ∈ I, ∃ z : Ring I c,
      algebraMap A (Ring I c) g = algebraMap A (Ring I c) d * z := by
    intro c d w hd g hg
    refine ⟨algebraMap A (Ring I c) ((w⁻¹ : Aˣ) : A) * divElem I c g hg, ?_⟩
    rw [hd, map_mul, mul_assoc, ← mul_assoc (algebraMap A _ c), mul_comm (algebraMap A _ c),
      mul_assoc, algebraMap_mul_divElem, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  obtain ⟨φ, hφ⟩ := exists_ringHom I a (algebraMap A (Ring I b)) (reg b a u⁻¹ hb') (dvd b a u⁻¹ hb')
  obtain ⟨ψ, hψ⟩ := exists_ringHom I b (algebraMap A (Ring I a)) (reg a b u hb) (dvd a b u hb)
  have hφr : ∀ r, φ (algebraMap A _ r) = algebraMap A _ r := fun r => RingHom.congr_fun hφ r
  have hψr : ∀ r, ψ (algebraMap A _ r) = algebraMap A _ r := fun r => RingHom.congr_fun hψ r
  have h1 : ψ.comp φ = RingHom.id _ := by
    apply ringHom_ext I a
    · intro r; simp [hφr, hψr]
    · intro c c' h
      simp only [RingHom.comp_apply, hφr, hψr] at h
      exact mul_left_cancel_algebraMap I a h
  have h2 : φ.comp ψ = RingHom.id _ := by
    apply ringHom_ext I b
    · intro r; simp [hφr, hψr]
    · intro c c' h
      simp only [RingHom.comp_apply, hφr, hψr] at h
      exact mul_left_cancel_algebraMap I b h
  refine ⟨RingEquiv.ofRingHom φ ψ h2 h1, ?_⟩
  exact hφ

theorem nonempty_algEquiv_of_eq {I I' : Ideal A} {a a' : A} (hI : I = I') (ha : a = a') :
    Nonempty (Ring I a ≃ₐ[A] Ring I' a') := by
  subst hI ha
  exact ⟨AlgEquiv.refl⟩

theorem exists_ringEquiv_of_eq {I I' : Ideal A} {a a' : A} (hI : I = I') (ha : a = a') :
    ∃ e : Ring I a ≃+* Ring I' a', e.toRingHom.comp (algebraMap A (Ring I a)) = algebraMap A (Ring I' a') := by
  subst hI ha
  exact ⟨RingEquiv.refl _, rfl⟩

end RingLevel

section Dictionary

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def secTop (π : R) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)

noncomputable def sec (π : R) (U : X.Opens) : Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom (secTop f π)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem sec_def (π : R) (U : X.Opens) : sec f π U =
    (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)) :=
  rfl

noncomputable def toSec (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem toSec_apply (π : R) (U : X.Opens) : toSec f U π = sec f π U := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem map_sec (π : R) {U V : X.Opens} (i : op U ⟶ op V) :
    (X.presheaf.map i).hom (sec f π U) = sec f π V := by
  simp only [sec, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_basicOpen_secTop_iff (π : R) (x : X) :
    x ∈ X.basicOpen (secTop f π) ↔ π ∉ (f x).asIdeal := by
  have h : f ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π) =
      X.basicOpen (secTop f π) := Scheme.preimage_basicOpen f _
  rw [← h, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen π (f x)

theorem eq_closedPoint_iff {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (q : PrimeSpectrum R) : q = IsLocalRing.closedPoint R ↔ π ∈ q.asIdeal := by
  constructor
  · rintro rfl
    change π ∈ IsLocalRing.maximalIdeal R
    rw [hπ]; exact Ideal.mem_span_singleton_self π
  · intro h
    apply PrimeSpectrum.ext
    change q.asIdeal = IsLocalRing.maximalIdeal R
    have hle : IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
      rw [hπ, Ideal.span_singleton_le_iff_mem]; exact h
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top hle).symm

theorem mem_basicOpen_secTop_iff' {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (x : X) :
    x ∈ X.basicOpen (secTop f π) ↔ f x ≠ IsLocalRing.closedPoint R :=
  (mem_basicOpen_secTop_iff f π x).trans (eq_closedPoint_iff hπ (f x)).symm.not

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem basicOpen_sec (π : R) (U : X.Opens) :
    X.basicOpen (sec f π U) = U ⊓ X.basicOpen (secTop f π) :=
  Scheme.basicOpen_res X _ _

variable {U : X.Opens} (hU : IsAffineOpen U)

theorem primeIdealOf_fromSpec (q : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec q ∈ U) : hU.primeIdealOf ⟨hU.fromSpec q, hq⟩ = q := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem fromSpec_mem (q : PrimeSpectrum Γ(X, U)) : hU.fromSpec q ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩

theorem mem_basicOpen_iff_notMem (s : Γ(X, U)) (y : X) (hy : y ∈ U) :
    y ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen s]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen s
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem sec_mem_asIdeal_iff {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (y : X) (hy : y ∈ U) :
    sec f π U ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ↔ f y = IsLocalRing.closedPoint R := by
  have h := mem_basicOpen_iff_notMem hU (sec f π U) y hy
  rw [basicOpen_sec, TopologicalSpace.Opens.mem_inf, mem_basicOpen_secTop_iff' f hπ] at h
  tauto

variable (Y : Set X) (hY : IsClosed Y)

noncomputable def idealY : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩

theorem idealY_ideal (V : X.affineOpens) :
    (idealY Y hY).ideal V = PrimeSpectrum.vanishingIdeal (V.2.fromSpec ⁻¹' Y) :=
  Scheme.IdealSheafData.vanishingIdeal_ideal _ _

theorem idealY_ideal' : (idealY Y hY).ideal ⟨U, hU⟩ = PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' Y) :=
  Scheme.IdealSheafData.vanishingIdeal_ideal _ _

theorem mem_iff_ideal_le (y : X) (hy : y ∈ U) :
    y ∈ Y ↔ (idealY Y hY).ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [idealY_ideal', ← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus,
    PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hc : IsClosed (hU.fromSpec ⁻¹' Y) := hY.preimage hU.fromSpec.continuous
  erw [hc.closure_eq, Set.mem_preimage]
  change _ ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ Y
  rw [IsAffineOpen.fromSpec_primeIdealOf]

theorem vanishingIdeal_image_eq :
    PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}) =
      (idealY Y hY).ideal ⟨U, hU⟩ := by
  rw [idealY_ideal']
  congr 1
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    change hU.fromSpec (hU.primeIdealOf y) ∈ Y
    rw [IsAffineOpen.fromSpec_primeIdealOf]; exact hy
  · intro hq
    exact ⟨⟨hU.fromSpec q, fromSpec_mem hU q⟩, hq, primeIdealOf_fromSpec hU q _⟩

variable (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R)
include hYs

theorem sec_mem_ideal {π : R} (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    sec f π U ∈ (idealY Y hY).ideal ⟨U, hU⟩ := by
  rw [idealY_ideal', PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  have := (sec_mem_asIdeal_iff f hU hπ (hU.fromSpec q) (fromSpec_mem hU q)).mpr (hYs _ hq)
  rwa [primeIdealOf_fromSpec] at this

end Dictionary

section Global

p2m_open "AlgebraicGeometry.Scheme.AffineZariskiSite AffineDilatation"

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable (Y : Set X) (hY : IsClosed Y) (π : R)

abbrev idl (U : X.AffineZariskiSite) : Ideal Γ(X, U.1) := (idealY Y hY).ideal ⟨U.1, U.2⟩

abbrev objRing (U : X.AffineZariskiSite) : Type u := AffineDilatation.Ring (idl Y hY U) (sec f π U.1)

abbrev res {V U : X.AffineZariskiSite} (h : V ≤ U) : Γ(X, U.1) →+* Γ(X, V.1) :=
  (X.presheaf.map (homOfLE (toOpens_mono h)).op).hom

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem res_sec {V U : X.AffineZariskiSite} (h : V ≤ U) : res h (sec f π U.1) = sec f π V.1 :=
  map_sec f π _

theorem idl_map {V U : X.AffineZariskiSite} (h : V ≤ U) : (idl Y hY U).map (res h) = idl Y hY V :=
  (idealY Y hY).map_ideal (U := ⟨V.1, V.2⟩) (V := ⟨U.1, U.2⟩) (Scheme.AffineZariskiSite.toOpens_mono h)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem exists_transition {V U : X.AffineZariskiSite} (h : V ≤ U) :
    ∃ φ : objRing f Y hY π U →+* objRing f Y hY π V,
      φ.comp (algebraMap _ _) = (algebraMap _ (objRing f Y hY π V)).comp (res h) := by
  apply exists_ringHom
  · intro c c' hc
    rw [RingHom.comp_apply, res_sec] at hc
    exact mul_left_cancel_algebraMap _ _ hc
  · intro g hg
    have hg' : res h g ∈ idl Y hY V := by rw [← idl_map Y hY h]; exact Ideal.mem_map_of_mem _ hg
    exact ⟨divElem _ _ (res h g) hg', by
      rw [RingHom.comp_apply, RingHom.comp_apply, res_sec, algebraMap_mul_divElem]⟩

def transition {V U : X.AffineZariskiSite} (h : V ≤ U) : objRing f Y hY π U →+* objRing f Y hY π V :=
  (exists_transition f Y hY π h).choose

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_algebraMap {V U : X.AffineZariskiSite} (h : V ≤ U) (g : Γ(X, U.1)) :
    transition f Y hY π h (algebraMap _ _ g) = algebraMap _ _ (res h g) :=
  RingHom.congr_fun (exists_transition f Y hY π h).choose_spec g

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_unique {V U : X.AffineZariskiSite} (h : V ≤ U)
    (φ : objRing f Y hY π U →+* objRing f Y hY π V)
    (hφ : ∀ g, φ (algebraMap _ _ g) = algebraMap _ _ (res h g)) : φ = transition f Y hY π h := by
  apply ringHom_ext
  · intro g; rw [hφ, transition_algebraMap]
  · intro c c' hc
    rw [hφ, res_sec] at hc
    exact mul_left_cancel_algebraMap _ _ hc

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_refl (U : X.AffineZariskiSite) : transition f Y hY π (le_refl U) = RingHom.id _ := by
  symm; apply transition_unique
  intro g
  have : res (le_refl U) g = g := by
    change (X.presheaf.map (𝟙 (op U.1))).hom g = g
    rw [X.presheaf.map_id]; rfl
  rw [this]; rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem transition_trans {W V U : X.AffineZariskiSite} (h : W ≤ V) (h' : V ≤ U) :
    (transition f Y hY π h).comp (transition f Y hY π h') = transition f Y hY π (h.trans h') := by
  apply transition_unique
  intro g
  rw [RingHom.comp_apply, transition_algebraMap, transition_algebraMap]
  congr 1
  change ((X.presheaf.map (homOfLE _).op) ≫ X.presheaf.map (homOfLE _).op).hom g = _
  rw [← Functor.map_comp, ← op_comp, homOfLE_comp]

def diagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (objRing f Y hY π (unop U))
  map {U V} i := CommRingCat.ofHom (transition f Y hY π i.unop.le)
  map_id U := by
    ext1
    exact transition_refl f Y hY π (unop U)
  map_comp {U V W} i j := by
    ext1
    exact (transition_trans f Y hY π j.unop.le i.unop.le).symm

def toDiagram : (toOpensFunctor X).op ⋙ X.presheaf ⟶ diagram f Y hY π where
  app U := CommRingCat.ofHom (algebraMap Γ(X, (unop U).1) (objRing f Y hY π (unop U)))
  naturality {U V} i := by
    ext g
    exact (transition_algebraMap f Y hY π i.unop.le g).symm

variable {π}
variable (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
variable (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R)
include hπ hYs

theorem sec_mem_idl (U : X.AffineZariskiSite) : sec f π U.1 ∈ idl Y hY U :=
  sec_mem_ideal f U.2 Y hY hYs hπ

theorem coequifibered : (toDiagram f Y hY π).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  change @IsLocalization.Away (objRing f Y hY π U) _ (algebraMap Γ(X, U.1) (objRing f Y hY π U) r)
    (objRing f Y hY π (U.basicOpen r)) _ (transition f Y hY π (U.basicOpen_le r)).toAlgebra
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
  obtain ⟨φ, hφ⟩ := AffineDilatation.exists_algHom_isLocalization_map (idl Y hY U) (sec f π U.1)
    (sec_mem_idl f Y hY hπ hYs U) (Submonoid.powers r) Γ(X, X.basicOpen r)
  have hI : (idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)) = idl Y hY (U.basicOpen r) :=
    (idealY Y hY).map_ideal_basicOpen ⟨U.1, U.2⟩ r
  have ha : algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1) = sec f π (U.basicOpen r).1 :=
    map_sec f π _
  obtain ⟨e⟩ := nonempty_algEquiv_of_eq (A := Γ(X, X.basicOpen r)) hI ha
  have key : transition f Y hY π (U.basicOpen_le r) = e.toRingEquiv.toRingHom.comp φ.toRingHom := by
    symm
    apply transition_unique
    intro g
    change e (φ (algebraMap _ _ g)) = _
    rw [φ.commutes g, IsScalarTower.algebraMap_apply Γ(X, U.1) Γ(X, X.basicOpen r) _ g, e.commutes]
    rfl
  rw [key]
  letI : Algebra (objRing f Y hY π U)
      (AffineDilatation.Ring ((idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)))
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1))) := φ.toRingHom.toAlgebra
  letI : Algebra (objRing f Y hY π U) (objRing f Y hY π (U.basicOpen r)) :=
    (e.toRingEquiv.toRingHom.comp φ.toRingHom).toAlgebra
  have hM : Algebra.algebraMapSubmonoid (objRing f Y hY π U) (Submonoid.powers r) =
      Submonoid.powers (algebraMap Γ(X, U.1) (objRing f Y hY π U) r) := Submonoid.map_powers _ _
  haveI : IsLocalization (Submonoid.powers (algebraMap Γ(X, U.1) (objRing f Y hY π U) r))
      (AffineDilatation.Ring ((idl Y hY U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r)))
        (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r) (sec f π U.1))) := hM ▸ hφ
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers _)
    { e.toRingEquiv with commutes' := fun x => rfl }

def glueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (coequifibered f Y hY hπ hYs)

scoped instance : ((glueData f Y hY hπ hYs).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def D : Scheme.{u} := (glueData f Y hY hπ hYs).glued

def p : D f Y hY hπ hYs ⟶ X := (glueData f Y hY hπ hYs).toBase

def chart (U : X.AffineZariskiSite) : Spec (CommRingCat.of (objRing f Y hY π U)) ⟶ D f Y hY hπ hYs :=
  (glueData f Y hY hπ hYs).cover.f U

scoped instance (U : X.AffineZariskiSite) : IsOpenImmersion (chart f Y hY hπ hYs U) :=
  (glueData f Y hY hπ hYs).cover.map_prop U

theorem chart_def (U : X.AffineZariskiSite) :
    chart f Y hY hπ hYs U = colimit.ι (glueData f Y hY hπ hYs).functor U := rfl

theorem chart_p (U : X.AffineZariskiSite) :
    chart f Y hY hπ hYs U ≫ p f Y hY hπ hYs =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫ U.2.fromSpec := by
  exact colimit.ι_desc _ _

theorem preimage_p (U : X.AffineZariskiSite) :
    p f Y hY hπ hYs ⁻¹ᵁ U.1 = (chart f Y hY hπ hYs U).opensRange := by
  ext1
  rw [Scheme.Hom.coe_opensRange]
  have h := (glueData f Y hY hπ hYs).preimage_toBase_eq_range_ι U
  change (p f Y hY hπ hYs) ⁻¹' Set.range (U.1.ι) = Set.range (chart f Y hY hπ hYs U) at h
  rw [Scheme.Opens.range_ι] at h
  exact h

theorem isPullback_chart (U : X.AffineZariskiSite) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫ U.2.isoSpec.inv)
      (chart f Y hY hπ hYs U) U.1.ι (p f Y hY hπ hYs) :=
  (glueData f Y hY hπ hYs).isPullback_natTrans_ι_toBase U

theorem restrict_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (U : X.AffineZariskiSite) :
    P (p f Y hY hπ hYs ∣_ U.1) ↔
      P (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U)))) := by
  have h₁ := isPullback_chart f Y hY hπ hYs U
  have h₂ := isPullback_morphismRestrict (p f Y hY hπ hYs) U.1
  let e := h₂.isoIsPullback _ _ h₁
  have he : e.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) ≫
      U.2.isoSpec.inv) = p f Y hY hπ hYs ∣_ U.1 := h₂.isoIsPullback_hom_fst _ _ h₁
  rw [← he, ← Category.assoc, P.cancel_right_of_respectsIso, P.cancel_left_of_respectsIso]

scoped instance isAffineHom_p : IsAffineHom (p f Y hY hπ hYs) := by
  refine ⟨fun U hU => ?_⟩
  rw [preimage_p f Y hY hπ hYs ⟨U, hU⟩]
  exact isAffineOpen_opensRange _

theorem locallyOfFiniteType_p [LocallyOfFiniteType f] : LocallyOfFiniteType (p f Y hY hπ hYs) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @LocallyOfFiniteType) (fun U : X.affineOpens => U.1)
    (iSup_affineOpens_eq_top X) fun U => (restrict_iff f Y hY hπ hYs _ ⟨U.1, U.2⟩).mpr ?_
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap Γ(X, U.1) (objRing f Y hY π ⟨U.1, U.2⟩)).FiniteType
  rw [RingHom.finiteType_algebraMap]
  haveI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact AffineDilatation.finiteType_of_fg _ _ (IsNoetherian.noetherian _)

omit hYs in
theorem isUnit_sec {U : X.Opens} (hU : ∀ x ∈ U, f x ≠ IsLocalRing.closedPoint R) : IsUnit (sec f π U) := by
  have hle : U ≤ X.basicOpen (secTop f π) := fun x hx => (mem_basicOpen_secTop_iff' f hπ x).mpr (hU x hx)
  have h1 : IsUnit (sec f π (X.basicOpen (secTop f π))) := RingedSpace.isUnit_res_basicOpen _ _
  have h2 := h1.map (X.presheaf.map (homOfLE hle).op).hom
  rwa [map_sec] at h2

theorem isIso_restrict_affine (U : X.AffineZariskiSite) (hU : ∀ x ∈ U.1, f x ≠ IsLocalRing.closedPoint R) :
    IsIso (p f Y hY hπ hYs ∣_ U.1) := by
  refine (restrict_iff f Y hY hπ hYs (MorphismProperty.isomorphisms Scheme.{u}) U).mpr ?_
  have hb := algebraMap_bijective_of_isUnit (idl Y hY U) (isUnit_sec f hπ hU)
  change IsIso (Spec.map (RingEquiv.ofBijective _ hb).toCommRingCatIso.hom)
  infer_instance

theorem isIso_restrict (W : X.Opens) (hW : ∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) :
    IsIso (p f Y hY hπ hYs ∣_ W) := by
  have hcov : ⨆ U : {U : X.affineOpens // U.1 ≤ W}, W.ι ⁻¹ᵁ U.1.1 = ⊤ := by
    rw [← top_le_iff]
    rintro w -
    obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open w.2 W.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hwU⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{u}) _ hcov ?_
  intro U
  have hUeq : W.ι ''ᵁ (W.ι ⁻¹ᵁ U.1.1) = U.1.1 := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr U.2]
  rw [(MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ hUeq)]
  exact isIso_restrict_affine f Y hY hπ hYs ⟨U.1.1, U.1.2⟩ (fun x hx => hW x (U.2 hx))

theorem apply_mem (d : D f Y hY hπ hYs) (hd : f (p f Y hY hπ hYs d) = IsLocalRing.closedPoint R) :
    p f Y hY hπ hYs d ∈ Y := by
  obtain ⟨U, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (glueData f Y hY hπ hYs).functor d
  change f (p f Y hY hπ hYs (chart f Y hY hπ hYs U z)) = _ at hd
  change p f Y hY hπ hYs (chart f Y hY hπ hYs U z) ∈ Y
  have h1 : p f Y hY hπ hYs (chart f Y hY hπ hYs U z) =
      U.2.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) z) := by
    rw [← Scheme.Hom.comp_apply, chart_p, Scheme.Hom.comp_apply]
  rw [h1] at hd ⊢
  set q := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (objRing f Y hY π U))) z with hq
  have hyU := fromSpec_mem U.2 q
  rw [← sec_mem_asIdeal_iff f U.2 hπ _ hyU, primeIdealOf_fromSpec] at hd
  rw [mem_iff_ideal_le U.2 Y hY _ hyU, primeIdealOf_fromSpec]
  intro g hg
  have hq' : q.asIdeal = Ideal.comap (algebraMap Γ(X, U.1) (objRing f Y hY π U)) z.asIdeal := by
    rw [hq, Spec.map_apply]; rfl
  rw [hq'] at hd ⊢
  change (algebraMap Γ(X, U.1) (objRing f Y hY π U)) (sec f π U.1) ∈ z.asIdeal at hd
  change (algebraMap Γ(X, U.1) (objRing f Y hY π U)) g ∈ z.asIdeal
  have hmul : (algebraMap Γ(X, U.1) (objRing f Y hY π U)) g =
      (algebraMap Γ(X, U.1) (objRing f Y hY π U)) (sec f π U.1) * divElem (idl Y hY U) (sec f π U.1) g hg :=
    (algebraMap_mul_divElem _ _ g hg).symm
  rw [hmul]
  exact z.asIdeal.mul_mem_right _ hd

omit hπ hYs in

theorem exists_specIso {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B]
    [Algebra A B'] (E : B ≃+* B') (hE : E.toRingHom.comp (algebraMap A B) = algebraMap A B') :
    ∃ e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of B'),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B')) = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  refine ⟨Scheme.Spec.mapIso E.symm.toCommRingCatIso.op, ?_⟩
  change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  rw [← hE]
  ext x
  simp

theorem exists_chartIso (U : X.Opens) (hU : IsAffineOpen U) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    ∃ e : (↑(p f Y hY hπ hYs ⁻¹ᵁ U) : Scheme.{u}) ≅
        Spec (CommRingCat.of (AffineDilatation.Ring
          (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
          ((X.presheaf.map (homOfLE le_top).op).hom
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))))),
      (p f Y hY hπ hYs ⁻¹ᵁ U).ι ≫ p f Y hY hπ hYs = e.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
          (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
          ((X.presheaf.map (homOfLE le_top).op).hom
            (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)))))) ≫ hU.fromSpec := by
  let U' : X.AffineZariskiSite := ⟨U, hU⟩

  let e₁ : (↑(p f Y hY hπ hYs ⁻¹ᵁ U) : Scheme.{u}) ≅ Spec (CommRingCat.of (objRing f Y hY π U')) :=
    IsOpenImmersion.isoOfRangeEq (p f Y hY hπ hYs ⁻¹ᵁ U).ι (chart f Y hY hπ hYs U') (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
      exact congrArg SetLike.coe (preimage_p f Y hY hπ hYs U'))
  have he₁ : e₁.hom ≫ chart f Y hY hπ hYs U' = (p f Y hY hπ hYs ⁻¹ᵁ U).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

  have hassoc : Associated π ϖ := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← hπ, ← hϖ]
  obtain ⟨u, hu⟩ := hassoc
  have hb : sec f ϖ U = (Units.map (toSec f U).toMonoidHom u : Γ(X, U)ˣ) * sec f π U := by
    rw [← toSec_apply, ← toSec_apply, ← hu, map_mul, mul_comm]; rfl
  obtain ⟨e', he'⟩ := exists_ringEquiv_of_eq_unit_mul (idl Y hY U') (sec f π U) (sec f ϖ U) _ hb
    (sec_mem_idl f Y hY hπ hYs U')
  obtain ⟨e'', he''⟩ := exists_ringEquiv_of_eq (A := Γ(X, U)) (a := sec f ϖ U) (a' := sec f ϖ U)
    (vanishingIdeal_image_eq hU Y hY).symm rfl
  let E : objRing f Y hY π U' ≃+* AffineDilatation.Ring
      (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
      (sec f ϖ U) := e'.trans e''
  have hE : E.toRingHom.comp (algebraMap Γ(X, U) (objRing f Y hY π U')) = algebraMap _ _ := by
    have hEt : E.toRingHom = e''.toRingHom.comp e'.toRingHom := RingHom.ext fun x => rfl
    rw [hEt, RingHom.comp_assoc, he', he'']
  obtain ⟨e₂, he₂⟩ := exists_specIso (A := Γ(X, U)) E hE
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  rw [← he₁, Category.assoc, chart_p, Iso.trans_hom, Category.assoc]
  exact congrArg (e₁.hom ≫ ·)
    ((congrArg (· ≫ hU.fromSpec) he₂).symm.trans (Category.assoc _ _ _))

end Global

end P2mDilatation
p2m_reactivate "P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.P2mDilatation"

end
p2m_reactivate "P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed.P2mDilatation"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (Y : Set X) (hY : IsClosed Y) (hYs : ∀ y ∈ Y, f y = IsLocalRing.closedPoint R) :
    ∃ (D : Scheme.{u}) (p : D ⟶ X),
      IsAffineHom p ∧ LocallyOfFiniteType p ∧
      (∀ W : X.Opens, (∀ x ∈ W, f x ≠ IsLocalRing.closedPoint R) → IsIso (p ∣_ W)) ∧
      (∀ d : D, f (p d) = IsLocalRing.closedPoint R → p d ∈ Y) ∧
      (∀ (U : X.Opens) (hU : IsAffineOpen U) (π : R),
        IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ e : (↑(p ⁻¹ᵁ U) : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π))))),
          (p ⁻¹ᵁ U).ι ≫ p = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec) := by
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ : IsLocalRing.maximalIdeal R = Ideal.span {π} := hπirr.maximalIdeal_eq
  exact ⟨_, P2mDilatation.p f Y hY hπ hYs, inferInstance,
    P2mDilatation.locallyOfFiniteType_p f Y hY hπ hYs, P2mDilatation.isIso_restrict f Y hY hπ hYs,
    P2mDilatation.apply_mem f Y hY hπ hYs, P2mDilatation.exists_chartIso f Y hY hπ hYs⟩

end S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed
end P2MW
export P2MW.S_NeronModelInfra_exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed (solution)
