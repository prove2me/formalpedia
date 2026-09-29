-- Prove2me | solution 1 for NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d0170946-9c3b-5159-bb5d-96bf64fa35b0

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect
import Theorems.Thm_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
import Theorems.Thm_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
import Theorems.Thm_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
import Theorems.Thm_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_smoothLocus_le_preimage_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

universe v w

open TensorProduct IsLocalRing

noncomputable section

namespace NeronSmootheningDrop

theorem length_torsion_eq_of_equiv {S : Type u} [CommRing S] {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M'] (e : M ≃ₗ[S] M') :
    Module.length S (Submodule.torsion S M) = Module.length S (Submodule.torsion S M') := by
  have : (Submodule.torsion S M).map (e : M →ₗ[S] M') = Submodule.torsion S M' := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_torsion_iff]
    constructor
    · rintro ⟨x, ⟨a, ha⟩, rfl⟩
      refine ⟨a, ?_⟩
      change (a : S) • (e : M →ₗ[S] M') x = 0
      change (a : S) • x = 0 at ha
      rw [← map_smul, ha, map_zero]
    · rintro ⟨a, ha⟩
      refine ⟨e.symm y, ⟨a, ?_⟩, by simp⟩
      change (a : S) • e.symm y = 0
      change (a : S) • y = 0 at ha
      rw [← map_smul, ha, map_zero]
  rw [← this]
  exact (e.submoduleMap (Submodule.torsion S M)).length_eq

section Invariance

open TensorProduct

theorem smoothnessDefect_comp_eq {R : Type u} [CommRing R] {U X : Scheme.{u}} (g : U ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) {R' : Type u} [CommRing R'] [IsLocalRing R']
    (a : Spec (CommRingCat.of R') ⟶ U) [IsIso (g.stalkMap (a (IsLocalRing.closedPoint R')))] :
    smoothnessDefect (g ≫ f) a = smoothnessDefect f (a ≫ g) := by
  rw [smoothnessDefect_def, smoothnessDefect_def]
  set p : U := a (IsLocalRing.closedPoint R') with hp
  change _ = (letI : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
    letI : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
    Module.length R' (Submodule.torsion R' (R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R])))
  letI iRO : Algebra R (X.presheaf.stalk (g p)) := stalkAlgebra f (g p)
  letI iOR' : Algebra (X.presheaf.stalk (g p)) R' := pointAlgebra (a ≫ g)
  letI iRO' : Algebra R (U.presheaf.stalk p) := stalkAlgebra (g ≫ f) p
  letI iO'R' : Algebra (U.presheaf.stalk p) R' := pointAlgebra a
  letI iOO' : Algebra (X.presheaf.stalk (g p)) (U.presheaf.stalk p) := (g.stalkMap p).hom.toAlgebra
  haveI : IsScalarTower R (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro r
      change stalkAlgebraMap (g ≫ f) p r = (g.stalkMap p).hom (stalkAlgebraMap f (g p) r)
      rw [stalkAlgebraMap_apply, stalkAlgebraMap_apply, Scheme.Hom.germ_stalkMap_apply g ⊤ p trivial]
      rfl)
  haveI : IsScalarTower (X.presheaf.stalk (g p)) (U.presheaf.stalk p) R' :=
    IsScalarTower.of_algebraMap_eq' (by
      change (Scheme.stalkClosedPointTo (a ≫ g)).hom = (Scheme.stalkClosedPointTo a).hom.comp (g.stalkMap p).hom
      rw [Scheme.stalkClosedPointTo_comp]
      rfl)
  haveI : IsLocalization.Away (1 : X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (g.stalkMap p))
  haveI : Algebra.FormallyEtale (X.presheaf.stalk (g p)) (U.presheaf.stalk p) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : X.presheaf.stalk (g p)))
  let e₁ : (U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R] ≃ₗ[U.presheaf.stalk p]
      Ω[U.presheaf.stalk p⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (X.presheaf.stalk (g p)) (U.presheaf.stalk p)
  let e₂ : R' ⊗[U.presheaf.stalk p] Ω[U.presheaf.stalk p⁄R] ≃ₗ[R']
      R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R]) :=
    (e₁.symm.baseChange (U.presheaf.stalk p) R' _ _)
  let e₃ : R' ⊗[U.presheaf.stalk p] ((U.presheaf.stalk p) ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R])
      ≃ₗ[R'] R' ⊗[X.presheaf.stalk (g p)] Ω[X.presheaf.stalk (g p)⁄R] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (X.presheaf.stalk (g p)) (U.presheaf.stalk p) R' R'
      Ω[X.presheaf.stalk (g p)⁄R]
  exact length_torsion_eq_of_equiv (e₂.trans e₃)

end Invariance

theorem isIso_morphismRestrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  let W : (V : Scheme.{u}).Opens := V.ι ⁻¹ᵁ U
  have hW : V.ι ''ᵁ W = U := by
    apply le_antisymm
    · exact (Scheme.Hom.image_preimage_le _ _)
    · intro y hy
      exact ⟨⟨y, hUV hy⟩, hy, rfl⟩
  have h1 : IsIso (f ∣_ V ∣_ W) := inferInstance
  have h2 : IsIso (f ∣_ (V.ι ''ᵁ W)) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrict f V W)).mp h1
  rwa [hW] at h2

theorem exists_lift_of_apply_closedPoint_mem {U X : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g]
    {R' : Type u} [CommRing R'] [IsLocalRing R'] (a : Spec (CommRingCat.of R') ⟶ X)
    (h : a (IsLocalRing.closedPoint R') ∈ Set.range g) :
    ∃ a' : Spec (CommRingCat.of R') ⟶ U, a' ≫ g = a := by
  have hrange : Set.range a ⊆ Set.range g := by
    rintro _ ⟨z, rfl⟩
    have hz : a z ⤳ a (IsLocalRing.closedPoint R') :=
      (IsLocalRing.specializes_closedPoint z).map a.continuous
    exact g.isOpenEmbedding.isOpen_range.stableUnderGeneralization hz h
  exact ⟨IsOpenImmersion.lift g a hrange, IsOpenImmersion.lift_fac _ _ _⟩

section Chart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (U : X.Opens) (hU : IsAffineOpen U)

abbrev chartAlgebra : Algebra R Γ(X, U) :=
  ((X.presheaf.map (homOfLE le_top).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra

theorem fromSpec_comp_eq :
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U) (self := chartAlgebra f U))) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (V := U) (U := ⊤) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  congr 1

include hU in

theorem finiteType_chartAlgebra [LocallyOfFiniteType f] :
    @Algebra.FiniteType R Γ(X, U) _ _ (chartAlgebra f U) := by
  have h := f.finiteType_appLE (isAffineOpen_top (Spec (CommRingCat.of R))) hU (le_top : U ≤ f ⁻¹ᵁ ⊤)
  have h' := h.comp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  exact h'

end Chart

section GenericPoint

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

theorem apply_bot_mem_smoothLocus (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K)))
    {R' : Type u} [CommRing R'] [IsDomain R'] [Algebra R R'] (hinj : Function.Injective (algebraMap R R'))
    (a : Spec (CommRingCat.of R') ⟶ X) (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R'))) :
    a (⊥ : PrimeSpectrum R') ∈ f.smoothLocus := by
  haveI := hK
  have h1 : f (a (⊥ : PrimeSpectrum R')) = (⊥ : PrimeSpectrum R) := by
    rw [← Scheme.Hom.comp_apply, ha]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R R') ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj
  have h2 : (specGenericFibreInclusion R K) (⊥ : PrimeSpectrum K) = (⊥ : PrimeSpectrum R) := by
    rw [specGenericFibreInclusion_eq]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := specGenericFibreInclusion R K) (a (⊥ : PrimeSpectrum R')) (⊥ : PrimeSpectrum K) (by rw [h1, h2])
  haveI : Flat (specGenericFibreInclusion R K) := by
    rw [specGenericFibreInclusion_eq, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
    have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
    exact RingHom.flat_algebraMap_iff.mpr this
  have hle := AlgebraicGeometry.Scheme.Hom.smoothLocus_le_preimage_of_isPullback
    (IsPullback.of_hasPullback f (specGenericFibreInclusion R K))
  have hz' : z ∈ (pullback.snd f (specGenericFibreInclusion R K)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]; trivial
  have := hle hz'
  rwa [Scheme.Hom.mem_preimage, hz] at this

end GenericPoint

section SmoothLocusChart

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [LocallyOfFinitePresentation f] (U : X.Opens) (hU : IsAffineOpen U)

theorem mem_smoothLocus_iff_mem_algebra_smoothLocus (x : X) (hx : x ∈ U) :
    x ∈ f.smoothLocus ↔
      (letI : Algebra R Γ(X, U) := chartAlgebra f U
       hU.primeIdealOf ⟨x, hx⟩ ∈ Algebra.smoothLocus R Γ(X, U)) := by
  letI iR : Algebra R Γ(X, U) := chartAlgebra f U
  letI iΓ : Algebra Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U) := (f.appLE ⊤ U le_top).hom.toAlgebra
  letI iRΓ : Algebra R Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toAlgebra
  haveI : IsScalarTower R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [Scheme.Hom.mem_smoothLocus,
    AlgebraicGeometry.formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) U hU le_top hx]
  change Algebra.IsSmoothAt Γ(Spec (CommRingCat.of R), ⊤) (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔
    Algebra.IsSmoothAt R (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  haveI : IsLocalization.Away (1 : R) Γ(Spec (CommRingCat.of R), ⊤) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)
  haveI : Algebra.FormallyEtale R Γ(Spec (CommRingCat.of R), ⊤) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : R))
  exact (Algebra.FormallySmooth.iff_restrictScalars (R := R) (A := Γ(Spec (CommRingCat.of R), ⊤))).symm

end SmoothLocusChart

theorem primeIdealOf_fromSpec_apply {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (z : PrimeSpectrum Γ(X, U)) (h : hU.fromSpec z ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec z, h⟩ = z := by
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf]

end NeronSmootheningDrop

end

open NeronSmootheningDrop in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType (v ≫ f) ∧ QuasiCompact (v ≫ f) ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ f.smoothLocus) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
            x₁.1 ≫ v = x.1) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
          smoothnessDefect (v ≫ f) x₁.1 + 1 ≤ max 1 (smoothnessDefect f (x₁.1 ≫ v)))  := by
  classical
  obtain ⟨t, Y, hYc, hanti, hYt, hYs, hYsm, hY0, hchart⟩ :=
    NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd K f hK
  obtain ⟨X₁, v, hsep, hlft, hqc, hiso, hisoY, hlift, hW⟩ :=
    NeronModelInfra.exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
      K f t Y hYc hanti hYt hYs
  haveI := hsep; haveI := hlft; haveI := hqc
  refine ⟨X₁, v, hsep, inferInstance, inferInstance, hiso, ?_, ?_, ?_⟩
  ·
    haveI := hisoY
    exact isIso_morphismRestrict_of_le v (U := f.smoothLocus) (V := ⟨(Y 0)ᶜ, (hYc 0).isOpen_compl⟩)
      (fun y hy hy0 => hYsm y hy0 hy)
  · intro R' _ _ _ _ _ hR' x
    obtain ⟨x₁, hx₁, -⟩ := hlift R' hR'.map_maximalIdeal x
    exact ⟨x₁, hx₁⟩
  · intro R' _ _ _ _ _ hR' x₁

    let x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f :=
      ⟨x₁.1 ≫ v, by rw [Category.assoc]; exact x₁.2⟩
    have hinj : Function.Injective (algebraMap R R') := by
      rw [RingHom.injective_iff_ker_eq_bot]
      by_contra hne
      have hmax : (RingHom.ker (algebraMap R R')).IsMaximal :=
        (RingHom.ker_isPrime (algebraMap R R')).isMaximal hne
      have hker : RingHom.ker (algebraMap R R') = maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
      have : maximalIdeal R' = ⊥ := by
        rw [← hR'.map_maximalIdeal, ← hker, Ideal.map_eq_bot_iff_le_ker]
      exact IsDiscreteValuationRing.not_a_field R' this
    have hgen : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') ∈ f.smoothLocus :=
      apply_bot_mem_smoothLocus K f hK hinj (x₁.1 ≫ v) x.2
    obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπ : maximalIdeal R = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr

    set s : X := (x₁.1 ≫ v) (IsLocalRing.closedPoint R') with hs_def
    by_cases hs : s ∈ Y 0
    swap
    ·
      have hsm : s ∈ (f.smoothLocus : Set X) := by
        by_contra h; exact hs (hY0 R' hR' x h)
      have h0 : smoothnessDefect f (x₁.1 ≫ v) = 0 :=
        (NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus f (x₁.1 ≫ v) hgen).mpr
          hsm
      let V : X.Opens := ⟨(Y 0)ᶜ, (hYc 0).isOpen_compl⟩
      haveI : IsIso (v ∣_ V) := hisoY
      have hx₁V : x₁.1 (IsLocalRing.closedPoint R') ∈ Set.range (v ⁻¹ᵁ V).ι := by
        rw [Scheme.Opens.range_ι]; exact hs
      obtain ⟨y, hy⟩ := exists_lift_of_apply_closedPoint_mem (v ⁻¹ᵁ V).ι x₁.1 hx₁V
      have e1 : smoothnessDefect (v ≫ f) x₁.1 = smoothnessDefect f (x₁.1 ≫ v) := by
        rw [← hy, ← smoothnessDefect_comp_eq ((v ⁻¹ᵁ V).ι) (v ≫ f) y]
        have hfac : (v ⁻¹ᵁ V).ι ≫ v ≫ f = (v ∣_ V) ≫ (V.ι ≫ f) := by
          rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
        rw [hfac, smoothnessDefect_comp_eq (v ∣_ V) (V.ι ≫ f) y, smoothnessDefect_comp_eq V.ι f (y ≫ v ∣_ V),
          Category.assoc, Category.assoc, morphismRestrict_ι]
      rw [e1, h0]
      simp
    ·
      have hex : ∃ j, s ∉ Y j := ⟨t, by rw [hYt]; exact Set.notMem_empty s⟩
      have hj : s ∉ Y (Nat.find hex) := Nat.find_spec hex
      have hj0 : Nat.find hex ≠ 0 := fun h => by rw [h] at hj; exact hj hs
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hsi : s ∈ Y i := by
        by_contra h; exact Nat.find_min hex (show i < Nat.find hex by omega) h
      have hsi1 : s ∉ Y (i + 1) := by have h' := hj; rwa [hi] at h'
      have hit : i < t := by
        have := Nat.find_le (h := hex) (n := t) (by rw [hYt]; exact Set.notMem_empty s)
        omega
      obtain ⟨U, hU, hxU, hUY, hN, hgood⟩ := hchart i hit R' hR' x hsi hsi1
      obtain ⟨W, e, hWv, hWpt⟩ := hW i hit U hU hUY π hπ
      have hx₁W : x₁.1 (IsLocalRing.closedPoint R') ∈ W := hWpt R' hR'.map_maximalIdeal x₁ hsi hxU
      letI iRA : Algebra R Γ(X, U) := chartAlgebra f U

      let J : Ideal Γ(X, U) :=
        PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i})
      let A' : Type u := AffineDilatation.Ring J (algebraMap R Γ(X, U) π)

      obtain ⟨a, ha⟩ := exists_lift_of_apply_closedPoint_mem hU.fromSpec (x₁.1 ≫ v)
        (by rw [IsAffineOpen.range_fromSpec]; exact hxU)
      have hfS := fromSpec_comp_eq f U hU

      obtain ⟨y₁, hy₁⟩ := exists_lift_of_apply_closedPoint_mem W.ι x₁.1 (by rw [Scheme.Opens.range_ι]; exact hx₁W)
      set z : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of A') := y₁ ≫ e.hom with hz
      have hza : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) A')) = a := by
        rw [← cancel_mono hU.fromSpec, Category.assoc, ha, ← hy₁, hz]
        simp only [Category.assoc]
        rw [hWv]

      set φr := Spec.preimage a with hφr
      set φ'r := Spec.preimage z with hφ'r
      have haφ : Spec.map φr = a := Spec.map_preimage a
      have hzφ : Spec.map φ'r = z := Spec.map_preimage z
      have hcompat : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫ φr = CommRingCat.ofHom (algebraMap R R') := by
        apply Spec.map_injective
        rw [Spec.map_comp, haφ, ← hfS, ← Category.assoc, ha, Category.assoc]
        exact x₁.2
      have hcompat' : CommRingCat.ofHom (algebraMap Γ(X, U) A') ≫ φ'r = φr := by
        apply Spec.map_injective
        rw [Spec.map_comp, hzφ, hza, haφ]
      let φ : Γ(X, U) →ₐ[R] R' := AlgHom.mk φr.hom fun r => by
        have := congrArg (fun ψ => ψ.hom r) hcompat
        first | exact this | simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] using this
      let φ' : A' →ₐ[R] R' := AlgHom.mk φ'r.hom fun r => by
        have h1 := congrArg (fun ψ => ψ.hom (algebraMap R Γ(X, U) r)) hcompat'
        have h2 := congrArg (fun ψ => ψ.hom r) hcompat
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at h1 h2
        change φ'r.hom (algebraMap R A' r) = algebraMap R R' r
        rw [IsScalarTower.algebraMap_apply R Γ(X, U) A' r]
        exact h1.trans h2
      have hφ' : ∀ b : Γ(X, U), φ' (algebraMap Γ(X, U) A' b) = φ b := fun b => by
        have := congrArg (fun ψ => ψ.hom b) hcompat'
        first | exact this | simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] using this

      have hsU : hU.fromSpec (a (IsLocalRing.closedPoint R')) = s := by
        rw [← Scheme.Hom.comp_apply, ha]
      have h𝔭 : hU.primeIdealOf ⟨s, hxU⟩ = a (IsLocalRing.closedPoint R') := by
        have := primeIdealOf_fromSpec_apply hU (a (IsLocalRing.closedPoint R')) (hsU.symm ▸ hxU)
        convert this using 3; exact hsU.symm
      have h𝔭' : (hU.primeIdealOf ⟨s, hxU⟩).asIdeal = (maximalIdeal R').comap φ := by
        rw [h𝔭, ← haφ]; rfl
      have hJ𝔭 : J ≤ (hU.primeIdealOf ⟨s, hxU⟩).asIdeal := fun g hg =>
        (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg _ ⟨⟨s, hxU⟩, hsi, rfl⟩
      let 𝔮 : Ideal (Γ(X, U) ⧸ J) := (hU.primeIdealOf ⟨s, hxU⟩).asIdeal.map (Ideal.Quotient.mk J)
      haveI h𝔮p : 𝔮.IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have h𝔮c : 𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨s, hxU⟩).asIdeal := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr hJ𝔭]

      have hπJ : algebraMap R Γ(X, U) π ∈ J := by
        rw [PrimeSpectrum.mem_vanishingIdeal]
        rintro _ ⟨y, hy, rfl⟩
        have hy0 : (y : X) ∈ Y 0 := (antitone_nat_of_succ_le hanti (Nat.zero_le i)) hy
        have h1 : (hU.fromSpec ≫ f) (hU.primeIdealOf y) = IsLocalRing.closedPoint R := by
          rw [Scheme.Hom.comp_apply, IsAffineOpen.fromSpec_primeIdealOf]; exact hYs _ hy0
        rw [hfS] at h1
        have h2 : π ∈ ((Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) (hU.primeIdealOf y)).asIdeal := by
          rw [h1]
          change π ∈ maximalIdeal R
          rw [hπ]; exact Ideal.mem_span_singleton_self π
        exact h2
      have hle : maximalIdeal R ≤ J.comap (algebraMap R Γ(X, U)) := by
        rw [hπ, Ideal.span_singleton_le_iff_mem]; exact hπJ
      letI ik : Algebra (ResidueField R) (Γ(X, U) ⧸ J) := (Ideal.quotientMap J (algebraMap R Γ(X, U)) hle).toAlgebra
      haveI : IsScalarTower R (ResidueField R) (Γ(X, U) ⧸ J) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => rfl)
      obtain ⟨hsmooth, hfree⟩ := hgood 𝔮 h𝔮c

      have hbotU : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') ∈ U := by
        have hb0 : (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') = hU.fromSpec (a (⊥ : PrimeSpectrum R')) := by
          rw [← Scheme.Hom.comp_apply, ha]
        have hr := hU.range_fromSpec
        rw [Set.ext_iff] at hr
        rw [hb0]
        exact (hr _).mp ⟨_, rfl⟩
      have hgen' : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈ Algebra.smoothLocus R Γ(X, U) := by
        have key := (mem_smoothLocus_iff_mem_algebra_smoothLocus f U hU _ hbotU).mp hgen
        have hpt : hU.primeIdealOf ⟨(x₁.1 ≫ v) (⊥ : PrimeSpectrum R'), hbotU⟩ = a (⊥ : PrimeSpectrum R') := by
          have hb : hU.fromSpec (a (⊥ : PrimeSpectrum R')) = (x₁.1 ≫ v) (⊥ : PrimeSpectrum R') := by
            rw [← Scheme.Hom.comp_apply, ha]
          have := primeIdealOf_fromSpec_apply hU (a (⊥ : PrimeSpectrum R')) (hb.symm ▸ hbotU)
          convert this using 3; exact hb.symm
        rw [hpt, ← haφ] at key
        exact key

      haveI : Algebra.FiniteType R Γ(X, U) := finiteType_chartAlgebra f U hU
      have key := NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
        π hπ J hπJ hN R' hR' φ hgen' 𝔮 (by rw [h𝔮c, h𝔭']) hsmooth hfree φ' hφ'

      have e_right : smoothnessDefect f (x₁.1 ≫ v) =
          smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))))
            (Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
        rw [← ha, ← smoothnessDefect_comp_eq hU.fromSpec f a, hfS, ← haφ]
        rfl
      have hsc : CommRingCat.ofHom (algebraMap R Γ(X, U)) ≫ CommRingCat.ofHom (algebraMap Γ(X, U) A') =
          CommRingCat.ofHom (algebraMap R A') := by
        rw [← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R Γ(X, U) A']
      have e_left : smoothnessDefect (v ≫ f) x₁.1 =
          smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A')))
            (Spec.map (CommRingCat.ofHom φ'.toRingHom)) := by
        rw [← hy₁, ← smoothnessDefect_comp_eq W.ι (v ≫ f) y₁]
        have hWvf : W.ι ≫ v ≫ f =
            e.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) A')) ≫ hU.fromSpec ≫ f) := by
          rw [← Category.assoc, hWv]; simp only [Category.assoc]
        rw [hWvf, smoothnessDefect_comp_eq e.hom _ y₁, hfS, ← Spec.map_comp, hsc, ← hz, ← hzφ]
        rfl
      rw [e_left, e_right]
      exact key

end S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd
end P2MW
export P2MW.S_NeronModelInfra_exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd (solution)
