-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d3dd9a44-581e-53e3-8754-3e3d9c67647f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mSurjIsog

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

section Alg

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem isIntegral_quotient_of_generators {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (hs : Algebra.adjoin R (s : Set C) = ⊤) (r : R)
    (hint : ∀ z ∈ s, IsIntegral R (r • z)) (m : Ideal R) [m.IsMaximal] (hrm : r ∉ m) :
    Algebra.IsIntegral (R ⧸ m) (C ⧸ m.map (algebraMap R C)) := by
  classical
  letI := Ideal.Quotient.field m
  set I : Ideal C := m.map (algebraMap R C) with hI
  let π : C →ₐ[R] C ⧸ I := Ideal.Quotient.mkₐ R I
  have hu : (Ideal.Quotient.mk m r) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hgen : ∀ z ∈ s, IsIntegral (R ⧸ m) (π z) := by
    intro z hz
    have h1 : IsIntegral R (π (r • z)) := (hint z hz).map π
    have h2 : IsIntegral (R ⧸ m) (π (r • z)) := h1.tower_top
    have h3 : π (r • z) = (Ideal.Quotient.mk m r) • π z := by
      rw [map_smul]
      exact (IsScalarTower.algebraMap_smul (R ⧸ m) r (π z)).symm
    rw [h3] at h2
    have h4 := h2.smul ((Ideal.Quotient.mk m r)⁻¹)
    rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at h4
  refine ⟨fun x => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsIntegral (R ⧸ m) (π c)
  have hc : c ∈ Algebra.adjoin R (s : Set C) := by rw [hs]; exact Algebra.mem_top
  induction hc using Algebra.adjoin_induction with
  | mem z hz => exact hgen z hz
  | algebraMap a =>
      rw [AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply R (R ⧸ m) (C ⧸ I)]
      exact isIntegral_algebraMap
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem exists_ne_zero_forall_finite_liesOver (R C : Type*) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Algebra.FiniteType R C] [Algebra.IsAlgebraic R C] :
    ∃ r : R, r ≠ 0 ∧ ∀ (m : Ideal R), m.IsMaximal → r ∉ m →
      {Q : PrimeSpectrum C | Q.asIdeal.comap (algebraMap R C) = m}.Finite := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  obtain ⟨r, hr0, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples R s
  refine ⟨r, hr0, fun m hm hrm => ?_⟩
  letI : m.IsMaximal := hm
  letI := Ideal.Quotient.field m
  set I : Ideal C := m.map (algebraMap R C) with hI
  haveI hintC' : Algebra.IsIntegral (R ⧸ m) (C ⧸ I) :=
    isIntegral_quotient_of_generators s hs r hint m hrm
  haveI : Algebra.FiniteType R (C ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Algebra.FiniteType (R ⧸ m) (C ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ m) (C ⧸ I)
  haveI : Module.Finite (R ⧸ m) (C ⧸ I) := Algebra.IsIntegral.finite
  haveI : IsArtinianRing (C ⧸ I) := IsArtinianRing.of_finite (R ⧸ m) (C ⧸ I)

  have hsub : {Q : PrimeSpectrum C | Q.asIdeal.comap (algebraMap R C) = m} ⊆
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    intro Q hQ
    have hIQ : I ≤ Q.asIdeal := by
      rw [hI, Ideal.map_le_iff_le_comap]
      exact le_of_eq hQ.symm
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ Q.asIdeal := by
      rwa [Ideal.mk_ker]
    refine ⟨⟨Q.asIdeal.map (Ideal.Quotient.mk I), ?_⟩, ?_⟩
    · exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    · ext1
      change (Q.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q.asIdeal
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left]
      rwa [← RingHom.ker_eq_comap_bot]
  exact (Set.finite_range _).subset hsub

universe u₁ u₂ u₃

theorem isAlgebraic_of_trdeg_eq (K : Type u₁) (R : Type u₂) (C : Type u₃) [Field K] [CommRing R]
    [IsDomain R] [CommRing C] [IsDomain C] [Algebra K R] [Algebra K C] [Algebra R C]
    [IsScalarTower K R C] [Algebra.FiniteType K R] (hinj : Function.Injective (algebraMap R C))
    (h : Cardinal.lift.{u₃} (Algebra.trdeg K R) = Cardinal.lift.{u₂} (Algebra.trdeg K C)) :
    Algebra.IsAlgebraic R C := by
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hinj
  haveI : FaithfulSMul K R :=
    (faithfulSMul_iff_algebraMap_injective K R).mpr (algebraMap K R).injective
  have hadd := lift_trdeg_add_eq K R C
  have hfin : Algebra.trdeg K R < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  rw [← h] at hadd

  have hb : Cardinal.lift.{u₂} (Algebra.trdeg R C) = 0 := by
    have hfin' : Cardinal.lift.{u₃} (Algebra.trdeg K R) < Cardinal.aleph0 := by
      simpa using hfin
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin'
    rw [hn] at hadd
    by_contra hne
    have hpos : 1 ≤ Cardinal.lift.{u₂} (Algebra.trdeg R C) := Cardinal.one_le_iff_ne_zero.mpr hne
    have : (n : Cardinal) + 1 ≤ (n : Cardinal) + Cardinal.lift.{u₂} (Algebra.trdeg R C) :=
      add_le_add (le_refl _) hpos
    rw [hadd] at this
    have h' : ((n + 1 : ℕ) : Cardinal.{max u₂ u₃}) ≤ (n : Cardinal.{max u₂ u₃}) := by
      exact_mod_cast this
    exact absurd (Nat.cast_le.mp h') (by omega)
  have hb' : Algebra.trdeg R C = 0 := by
    simpa using hb
  exact trdeg_eq_zero_iff.mp hb'

end Alg

section Sections

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

def algK (U : A.Opens) : K →+* Γ(A, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top).hom

theorem map_comp_algK {U V : A.Opens} (i : V ≤ U) :
    (A.presheaf.map (homOfLE i).op).hom.comp (algK f U) = algK f V := by
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫
    A.presheaf.map (homOfLE i).op).hom = _
  rw [Scheme.Hom.appLE_map]
  rfl

def algFF [IrreducibleSpace A] : K →+* A.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ ⊤ le_top ≫
    A.presheaf.germ ⊤ (genericPoint A) trivial).hom

theorem germ_comp_algK [IrreducibleSpace A] (U : A.Opens) [hU : Nonempty U] :
    (A.germToFunctionField U).hom.comp (algK f U) = algFF f := by
  have hη : genericPoint A ∈ U :=
    ((genericPoint_spec A).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫
    A.presheaf.germ U (genericPoint A) hη).hom = _
  rw [← Scheme.Hom.appLE_map f (le_top : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤) (homOfLE (le_top : U ≤ ⊤)).op,
    Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem trdeg_sections_eq [IsIntegral A] (U : A.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (algK f U).toAlgebra
    letI := (algFF f).toAlgebra
    Algebra.trdeg K Γ(A, U) = Algebra.trdeg K A.functionField := by
  letI := (algK f U).toAlgebra
  letI := (algFF f).toAlgebra
  haveI : IsScalarTower K Γ(A, U) A.functionField :=
    IsScalarTower.of_algebraMap_eq' (germ_comp_algK f U).symm
  haveI := functionField_isFractionRing_of_isAffineOpen A U hU
  haveI : FaithfulSMul K Γ(A, U) :=
    (faithfulSMul_iff_algebraMap_injective K _).mpr (algebraMap K Γ(A, U)).injective
  haveI : FaithfulSMul Γ(A, U) A.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(A, U) _)
  have halg : Algebra.IsAlgebraic Γ(A, U) A.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(A, U))
  have h0 : Algebra.trdeg Γ(A, U) (A.functionField : Type u) = 0 := trdeg_eq_zero_iff.mpr halg
  have hadd := trdeg_add_eq K Γ(A, U) (A := (A.functionField : Type u))
  rw [h0, add_zero] at hadd
  exact hadd

omit [Field K] in
theorem appLE_congr_hom {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ g ⁻¹ᵁ U) (e' : V ≤ g' ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V e' := by
  subst h; rfl

variable (γ : A ⟶ A) (hγ : γ ≫ f = f)
include hγ

theorem appLE_comp_algK {U W : A.Opens} (e : W ≤ γ ⁻¹ᵁ U) :
    (γ.appLE U W e).hom.comp (algK f U) = algK f W := by
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫ γ.appLE U W e).hom = _
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hγ ⊤ W _ le_top]
  rfl

omit hγ in

theorem appLE_injective [IsIntegral A] (hsurj : Function.Surjective γ) {U W : A.Opens} [hW : Nonempty W]
    (e : W ≤ γ ⁻¹ᵁ U) : Function.Injective (γ.appLE U W e).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : (A.presheaf.map (homOfLE e).op).hom (γ.app U x) = 0 := by
    rw [← hx]; rfl
  have h2 : γ.app U x = 0 := by
    rw [← (A.presheaf.map (homOfLE e).op).hom.map_zero] at h1
    exact map_injective_of_isIntegral A (homOfLE e) h1
  have h3 : γ ⁻¹ᵁ (A.basicOpen x) = ⊥ := by
    rw [Scheme.preimage_basicOpen, h2, Scheme.basicOpen_zero]
  have h4 : A.basicOpen x = ⊥ := by
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hy
    obtain ⟨z, rfl⟩ := hsurj y
    have : z ∈ (γ ⁻¹ᵁ (A.basicOpen x) : A.Opens) := hy
    rw [h3] at this
    exact this
  exact (basicOpen_eq_bot_iff x).mp h4

theorem exists_forall_finite_fibre_inter [IsIntegral A] [LocallyOfFiniteType f] (hsurj : Function.Surjective γ)
    {U W : A.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) [Nonempty U] [Nonempty W]
    (e : W ≤ γ ⁻¹ᵁ U) :
    ∃ r : Γ(A, U), r ≠ 0 ∧ ∀ (y : A) (_ : y ∈ U), IsClosed ({y} : Set A) → y ∈ A.basicOpen r →
      {p : A | p ∈ W ∧ γ p = y}.Finite := by
  classical

  let φ : Γ(A, U) →+* Γ(A, W) := (γ.appLE U W e).hom
  letI : Algebra K Γ(A, U) := (algK f U).toAlgebra
  letI : Algebra K Γ(A, W) := (algK f W).toAlgebra
  letI : Algebra Γ(A, U) Γ(A, W) := φ.toAlgebra
  haveI : IsScalarTower K Γ(A, U) Γ(A, W) :=
    IsScalarTower.of_algebraMap_eq' (appLE_comp_algK f γ hγ e).symm

  haveI : LocallyOfFiniteType γ := by
    have : LocallyOfFiniteType (γ ≫ f) := by rw [hγ]; infer_instance
    exact locallyOfFiniteType_of_comp γ f
  have hft : φ.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType γ inferInstance ⟨U, hU⟩ ⟨W, hW⟩ e
  haveI : Algebra.FiniteType Γ(A, U) Γ(A, W) := hft
  have hftK : (algK f U).FiniteType := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
        le_top
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType K Γ(A, U) := hftK

  haveI : Algebra.IsAlgebraic Γ(A, U) Γ(A, W) := by
    refine isAlgebraic_of_trdeg_eq K Γ(A, U) Γ(A, W) (appLE_injective γ hsurj e) ?_
    letI : Algebra K A.functionField := (algFF f).toAlgebra
    rw [trdeg_sections_eq f U hU, trdeg_sections_eq f W hW]
  obtain ⟨r, hr0, hfin⟩ := exists_ne_zero_forall_finite_liesOver Γ(A, U) Γ(A, W)
  refine ⟨r, hr0, fun y hyU hyc hyr => ?_⟩

  let m := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  have hm : m.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨y, hyU⟩ hyc
  have hrm : r ∉ m := by
    have h1 : hU.fromSpec (hU.primeIdealOf ⟨y, hyU⟩) ∈ A.basicOpen r := by
      rw [hU.fromSpec_primeIdealOf]; exact hyr
    have h2 : hU.primeIdealOf ⟨y, hyU⟩ ∈ hU.fromSpec ⁻¹ᵁ (A.basicOpen r) := h1
    rw [hU.fromSpec_preimage_basicOpen] at h2
    exact h2
  have hF := hfin m hm hrm

  let Θ : {p : A | p ∈ W ∧ γ p = y} → PrimeSpectrum Γ(A, W) := fun p => hW.primeIdealOf ⟨p.1, p.2.1⟩
  have hΘinj : Function.Injective Θ := by
    intro p q hpq
    apply Subtype.ext
    have h := congrArg (fun P => (hW.fromSpec P : A)) hpq
    simpa only [Θ, hW.fromSpec_primeIdealOf] using h
  have hΘmem : ∀ p, Θ p ∈ {Q : PrimeSpectrum Γ(A, W) | Q.asIdeal.comap (algebraMap Γ(A, U) Γ(A, W)) = m} := by
    intro p
    change (PrimeSpectrum.comap φ (Θ p)).asIdeal = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
    have key : hU.fromSpec (PrimeSpectrum.comap φ (Θ p)) = hU.fromSpec (hU.primeIdealOf ⟨y, hyU⟩) := by
      rw [hU.fromSpec_primeIdealOf]
      change hU.fromSpec ((Spec.map (γ.appLE U W e)) (hW.primeIdealOf ⟨p.1, p.2.1⟩)) = y
      rw [← Scheme.Hom.comp_apply, hU.SpecMap_appLE_fromSpec γ hW e, Scheme.Hom.comp_apply,
        hW.fromSpec_primeIdealOf]
      exact p.2.2
    rw [hU.isOpenImmersion_fromSpec.base_open.injective key]
  have : Finite {p : A | p ∈ W ∧ γ p = y} := by
    haveI : Finite {Q : PrimeSpectrum Γ(A, W) | Q.asIdeal.comap (algebraMap Γ(A, U) Γ(A, W)) = m} :=
      hF.to_subtype
    exact Finite.of_injective (fun p => (⟨Θ p, hΘmem p⟩ : {Q : PrimeSpectrum Γ(A, W) |
      Q.asIdeal.comap (algebraMap Γ(A, U) Γ(A, W)) = m})) (fun p q h => hΘinj (congrArg Subtype.val h))
  exact Set.toFinite _

end Sections

section KPoints

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem finiteType_algK [LocallyOfFiniteType f] {W : A.Opens} (hW : IsAffineOpen W) :
    (algK f W).FiniteType := by
  have h1 : (f.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      le_top
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)

theorem exists_section_mem [IsAlgClosed K] [LocallyOfFiniteType f] (V : A.Opens)
    (hV : (V : Set A).Nonempty) :
    ∃ a : Spec (CommRingCat.of K) ⟶ A, a ≫ f = 𝟙 _ ∧ ∀ s, a s ∈ V := by
  classical
  obtain ⟨x, hxV⟩ := hV
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  letI : Algebra K Γ(A, W) := (algK f W).toAlgebra
  haveI : Algebra.FiniteType K Γ(A, W) := finiteType_algK f hW
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal Γ(A, W)
  letI := Ideal.Quotient.field 𝔪
  haveI : Algebra.FiniteType K (Γ(A, W) ⧸ 𝔪) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K 𝔪) (Ideal.Quotient.mkₐ_surjective K 𝔪)
  haveI : Module.Finite K (Γ(A, W) ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing K _
  haveI : Algebra.IsIntegral K (Γ(A, W) ⧸ 𝔪) := Algebra.IsIntegral.of_finite K _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := Γ(A, W) ⧸ 𝔪)
  let eKS : K ≃+* Γ(A, W) ⧸ 𝔪 := RingEquiv.ofBijective (algebraMap K (Γ(A, W) ⧸ 𝔪)) hbij
  let ψ : Γ(A, W) →+* K := eKS.symm.toRingHom.comp (Ideal.Quotient.mk 𝔪)
  have hψ : ψ.comp (algK f W) = RingHom.id K := by
    ext c
    change eKS.symm (Ideal.Quotient.mk 𝔪 (algebraMap K Γ(A, W) c)) = c
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact eKS.symm_apply_apply c
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec, ?_, ?_⟩
  · rw [Category.assoc,
      ← (isAffineOpen_top (Spec (CommRingCat.of K))).SpecMap_appLE_fromSpec f hW le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp]
    have h : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ W le_top ≫ CommRingCat.ofHom ψ =
        𝟙 _ := by
      ext1
      change ψ.comp (algK f W) = RingHom.id K
      exact hψ
    rw [h, Spec.map_id]
  · intro s
    apply hWV
    change (Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec) s ∈ (W : Set A)
    rw [← hW.range_fromSpec, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

end KPoints

section GroupLaw

open NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

def IsHom (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    (L.mul t x y) ⊚ β = L.mul t (x ⊚ β) (y ⊚ β)

section Points

variable (L : RelativeGroupLaw K f)

theorem pull_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) (β : SchemeHomOver f f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (x ⊚ β) =
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) ⊚ β :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

theorem pull_one {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  L.one_natural t t' ψ hψ

theorem pull_inv {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {t' : T' ⟶ Spec (CommRingCat.of K)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h1 : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, pull_one]
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) *
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = 1 at h1
  exact eq_inv_of_mul_eq_one_left h1

variable {L}
variable {β : SchemeHomOver f f} (hβ : IsHom L β)
include hβ

theorem hom_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (L.one t) ⊚ β = L.one t := by
  letI := L.pointGroup t
  have h : (L.one t) ⊚ β = L.mul t ((L.one t) ⊚ β) ((L.one t) ⊚ β) := by
    conv_lhs => rw [← L.one_mul t (L.one t)]
    exact hβ t _ _
  change (L.one t) ⊚ β = ((L.one t) ⊚ β) * ((L.one t) ⊚ β) at h
  exact (mul_eq_left.mp h.symm)

theorem hom_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) :
    (L.inv t x) ⊚ β = L.inv t (x ⊚ β) := by
  letI := L.pointGroup t
  have h1 : L.mul t ((L.inv t x) ⊚ β) (x ⊚ β) = L.one t := by
    rw [← hβ, L.inv_mul_cancel, hom_one hβ]
  change ((L.inv t x) ⊚ β) * (x ⊚ β) = 1 at h1
  exact eq_inv_of_mul_eq_one_left h1

end Points

section Translate

variable (L : RelativeGroupLaw K f) {β : SchemeHomOver f f} (hβ : IsHom L β)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (ξ : SchemeHomOver t f)

abbrev P₀ : Scheme.{u} := pullback (L.endKerStr β) t

abbrev P₁ : Scheme.{u} := pullback β.1 (ξ.1 ≫ β.1)

abbrev t₀ : P₀ L t (β := β) ⟶ Spec (CommRingCat.of K) := pullback.snd (L.endKerStr β) t ≫ t

abbrev t₁ : P₁ t ξ (β := β) ⟶ Spec (CommRingCat.of K) := pullback.snd β.1 (ξ.1 ≫ β.1) ≫ t

def k₀ : SchemeHomOver (t₀ L t (β := β)) f :=
  ⟨pullback.fst (L.endKerStr β) t ≫ L.endKerι β, by
    rw [Category.assoc, RelativeGroupLaw.endKerι_comp_base, pullback.condition]⟩

def x₀ : SchemeHomOver (t₀ L t (β := β)) f :=
  ⟨pullback.snd (L.endKerStr β) t ≫ ξ.1, by rw [Category.assoc, ξ.2]⟩

def q₁ : SchemeHomOver (t₁ t ξ (β := β)) f :=
  ⟨pullback.fst β.1 (ξ.1 ≫ β.1), by
    have h : pullback.fst β.1 (ξ.1 ≫ β.1) ≫ f = pullback.fst β.1 (ξ.1 ≫ β.1) ≫ (β.1 ≫ f) := by
      rw [β.2]
    rw [h, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, β.2, ξ.2]⟩

def x₁ : SchemeHomOver (t₁ t ξ (β := β)) f :=
  ⟨pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1, by rw [Category.assoc, ξ.2]⟩

theorem k₀_comp : (k₀ L t (β := β)) ⊚ β = L.one (t₀ L t (β := β)) := by
  apply Subtype.ext
  change (pullback.fst (L.endKerStr β) t ≫ L.endKerι β) ≫ β.1 = (L.one _).1
  rw [one_coe L (t₀ L t)]
  change _ = (pullback.snd (L.endKerStr β) t ≫ t) ≫ _
  rw [Category.assoc, RelativeGroupLaw.endKerι_comp, ← Category.assoc, pullback.condition,
    Category.assoc]

theorem q₁_comp : (q₁ t ξ (β := β)) ⊚ β = (x₁ t ξ (β := β)) ⊚ β := by
  apply Subtype.ext
  change pullback.fst β.1 (ξ.1 ≫ β.1) ≫ β.1 = (pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1) ≫ β.1
  rw [pullback.condition, Category.assoc]

include hβ

def Φ : P₀ L t (β := β) ⟶ P₁ t ξ (β := β) :=
  pullback.lift (L.mul _ (k₀ L t) (x₀ L t ξ)).1 (pullback.snd (L.endKerStr β) t) (by
    have h : (L.mul _ (k₀ L t (β := β)) (x₀ L t ξ)) ⊚ β = (x₀ L t ξ) ⊚ β := by
      rw [hβ, k₀_comp, L.one_mul]
    have h' := congrArg Subtype.val h
    change (L.mul _ (k₀ L t (β := β)) (x₀ L t ξ)).1 ≫ β.1 =
      (pullback.snd (L.endKerStr β) t ≫ ξ.1) ≫ β.1 at h'
    rw [h', Category.assoc])

@[reassoc (attr := simp)]
theorem Φ_fst : Φ L hβ t ξ ≫ pullback.fst β.1 (ξ.1 ≫ β.1) = (L.mul _ (k₀ L t) (x₀ L t ξ)).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Φ_snd : Φ L hβ t ξ ≫ pullback.snd β.1 (ξ.1 ≫ β.1) = pullback.snd (L.endKerStr β) t :=
  pullback.lift_snd _ _ _

def c : P₁ t ξ (β := β) ⟶ L.endKer β :=
  pullback.lift (L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ))).1 (t₁ t ξ (β := β)) (by
    have h : (L.mul _ (q₁ t ξ (β := β)) (L.inv _ (x₁ t ξ))) ⊚ β = L.one _ := by
      rw [hβ, hom_inv hβ, q₁_comp]
      letI := L.pointGroup (t₁ t ξ (β := β))
      change ((x₁ t ξ (β := β)) ⊚ β) * ((x₁ t ξ (β := β)) ⊚ β)⁻¹ = 1
      exact mul_inv_cancel _
    have h' := congrArg Subtype.val h
    change (L.mul _ (q₁ t ξ (β := β)) (L.inv _ (x₁ t ξ))).1 ≫ β.1 = (L.one _).1 at h'
    rw [h', one_coe L])

@[reassoc (attr := simp)]
theorem c_fst : c L hβ t ξ ≫ L.endKerι β = (L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ))).1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem c_snd : c L hβ t ξ ≫ L.endKerStr β = t₁ t ξ (β := β) :=
  pullback.lift_snd _ _ _

def Ψ : P₁ t ξ (β := β) ⟶ P₀ L t (β := β) :=
  pullback.lift (c L hβ t ξ) (pullback.snd β.1 (ξ.1 ≫ β.1)) (by rw [c_snd])

@[reassoc (attr := simp)]
theorem Ψ_fst : Ψ L hβ t ξ ≫ pullback.fst (L.endKerStr β) t = c L hβ t ξ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Ψ_snd : Ψ L hβ t ξ ≫ pullback.snd (L.endKerStr β) t = pullback.snd β.1 (ξ.1 ≫ β.1) :=
  pullback.lift_snd _ _ _

theorem Ψ_t₀ : Ψ L hβ t ξ ≫ t₀ L t (β := β) = t₁ t ξ (β := β) := by
  rw [← Category.assoc, Ψ_snd]

theorem Ψ_pull_k₀ :
    GoodReductionJacobian.schemeHomOverComp (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (k₀ L t) =
      L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ)) := by
  apply Subtype.ext
  change Ψ L hβ t ξ ≫ (pullback.fst (L.endKerStr β) t ≫ L.endKerι β) = _
  rw [← Category.assoc, Ψ_fst, c_fst]

theorem Ψ_pull_x₀ :
    GoodReductionJacobian.schemeHomOverComp (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (x₀ L t ξ) = x₁ t ξ := by
  apply Subtype.ext
  change Ψ L hβ t ξ ≫ (pullback.snd (L.endKerStr β) t ≫ ξ.1) = pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1
  rw [← Category.assoc, Ψ_snd]

theorem Ψ_Φ : Ψ L hβ t ξ ≫ Φ L hβ t ξ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Φ_fst, Category.id_comp]
    have h := L.mul_natural _ _ (Ψ L hβ t ξ) (Ψ_t₀ L hβ t ξ) (k₀ L t) (x₀ L t ξ)
    have h' := congrArg Subtype.val h
    change Ψ L hβ t ξ ≫ (L.mul _ (k₀ L t) (x₀ L t ξ)).1 = _ at h'
    rw [h', Ψ_pull_k₀, Ψ_pull_x₀]
    letI := L.pointGroup (t₁ t ξ (β := β))
    change ((q₁ t ξ (β := β)) * (x₁ t ξ (β := β))⁻¹ * (x₁ t ξ (β := β))).1 = _
    rw [inv_mul_cancel_right]
    rfl
  · rw [Category.assoc, Φ_snd, Ψ_snd, Category.id_comp]

theorem Φ_t₁ : Φ L hβ t ξ ≫ t₁ t ξ (β := β) = t₀ L t (β := β) := by
  rw [← Category.assoc, Φ_snd]

theorem Φ_pull_q₁ :
    GoodReductionJacobian.schemeHomOverComp (Φ L hβ t ξ) (Φ_t₁ L hβ t ξ) (q₁ t ξ) =
      L.mul _ (k₀ L t) (x₀ L t ξ) := by
  apply Subtype.ext
  change Φ L hβ t ξ ≫ pullback.fst β.1 (ξ.1 ≫ β.1) = _
  rw [Φ_fst]

theorem Φ_pull_x₁ :
    GoodReductionJacobian.schemeHomOverComp (Φ L hβ t ξ) (Φ_t₁ L hβ t ξ) (x₁ t ξ) = x₀ L t ξ := by
  apply Subtype.ext
  change Φ L hβ t ξ ≫ (pullback.snd β.1 (ξ.1 ≫ β.1) ≫ ξ.1) = pullback.snd (L.endKerStr β) t ≫ ξ.1
  rw [← Category.assoc, Φ_snd]

theorem Φ_Ψ : Φ L hβ t ξ ≫ Ψ L hβ t ξ = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Ψ_fst, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, c_fst]
      have h := L.mul_natural _ _ (Φ L hβ t ξ) (Φ_t₁ L hβ t ξ) (q₁ t ξ) (L.inv _ (x₁ t ξ))
      have h' := congrArg Subtype.val h
      change Φ L hβ t ξ ≫ (L.mul _ (q₁ t ξ) (L.inv _ (x₁ t ξ))).1 = _ at h'
      rw [h', pull_inv, Φ_pull_q₁, Φ_pull_x₁]
      letI := L.pointGroup (t₀ L t (β := β))
      change ((k₀ L t (β := β)) * (x₀ L t ξ) * (x₀ L t ξ)⁻¹).1 = _
      rw [mul_inv_cancel_right]
      rfl
    · rw [Category.assoc, c_snd, Φ_t₁, pullback.condition]
  · rw [Category.assoc, Ψ_snd, Φ_snd, Category.id_comp]

theorem Φ_injective : Function.Injective (Φ L hβ t ξ) := by
  intro z z' h
  have h1 := congrArg (Ψ L hβ t ξ) h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Φ_Ψ] at h1
  exact h1

end Translate

end GroupLaw

section Main

open NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

omit [IsAlgClosed K] in

theorem exists_open_forall_finite_fibre [IsIntegral A] [IsProper f] (γ : A ⟶ A) (hγ : γ ≫ f = f)
    (hsurj : Function.Surjective γ) :
    ∃ V : A.Opens, (V : Set A).Nonempty ∧ ∀ y ∈ V, IsClosed ({y} : Set A) → (γ ⁻¹' {y}).Finite := by
  classical
  haveI : IsProper γ := by
    have : IsProper (γ ≫ f) := by rw [hγ]; infer_instance
    exact IsProper.of_comp γ f

  haveI : Nonempty A := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact (IrreducibleSpace.toNonempty (X := A)).elim fun a => h.elim a
  obtain ⟨x₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨U, hU, hx₀U, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₀) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x₀, hx₀U⟩⟩

  have hc : IsCompact ((γ ⁻¹ᵁ U : A.Opens) : Set A) :=
    QuasiCompact.isCompact_preimage (f := γ) _ U.isOpen hU.isCompact
  obtain ⟨S, hSfin, hSU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hc
  haveI : Finite S := hSfin.to_subtype
  have hWle : ∀ W : S, (W.1.1 : A.Opens) ≤ γ ⁻¹ᵁ U := by
    intro W
    rw [hSU]
    exact le_iSup₂ (f := fun (i : A.affineOpens) (_ : i ∈ S) => (i : A.Opens)) W.1 W.2
  have key : ∀ W : S, ∃ r : Γ(A, U), r ≠ 0 ∧ ∀ (y : A) (_ : y ∈ U), IsClosed ({y} : Set A) →
      y ∈ A.basicOpen r → {p : A | p ∈ (W.1.1 : A.Opens) ∧ γ p = y}.Finite := by
    intro W
    by_cases hne : ((W.1.1 : A.Opens) : Set A).Nonempty
    · obtain ⟨w, hw⟩ := hne
      haveI : Nonempty (W.1.1 : A.Opens) := ⟨⟨w, hw⟩⟩
      exact exists_forall_finite_fibre_inter f γ hγ hsurj hU W.1.2 (hWle W)
    · refine ⟨1, one_ne_zero, fun y _ _ _ => ?_⟩
      have h0 : {p : A | p ∈ (W.1.1 : A.Opens) ∧ γ p = y} = ∅ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hp
        exact absurd ⟨p, hp⟩ hne
      rw [h0]; exact Set.finite_empty
  choose r hr0 hrfin using key
  haveI : Fintype S := Fintype.ofFinite S
  let rr : Γ(A, U) := ∏ W : S, r W
  have hrr0 : rr ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hr0 W
  have hrrle : ∀ W : S, A.basicOpen rr ≤ A.basicOpen (r W) := by
    intro W
    have h : rr = r W * ∏ W' ∈ Finset.univ.erase W, r W' := by
      rw [Finset.mul_prod_erase _ _ (Finset.mem_univ W)]
    rw [h, Scheme.basicOpen_mul]
    exact inf_le_left
  refine ⟨A.basicOpen rr, ?_, ?_⟩
  · rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hrr0
    rw [← basicOpen_eq_bot_iff]
    exact Opens.ext h
  · intro y hy hyc
    have hyU : y ∈ U := A.basicOpen_le rr hy
    have hsub : γ ⁻¹' {y} ⊆ ⋃ W : S, {p : A | p ∈ (W.1.1 : A.Opens) ∧ γ p = y} := by
      intro p hp
      have hp' : γ p = y := hp
      have hpU : p ∈ (γ ⁻¹ᵁ U : A.Opens) := by
        change γ p ∈ U; rw [hp']; exact hyU
      rw [hSU] at hpU
      obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hpU
      obtain ⟨hWS, hpW⟩ := Opens.mem_iSup.mp hW
      exact Set.mem_iUnion.mpr ⟨⟨W, hWS⟩, hpW, hp'⟩
    exact (Set.finite_iUnion fun W => hrfin W y hyU hyc (hrrle W hy)).subset hsub

theorem isFinite_endKerStr (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    {γ : SchemeHomOver f f} (hγ : IsHom L γ) (hsurj : Function.Surjective γ.1) :
    IsFinite (L.endKerStr γ) := by
  classical
  haveI : IsProper f := hA.proper
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IsProper γ.1 := by
    have : IsProper (γ.1 ≫ f) := by rw [γ.2]; infer_instance
    exact IsProper.of_comp γ.1 f

  obtain ⟨V, hVne, hVfin⟩ := exists_open_forall_finite_fibre (f := f) γ.1 γ.2 hsurj

  have hVne' : ((γ.1 ⁻¹ᵁ V : A.Opens) : Set A).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨w, rfl⟩ := hsurj v
    exact ⟨w, hv⟩
  obtain ⟨a, haf, haV⟩ := exists_section_mem f (γ.1 ⁻¹ᵁ V) hVne'
  let pt : Spec (CommRingCat.of K) := default
  let y : A := γ.1 (a pt)
  have hyV : y ∈ V := haV pt

  haveI hci : IsClosedImmersion (a ≫ γ.1) := by
    have : IsClosedImmersion ((a ≫ γ.1) ≫ f) := by
      rw [Category.assoc, γ.2, haf]; infer_instance
    exact IsClosedImmersion.of_comp (a ≫ γ.1) f
  have hrange : Set.range (a ≫ γ.1) = {y} := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      rw [Subsingleton.elim s pt, Scheme.Hom.comp_apply]; rfl
    · rintro rfl
      exact ⟨pt, by rw [Scheme.Hom.comp_apply]⟩
  have hyc : IsClosed ({y} : Set A) := by
    rw [← hrange]
    exact (a ≫ γ.1).isClosedEmbedding.isClosed_range
  have hfin : (γ.1 ⁻¹' {y}).Finite := hVfin y hyV hyc

  let ξ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f := ⟨a, by rw [haf]⟩
  haveI : Finite (P₁ (𝟙 _) ξ (β := γ)) := by
    have hinj : Function.Injective (pullback.fst γ.1 (ξ.1 ≫ γ.1)) :=
      (pullback.fst γ.1 (ξ.1 ≫ γ.1)).isClosedEmbedding.injective
    have hsub : Set.range (pullback.fst γ.1 (ξ.1 ≫ γ.1)) ⊆ γ.1 ⁻¹' {y} := by
      rintro _ ⟨z, rfl⟩
      change γ.1 (pullback.fst γ.1 (ξ.1 ≫ γ.1) z) = y
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
        Subsingleton.elim (pullback.snd γ.1 (ξ.1 ≫ γ.1) z) pt]
      rfl
    haveI : Finite (Set.range (pullback.fst γ.1 (ξ.1 ≫ γ.1))) := (hfin.subset hsub).to_subtype
    exact Finite.of_injective_finite_range hinj

  haveI : Finite (P₀ L (𝟙 _) (β := γ)) := Finite.of_injective _ (Φ_injective L hγ (𝟙 _) ξ)
  haveI : Finite (L.endKer γ) := by
    refine Finite.of_surjective (pullback.fst (L.endKerStr γ) (𝟙 (Spec (CommRingCat.of K)))) ?_
    intro z
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := L.endKerStr γ)
      (g := 𝟙 (Spec (CommRingCat.of K))) z ((L.endKerStr γ) z) (by rfl)
    exact ⟨w, hw⟩

  haveI : LocallyOfFiniteType γ.1 := inferInstance
  haveI : IsProper (L.endKerStr γ) :=
    MorphismProperty.pullback_snd (P := @IsProper) γ.1 _ inferInstance
  haveI : LocallyOfFiniteType (L.endKerStr γ) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) γ.1 _ inferInstance
  haveI : LocallyQuasiFinite (L.endKerStr γ) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Main

end P2mSurjIsog

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    [Surjective γ.1] :
    IsFinite (L.endKerStr γ) :=
  P2mSurjIsog.isFinite_endKerStr L hA (fun t x y => hγ t x y) γ.1.surjective

end

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective (solution)
