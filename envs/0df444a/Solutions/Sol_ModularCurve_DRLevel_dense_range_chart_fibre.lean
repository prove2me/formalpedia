-- Prove2me | solution 1 for ModularCurve.DRLevel.dense_range_chart_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/07de14c8-f4e1-55a8-8c42-3a56b728529f

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRLevel_not_isOpen_singleton_fibre
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_dense_range_chart_fibre
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_dense_range_chart_fibre.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_dense_range_chart_fibre.ModularCurve.DRLevel"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRLevel.fibre IgusaScheme.mem_chartAlg_iff IgusaScheme.subset_chartAlg IgusaScheme.chartAlgFin IgusaScheme.chartAlgInf IgusaScheme.chartAlgMid IgusaScheme.jInvChartInf IgusaScheme.inclInf IgusaScheme.isLocalization_away_inclInf IgusaScheme.XFin IgusaScheme.XInf IgusaScheme.XMid IgusaScheme.fFin IgusaScheme.fInf IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf IgusaScheme.glue_condition IgusaScheme.ιFin_igusaTo IgusaScheme.ιInf_igusaTo IgusaScheme.mem_range_ιFin_or_mem_range_ιInf DRLevel.not_isOpen_singleton_fibre IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase fibre not_isOpen_singleton_fibre"
namespace E6_densechart
p2m_open "ModularCurve.DRLevel ModularCurve"

private theorem range_chart_eq
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type) [CommRing κ] [Algebra R κ]
    (c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A)))) :
    Set.range c.base = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ⁻¹' Set.range ι.base := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]
    exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

private theorem exists_chart
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type) [CommRing κ] [Algebra R κ] :
    ∃ c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]
    exact sq.w.symm
  exact ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

set_option maxHeartbeats 16000000 in
private theorem finite_setOf_tmul_mem
    {R : Type} [CommRing R] {F : Type} [Field F] [Algebra R F] (S : Subalgebra R F) (s : F) (hs : s ∈ S)
    (hint : ∀ x : ↥S, IsIntegral ↥(Algebra.adjoin R ({s} : Set F)) (x : F))
    (κ : Type) [Field κ] [Algebra R κ] [Algebra.FiniteType κ (κ ⊗[R] ↥S)] :
    {z : PrimeSpectrum (κ ⊗[R] ↥S) | ((1 : κ) ⊗ₜ[R] (⟨s, hs⟩ : ↥S)) ∈ z.asIdeal}.Finite := by
  classical
  set t : κ ⊗[R] ↥S := (1 : κ) ⊗ₜ[R] (⟨s, hs⟩ : ↥S) with ht
  set I : Ideal (κ ⊗[R] ↥S) := Ideal.span {t} with hI
  set A := Algebra.adjoin R ({s} : Set F) with hA
  have hAS : A ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.2 hs)

  let θ : ↥A →+* (κ ⊗[R] ↥S) ⧸ I :=
    (Ideal.Quotient.mk I).comp ((Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥S)).toRingHom.comp
      (Subalgebra.inclusion hAS).toRingHom)
  have hθ : ∀ a : ↥A, θ a ∈ Set.range (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) : κ →+* (κ ⊗[R] ↥S) ⧸ I) := by
    intro a
    obtain ⟨a, ha⟩ := a
    refine Algebra.adjoin_induction (hx := ha) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      show Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] (Subalgebra.inclusion hAS ⟨x, Algebra.subset_adjoin hx⟩)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]
      apply Ideal.subset_span
      rw [Set.mem_singleton_iff, ht]
      congr 1
      exact Subtype.ext hx
    · intro r
      refine ⟨algebraMap R κ r, ?_⟩
      show algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) (algebraMap R κ r) =
        Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight (Subalgebra.inclusion hAS (algebraMap R (↥A) r)))
      rw [AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rintro x y hx hy ⟨cx, hcx⟩ ⟨cy, hcy⟩
      refine ⟨cx + cy, ?_⟩
      rw [map_add, hcx, hcy, ← map_add]
      rfl
    · rintro x y hx hy ⟨cx, hcx⟩ ⟨cy, hcy⟩
      refine ⟨cx * cy, ?_⟩
      rw [map_mul, hcx, hcy, ← map_mul]
      rfl

  letI : Algebra ↥A ↥S := (Subalgebra.inclusion hAS).toRingHom.toAlgebra
  haveI : IsScalarTower ↥A ↥S F := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hgen : ∀ x : ↥S, Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x) ∈ integralClosure κ ((κ ⊗[R] ↥S) ⧸ I) := by
    intro x
    rw [mem_integralClosure_iff]
    rcases subsingleton_or_nontrivial ((κ ⊗[R] ↥S) ⧸ I) with hBI | hBI
    · rw [Subsingleton.elim (Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x)) 0]; exact isIntegral_zero
    have hx : IsIntegral ↥A x :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥A ↥S F) Subtype.val_injective).1 (hint x)
    obtain ⟨p, hpm, hpx⟩ := hx

    have hroot : (p.map θ).eval (Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x)) = 0 := by
      rw [Polynomial.eval_map]
      have : (Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥S)).toRingHom
          (Polynomial.eval₂ (algebraMap ↥A ↥S) x p) = 0 := by
        rw [hpx, map_zero]
      rw [Polynomial.hom_eval₂] at this
      exact this

    have hlifts : p.map θ ∈ Polynomial.lifts (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hθ _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hpm.map θ)
    refine ⟨q, hqm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hq]
    exact hroot

  have htop : integralClosure κ ((κ ⊗[R] ↥S) ⧸ I) = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction b using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subalgebra.zero_mem _
    | tmul a x =>
        have h1 : a ⊗ₜ[R] x = (a ⊗ₜ[R] (1 : ↥S)) * ((1 : κ) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have h2 : Ideal.Quotient.mk I (a ⊗ₜ[R] (1 : ↥S)) = (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) : κ →+* (κ ⊗[R] ↥S) ⧸ I) a := by
          rw [← Ideal.Quotient.mk_algebraMap]
          rfl
        rw [h1, map_mul, h2]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (hgen x)
    | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ (hu trivial) (hv trivial)
  haveI hintQ : Algebra.IsIntegral κ ((κ ⊗[R] ↥S) ⧸ I) := integralClosure_eq_top_iff.1 htop

  haveI : Ring.KrullDimLE 0 ((κ ⊗[R] ↥S) ⧸ I) := Ring.KrullDimLE.mk₀ fun P hP => by
    haveI := hP
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := κ) (S := (κ ⊗[R] ↥S) ⧸ I) P ?_
    rw [Ideal.eq_bot_of_prime (Ideal.comap (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I)) P)]
    exact Ideal.bot_isMaximal
  haveI : IsNoetherianRing (κ ⊗[R] ↥S) := Algebra.FiniteType.isNoetherianRing κ _
  haveI : IsNoetherianRing ((κ ⊗[R] ↥S) ⧸ I) := inferInstance
  haveI : IsArtinianRing ((κ ⊗[R] ↥S) ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := (κ ⊗[R] ↥S) ⧸ I)
  haveI : Finite {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime} :=
    (IsArtinianRing.setOf_isPrime_finite ((κ ⊗[R] ↥S) ⧸ I)).to_subtype

  have hIle : ∀ z : PrimeSpectrum (κ ⊗[R] ↥S), t ∈ z.asIdeal → RingHom.ker (Ideal.Quotient.mk I) ≤ z.asIdeal := by
    intro z hz
    rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hz
  refine Set.finite_coe_iff.1 (Finite.of_injective
    (fun z : {z : PrimeSpectrum (κ ⊗[R] ↥S) | t ∈ z.asIdeal} =>
      (⟨z.1.asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hIle z.1 z.2)⟩ :
        {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime})) ?_)
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
  have h' : (z.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) =
      (z'.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) :=
    congrArg (fun J : {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime} => J.1.comap (Ideal.Quotient.mk I)) h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.2 (hIle z hz), sup_eq_left.2 (hIle z' hz')] at h'
  exact Subtype.ext (PrimeSpectrum.ext h')

private theorem ig_ιFin_eq_ιInf_iff (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (x₀ : IgusaScheme.XFin N ℓ) (xi : IgusaScheme.XInf N ℓ) :
    (IgusaScheme.ιFin N ℓ).base x₀ = (IgusaScheme.ιInf N ℓ).base xi ↔
      ∃ w : IgusaScheme.XMid N ℓ, (IgusaScheme.fFin N ℓ).base w = x₀ ∧ (IgusaScheme.fInf N ℓ).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (IgusaScheme.fFin N ℓ) (IgusaScheme.fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (IgusaScheme.fFin N ℓ ≫ IgusaScheme.ιFin N ℓ).base w = (IgusaScheme.fInf N ℓ ≫ IgusaScheme.ιInf N ℓ).base w
    rw [IgusaScheme.glue_condition]

private theorem ig_range_fInf (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (IgusaScheme.fInf N ℓ).base =
      ((PrimeSpectrum.basicOpen (IgusaScheme.jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(IgusaScheme.chartAlgInf N ℓ))) :
          Set (PrimeSpectrum ↥(IgusaScheme.chartAlgInf N ℓ))) := by
  letI := (IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := IgusaScheme.isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(IgusaScheme.chartAlgMid N ℓ) (IgusaScheme.jInvChartInf N ℓ)

private theorem ig_ιInf_mem_range_ιFin_iff (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (xi : IgusaScheme.XInf N ℓ) :
    (IgusaScheme.ιInf N ℓ).base xi ∈ Set.range (IgusaScheme.ιFin N ℓ).base ↔
      IgusaScheme.jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(IgusaScheme.fFin N ℓ).base w, (ig_ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨w, rfl, rfl⟩⟩

end ModularCurve.DRLevel.E6_densechart

open ModularCurve.DRLevel.E6_densechart in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (κ : Type) [Field κ] [CharP κ q] [Algebra (DRLevel.R q) κ]
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))))) :
    Dense (Set.range c.base) := by
  classical

  haveI : Algebra.FiniteType (DRLevel.R q) ↥(IgusaScheme.chartAlgInf (N₀ * q) q) :=
    (ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N₀ * q) q).2
  haveI : Algebra.FiniteType κ (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) := inferInstance

  obtain ⟨c', hc'fst, hc'snd⟩ := exists_chart (DRLevel.toBase N₀ q) ↥(IgusaScheme.chartAlgInf (N₀ * q) q)
    (IgusaScheme.ιInf (N₀ * q) q) (IgusaScheme.ιInf_igusaTo (N₀ * q) q) κ
  have hrange := range_chart_eq (DRLevel.toBase N₀ q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
    (IgusaScheme.ιFin (N₀ * q) q) (IgusaScheme.ιFin_igusaTo (N₀ * q) q) κ c hcfst hcsnd
  have hrange' := range_chart_eq (DRLevel.toBase N₀ q) ↥(IgusaScheme.chartAlgInf (N₀ * q) q)
    (IgusaScheme.ιInf (N₀ * q) q) (IgusaScheme.ιInf_igusaTo (N₀ * q) q) κ c' hc'fst hc'snd

  have hfin := finite_setOf_tmul_mem (IgusaScheme.chartAlgInf (N₀ * q) q) ((jFull (N₀ * q))⁻¹)
    (IgusaScheme.subset_chartAlg (N₀ * q) q _ rfl) (fun x => (IgusaScheme.mem_chartAlg_iff (N₀ * q) q).1 x.2) κ

  have hcompl : (Set.range c.base)ᶜ ⊆ c'.base ''
      {z | ((1 : κ) ⊗ₜ[DRLevel.R q] (⟨(jFull (N₀ * q))⁻¹, IgusaScheme.subset_chartAlg (N₀ * q) q _ rfl⟩ :
        ↥(IgusaScheme.chartAlgInf (N₀ * q) q))) ∈ z.asIdeal} := by
    intro w hw
    rw [Set.mem_compl_iff, hrange, Set.mem_preimage] at hw
    rcases IgusaScheme.mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q
        ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base w)
      with hfin' | hinf
    · exact absurd hfin' hw
    · have hw' : w ∈ Set.range c'.base := by rw [hrange']; exact hinf
      obtain ⟨z, rfl⟩ := hw'
      refine ⟨z, ?_, rfl⟩

      have hz : (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))).base
          (c'.base z) = (IgusaScheme.ιInf (N₀ * q) q).base
            ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := DRLevel.R q) (A := κ)
              (B := ↥(IgusaScheme.chartAlgInf (N₀ * q) q))).toRingHom)).base z) := by
        rw [← Scheme.Hom.comp_apply, hc'fst, Scheme.Hom.comp_apply]
      rw [hz, ig_ιInf_mem_range_ιFin_iff, not_not] at hw
      exact hw
  have hfinc : (Set.range c.base)ᶜ.Finite := (hfin.image c'.base).subset hcompl

  rw [dense_iff_inter_open]
  intro U hU hUne
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hUsub : U ⊆ (Set.range c.base)ᶜ := fun u hu hu' => by
    have : u ∈ U ∩ Set.range c.base := ⟨hu, hu'⟩
    rw [hempty] at this
    exact this
  obtain ⟨x, -, hx⟩ := exists_isOpen_singleton_of_isOpen_finite (hfinc.subset hUsub) hUne hU
  exact ModularCurve.DRLevel.not_isOpen_singleton_fibre N₀ q κ (algebraMap (DRLevel.R q) κ) x hx

#print axioms solution

end S_ModularCurve_DRLevel_dense_range_chart_fibre
end P2MW
export P2MW.S_ModularCurve_DRLevel_dense_range_chart_fibre (solution)
