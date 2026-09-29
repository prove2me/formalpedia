-- Prove2me | solution 1 for ModularCurve.XOneP.mem_minimalPrimes_span_of_iotaFin_eq_fst_genericPoint_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/17c5e081-d66d-5756-88f9-6185b6e89028

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_mem_minimalPrimes_span_of_iotaFin_eq_fst_genericPoint_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k] (hϖk : algebraMap A k ϖ = 0)
    (Z : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) (hZ : Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j))
    (hy : (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base hZ.1.genericPoint) :
    y.asIdeal ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes := by
  classical

  let X := ModularCurve.TwoChartModel A (↥K) j
  let f : X ⟶ Spec (CommRingCat.of A) := ModularCurve.TwoChart.modelTo A (↥K) j
  let ι := ModularCurve.TwoChart.ιFin A (↥K) j
  let B : Type := ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)
  let gk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := specMap A k
  let pr := pullback.fst f gk
  let η := hZ.1.genericPoint
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hη : IsGenericPoint η Z := hZ.1.isGenericPoint_genericPoint hZc

  have hfι : ∀ y' : ↥(ModularCurve.TwoChart.XFin A (↥K) j), (f.base (ι.base y')).asIdeal = Ideal.comap (algebraMap A B) y'.asIdeal := by
    intro y'
    show ((ι ≫ f).base y').asIdeal = _
    rw [ModularCurve.TwoChart.ιFin_modelTo, Spec.map_base]
    rfl

  have hover : ∀ ξ : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), ϖ ∈ (f.base (pr.base ξ)).asIdeal := by
    intro ξ
    have h1 : f.base (pr.base ξ) = gk.base ((pullback.snd f gk).base ξ) := by
      show (pullback.fst f gk ≫ f).base ξ = (pullback.snd f gk ≫ gk).base ξ
      rw [pullback.condition]
    rw [h1]
    show ϖ ∈ ((Spec.map (CommRingCat.ofHom (algebraMap A k))).base _).asIdeal
    rw [Spec.map_base]
    show ϖ ∈ Ideal.comap (algebraMap A k) _
    rw [Ideal.mem_comap, hϖk]
    exact Ideal.zero_mem _

  have hϖy : algebraMap A B ϖ ∈ y.asIdeal := by
    have h := hover η
    rw [← hy] at h
    change ϖ ∈ (f.base (ι.base y)).asIdeal at h
    rw [hfι] at h
    exact Ideal.mem_comap.mp h
  refine ⟨⟨y.isPrime, ?_⟩, ?_⟩
  · rw [Ideal.span_singleton_le_iff_mem]; exact hϖy

  rintro 𝔓 ⟨h𝔓, hϖ𝔓⟩ h𝔓y

  let κ : Type := IsLocalRing.ResidueField A
  let mk : A →+* κ := IsLocalRing.residue A
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hϖk, zero_mul]
  let ℓ : κ →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k) hkill
  letI : Algebra κ k := ℓ.toAlgebra
  have hℓ : (algebraMap κ k).comp mk = algebraMap A k := by
    ext a; exact Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) (algebraMap A k) hkill
  let gκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom mk)
  let gℓ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of κ) := Spec.map (CommRingCat.ofHom (algebraMap κ k))
  have hfac : gk = gℓ ≫ gκ := by
    show Spec.map (CommRingCat.ofHom (algebraMap A k)) = _
    rw [← Spec.map_comp]
    show _ = Spec.map (CommRingCat.ofHom ((algebraMap κ k).comp mk))
    rw [hℓ]
  haveI : IsClosedImmersion gκ := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let jκ := pullback.fst f gκ
  let qκ := pullback.snd f gκ
  haveI : IsClosedImmersion jκ := inferInstance
  let fst' := pullback.fst qκ gℓ
  haveI : Flat fst' := inferInstance
  have hgen : GeneralizingMap fst'.base := Flat.generalizingMap fst'
  let E : pullback qκ gℓ ≅ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) :=
    pullbackLeftPullbackSndIso f gκ gℓ ≪≫ pullback.congrHom rfl hfac.symm
  have hE : E.hom ≫ pr = fst' ≫ jκ := by
    show (pullbackLeftPullbackSndIso f gκ gℓ ≪≫ pullback.congrHom rfl hfac.symm).hom ≫ pullback.fst f gk = _
    rw [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst]
  have hE' : ∀ ξ, pr.base (E.hom.base ξ) = jκ.base (fst'.base ξ) := fun ξ => by
    show (E.hom ≫ pr).base ξ = (fst' ≫ jκ).base ξ
    rw [hE]

  let y₀ : ↥(ModularCurve.TwoChart.XFin A (↥K) j) := ⟨𝔓, h𝔓⟩
  have hsp : ι.base y₀ ⤳ ι.base y :=
    ((PrimeSpectrum.le_iff_specializes y₀ y).mp h𝔓y).map ι.base.hom.continuous

  have hrange : ∀ x : ↥X, ϖ ∈ (f.base x).asIdeal → x ∈ Set.range jκ.base := by
    intro x hx
    rw [Scheme.Pullback.range_fst]
    show f.base x ∈ Set.range gκ.base
    refine ⟨IsLocalRing.closedPoint κ, ?_⟩
    apply PrimeSpectrum.ext
    have hmax : (f.base x).asIdeal = IsLocalRing.maximalIdeal A := by
      refine ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (f.base x).isPrime.ne_top ?_).symm
      rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hx
    rw [hmax]
    show ((Spec.map (CommRingCat.ofHom mk)).base (IsLocalRing.closedPoint κ)).asIdeal = _
    rw [Spec.map_base]
    show Ideal.comap mk (IsLocalRing.maximalIdeal κ) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact IsLocalRing.ker_residue
  obtain ⟨xκ', hxκ'⟩ := hrange (ι.base y₀) (by
    rw [hfι]; exact Ideal.mem_comap.mpr (by
      show algebraMap A B ϖ ∈ 𝔓
      exact hϖ𝔓 (Ideal.subset_span (Set.mem_singleton _))))

  let ηt := E.inv.base η
  have hηE : E.hom.base ηt = η := by
    show (E.inv ≫ E.hom).base η = η
    rw [E.inv_hom_id]; rfl
  have hprη : pr.base η = jκ.base (fst'.base ηt) := by rw [← hE', hηE]

  have hspκ : xκ' ⤳ fst'.base ηt := by
    rw [← jκ.isClosedEmbedding.isInducing.specializes_iff, hxκ', ← hprη, ← hy]
    exact hsp

  obtain ⟨ηu, hηu, hfst'⟩ := hgen hspκ
  let η' := E.hom.base ηu
  have hη'sp : η' ⤳ η := by
    rw [← hηE]; exact hηu.map E.hom.base.hom.continuous

  have hη'eq : η' = η := by
    have hcl : closure ({η} : Set _) ⊆ closure {η'} := specializes_iff_closure_subset.mp hη'sp
    rw [hη.def] at hcl
    have hirr : IsIrreducible (closure ({η'} : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))) :=
      isIrreducible_singleton.closure
    have hle := hZ.2 hirr hcl
    have hgen' : IsGenericPoint η' Z := le_antisymm hle hcl
    exact hgen'.eq hη

  have hιeq : ι.base y₀ = ι.base y := by
    rw [hy]
    show ι.base y₀ = pr.base η
    rw [← hη'eq]
    show ι.base y₀ = pr.base (E.hom.base ηu)
    rw [hE', hfst', hxκ']
  have hy₀ : y₀ = y := ι.isOpenEmbedding.toIsEmbedding.injective hιeq
  have : 𝔓 = y.asIdeal := congrArg PrimeSpectrum.asIdeal hy₀
  exact this ▸ le_rfl

end S_ModularCurve_XOneP_mem_minimalPrimes_span_of_iotaFin_eq_fst_genericPoint_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_mem_minimalPrimes_span_of_iotaFin_eq_fst_genericPoint_specialFibre_twoChartModel_x1_mul (solution)
