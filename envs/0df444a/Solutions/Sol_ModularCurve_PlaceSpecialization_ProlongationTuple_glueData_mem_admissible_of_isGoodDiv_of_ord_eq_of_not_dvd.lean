-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a9fb57b2-f596-5987-a1b8-dd24735bff27

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence nodePairsOfPlaces IsAffineGeomPlace arithFrobC hasPrincipalDivisors_modularFunctionFieldC_of_perfectField isAffineGeomPlace_frobOnPlacesGeomLevel"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace isStrictFst_or_isStrictSnd_iff"
namespace Bideg
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem mapDomain_apply_eq_zero {α β M : Type*} [AddCommMonoid M] (g : α → β) (X : α →₀ M) (b : β)
    (h : ∀ a ∈ X.support, g a ≠ b) : Finsupp.mapDomain g X b = 0 := by
  classical
  by_contra hne
  have hb : b ∈ (Finsupp.mapDomain g X).support := Finsupp.mem_support_iff.mpr hne
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hb)
  exact h a ha rfl

theorem reduceSnd_not_fixed (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : P.IsStrictFst W ∨ P.IsStrictSnd W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W)) ≠ P.reduceSnd W := by
  rcases h with ⟨h1, h2⟩ | ⟨-, h2⟩
  · intro hfix
    apply h2
    apply frobOnPlacesGeomLevel_injective k N data hKr
    rw [h1]
    exact hfix
  · exact h2

theorem reduceFst_not_fixed (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : P.IsStrictFst W ∨ P.IsStrictSnd W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst W)) ≠ P.reduceFst W :=
  (P.isStrictFst_or_isStrictSnd_iff W).mp h

end ModularCurve.PlaceSpecialization.Bideg

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : P.ProlongationTuple) (hR : R.IsModel) (hNR : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (hW : ∀ s ∈ nodePairsOfPlaces (arithFrobC q k N) W,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.1) = s.1 ∧
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr s.2) = s.2)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hr₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ V, D V = V.ord f)
    (hgood : P.IsGoodDiv D) :
    P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) D ∈
      GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by
  classical

  have hinj := frobOnPlacesGeomLevel_injective k N data hKr

  have hne₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := fun h => hr₁ (by rw [ProlongationTuple.residue₁_apply, h, map_zero])
  have hne₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := fun h => hr₂ (by rw [ProlongationTuple.residue₂_apply, h, map_zero])

  have hsf : ∀ V ∈ D.support,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) ≠ P.reduceFst V :=
    fun V hV => Bideg.reduceFst_not_fixed P V (hgood V hV)
  have hss : ∀ V ∈ D.support,
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V)) ≠ P.reduceSnd V :=
    fun V hV => Bideg.reduceSnd_not_fixed P V (hgood V hV)

  have hprem : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V = v → 0 ≤ V.ord f := by
    intro v hv V hV
    have : D V = 0 := by
      by_contra hDV
      exact hsf V (Finsupp.mem_support_iff.mpr hDV) (hV ▸ hv)
    rw [← hD V, this]

  have hDfix : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      Finsupp.mapDomain P.reduceFst D v = 0 := by
    intro v hv
    exact Bideg.mapDomain_apply_eq_zero _ _ _ fun V hV hVv => hsf V hV (hVv ▸ hv)

  have haff₁ : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v → IsAffineGeomPlace k N v →
      v.ord (R.residue₁ ⟨f, h₁⟩) = 0 ∧
        (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩) = 0 := by
    intro v hv haff
    have hsum := hO f h₁ h₂ hne₁ hne₂ D hD v hv haff
    rw [hDfix v hv] at hsum
    obtain ⟨hr1, hr2⟩ := hNR.1 f h₁ h₂ v hv haff (hprem v hv)
    have := hr1 hr₁
    have := hr2 hr₂
    omega
  have haff₂ : ∀ u : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) = u → IsAffineGeomPlace k N u →
      u.ord (R.residue₂ ⟨f, h₂⟩) = 0 := by
    intro u hu haff

    have hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr u)) = frobOnPlacesGeomLevel k N data hKr u := by rw [hu]
    have h := (haff₁ _ hv (isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr u haff)).2
    rwa [hu] at h

  have hcusp₁ : ∀ v : Place k (modularFunctionFieldC k N), ¬ IsAffineGeomPlace k N v →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v.ord (R.residue₁ ⟨f, h₁⟩) = 0 := by
    intro v hv hvfix
    obtain ⟨⟨C, hC, hCv⟩, -⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v hv
    have h := hR.2.2.1 f h₁ h₂ hne₁ hne₂ D hD C hC
    rw [hCv] at h
    rw [← h]
    apply Bideg.mapDomain_apply_eq_zero
    intro V hV hVv
    have hV' : V ∈ D.support := by
      rw [Finsupp.support_filter] at hV
      exact (Finset.mem_filter.mp hV).1
    exact hsf V hV' (hVv ▸ hvfix)
  have hcusp₂ : ∀ v : Place k (modularFunctionFieldC k N), ¬ IsAffineGeomPlace k N v →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v.ord (R.residue₂ ⟨f, h₂⟩) = 0 := by
    intro v hv hvfix
    obtain ⟨-, ⟨C, hC, hCv⟩⟩ :=
      exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v hv
    have h := hR.2.2.2 f h₁ h₂ hne₁ hne₂ D hD C hC
    rw [hCv] at h
    rw [← h]
    apply Bideg.mapDomain_apply_eq_zero
    intro V hV hVv
    have hV' : V ∈ D.support := by
      rw [Finsupp.support_filter] at hV
      exact (Finset.mem_filter.mp hV).1
    exact hss V hV' (hVv ▸ hvfix)

  have hfix₁ : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v.ord (R.residue₁ ⟨f, h₁⟩) = 0 := fun v hv => by
    by_cases haff : IsAffineGeomPlace k N v
    · exact (haff₁ v hv haff).1
    · exact hcusp₁ v haff hv
  have hfix₂ : ∀ v : Place k (modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v.ord (R.residue₂ ⟨f, h₂⟩) = 0 := fun v hv => by
    by_cases haff : IsAffineGeomPlace k N v
    · exact haff₂ v hv haff
    · exact hcusp₂ v haff hv

  obtain ⟨G₁, hG₁, hdeg₁⟩ := (hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N).exists_divisor
    (R.residue₁ ⟨f, h₁⟩) hr₁
  obtain ⟨G₂, hG₂, hdeg₂⟩ := (hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N).exists_divisor
    (R.residue₂ ⟨f, h₂⟩) hr₂

  have hE₁ : Finsupp.mapDomain P.reduceFst (P.fstDiv D) = G₁ := by
    ext v
    by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
    · rw [hG₁ v, hfix₁ v hv]
      apply Bideg.mapDomain_apply_eq_zero
      intro V hV hVv
      have hV' : P.IsStrictFst V := by
        unfold fstDiv at hV
        rw [Finsupp.support_filter] at hV
        exact (Finset.mem_filter.mp hV).2
      exact hV'.2 (hVv ▸ hv)
    · rw [hG₁ v]
      have h := hR.1 f h₁ h₂ hne₁ hne₂ D hD v hv
      unfold fstDiv
      convert h using 2
  have hE₂ : Finsupp.mapDomain P.reduceSnd (P.sndDiv D) = G₂ := by
    ext v
    by_cases hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
    · rw [hG₂ v, hfix₂ v hv]
      apply Bideg.mapDomain_apply_eq_zero
      intro V hV hVv
      have hV' : P.IsStrictSnd V := by
        unfold sndDiv at hV
        rw [Finsupp.support_filter] at hV
        exact (Finset.mem_filter.mp hV).2
      exact hV'.2 (hVv ▸ hv)
    · rw [hG₂ v]
      have h := hR.2.1 f h₁ h₂ hne₁ hne₂ D hD v hv
      unfold sndDiv
      convert h using 2

  rw [GluingData.mem_admissible]
  refine ⟨?_, ?_, ?_⟩
  · show Finsupp.mapDomain P.reduceFst (P.fstDiv D) ∈ _
    rw [hE₁, Divisor.mem_degZero, hdeg₁]
  · show Finsupp.mapDomain P.reduceSnd (P.sndDiv D) ∈ _
    rw [hE₂, Divisor.mem_degZero, hdeg₂]
  · intro s hs
    constructor
    · show Finsupp.mapDomain P.reduceFst (P.fstDiv D) s.1 = 0
      rw [hE₁, hG₁, hfix₁ _ (hW s hs).1]
    · show Finsupp.mapDomain P.reduceSnd (P.sndDiv D) s.2 = 0
      rw [hE₂, hG₂, hfix₂ _ (hW s hs).2]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd (solution)
