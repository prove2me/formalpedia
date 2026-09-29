-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f073f686-0219-5e48-bcd2-4450e4f98e40

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
import Theorems.Thm_ModularCurve_exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
import Theorems.Thm_ModularCurve_heckeBetaBar_coeffEmb
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

open ModularCurve.PlaceSpecialization.ProlongationTuple

section

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

omit [IsAlgClosed k] [DecidableEq k] in

private theorem aux_of_frob_frob_eq
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c))
      = P.reduceSnd c) :
    P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) := by
  rcases P.d1 c with h | h
  · have h' : P.reduceFst c = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c) := h
    rw [h']
    exact hfix.symm
  · exact (show frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) = P.reduceSnd c from h).symm

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in

private theorem aux_liesOverPrime (red : A →+* k) : A.LiesOverPrime q := by
  have hmem : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := hu.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h
    exact not_isUnit_zero h
  have h1 := (A.valuation_lt_one_iff (q : A)).mp hmem
  have h2 : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := map_natCast A.subtype q
  rw [h2] at h1
  show (q : AlgebraicClosure ℚ) ∈ A.nonunits
  exact h1

private noncomputable def jN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

private theorem aux_heckeAlphaBar_jN : heckeAlphaBar (AlgebraicClosure ℚ) N q (jN N) = jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q (jN N))

private theorem aux_heckeBetaBar_jN : heckeBetaBar (AlgebraicClosure ℚ) N q (jN N) = jQFun N q :=
  Subtype.ext (heckeBetaBar_coeffEmb N q (modularFunctionField_le_full N (jq_mem N)))

omit [IsAlgClosed k] [DecidableEq k] in

private theorem aux_of_ord_jQFun_neg
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsInftySide P c)
    (hmoved : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c))
      ≠ P.reduceSnd c)
    (hord : c.ord (jQFun N q) < 0) :
    P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) := by
  rcases P.d1 c with hphi | hdone
  · exfalso
    have hq : q.Prime := Fact.out
    obtain ⟨v, hv⟩ : ∃ v, c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = v := ⟨_, rfl⟩

    have hmoved' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp v))
        ≠ P.sp v := by
      rw [← hv]; exact hmoved
    have hphi' : P.sp (c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        = frobOnPlacesGeomLevel k N data hKr (P.sp v) := by
      rw [← hv]; exact hphi
    obtain ⟨W₀, -, -, hW₀e, huniq⟩ := P.d2 v hmoved'
    have hc₀ : c = W₀ := huniq c hv hphi'
    have heβ : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) c = 1 := by
      rw [hc₀]; exact hW₀e

    have hF1 : c.ord (jQFun N q)
        = (Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) c : ℤ) * v.ord (jN N) := by
      rw [← aux_heckeBetaBar_jN, Place.ord_restrictAlong _ hβ c (jN N), hv]
    rw [heβ, Nat.cast_one, one_mul] at hF1
    have hvneg : v.ord (jN N) < 0 := by rw [← hF1]; exact hord

    have hA : A.LiesOverPrime q := aux_liesOverPrime red
    obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA
    have hσζ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ q := fun ζ hζ =>
      ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd hq A hA hσ hqN ζ hζ
    obtain ⟨W₁, -, hW₁v, -, -, -, hW₁α, -⟩ :=
      exists_pair_fiberAlong_heckeBetaBar_of_ord_neg N q hqN hα hβ σ hσζ v hvneg

    have hW₁phi : P.sp (W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        = frobOnPlacesGeomLevel k N data hKr (P.sp v) := by
      rw [hW₁α]; exact P.d6_frobenius σ hσ v
    have hc₁ : c = W₁ := hc₀.trans (huniq W₁ hW₁v hW₁phi).symm
    have hcα : c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
        = arithmeticGalois (modularFunctionFieldFull N) σ • v := by
      rw [hc₁]; exact hW₁α

    have hfixj : arithmeticGalois (modularFunctionFieldFull N) σ • jN N = jN N :=
      arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ (modularFunctionField_le_full N (jq_mem N))
    have hG : (arithmeticGalois (modularFunctionFieldFull N) σ • v).ord (jN N) = v.ord (jN N) := by
      have h := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull N) σ) v (jN N)
      rwa [hfixj] at h
    have hF2 : c.ord (jFun N q)
        = (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c : ℤ) * v.ord (jN N) := by
      rw [← aux_heckeAlphaBar_jN, Place.ord_restrictAlong _ hα c (jN N), hcα, hG]

    obtain ⟨-, τ, hτ, hval⟩ := hc
    have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have hτz : τ = 0 := Subtype.ext h0
      rw [hτz, map_zero] at hτ
      exact zero_ne_one hτ
    have ht0 : c.ord (tInfty N q) = 0 := hval.ord_eq_zero hτ0
    have htne : jQFun N q / jFun N q ^ q ≠ 0 := hval.ne_zero hτ0
    obtain ⟨hjq0, hjpow0⟩ := div_ne_zero_iff.mp htne
    have hchart : c.ord (jQFun N q) = (q : ℤ) * c.ord (jFun N q) := by
      have h : c.ord (jQFun N q / jFun N q ^ q) = 0 := ht0
      rw [div_eq_mul_inv, c.ord_mul hjq0 (inv_ne_zero hjpow0), c.ord_inv, ← zpow_natCast,
        c.ord_zpow] at h
      linarith

    have hkey : (1 : ℤ) * v.ord (jN N)
        = ((q : ℤ) * (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c : ℤ))
          * v.ord (jN N) := by
      rw [one_mul, mul_assoc, ← hF2, ← hchart, hF1]
    have h1 : (q : ℤ) * (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c : ℤ)
        = 1 := (mul_right_cancel₀ hvneg.ne hkey).symm
    have h1' : q * Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) c = 1 := by
      exact_mod_cast h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp ⟨_, h1'.symm⟩)
  · exact (show frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) = P.reduceSnd c from hdone).symm

end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∀ c, IsInftySide P c → P.reduceSnd c = frobOnPlacesGeomLevel k N data hKr (P.reduceFst c) := by
  intro c hc
  by_cases hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd c))
      = P.reduceSnd c
  · exact aux_of_frob_frob_eq P c hfix
  · by_cases hord : 0 ≤ c.ord (jQFun N q)
    · exact ProlongationTuple.reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide_of_ne_of_ord_jQFun_nonneg
        P hqN c hc hfix hord
    · exact aux_of_ord_jQFun_neg P hqN c hc hfix (not_le.mp hord)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceSnd_eq_frobOnPlacesGeomLevel_reduceFst_of_isInftySide (solution)
