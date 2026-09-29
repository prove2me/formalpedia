-- Prove2me | solution 1 for ModularCurve.JZero.naiveHeight_reduce
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/12c96a43-c0e5-566f-83b2-796d9d9d6825

import Definitions.Def_ModularCurve_AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PrincipalIdealDomain
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_sum_fiberOver
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspInftyBar
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Theorems.Thm_ModularCurve_JZero_exists_galoisStable_rep
import Theorems.Thm_Height_logHeight_coeff_factor_le
import Theorems.Thm_ModularCurve_symVec_mem_of_stable
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_rational_presentation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_height_system_modularFunctionFieldBar
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_naiveHeight_reduce
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 640000

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve"

section mwRED_aux1_helpers

open Polynomial IsDedekindDomain

private theorem mwRED_logHeight_coeff_mul_le (K : Type*) [Field K] [NumberField K] (n m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ p q : Polynomial K, p.natDegree ≤ n → q.natDegree ≤ m →
      Height.logHeight (fun k : Fin (n + m + 1) => (p * q).coeff k)
        ≤ Height.logHeight (fun k : Fin (n + 1) => p.coeff k)
          + Height.logHeight (fun k : Fin (m + 1) => q.coeff k) + c := by
  classical

  let A : Fin (n + m + 1) × (Fin (n + 1) × Fin (m + 1)) → K :=
    fun ka => if (ka.2.1 : ℕ) + ka.2.2 = ka.1 then 1 else 0
  refine ⟨Height.totalWeight K * Real.log (Nat.card (Fin (n + 1) × Fin (m + 1)))
      + Height.logHeight A, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Height.totalWeight K * Real.log (Nat.card (Fin (n + 1) × Fin (m + 1))) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have h2 := Height.logHeight_nonneg A
    linarith
  intro p q hp hq

  let x : Fin (n + 1) → K := fun i => p.coeff i
  let y : Fin (m + 1) → K := fun j => q.coeff j
  let t : Fin (n + 1) × Fin (m + 1) → K := fun a => x a.1 * y a.2
  have hpsum : p = ∑ i : Fin (n + 1), monomial (i : ℕ) (p.coeff i) := by
    conv_lhs => rw [as_sum_range' p (n + 1) (Nat.lt_succ_of_le hp)]
    rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) (n + 1)]
  have hqsum : q = ∑ j : Fin (m + 1), monomial (j : ℕ) (q.coeff j) := by
    conv_lhs => rw [as_sum_range' q (m + 1) (Nat.lt_succ_of_le hq)]
    rw [Fin.sum_univ_eq_sum_range (fun j => monomial j (q.coeff j)) (m + 1)]
  have key : (fun k : Fin (n + m + 1) => (p * q).coeff k)
      = fun k => ∑ a, A (k, a) * t a := by
    funext k
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [hpsum, hqsum, Finset.sum_mul_sum, finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [monomial_mul_monomial, coeff_monomial]
    simp only [A, t, x, y]
    by_cases h : (i : ℕ) + j = k
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  have hlin := Height.logHeight_linearMap_apply_le A t
  have htab : Height.logHeight t ≤ Height.logHeight x + Height.logHeight y := by
    by_cases hx : x = 0
    · have ht : t = 0 := by funext a; simp [t, hx]
      rw [ht, Height.logHeight_zero]
      exact add_nonneg (Height.logHeight_nonneg _) (Height.logHeight_nonneg _)
    by_cases hy : y = 0
    · have ht : t = 0 := by funext a; simp [t, hy]
      rw [ht, Height.logHeight_zero]
      exact add_nonneg (Height.logHeight_nonneg _) (Height.logHeight_nonneg _)
    exact (Height.logHeight_fun_mul_eq hx hy).le
  rw [key]
  linarith

private theorem mwRED_logHeight_coeff_pad (K : Type*) [Field K] [NumberField K] (p : Polynomial K)
    {n m : ℕ} (hn : p.natDegree ≤ n) (hnm : n ≤ m) :
    Height.logHeight (fun k : Fin (m + 1) => p.coeff k)
      = Height.logHeight (fun k : Fin (n + 1) => p.coeff k) := by
  let e : Fin (n + 1) ⊕ Fin (m - n) ≃ Fin (m + 1) :=
    finSumFinEquiv.trans (finCongr (by omega))
  rw [← Height.logHeight_comp_equiv e]
  have hcomp : (fun k : Fin (m + 1) => p.coeff k) ∘ e
      = Sum.elim (fun k : Fin (n + 1) => p.coeff k) (0 : Fin (m - n) → K) := by
    funext i
    cases i with
    | inl a => simp [e]
    | inr b =>
      simp only [Function.comp_apply, Sum.elim_inr, Pi.zero_apply, e, Equiv.trans_apply,
        finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hcomp, Height.logHeight_sumElim_zero_eq]

private theorem mwRED_logHeight_coeff_rev (K : Type*) [Field K] [NumberField K] (p : Polynomial K)
    (n : ℕ) :
    Height.logHeight (fun k : Fin (n + 1) => p.coeff (n - k))
      = Height.logHeight (fun k : Fin (n + 1) => p.coeff k) := by
  rw [← Height.logHeight_comp_equiv Fin.revPerm (fun k : Fin (n + 1) => p.coeff k)]
  congr 1
  funext k
  simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  congr 1
  omega

private theorem mwRED_dvd_of_rootMultiplicity_le {L : Type*} [Field L] [IsAlgClosed L]
    {A B : Polynomial L} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ c : L, A.rootMultiplicity c ≤ B.rootMultiplicity c) : A ∣ B := by
  classical
  rw [IsAlgClosed.dvd_iff_roots_le_roots hA hB, Multiset.le_iff_count]
  intro c
  rw [count_roots, count_roots]
  exact h c

private theorem mwRED_exists_lift_of_window {K L : Type*} [Field K] [Field L] [Algebra K L]
    {g : ℕ} {S : Polynomial L} (hS : S.natDegree ≤ g) (s : Fin (g + 1) → K)
    (hs : ∀ k, algebraMap K L (s k) = S.coeff (g - k)) :
    ∃ SK : Polynomial K, SK.map (algebraMap K L) = S ∧
      (fun k : Fin (g + 1) => SK.coeff (g - k)) = s := by
  have hlift : S ∈ Polynomial.lifts (algebraMap K L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    by_cases hi : i ≤ g
    · refine ⟨s ⟨g - i, by omega⟩, ?_⟩
      rw [hs]
      congr 1
      simp only
      omega
    · exact ⟨0, by rw [map_zero, coeff_eq_zero_of_natDegree_lt (by omega)]⟩
  obtain ⟨SK, hSK⟩ := (mem_lifts S).mp hlift
  refine ⟨SK, hSK, funext fun k => (algebraMap K L).injective ?_⟩
  rw [hs k, ← hSK, coeff_map]

private theorem mwRED_logHeight_window_le_of_rootMultiplicity (K L : Type*) [Field K]
    [NumberField K] [Field L] [IsAlgClosed L] [Algebra K L] (g' g'' dP : ℕ) (hle : g' ≤ g'') :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (S S' : Polynomial L) (P : Polynomial K),
      S.Monic → S'.Monic → P ≠ 0 → S.natDegree ≤ g'' → S'.natDegree ≤ g' → P.natDegree ≤ dP →
      (∀ c : L, S'.rootMultiplicity c
          ≤ S.rootMultiplicity c + (P.map (algebraMap K L)).rootMultiplicity c) →
      ∀ (s : Fin (g'' + 1) → K) (s' : Fin (g' + 1) → K),
        (∀ k, algebraMap K L (s k) = S.coeff (g'' - k)) →
        (∀ k, algebraMap K L (s' k) = S'.coeff (g' - k)) →
        Height.logHeight s' ≤ Height.logHeight s
          + Height.logHeight (fun k : Fin (dP + 1) => P.coeff k) + c := by
  classical
  obtain ⟨c₁, hc₁⟩ := Height.logHeight_coeff_factor_le K (g'' + dP)
  obtain ⟨c₂, hc₂0, hc₂⟩ := mwRED_logHeight_coeff_mul_le K g'' dP
  refine ⟨max (c₁ + c₂) 0, le_max_right _ _, ?_⟩
  intro S S' P hSm hS'm hP0 hSd hS'd hPd hroot s s' hs hs'
  obtain ⟨SK, hSK, hSKw⟩ := mwRED_exists_lift_of_window hSd s hs
  obtain ⟨SK', hSK', hSK'w⟩ := mwRED_exists_lift_of_window hS'd s' hs'
  have hinj := (algebraMap K L).injective
  have hSKm : SK.Monic := by rw [hinj.monic_map_iff, hSK]; exact hSm
  have hSK'm : SK'.Monic := by rw [hinj.monic_map_iff, hSK']; exact hS'm
  have hSKd : SK.natDegree ≤ g'' := by rw [← natDegree_map (algebraMap K L), hSK]; exact hSd
  have hSK'd : SK'.natDegree ≤ g' := by rw [← natDegree_map (algebraMap K L), hSK']; exact hS'd

  set u : K := P.leadingCoeff⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hP0)
  set PC : Polynomial K := P * C u with hPC
  have hPC0 : PC ≠ 0 := mul_ne_zero hP0 (by simpa using hu0)
  have hPCd : PC.natDegree ≤ dP := le_trans (natDegree_mul_C_le _ _) hPd

  have hdvdL : SK'.map (algebraMap K L) ∣ (SK * PC).map (algebraMap K L) := by
    rw [hSK', Polynomial.map_mul, hSK, hPC, Polynomial.map_mul, map_C]
    have hSL0 : S ≠ 0 := hSm.ne_zero
    have hS'L0 : S' ≠ 0 := hS'm.ne_zero
    have hPL0 : P.map (algebraMap K L) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hP0
    have huL0 : algebraMap K L u ≠ 0 := (map_ne_zero_iff _ hinj).mpr hu0
    have hprod0 : S * (P.map (algebraMap K L) * C (algebraMap K L u)) ≠ 0 :=
      mul_ne_zero hSL0 (mul_ne_zero hPL0 (by simpa using huL0))
    refine mwRED_dvd_of_rootMultiplicity_le hS'L0 hprod0 fun c => ?_
    rw [rootMultiplicity_mul hprod0, rootMultiplicity_mul (mul_ne_zero hPL0 (by simpa using huL0)),
      rootMultiplicity_C, add_zero]
    exact hroot c
  have hdvd : SK' ∣ SK * PC := (map_dvd_map (algebraMap K L) hinj hSK'm).mp hdvdL

  have hprod0K : SK * PC ≠ 0 := mul_ne_zero hSKm.ne_zero hPC0
  have hprodd : (SK * PC).natDegree ≤ g'' + dP :=
    le_trans natDegree_mul_le (Nat.add_le_add hSKd hPCd)
  have step1 := hc₁ (SK * PC) SK' hprod0K hprodd hSK'm hdvd
  have step2 := hc₂ SK PC hSKd hPCd
  have hPCcoeff : (fun k : Fin (dP + 1) => PC.coeff k) = u • fun k : Fin (dP + 1) => P.coeff k := by
    funext k
    simp only [hPC, Pi.smul_apply, smul_eq_mul, coeff_mul_C]
    ring
  have step3 : Height.logHeight (fun k : Fin (dP + 1) => PC.coeff k)
      = Height.logHeight (fun k : Fin (dP + 1) => P.coeff k) := by
    rw [hPCcoeff, Height.logHeight_smul_eq_logHeight _ hu0]

  have hL : Height.logHeight s' = Height.logHeight (fun k : Fin (g'' + dP + 1) => SK'.coeff k) := by
    rw [← hSK'w, mwRED_logHeight_coeff_rev K SK' g',
      mwRED_logHeight_coeff_pad K SK' hSK'd (by omega : g' ≤ g'' + dP)]
  have hR : Height.logHeight s = Height.logHeight (fun k : Fin (g'' + 1) => SK.coeff k) := by
    rw [← hSKw, mwRED_logHeight_coeff_rev K SK g'']
  rw [hL, hR]
  have hmax : c₁ + c₂ ≤ max (c₁ + c₂) 0 := le_max_left _ _
  linarith

noncomputable section

section Base

variable {k : Type*} [Field k]

private def mwRED_primeAt (c : k) : HeightOneSpectrum (Polynomial k) where
  asIdeal := Ideal.span {X - C c}
  isPrime := (Ideal.span_singleton_prime (X_sub_C_ne_zero c)).mpr (prime_X_sub_C c)
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero c

private def mwRED_placeAt (c : k) : Place k (RatFunc k) :=
  Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) (mwRED_primeAt c)

private theorem mwRED_ord_placeAt_X_sub_C (c : k) :
    (mwRED_placeAt c).ord (algebraMap (Polynomial k) (RatFunc k) (X - C c)) = 1 :=
  RationalFunctionField.ord_ofHeightOneSpectrum_of_span (mwRED_primeAt c) (X_sub_C_ne_zero c) rfl

private theorem mwRED_ord_placeAt_algebraMap (c : k) {P : Polynomial k} (hP : P ≠ 0) :
    (mwRED_placeAt c).ord (algebraMap (Polynomial k) (RatFunc k) P) = P.rootMultiplicity c := by
  set m := P.rootMultiplicity c with hm
  set P₁ := P /ₘ (X - C c) ^ m with hP₁
  have hdec : (X - C c) ^ m * P₁ = P := pow_mul_divByMonic_rootMultiplicity_eq P c
  have hP₁0 : P₁ ≠ 0 := by
    intro h; rw [h, mul_zero] at hdec; exact hP hdec.symm
  have hP₁eval : P₁.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hP
  have hndvd : ¬ (X - C c ∣ P₁) := by
    rw [dvd_iff_isRoot]; exact hP₁eval
  have hinj := IsFractionRing.injective (Polynomial k) (RatFunc k)
  have hXc0 : algebraMap (Polynomial k) (RatFunc k) (X - C c) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero c)
  have hpow0 : algebraMap (Polynomial k) (RatFunc k) ((X - C c) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ (X_sub_C_ne_zero c))
  have hP₁0' : algebraMap (Polynomial k) (RatFunc k) P₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hP₁0
  have hord₁ : (mwRED_placeAt c).ord (algebraMap (Polynomial k) (RatFunc k) P₁) = 0 := by
    by_contra hne
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := k) (F := RatFunc k)
      (mwRED_primeAt c) hP₁0).mp hne
    exact hndvd (Ideal.mem_span_singleton.mp hmem)
  have hordpow : (mwRED_placeAt c).ord (algebraMap (Polynomial k) (RatFunc k) ((X - C c) ^ m))
      = m := by
    rw [map_pow, ← zpow_natCast, Place.ord_zpow, mwRED_ord_placeAt_X_sub_C, mul_one]
  rw [← hdec, map_mul, (mwRED_placeAt c).ord_mul hpow0 hP₁0', hordpow, hord₁, add_zero]

private theorem mwRED_algebraMap_mem_of_mem (c : k) (v : Place k (RatFunc k))
    (hX : algebraMap (Polynomial k) (RatFunc k) (X - C c) ∈ v.toValuationSubring)
    (r : Polynomial k) : algebraMap (Polynomial k) (RatFunc k) r ∈ v.toValuationSubring := by
  have hX' : algebraMap (Polynomial k) (RatFunc k) X ∈ v.toValuationSubring := by
    have h := add_mem hX (v.algebraMap_mem' c)
    rwa [map_sub, IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k), algebraMap_eq (R := k),
      sub_add_cancel] at h
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
    refine mul_mem ?_ (pow_mem hX' n)
    rw [← algebraMap_eq (R := k), ← IsScalarTower.algebraMap_apply]
    exact v.algebraMap_mem' a

private theorem mwRED_eq_placeAt_of_ord_pos (c : k) (v : Place k (RatFunc k))
    (hv : 0 < v.ord (algebraMap (Polynomial k) (RatFunc k) (X - C c))) : v = mwRED_placeAt c := by
  have hinj := IsFractionRing.injective (Polynomial k) (RatFunc k)
  have hXc0 : algebraMap (Polynomial k) (RatFunc k) (X - C c) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (X_sub_C_ne_zero c)
  have hXmem : algebraMap (Polynomial k) (RatFunc k) (X - C c) ∈ v.toValuationSubring :=
    Place.mem_of_ord_nonneg v hXc0 hv.le
  have hw : ∀ r : Polynomial k, algebraMap (Polynomial k) (RatFunc k) r ∈ v.toValuationSubring :=
    mwRED_algebraMap_mem_of_mem c v hXmem
  have hcenter : Place.center (Polynomial k) v hw = Ideal.span {X - C c} := by
    have hmemc : X - C c ∈ Place.center (Polynomial k) v hw :=
      (Place.mem_center_iff_ord_pos v hw (X_sub_C_ne_zero c)).mpr hv
    have hmax : (Ideal.span {X - C c} : Ideal (Polynomial k)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C c)
    refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hmemc
  have hHOS : Place.centerHeightOneSpectrum (Polynomial k) v hw = mwRED_primeAt c :=
    HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [Place.toValuationSubring_eq_of_forall_mem v hw, hHOS, mwRED_placeAt,
    Place.ofHeightOneSpectrum_toValuationSubring,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]

private theorem mwRED_eq_placeAt_iff (c : k) (v : Place k (RatFunc k)) :
    v = mwRED_placeAt c ↔ 0 < v.ord (algebraMap (Polynomial k) (RatFunc k) (X - C c)) := by
  refine ⟨fun h => ?_, mwRED_eq_placeAt_of_ord_pos c v⟩
  rw [h, mwRED_ord_placeAt_X_sub_C]; exact one_pos

end Base

section Along

variable {k F' : Type*} [Field k] [Field F'] [Algebra k F']

section InstanceForm

variable [Algebra (RatFunc k) F'] [IsScalarTower k (RatFunc k) F'] [Module.Finite (RatFunc k) F']

private theorem mwRED_restrict_eq_placeAt_iff (c : k) (w : Place k F') :
    w.restrict (RatFunc k) = mwRED_placeAt c ↔
      0 < w.ord (algebraMap (RatFunc k) F' (algebraMap (Polynomial k) (RatFunc k) (X - C c))) := by
  rw [mwRED_eq_placeAt_iff, Place.ord_restrict]
  have he := w.ramificationIndex_pos (F := RatFunc k)
  constructor
  · intro h; exact Int.mul_pos (by exact_mod_cast he) h
  · intro h
    exact pos_of_mul_pos_right h (by exact_mod_cast he.le)

private theorem mwRED_inertiaDeg_eq_one (hdeg : ∀ w : Place k F', w.deg = 1) (w : Place k F') :
    w.inertiaDeg (RatFunc k) = 1 := by
  have h := w.deg_restrict_mul_inertiaDeg (F := RatFunc k)
  rw [hdeg w] at h
  exact Nat.eq_one_of_mul_eq_one_left h

private theorem mwRED_sum_ord_fiber_eq' [IsAlgClosed k] [CharZero k]
    (hdeg : ∀ w : Place k F', w.deg = 1)
    {f : F'} (hf : f ≠ 0) {P Q : Polynomial k} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnorm : Algebra.norm (RatFunc k) f =
        algebraMap (Polynomial k) (RatFunc k) P / algebraMap (Polynomial k) (RatFunc k) Q)
    (c : k) (S : Finset (Place k F'))
    (hS : ∀ w, w ∈ S ↔
      0 < w.ord (algebraMap (RatFunc k) F' (algebraMap (Polynomial k) (RatFunc k) (X - C c)))) :
    ∑ w ∈ S, w.ord f = (P.rootMultiplicity c : ℤ) - Q.rootMultiplicity c := by
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : Algebra.IsSeparable (RatFunc k) F' := inferInstance
  have hSfib : S = (mwRED_placeAt c).fiberOver F' := by
    ext w
    rw [hS, Place.mem_fiberOver, mwRED_restrict_eq_placeAt_iff]
  have hnormord := Place.ord_norm_eq_sum_fiberOver (K := k) (F := RatFunc k) (F' := F')
    (mwRED_placeAt c) hf
  rw [← hSfib] at hnormord
  have hsum : ∑ w ∈ S, ((w.inertiaDeg (RatFunc k) : ℤ) * w.ord f) = ∑ w ∈ S, w.ord f := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mwRED_inertiaDeg_eq_one hdeg w, Nat.cast_one, one_mul]
  rw [← hsum, ← hnormord, hnorm]
  have hinj := IsFractionRing.injective (Polynomial k) (RatFunc k)
  have hP' : algebraMap (Polynomial k) (RatFunc k) P ≠ 0 := (map_ne_zero_iff _ hinj).mpr hP
  have hQ' : algebraMap (Polynomial k) (RatFunc k) Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ
  rw [div_eq_mul_inv, (mwRED_placeAt c).ord_mul hP' (inv_ne_zero hQ'), (mwRED_placeAt c).ord_inv,
    mwRED_ord_placeAt_algebraMap c hP, mwRED_ord_placeAt_algebraMap c hQ]
  ring

end InstanceForm

variable (φ : RatFunc k →ₐ[k] F')

private theorem mwRED_phi_X_sub_C (c : k) :
    φ (algebraMap (Polynomial k) (RatFunc k) (X - C c)) = φ RatFunc.X - algebraMap k F' c := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_sub,
    AlgHom.commutes]

private theorem mwRED_sum_ord_fiber_eq [IsAlgClosed k] [CharZero k]
    (hfin : FiniteAlong k φ) (hdeg : ∀ w : Place k F', w.deg = 1)
    {f : F'} (hf : f ≠ 0) {P Q : Polynomial k} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hnorm : letI := algebraAlong φ
      Algebra.norm (RatFunc k) f =
        algebraMap (Polynomial k) (RatFunc k) P / algebraMap (Polynomial k) (RatFunc k) Q)
    (c : k) (S : Finset (Place k F'))
    (hS : ∀ w, w ∈ S ↔ 0 < w.ord (φ RatFunc.X - algebraMap k F' c)) :
    ∑ w ∈ S, w.ord f = (P.rootMultiplicity c : ℤ) - Q.rootMultiplicity c := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite (RatFunc k) F' := hfin
  refine mwRED_sum_ord_fiber_eq' hdeg hf hP hQ hnorm c S fun w => ?_
  rw [hS, ← mwRED_phi_X_sub_C]
  rfl

end Along

end

set_option autoImplicit false in

private def mwRED_normWitness (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (n : ℕ) (f : modularFunctionFieldBar N) (P : Polynomial K) : Prop :=
  P ≠ 0 ∧ P.natDegree ≤ n ∧
  ∃ φ : RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N,
    φ RatFunc.X = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ ∧
    FiniteAlong (AlgebraicClosure ℚ) φ ∧
    ∃ Q : Polynomial K, Q ≠ 0 ∧
      (letI := algebraAlong φ
       Algebra.norm (RatFunc (AlgebraicClosure ℚ)) f =
         algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
             (P.map (algebraMap K (AlgebraicClosure ℚ))) /
           algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
             (Q.map (algebraMap K (AlgebraicClosure ℚ))))

section MwREDRd
open Height Matrix MvPolynomial Finset

namespace MwRED

variable {k : Type*} [Field k]

private def HasMinor {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) (t : ℕ) : Prop :=
  ∃ ri : Fin t → Fin r, ∃ ci : Fin t → Fin s,
    Function.Injective ri ∧ Function.Injective ci ∧ (M.submatrix ri ci).det ≠ 0

private theorem hasMinor_zero {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) : HasMinor M 0 :=
  ⟨Fin.elim0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, by
    rw [Matrix.det_fin_zero]; exact one_ne_zero⟩

private theorem isHomogeneous_detX {t : ℕ} {σ : Type*} (g : Fin t → Fin t → σ) :
    ((Matrix.of fun a b : Fin t => (X (g a b) : MvPolynomial σ k)).det).IsHomogeneous t := by
  rw [Matrix.det_apply', ← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [mem_homogeneousSubmodule]
  have hprod : (∏ i, (X (g (τ i) i) : MvPolynomial σ k)).IsHomogeneous (∑ _i : Fin t, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X k (g (τ i) i)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hprod
  simp only [Matrix.of_apply]
  rw [show ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ k) = MvPolynomial.C ((Equiv.Perm.sign τ : ℤ) : k) from
    (map_intCast (MvPolynomial.C : k →+* MvPolynomial σ k) _).symm]
  exact hprod.C_mul _

private theorem eval_detX {t : ℕ} {σ : Type*} (g : Fin t → Fin t → σ) (x : σ → k) :
    eval x ((Matrix.of fun a b : Fin t => (X (g a b) : MvPolynomial σ k)).det)
      = (Matrix.of fun a b : Fin t => x (g a b)).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

private theorem snoc_injective {n m : ℕ} {f : Fin n → Fin m} (hf : Function.Injective f) {a : Fin m}
    (ha : a ∉ Set.range f) : Function.Injective (Fin.snoc f a : Fin (n + 1) → Fin m) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
      exact absurd ⟨j, hij.symm⟩ ha
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
      exact absurd ⟨i, hij⟩ ha
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc (hf hij)

private theorem not_hasMinor_of_kernel {r s : ℕ} {K : Type*} [Field K] [Algebra k K]
    {M : Matrix (Fin r) (Fin s) k} {x : Fin s → K} (hx : x ≠ 0)
    (hMx : (M.map (algebraMap k K)).mulVec x = 0) : ¬ HasMinor M s := by
  rintro ⟨ri, ci, hri, hci, hdet⟩
  have hcib : Function.Bijective ci := (Finite.injective_iff_bijective).mp hci
  let e : Fin s ≃ Fin s := Equiv.ofBijective ci hcib
  have hdetK : (((M.map (algebraMap k K)).submatrix ri ci)).det ≠ 0 := by
    have hsub : (M.map (algebraMap k K)).submatrix ri ci
        = (M.submatrix ri ci).map (algebraMap k K) := by
      ext a b
      simp
    rw [hsub, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hdet ((algebraMap k K).injective (by rw [h, map_zero]))
  have hxe : x ∘ e ≠ 0 := by
    intro h
    apply hx
    funext c
    have := congrFun h (e.symm c)
    simpa using this
  have hker : ((M.map (algebraMap k K)).submatrix ri ⇑e).mulVec (x ∘ ⇑e) = 0 := by
    have h1 := Matrix.submatrix_mulVec_equiv (M.map (algebraMap k K)) (x ∘ ⇑e) ri e
    have hxee : (x ∘ ⇑e) ∘ ⇑e.symm = x := by
      funext c; simp
    rw [hxee, hMx] at h1
    rw [h1]
    rfl
  exact hdetK (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x ∘ e, hxe, hker⟩)

open Classical in

private noncomputable def minorRank {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) : ℕ :=
  Nat.findGreatest (HasMinor M) s

open Classical in
private theorem hasMinor_minorRank {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) :
    HasMinor M (minorRank M) :=
  Nat.findGreatest_spec (Nat.zero_le s) (hasMinor_zero M)

open Classical in
private theorem not_hasMinor_of_minorRank_lt {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) {u : ℕ}
    (h1 : minorRank M < u) (h2 : u ≤ s) : ¬ HasMinor M u :=
  Nat.findGreatest_is_greatest h1 h2

open Classical in
private theorem minorRank_le {r s : ℕ} (M : Matrix (Fin r) (Fin s) k) : minorRank M ≤ s :=
  Nat.findGreatest_le s

private theorem HasMinor.of_eq {r s : ℕ} {M : Matrix (Fin r) (Fin s) k} {t u : ℕ} (h : HasMinor M t)
    (e : t = u) : HasMinor M u := e ▸ h

private theorem exists_kernel_vector {r s : ℕ} {K : Type*} [Field K] [Algebra k K]
    (M : Matrix (Fin r) (Fin s) k) (x : Fin s → K) (hx : x ≠ 0)
    (hMx : (M.map (algebraMap k K)).mulVec x = 0) :
    ∃ (ri : Fin (minorRank M) → Fin r) (J : Fin (minorRank M + 1) → Fin s),
      minorRank M < s ∧ Function.Injective ri ∧ Function.Injective J ∧
      ∃ p : Fin s → k, p ≠ 0 ∧ M.mulVec p = 0 ∧
        (∀ c : Fin s, p c ≠ 0 → ∃ jc : Fin (minorRank M + 1),
          c = J jc ∧ p c = (-1) ^ ((minorRank M : ℕ) + (jc : ℕ))
            * (M.submatrix ri (J ∘ jc.succAbove)).det) := by
  classical
  obtain ⟨ri, ci, hri, hci, hdet⟩ := hasMinor_minorRank M
  have hts : minorRank M < s := by
    rcases lt_or_eq_of_le (minorRank_le M) with h | h
    · exact h
    · exfalso
      exact not_hasMinor_of_kernel hx hMx ((hasMinor_minorRank M).of_eq h)
  have hfresh : ∃ j₀ : Fin s, j₀ ∉ Set.range ci := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective ci := fun j => hcon j
    have := Fintype.card_le_of_surjective ci hsurj
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨j₀, hj₀⟩ := hfresh
  set J : Fin (minorRank M + 1) → Fin s := Fin.snoc ci j₀ with hJdef
  have hJinj : Function.Injective J := snoc_injective hci hj₀
  set cof : Fin (minorRank M + 1) → k := fun j =>
    (-1) ^ ((minorRank M : ℕ) + (j : ℕ)) * (M.submatrix ri (J ∘ j.succAbove)).det with hcofdef
  set p : Fin s → k := fun c => ∑ j, if c = J j then cof j else 0 with hpdef
  have hpJ : ∀ j, p (J j) = cof j := by
    intro j
    simp only [hpdef]
    rw [Finset.sum_eq_single j (fun j' _ hne => if_neg fun h => hne ((hJinj h).symm))
      (fun h => absurd (Finset.mem_univ j) h)]
    exact if_pos rfl
  have hJcomp : J ∘ (Fin.last (minorRank M)).succAbove = ci := by
    funext b
    simp only [Function.comp_apply, Fin.succAbove_last, hJdef, Fin.snoc_castSucc]
  have hcoflast : cof (Fin.last (minorRank M)) = (M.submatrix ri ci).det := by
    simp only [hcofdef, hJcomp, Fin.val_last]
    rw [Even.neg_one_pow ⟨minorRank M, rfl⟩, one_mul]
  have hpne : p ≠ 0 := fun h => hdet (by
    have h0 := congrFun h (J (Fin.last (minorRank M)))
    rw [hpJ, hcoflast, Pi.zero_apply] at h0
    exact h0)
  have hmulvec : M.mulVec p = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, hpdef]
    have hstep : ∑ c, M i c * ∑ j, (if c = J j then cof j else 0)
        = ∑ j, M i (J j) * cof j := by
      calc ∑ c, M i c * ∑ j, (if c = J j then cof j else 0)
          = ∑ c, ∑ j, (if c = J j then M i c * cof j else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [mul_ite, mul_zero]
        _ = ∑ j, ∑ c, (if c = J j then M i c * cof j else 0) := Finset.sum_comm
        _ = ∑ j, M i (J j) * cof j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_ite_eq']
            simp
    rw [hstep]
    set B : Matrix (Fin (minorRank M + 1)) (Fin (minorRank M + 1)) k :=
      M.submatrix (Fin.snoc ri i) J with hBdef
    have hdetB : B.det = ∑ j, M i (J j) * cof j := by
      rw [Matrix.det_succ_row B (Fin.last (minorRank M))]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hrow : B (Fin.last (minorRank M)) j = M i (J j) := by
        simp only [hBdef, Matrix.submatrix_apply, Fin.snoc_last]
      have hminor : B.submatrix (Fin.last (minorRank M)).succAbove j.succAbove
          = M.submatrix ri (J ∘ j.succAbove) := by
        ext a b
        simp only [hBdef, Matrix.submatrix_apply, Function.comp_apply, Fin.succAbove_last,
          Fin.snoc_castSucc]
      rw [hrow, hminor]
      simp only [hcofdef, Fin.val_last]
      ring
    have hdetB0 : B.det = 0 := by
      by_cases hmem : i ∈ Set.range ri
      · obtain ⟨a, ha⟩ := hmem
        refine Matrix.det_zero_of_row_eq (Fin.castSucc_lt_last a).ne ?_
        funext j
        simp only [hBdef, Matrix.submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last, ha]
      · by_contra hne
        rw [hBdef] at hne
        have hM1 : HasMinor M (minorRank M + 1) :=
          ⟨Fin.snoc ri i, J, snoc_injective hri hmem, hJinj, hne⟩
        exact not_hasMinor_of_minorRank_lt M (Nat.lt_succ_self _) (by omega) hM1
    rw [← hdetB0, hdetB]
  refine ⟨ri, J, hts, hri, hJinj, p, hpne, hmulvec, fun c hc => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hc
  simp only [hpdef]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  intro hcj
  exact hcon j hcj (by rw [hcj, hpJ])

end MwRED

namespace MwRED

variable {k : Type*} [Field k]

open Classical in

private noncomputable def minorFamily (k : Type*) [Field k] (r s t : ℕ) :
    Bool × (Fin t → Fin r) × (Fin t → Fin s) → MvPolynomial (Fin r × Fin s) k :=
  fun d => MvPolynomial.C (if d.1 then (1 : k) else -1)
    * (Matrix.of fun a b : Fin t => (X (d.2.1 a, d.2.2 b) : MvPolynomial (Fin r × Fin s) k)).det

private theorem isHomogeneous_minorFamily (r s t : ℕ)
    (d : Bool × (Fin t → Fin r) × (Fin t → Fin s)) :
    ((minorFamily k r s t) d).IsHomogeneous t :=
  (isHomogeneous_detX fun a b => (d.2.1 a, d.2.2 b)).C_mul _

private theorem eval_minorFamily (r s t : ℕ) (d : Bool × (Fin t → Fin r) × (Fin t → Fin s))
    (x : Fin r × Fin s → k) :
    eval x (minorFamily k r s t d)
      = (if d.1 then (1 : k) else -1)
        * (Matrix.of fun a b : Fin t => x (d.2.1 a, d.2.2 b)).det := by
  rw [minorFamily, map_mul, MvPolynomial.eval_C, eval_detX]

section Height

variable [Height.AdmissibleAbsValues k]

private noncomputable def minorConst (k : Type*) [Field k] [Height.AdmissibleAbsValues k]
    (r s t : ℕ) : ℝ :=
  Real.log (max (Height.mulHeightBound (minorFamily k r s t)) 1)

private theorem minorConst_nonneg (r s t : ℕ) : 0 ≤ minorConst k r s t :=
  Real.log_nonneg (le_max_right _ 1)

private theorem exists_kernel_logHeight_le (k : Type*) [Field k] [Height.AdmissibleAbsValues k]
    (K : Type*) [Field K] [Algebra k K] (r s : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Matrix (Fin r) (Fin s) k) (x : Fin s → K), x ≠ 0 →
      (M.map (algebraMap k K)).mulVec x = 0 →
      ∃ p : Fin s → k, p ≠ 0 ∧ M.mulVec p = 0 ∧
        Height.logHeight p
          ≤ c + s * Height.logHeight (fun ij : Fin r × Fin s => M ij.1 ij.2) := by
  classical
  refine ⟨(Finset.range (s + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos s)⟩
    (fun t => minorConst k r s t), ?_, ?_⟩
  · exact le_trans (minorConst_nonneg r s 0)
      (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.succ_pos s)))
  intro M x hx hMx
  obtain ⟨ri, J, hts, hri, hJinj, p, hpne, hmul, hspec⟩ := exists_kernel_vector M x hx hMx
  refine ⟨p, hpne, hmul, ?_⟩
  set ent : Fin r × Fin s → k := fun ij => M ij.1 ij.2 with hent

  have hsel : ∀ c : Fin s, p c ≠ 0 → ∃ d : Bool × (Fin (minorRank M) → Fin r)
      × (Fin (minorRank M) → Fin s), p c = eval ent (minorFamily k r s (minorRank M) d) := by
    intro c hc
    obtain ⟨jc, hcJ, hpc⟩ := hspec c hc
    refine ⟨⟨decide (Even ((minorRank M : ℕ) + (jc : ℕ))), ri, J ∘ jc.succAbove⟩, ?_⟩
    rw [eval_minorFamily]
    have hof : (Matrix.of fun a b : Fin (minorRank M) =>
        ent (ri a, (J ∘ jc.succAbove) b)) = M.submatrix ri (J ∘ jc.succAbove) := by
      ext a b
      simp [hent]
    rw [hof, hpc]
    by_cases he : Even ((minorRank M : ℕ) + (jc : ℕ))
    · rw [Even.neg_one_pow he, if_pos (by simpa using he), one_mul]
    · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp he), if_neg (by simpa using he), neg_one_mul]

  have h1 : Height.logHeight p
      ≤ Height.logHeight (fun d : Bool × (Fin (minorRank M) → Fin r)
          × (Fin (minorRank M) → Fin s) => eval ent (minorFamily k r s (minorRank M) d)) := by
    rw [Height.logHeight_eq_logHeight_restrict_support p]
    have hfun : (fun i : Function.support p => p ↑i)
        = (fun d : Bool × (Fin (minorRank M) → Fin r) × (Fin (minorRank M) → Fin s) =>
            eval ent (minorFamily k r s (minorRank M) d))
          ∘ (fun i : Function.support p => Classical.choose (hsel ↑i i.2)) := by
      funext i
      exact Classical.choose_spec (hsel ↑i i.2)
    rw [hfun]
    exact Height.logHeight_comp_le _ _
  have h2 : Height.logHeight (fun d : Bool × (Fin (minorRank M) → Fin r)
        × (Fin (minorRank M) → Fin s) => eval ent (minorFamily k r s (minorRank M) d))
      ≤ minorConst k r s (minorRank M) + (minorRank M : ℝ) * Height.logHeight ent :=
    Height.logHeight_eval_le (fun d => isHomogeneous_minorFamily r s (minorRank M) d) ent
  have h3 : minorConst k r s (minorRank M)
      ≤ (Finset.range (s + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos s)⟩
        (fun t => minorConst k r s t) :=
    Finset.le_sup' _ (Finset.mem_range.mpr (by omega))
  have h4 : (minorRank M : ℝ) * Height.logHeight ent ≤ (s : ℝ) * Height.logHeight ent :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast le_of_lt hts) (Height.logHeight_nonneg ent)
  calc Height.logHeight p
      ≤ minorConst k r s (minorRank M) + (minorRank M : ℝ) * Height.logHeight ent :=
        le_trans h1 h2
    _ ≤ _ := add_le_add h3 h4

private theorem exists_kernel_logHeight_le' (k : Type*) [Field k] [Height.AdmissibleAbsValues k]
    (K : Type*) [Field K] [Algebra k K] (ρ σ : Type*) [Fintype ρ] [Fintype σ]
    [DecidableEq σ] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (M : Matrix ρ σ k) (x : σ → K), x ≠ 0 →
      (M.map (algebraMap k K)).mulVec x = 0 →
      ∃ p : σ → k, p ≠ 0 ∧ M.mulVec p = 0 ∧
        Height.logHeight p
          ≤ c + (Fintype.card σ) * Height.logHeight (fun ij : ρ × σ => M ij.1 ij.2) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_kernel_logHeight_le k K (Fintype.card ρ) (Fintype.card σ)
  refine ⟨c, hc0, ?_⟩
  intro M x hx hMx
  set eρ : ρ ≃ Fin (Fintype.card ρ) := Fintype.equivFin ρ
  set eσ : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  set M' : Matrix (Fin (Fintype.card ρ)) (Fin (Fintype.card σ)) k :=
    M.submatrix eρ.symm eσ.symm with hM'def
  have hx' : x ∘ eσ.symm ≠ 0 := by
    intro h
    apply hx
    funext j
    have := congrFun h (eσ j)
    simpa using this
  have hMx' : (M'.map (algebraMap k K)).mulVec (x ∘ eσ.symm) = 0 := by
    have h1 : (M'.map (algebraMap k K)) = (M.map (algebraMap k K)).submatrix eρ.symm ⇑eσ.symm := by
      ext a b
      simp [hM'def]
    rw [h1]
    have h2 := Matrix.submatrix_mulVec_equiv (M.map (algebraMap k K)) (x ∘ ⇑eσ.symm)
      (⇑eρ.symm) eσ.symm
    have h3 : (x ∘ ⇑eσ.symm) ∘ ⇑eσ.symm.symm = x := by
      funext j
      simp
    rw [h3, hMx] at h2
    rw [h2]
    rfl
  obtain ⟨p, hpne, hmul, hht⟩ := hc M' (x ∘ eσ.symm) hx' hMx'
  refine ⟨p ∘ eσ, ?_, ?_, ?_⟩
  · intro h
    apply hpne
    funext j
    have := congrFun h (eσ.symm j)
    simpa using this
  · have h1 : M.mulVec (p ∘ eσ) = fun i => M'.mulVec p (eρ i) := by
      funext i
      show ∑ j, M i j * (p ∘ eσ) j = ∑ j', M' (eρ i) j' * p j'
      rw [← Equiv.sum_comp eσ fun j' => M' (eρ i) j' * p j']
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hM'def]
    rw [h1]
    funext i
    rw [hmul]
    rfl
  · have h1 : Height.logHeight (p ∘ ⇑eσ) = Height.logHeight p :=
      Height.logHeight_comp_equiv eσ p
    have h2 : Height.logHeight (fun ij : Fin (Fintype.card ρ) × Fin (Fintype.card σ) =>
        M' ij.1 ij.2) = Height.logHeight (fun ij : ρ × σ => M ij.1 ij.2) := by
      have := Height.logHeight_comp_equiv (Equiv.prodCongr eρ.symm eσ.symm).symm
        (fun ij : Fin (Fintype.card ρ) × Fin (Fintype.card σ) => M' ij.1 ij.2)
      rw [← this]
      congr 1
      funext ij
      simp [hM'def]
    rw [h1, ← h2]
    exact hht

end Height

end MwRED

end MwREDRd

noncomputable section

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve Polynomial"

private def mwREDjbar (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

private theorem mwRED_smul_jbar (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • mwREDjbar N
      = mwREDjbar N :=
  ModularCurve.arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull N) σ (jq_mem_full N)

private structure MwREDPres (N : ℕ) [NeZero N] : Type where
  n : ℕ
  npos : 0 < n
  b : Fin n → modularFunctionFieldBar N
  hbQ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • b i = b i
  hbli : ∀ c : Fin n → Polynomial (AlgebraicClosure ℚ),
    (∑ i : Fin n, Polynomial.aeval (mwREDjbar N) (c i) * b i) = 0 → ∀ i, c i = 0
  hbsp : ∀ x : modularFunctionFieldBar N, ∃ (q : Polynomial (AlgebraicClosure ℚ))
      (c : Fin n → Polynomial (AlgebraicClosure ℚ)), q ≠ 0 ∧
      x * Polynomial.aeval (mwREDjbar N) q = ∑ i : Fin n, Polynomial.aeval (mwREDjbar N) (c i) * b i
  d : Polynomial ℚ
  hd : d ≠ 0
  A : Fin n → Matrix (Fin n) (Fin n) (Polynomial ℚ)
  hmul : ∀ i j : Fin n, b i * b j
      * Polynomial.aeval (mwREDjbar N) (d.map (algebraMap ℚ (AlgebraicClosure ℚ)))
      = ∑ k : Fin n, Polynomial.aeval (mwREDjbar N)
          ((A i k j).map (algebraMap ℚ (AlgebraicClosure ℚ))) * b k

private noncomputable def mwREDpack {R : Type*} [Semiring R] (n mdeg : ℕ)
    (u : Fin n × Fin (mdeg + 1) → R) (i : Fin n) : Polynomial R :=
  ∑ d : Fin (mdeg + 1), Polynomial.C (u (i, d)) * Polynomial.X ^ (d : ℕ)

private theorem mwRED_coeff_pack {R : Type*} [Semiring R] (n mdeg : ℕ)
    (u : Fin n × Fin (mdeg + 1) → R) (i : Fin n) (d : Fin (mdeg + 1)) :
    (mwREDpack n mdeg u i).coeff (d : ℕ) = u (i, d) := by
  unfold mwREDpack
  rw [Polynomial.finsetSum_coeff,
    Finset.sum_eq_single d (fun d' _ hne => ?_) (fun h => absurd (Finset.mem_univ d) h)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hne (Fin.val_injective h.symm)), mul_zero]

private theorem mwRED_map_pack {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (n mdeg : ℕ) (u : Fin n × Fin (mdeg + 1) → R) (i : Fin n) :
    (mwREDpack n mdeg u i).map φ = mwREDpack n mdeg (fun x => φ (u x)) i := by
  unfold mwREDpack
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

private noncomputable def mwREDcomb (N : ℕ) [NeZero N] (pres : MwREDPres N) (mdeg : ℕ)
    (q : Polynomial (AlgebraicClosure ℚ))
    (u : Fin pres.n × Fin (mdeg + 1) → AlgebraicClosure ℚ) : modularFunctionFieldBar N :=
  (∑ i : Fin pres.n, Polynomial.aeval (mwREDjbar N) (mwREDpack pres.n mdeg u i) * pres.b i)
    * (Polynomial.aeval (mwREDjbar N) q)⁻¹

private noncomputable def mwREDcombK (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (pres : MwREDPres N) (mdeg : ℕ) (qK : Polynomial K)
    (pk : Fin pres.n × Fin (mdeg + 1) → K) : modularFunctionFieldBar N :=
  mwREDcomb N pres mdeg (qK.map (algebraMap K (AlgebraicClosure ℚ)))
    (fun x => algebraMap K (AlgebraicClosure ℚ) (pk x))

private theorem mwRED_jbar_transcendental (N : ℕ) [NeZero N] :
    Transcendental (AlgebraicClosure ℚ) (mwREDjbar N) := by
  refine AlgebraicCurve.Place.transcendental_of_ord_ne_zero (cuspInftyBar N) (t := mwREDjbar N) ?_
  show (cuspInftyBar N).ord (mwREDjbar N) ≠ 0
  unfold mwREDjbar
  rw [ModularCurve.ord_cuspInftyBar_coeffEmb_jq]
  omega

private theorem mwRED_aeval_jbar_ne_zero (N : ℕ) [NeZero N]
    {p : Polynomial (AlgebraicClosure ℚ)} (hp : p ≠ 0) :
    Polynomial.aeval (mwREDjbar N) p ≠ 0 :=
  fun h => mwRED_jbar_transcendental N ⟨p, hp, h⟩

private theorem mwRED_smul_aeval (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (p : Polynomial (AlgebraicClosure ℚ)) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
        • (Polynomial.aeval (mwREDjbar N) p : modularFunctionFieldBar N)
      = Polynomial.aeval (mwREDjbar N)
          (p.map (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, smul_add, hp, hq, Polynomial.map_add, map_add]
  | monomial d a =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial,
      smul_mul', SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois, smul_pow',
      mwRED_smul_jbar]
    rfl

private theorem mwRED_smul_aeval_mapK (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ K.fixingSubgroup)
    (pk : Polynomial K) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
        • (Polynomial.aeval (mwREDjbar N) (pk.map (algebraMap K (AlgebraicClosure ℚ)))
            : modularFunctionFieldBar N)
      = Polynomial.aeval (mwREDjbar N) (pk.map (algebraMap K (AlgebraicClosure ℚ))) := by
  rw [mwRED_smul_aeval, Polynomial.map_map]
  congr 2
  refine RingHom.ext fun a => ?_
  exact (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ (a : AlgebraicClosure ℚ) a.2

private theorem mwRED_smul_inv (N : ℕ) [NeZero N]
    (g : SemilinearAut (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (x : modularFunctionFieldBar N) : g • x⁻¹ = (g • x)⁻¹ := by
  rw [SemilinearAut.smul_def, SemilinearAut.smul_def, map_inv₀]

private theorem mwRED_smul_combK (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (pres : MwREDPres N) (mdeg : ℕ) (qK : Polynomial K)
    (pk : Fin pres.n × Fin (mdeg + 1) → K)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ K.fixingSubgroup) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
        • mwREDcombK N K pres mdeg qK pk = mwREDcombK N K pres mdeg qK pk := by
  unfold mwREDcombK mwREDcomb
  rw [smul_mul', mwRED_smul_inv, mwRED_smul_aeval_mapK N K σ hσ qK, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul', pres.hbQ σ i]
  congr 1
  rw [show mwREDpack pres.n mdeg (fun x => algebraMap K (AlgebraicClosure ℚ) (pk x)) i
      = (mwREDpack pres.n mdeg pk i).map (algebraMap K (AlgebraicClosure ℚ)) from
    (mwRED_map_pack _ _ _ _ _).symm]
  exact mwRED_smul_aeval_mapK N K σ hσ (mwREDpack pres.n mdeg pk i)

private theorem mwRED_comb_ne_zero (N : ℕ) [NeZero N] (pres : MwREDPres N) (mdeg : ℕ)
    {q : Polynomial (AlgebraicClosure ℚ)} (hq : q ≠ 0)
    {u : Fin pres.n × Fin (mdeg + 1) → AlgebraicClosure ℚ} (hu : u ≠ 0) :
    mwREDcomb N pres mdeg q u ≠ 0 := by
  unfold mwREDcomb
  intro h
  rcases mul_eq_zero.mp h with h1 | h2
  ·
    apply hu
    have hc := pres.hbli (fun i => mwREDpack pres.n mdeg u i) h1
    funext x
    have := congrArg (fun p => Polynomial.coeff p (x.2 : ℕ)) (hc x.1)
    simpa [mwRED_coeff_pack] using this
  · exact mwRED_aeval_jbar_ne_zero N hq (inv_eq_zero.mp h2)

end

section mwRED_BR2supply_section

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve IsDedekindDomain"

open scoped IntermediateField.algebraAdjoinAdjoin

private theorem mwRED_isPrincipalIdealRing_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (j : F) : IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) := by
  let e : (Polynomial.aeval j : Polynomial K →ₐ[K] F).range ≃ₐ[K] Algebra.adjoin K ({j} : Set F) :=
    Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval K j).symm
  let f : Polynomial K →ₐ[K] Algebra.adjoin K ({j} : Set F) :=
    e.toAlgHom.comp (Polynomial.aeval j).rangeRestrict
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨p, hp⟩ : ∃ p : Polynomial K, (Polynomial.aeval j).rangeRestrict p = e.symm y := by
      obtain ⟨p, hp⟩ := (e.symm y).2
      exact ⟨p, Subtype.ext hp⟩
    refine ⟨p, ?_⟩
    show e ((Polynomial.aeval j).rangeRestrict p) = y
    rw [hp]
    exact e.apply_symm_apply y
  exact IsPrincipalIdealRing.of_surjective f.toRingHom hf

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ext Place.ord_zero Place.ord_zpow Divisor Divisor.degree Divisor.degree_single Divisor.degZero Divisor.mem_degZero HasPrincipalDivisors Pic0 Pic0.mk Pic0.mk_add Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring HasPrincipalDivisors.exists_divisor SemilinearAut SemilinearAut.smul_def SemilinearAut.smul_algebraMap SemilinearAut.ord_smul SemilinearAut.smul_single SemilinearAut.divisor_smul_apply algebraAlong isScalarTower_along FiniteAlong Place.ord_restrict Place.center Place.mem_center_iff_ord_pos Place.centerHeightOneSpectrum Place.toValuationSubring_eq_of_forall_mem Place.mem_fiberOver Place.ord_norm_eq_sum_fiberOver RationalFunctionField.ord_ofHeightOneSpectrum_of_span Place.ord_ofHeightOneSpectrum_ne_zero_iff Place.mem_of_ord_nonneg Place.ord_nonneg_of_mem Place.transcendental_of_ord_ne_zero" namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap deg ord ord_zero ord_mul ord_inv ord_zpow ord_smul ofHeightOneSpectrum ofHeightOneSpectrum_toValuationSubring algebraMap_mem' toValuationSubring mk ramificationIndex_pos restrict ord_restrict inertiaDeg deg_restrict_mul_inertiaDeg center mem_center_iff_ord_pos centerHeightOneSpectrum toValuationSubring_eq_of_forall_mem fiberOver mem_fiberOver ord_norm_eq_sum_fiberOver ord_ofHeightOneSpectrum_ne_zero_iff mem_of_ord_nonneg ord_nonneg_of_mem transcendental_of_ord_ne_zero" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.isIntegral_adjoin_of_forall_mem {K F : Type*} [Field K] [Field F]
    [Algebra K F] {j : F}
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {x : F} (hx : ∀ v : Place K F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    IsIntegral (Algebra.adjoin K ({j} : Set F)) x := by

  set A : Subalgebra K F := Algebra.adjoin K ({j} : Set F) with hA
  haveI : IsPrincipalIdealRing A := mwRED_isPrincipalIdealRing_adjoin j
  haveI : IsDedekindDomain A := inferInstance

  haveI : IsDedekindDomain (integralClosure A F) :=
    integralClosure.isDedekindDomain A (IntermediateField.adjoin K ({j} : Set F)) F
  haveI : IsFractionRing (integralClosure A F) F :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin K ({j} : Set F)) F

  have hmem : x ∈ (⨅ 𝔭 : HeightOneSpectrum (integralClosure A F),
      Localization.subalgebra.ofField F _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro 𝔭

    let v : Place K F := Place.ofHeightOneSpectrum (K := K) (R := integralClosure A F) (F := F) 𝔭
    have hjC : j ∈ integralClosure A F := by
      have hjA : j ∈ A := Algebra.self_mem_adjoin_singleton K j
      exact (mem_integralClosure_iff A F).mpr (isIntegral_algebraMap (R := A) (x := ⟨j, hjA⟩))
    have hjv : j ∈ v.toValuationSubring := by
      show j ∈ ((𝔭.valuation F).valuationSubring : ValuationSubring F)
      rw [Valuation.mem_valuationSubring_iff]
      exact 𝔭.valuation_le_one ⟨j, hjC⟩
    have hxv := hx v hjv
    change x ∈ ((𝔭.valuation F).valuationSubring : ValuationSubring F) at hxv
    rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hxv
    exact hxv
  rw [HeightOneSpectrum.iInf_localization_eq_bot (integralClosure A F) (K := F), Algebra.mem_bot]
    at hmem
  obtain ⟨c, rfl⟩ := hmem
  exact (mem_integralClosure_iff A F).mp c.2

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.trace_mem_adjoin_of_forall_mem {K F : Type*} [Field K] [Field F]
    [Algebra K F] {j : F}
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {x : F} (hx : ∀ v : Place K F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ((Algebra.trace (IntermediateField.adjoin K ({j} : Set F)) F x :
        IntermediateField.adjoin K ({j} : Set F)) : F) ∈ Algebra.adjoin K ({j} : Set F) := by
  haveI : IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) :=
    mwRED_isPrincipalIdealRing_adjoin j
  have hint : IsIntegral (Algebra.adjoin K ({j} : Set F)) x :=
    AlgebraicCurve.Place.isIntegral_adjoin_of_forall_mem hx
  have htr := Algebra.isIntegral_trace (L := IntermediateField.adjoin K ({j} : Set F)) hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral htr
  rw [← hy, IntermediateField.algebraAdjoinAdjoin.coe_algebraMap]
  exact y.2

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.exists_aeval_eq_trace_of_forall_mem {K F : Type*} [Field K]
    [Field F] [Algebra K F] {j : F}
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {x : F} (hx : ∀ v : Place K F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ∃ p : Polynomial K, Polynomial.aeval j p =
      ((Algebra.trace (IntermediateField.adjoin K ({j} : Set F)) F x :
        IntermediateField.adjoin K ({j} : Set F)) : F) := by
  have h := AlgebraicCurve.Place.trace_mem_adjoin_of_forall_mem hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  exact h

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.exists_aeval_eq_trace_of_forall_mem' {K F : Type*} [Field K]
    [Field F] [Algebra K F] {j : F} {E : IntermediateField K F}
    (hE : E = IntermediateField.adjoin K ({j} : Set F))
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    {x : F} (hx : ∀ v : Place K F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ∃ p : Polynomial K, Polynomial.aeval j p = ((Algebra.trace E F x : E) : F) := by
  subst hE
  exact AlgebraicCurve.Place.exists_aeval_eq_trace_of_forall_mem hx

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem AlgebraicCurve.Place.exists_aeval_eq_trace_natDegree_le {K F : Type*} [Field K]
    [Field F] [Algebra K F] {j : F} (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {y : F} (M : ℕ)
    (ha : ∀ v : Place K F, j ∈ v.toValuationSubring → y ∈ v.toValuationSubring)
    (hb : ∀ v : Place K F, j⁻¹ ∈ v.toValuationSubring → y * j⁻¹ ^ M ∈ v.toValuationSubring) :
    ∃ p : Polynomial K, p.natDegree ≤ M ∧ Polynomial.aeval j p =
      ((Algebra.trace (IntermediateField.adjoin K ({j} : Set F)) F y :
        IntermediateField.adjoin K ({j} : Set F)) : F) := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (isAlgebraic_zero)

  obtain ⟨p, hp⟩ := AlgebraicCurve.Place.exists_aeval_eq_trace_of_forall_mem ha

  have hE : IntermediateField.adjoin K ({j} : Set F) = IntermediateField.adjoin K ({j⁻¹} : Set F) := by
    refine le_antisymm ?_ ?_
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have h := inv_mem (IntermediateField.mem_adjoin_simple_self K j⁻¹)
      rwa [inv_inv] at h
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        (inv_mem (IntermediateField.mem_adjoin_simple_self K j))
  obtain ⟨q, hq⟩ := AlgebraicCurve.Place.exists_aeval_eq_trace_of_forall_mem' (j := j⁻¹) hE hb

  set jE : IntermediateField.adjoin K ({j} : Set F) := ⟨j, IntermediateField.mem_adjoin_simple_self K j⟩
    with hjE
  have hlin : ((Algebra.trace (IntermediateField.adjoin K ({j} : Set F)) F (y * j⁻¹ ^ M) :
        IntermediateField.adjoin K ({j} : Set F)) : F)
      = j⁻¹ ^ M * Polynomial.aeval j p := by
    have hsm : y * j⁻¹ ^ M = (jE⁻¹ ^ M) • y := by
      rw [IntermediateField.smul_def, smul_eq_mul, mul_comm]
      congr 1
    rw [hsm, map_smul, smul_eq_mul, IntermediateField.coe_mul, hp]
    congr 1

  have hpq : Polynomial.aeval j p = j ^ M * Polynomial.aeval j⁻¹ q := by
    rw [hq, hlin, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hj0, one_pow, one_mul]
  haveI : Invertible (j⁻¹ : F) := invertibleOfNonzero (inv_ne_zero hj0)
  have hrev : Polynomial.aeval j q.reverse * j⁻¹ ^ q.natDegree = Polynomial.aeval j⁻¹ q := by
    have h := Polynomial.eval₂_reverse_mul_pow (algebraMap K F) j⁻¹ q
    rw [invOf_eq_inv, inv_inv] at h
    exact h

  have hpoly : (Polynomial.X ^ q.natDegree * p : Polynomial K) = Polynomial.X ^ M * q.reverse := by
    apply transcendental_iff_injective.mp hj
    rw [map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_X, hpq, ← hrev]
    rw [mul_comm (j ^ q.natDegree), mul_assoc, mul_assoc, ← mul_pow, inv_mul_cancel₀ hj0, one_pow,
      mul_one]
  refine ⟨p, ?_, hp⟩
  by_cases hp0 : p = 0
  · rw [hp0, Polynomial.natDegree_zero]; exact Nat.zero_le _
  have h1 : (Polynomial.X ^ q.natDegree * p : Polynomial K).natDegree = q.natDegree + p.natDegree := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hp0, Polynomial.natDegree_X_pow]
  have h2 : (Polynomial.X ^ M * q.reverse : Polynomial K).natDegree ≤ M + q.natDegree := by
    refine le_trans Polynomial.natDegree_mul_le ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.add_le_add_left (Polynomial.reverse_natDegree_le q) M
  rw [hpoly] at h1
  omega

end mwRED_BR2supply_section

noncomputable section

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve Polynomial"

private theorem mwRED_standin_presentation (N : ℕ) [NeZero N] : Nonempty (MwREDPres N) := by
  obtain ⟨n, b, d, A, hn, hd, hbQ, hbli, hbsp, hmul⟩ :=
    ModularCurve.exists_rational_presentation_modularFunctionFieldBar N
  exact ⟨MwREDPres.mk n hn b hbQ hbli hbsp d hd A hmul⟩

set_option autoImplicit false in
private theorem mwRED_standin_system (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' g'' : ℕ) (hle : g' ≤ g'') (pres : MwREDPres N) :
    ∃ (mdeg rdim qdeg : ℕ) (α β : ℝ), 0 ≤ α ∧
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        ∀ hmem : ∀ k, symVec N g'' D k ∈ K,
        ∃ qK : Polynomial K, qK ≠ 0 ∧ qK.natDegree ≤ qdeg ∧
        ∃ Msys : Matrix (Fin rdim) (Fin pres.n × Fin (mdeg + 1)) K,
          Height.logHeight (fun ij : Fin rdim × (Fin pres.n × Fin (mdeg + 1)) => Msys ij.1 ij.2)
            ≤ α * Height.logHeight (fun k : Fin (g'' + 1) => (⟨symVec N g'' D k, hmem k⟩ : K)) + β ∧
          (∀ u : Fin pres.n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 →
            ((Msys.map (algebraMap K (AlgebraicClosure ℚ))).mulVec u = 0 ↔
              ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
                0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v
                  + v.ord (mwREDcomb N pres mdeg
                      (qK.map (algebraMap K (AlgebraicClosure ℚ))) u))) ∧
          (∀ f : modularFunctionFieldBar N, f ≠ 0 →
            (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
              0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                    : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v + v.ord f) →
            ∃ u : Fin pres.n × Fin (mdeg + 1) → AlgebraicClosure ℚ, u ≠ 0 ∧
              mwREDcomb N pres mdeg (qK.map (algebraMap K (AlgebraicClosure ℚ))) u = f) := by
  obtain ⟨mdeg, rdim, qdeg, α, β, hα, h⟩ :=
    ModularCurve.exists_height_system_modularFunctionFieldBar N K g' g'' hle
      pres.n pres.b pres.hbQ pres.hbli pres.hbsp
  exact ⟨mdeg, rdim, qdeg, α, β, hα, h⟩

section MwREDdetSection
open Polynomial

namespace MwREDdet

variable {K : Type*} [Field K] {ι : Type*}

private def CoeffHom (q : Polynomial (MvPolynomial ι K)) (d : ℕ) : Prop :=
  ∀ k, (q.coeff k).IsHomogeneous d

private theorem CoeffHom.of_eq {q : Polynomial (MvPolynomial ι K)} {d d' : ℕ} (h : CoeffHom q d)
    (e : d = d') : CoeffHom q d' := e ▸ h

private theorem CoeffHom.zero (d : ℕ) : CoeffHom (0 : Polynomial (MvPolynomial ι K)) d :=
  fun _ => by rw [coeff_zero]; exact MvPolynomial.isHomogeneous_zero _ _ _

private theorem CoeffHom.one : CoeffHom (1 : Polynomial (MvPolynomial ι K)) 0 := by
  intro k
  rw [coeff_one]
  split_ifs
  · exact MvPolynomial.isHomogeneous_one _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

private theorem CoeffHom.add {q q' : Polynomial (MvPolynomial ι K)} {d : ℕ} (h : CoeffHom q d)
    (h' : CoeffHom q' d) : CoeffHom (q + q') d :=
  fun k => by rw [coeff_add]; exact (h k).add (h' k)

private theorem CoeffHom.sum {α : Type*} (s : Finset α) (g : α → Polynomial (MvPolynomial ι K))
    (d : ℕ) (h : ∀ a ∈ s, CoeffHom (g a) d) : CoeffHom (∑ a ∈ s, g a) d := by
  intro k
  rw [finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum s _ d fun a ha => h a ha k

private theorem CoeffHom.mul {q q' : Polynomial (MvPolynomial ι K)} {d d' : ℕ} (h : CoeffHom q d)
    (h' : CoeffHom q' d') : CoeffHom (q * q') (d + d') := by
  intro k
  rw [coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun x _ => (h x.1).mul (h' x.2)

private theorem CoeffHom.prod {α : Type*} (s : Finset α) (g : α → Polynomial (MvPolynomial ι K))
    (h : ∀ a ∈ s, CoeffHom (g a) 1) : CoeffHom (∏ a ∈ s, g a) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.card_empty]; exact CoeffHom.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private theorem CoeffHom.intCast_mul {q : Polynomial (MvPolynomial ι K)} {d : ℕ} (h : CoeffHom q d)
    (a : ℤ) : CoeffHom ((a : Polynomial (MvPolynomial ι K)) * q) d := by
  intro k
  rw [coeff_intCast_mul, ← map_intCast (MvPolynomial.C : K →+* MvPolynomial ι K) a]
  exact (h k).C_mul _

private theorem CoeffHom.mapC (q : Polynomial K) :
    CoeffHom (q.map (MvPolynomial.C : K →+* MvPolynomial ι K)) 0 := by
  intro k
  rw [coeff_map]
  exact MvPolynomial.isHomogeneous_C _ _

private noncomputable def _root_.MwREDdet.pgen {r : ℕ} (m : ℕ) (i : Fin r) :
    Polynomial (MvPolynomial (Fin r × Fin (m + 1)) K) :=
  ∑ k : Fin (m + 1), monomial (k : ℕ) (MvPolynomial.X (i, k))

p2m_export "MwREDdet" "pgen"
private theorem CoeffHom.pgen {r : ℕ} (m : ℕ) (i : Fin r) : CoeffHom (pgen (K := K) m i) 1 := by
  intro k
  rw [MwREDdet.pgen, finsetSum_coeff]
  refine MvPolynomial.IsHomogeneous.sum _ _ 1 fun k' _ => ?_
  rw [coeff_monomial]
  split_ifs
  · exact MvPolynomial.isHomogeneous_X _ _
  · exact MvPolynomial.isHomogeneous_zero _ _ _

private theorem map_pgen {r : ℕ} (m : ℕ) (i : Fin r) (p : Fin r → Polynomial K)
    (hp : ∀ i, (p i).natDegree ≤ m) :
    (pgen (K := K) m i).map (MvPolynomial.eval fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2)
      = p i := by
  rw [MwREDdet.pgen, Polynomial.map_sum]
  simp only [Polynomial.map_monomial, MvPolynomial.eval_X]
  conv_rhs => rw [as_sum_range' (p i) (m + 1) (Nat.lt_succ_of_le (hp i))]
  rw [Fin.sum_univ_eq_sum_range (fun k => monomial k ((p i).coeff k)) (m + 1)]

private noncomputable def Agen {r : ℕ} (m : ℕ) (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K))
    (i : Fin r) : Matrix (Fin r) (Fin r) (Polynomial (MvPolynomial (Fin r × Fin (m + 1)) K)) :=
  (A i).map fun q : Polynomial K =>
    q.map (MvPolynomial.C : K →+* MvPolynomial (Fin r × Fin (m + 1)) K)

private noncomputable def Mgen {r : ℕ} (m : ℕ) (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K)) :
    Matrix (Fin r) (Fin r) (Polynomial (MvPolynomial (Fin r × Fin (m + 1)) K)) :=
  ∑ i : Fin r, pgen (K := K) m i • Agen m A i

private noncomputable def _root_.MwREDdet.Pgen {r : ℕ} (m : ℕ) (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K)) :
    Polynomial (MvPolynomial (Fin r × Fin (m + 1)) K) :=
  (Mgen m A).det

p2m_export "MwREDdet" "Pgen"
private theorem CoeffHom.Pgen {r : ℕ} (m : ℕ) (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K)) :
    CoeffHom (Pgen (K := K) m A) r := by
  rw [MwREDdet.Pgen, Matrix.det_apply']
  refine CoeffHom.sum _ _ r fun σ _ => CoeffHom.intCast_mul ?_ _
  have hcard : (Finset.univ : Finset (Fin r)).card = r := Finset.card_fin r
  refine (CoeffHom.prod _ _ fun a _ => ?_).of_eq hcard
  rw [MwREDdet.Mgen, Matrix.sum_apply]
  refine CoeffHom.sum _ _ 1 fun i _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, MwREDdet.Agen, Matrix.map_apply]
  exact ((CoeffHom.pgen m i).mul (CoeffHom.mapC _)).of_eq rfl

private theorem map_Pgen {r : ℕ} (m : ℕ) (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K))
    (p : Fin r → Polynomial K) (hp : ∀ i, (p i).natDegree ≤ m) :
    (Pgen (K := K) m A).map (MvPolynomial.eval fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2)
      = Matrix.det (∑ i : Fin r, p i • A i) := by
  set ev : MvPolynomial (Fin r × Fin (m + 1)) K →+* K :=
    MvPolynomial.eval fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2 with hev
  rw [MwREDdet.Pgen, show (Polynomial.map ev) = (mapRingHom ev : _ → _) from rfl, RingHom.map_det,
    RingHom.mapMatrix_apply]
  congr 1
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, MwREDdet.Mgen, Matrix.sum_apply, Matrix.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, MwREDdet.Agen,
    Matrix.map_apply, coe_mapRingHom, map_pgen m i p hp, Polynomial.map_map]
  congr 1
  have hcomp : ev.comp (MvPolynomial.C : K →+* MvPolynomial (Fin r × Fin (m + 1)) K) = RingHom.id K :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, hev, MvPolynomial.eval_C, RingHom.id_apply]
  rw [hcomp, Polynomial.map_id]

private theorem logHeight_coeff_det_le (K : Type*) [Field K] [NumberField K] (r m w : ℕ)
    (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K)) :
    ∃ c : ℝ, ∀ p : Fin r → Polynomial K, (∀ i, (p i).natDegree ≤ m) →
      Height.logHeight (fun k : Fin (w + 1) => (Matrix.det (∑ i, p i • A i)).coeff k)
        ≤ r * Height.logHeight (fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2) + c := by
  let F : Fin (w + 1) → MvPolynomial (Fin r × Fin (m + 1)) K := fun k => (Pgen m A).coeff k
  have hF : ∀ k, (F k).IsHomogeneous r := fun k => CoeffHom.Pgen m A k
  obtain ⟨C, hC⟩ := Height.logHeight_eval_le' hF
  refine ⟨C, fun p hp => ?_⟩
  have key : (fun k : Fin (w + 1) => (Matrix.det (∑ i, p i • A i)).coeff k)
      = fun k => MvPolynomial.eval (fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2) (F k) := by
    funext k
    rw [← map_Pgen m A p hp, coeff_map]
  rw [key]
  have h := hC fun ik : Fin r × Fin (m + 1) => (p ik.1).coeff ik.2
  linarith

private theorem natDegree_det_le {r d : ℕ} (M : Matrix (Fin r) (Fin r) (Polynomial K))
    (hM : ∀ a b, (M a b).natDegree ≤ d) : (Matrix.det M).natDegree ≤ r * d := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans natDegree_mul_le ?_
  rw [natDegree_intCast, zero_add]
  refine le_trans (natDegree_prod_le _ _) ?_
  calc ∑ i : Fin r, (M (σ i) i).natDegree ≤ ∑ _i : Fin r, d := Finset.sum_le_sum fun i _ => hM _ _
    _ = r * d := by rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]

private theorem natDegree_sum_smul_apply_le {r m mA : ℕ} (A : Fin r → Matrix (Fin r) (Fin r) (Polynomial K))
    (hA : ∀ i a b, (A i a b).natDegree ≤ mA) (p : Fin r → Polynomial K)
    (hp : ∀ i, (p i).natDegree ≤ m) (a b : Fin r) :
    ((∑ i, p i • A i) a b).natDegree ≤ m + mA := by
  rw [Matrix.sum_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  exact le_trans natDegree_mul_le (Nat.add_le_add (hp i) (hA i a b))

end MwREDdet

end MwREDdetSection

noncomputable section

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve Polynomial"

section mwRED_normP_section

variable (N : ℕ) [NeZero N]

private def mwRED_phi :
    RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
  RatFunc.liftAlgHom (Polynomial.aeval (mwREDjbar N))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (mwRED_jbar_transcendental N)))

private theorem mwRED_phi_div (p q : Polynomial (AlgebraicClosure ℚ)) :
    mwRED_phi N (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) p /
        algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) q)
      = Polynomial.aeval (mwREDjbar N) p / Polynomial.aeval (mwREDjbar N) q :=
  RatFunc.liftAlgHom_apply_div _ _ p q

private theorem mwRED_phi_algebraMap (p : Polynomial (AlgebraicClosure ℚ)) :
    mwRED_phi N (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) p)
      = Polynomial.aeval (mwREDjbar N) p := by
  have h := mwRED_phi_div N p 1
  rwa [map_one, div_one, map_one, div_one] at h

private theorem mwRED_phi_X : mwRED_phi N RatFunc.X = mwREDjbar N := by
  rw [← RatFunc.algebraMap_X, mwRED_phi_algebraMap, aeval_X]

variable (pres : MwREDPres N)

private theorem mwRED_linearIndependent :
    letI := algebraAlong (mwRED_phi N)
    LinearIndependent (RatFunc (AlgebraicClosure ℚ)) pres.b := by
  letI := algebraAlong (mwRED_phi N)
  letI : Algebra (Polynomial (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
    (Polynomial.aeval (mwREDjbar N)).toRingHom.toAlgebra
  haveI : IsScalarTower (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
      (modularFunctionFieldBar N) := by
    refine IsScalarTower.of_algebraMap_eq fun p => ?_
    show Polynomial.aeval (mwREDjbar N) p
      = mwRED_phi N (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) p)
    exact (mwRED_phi_algebraMap N p).symm
  rw [← LinearIndependent.iff_fractionRing (Polynomial (AlgebraicClosure ℚ))
    (RatFunc (AlgebraicClosure ℚ)), Fintype.linearIndependent_iff]
  intro c hc
  refine pres.hbli c ?_
  rw [← hc]
  exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def (c i) (pres.b i)).symm

private theorem mwRED_span :
    letI := algebraAlong (mwRED_phi N)
    ⊤ ≤ Submodule.span (RatFunc (AlgebraicClosure ℚ)) (Set.range pres.b) := by
  letI := algebraAlong (mwRED_phi N)
  intro x _
  obtain ⟨q, c, hq, hx⟩ := pres.hbsp x
  have hq' : Polynomial.aeval (mwREDjbar N) q ≠ 0 := mwRED_aeval_jbar_ne_zero N hq
  have hx' : x = ∑ i, (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
      (c i) / algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) q)
        • pres.b i := by
    have h1 : x = (∑ i, Polynomial.aeval (mwREDjbar N) (c i) * pres.b i)
        * (Polynomial.aeval (mwREDjbar N) q)⁻¹ := by
      rw [← hx, mul_inv_cancel_right₀ hq']
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def]
    show _ = mwRED_phi N _ * _
    rw [mwRED_phi_div, div_eq_mul_inv]
    ring
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private def mwRED_basis :
    letI := algebraAlong (mwRED_phi N)
    Module.Basis (Fin pres.n) (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
  letI := algebraAlong (mwRED_phi N)
  Module.Basis.mk (mwRED_linearIndependent N pres) (mwRED_span N pres)

private theorem mwRED_basis_apply :
    letI := algebraAlong (mwRED_phi N)
    ⇑(mwRED_basis N pres) = pres.b := by
  letI := algebraAlong (mwRED_phi N)
  exact Module.Basis.coe_mk _ _

include pres in
private theorem mwRED_finiteAlong : FiniteAlong (AlgebraicClosure ℚ) (mwRED_phi N) := by
  letI := algebraAlong (mwRED_phi N)
  exact Module.Finite.of_basis (mwRED_basis N pres)

private theorem mwRED_norm_comb (mdeg : ℕ) (q : Polynomial (AlgebraicClosure ℚ)) (hq : q ≠ 0)
    (u : Fin pres.n × Fin (mdeg + 1) → AlgebraicClosure ℚ) :
    letI := algebraAlong (mwRED_phi N)
    Algebra.norm (RatFunc (AlgebraicClosure ℚ)) (mwREDcomb N pres mdeg q u) =
      algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
          (Matrix.det (∑ i, mwREDpack pres.n mdeg u i •
            (pres.A i).map (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))))) /
        algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
          ((q * pres.d.map (algebraMap ℚ (AlgebraicClosure ℚ))) ^ pres.n) := by
  letI := algebraAlong (mwRED_phi N)
  classical

  set jb : modularFunctionFieldBar N := mwREDjbar N with hjb
  set db : Polynomial (AlgebraicClosure ℚ) := pres.d.map (algebraMap ℚ (AlgebraicClosure ℚ))
    with hdb
  set Ab : Fin pres.n → Matrix (Fin pres.n) (Fin pres.n) (Polynomial (AlgebraicClosure ℚ)) :=
    fun i => (pres.A i).map (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))) with hAb
  set pb : Fin pres.n → Polynomial (AlgebraicClosure ℚ) := fun i => mwREDpack pres.n mdeg u i
    with hpb
  set Mb : Matrix (Fin pres.n) (Fin pres.n) (Polynomial (AlgebraicClosure ℚ)) :=
    ∑ i, pb i • Ab i with hMb
  have hdb0 : db ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ (AlgebraicClosure ℚ)).injective).mpr pres.hd
  have hqa : Polynomial.aeval jb q ≠ 0 := mwRED_aeval_jbar_ne_zero N hq
  have hda : Polynomial.aeval jb db ≠ 0 := mwRED_aeval_jbar_ne_zero N hdb0

  have hbb : ∀ i j' : Fin pres.n, pres.b i * pres.b j'
      = (∑ k, Polynomial.aeval jb (Ab i k j') * pres.b k) * (Polynomial.aeval jb db)⁻¹ := by
    intro i j'
    rw [eq_mul_inv_iff_mul_eq₀ hda]
    have h := pres.hmul i j'
    simp only [hAb, Matrix.map_apply]
    exact h

  have hMb_apply : ∀ k j' : Fin pres.n, Polynomial.aeval jb (Mb k j')
      = ∑ i, Polynomial.aeval jb (pb i) * Polynomial.aeval jb (Ab i k j') := by
    intro k j'
    rw [hMb, Matrix.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]

  have hcoord : ∀ j' : Fin pres.n, mwREDcomb N pres mdeg q u * pres.b j'
      = ∑ k, (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (Mb k j')
          / algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (q * db))
            • pres.b k := by
    intro j'
    have hR : ∀ k : Fin pres.n,
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (Mb k j')
          / algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (q * db))
            • pres.b k
        = (∑ i, Polynomial.aeval jb (pb i) * Polynomial.aeval jb (Ab i k j'))
            * ((Polynomial.aeval jb q)⁻¹ * (Polynomial.aeval jb db)⁻¹) * pres.b k := by
      intro k
      rw [Algebra.smul_def]
      show mwRED_phi N _ * _ = _
      rw [mwRED_phi_div, hMb_apply, map_mul, div_eq_mul_inv, mul_inv]
    have hL : mwREDcomb N pres mdeg q u * pres.b j'
        = ∑ i, ∑ k, Polynomial.aeval jb (pb i) * Polynomial.aeval jb (Ab i k j') * pres.b k
            * ((Polynomial.aeval jb q)⁻¹ * (Polynomial.aeval jb db)⁻¹) := by
      unfold mwREDcomb
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      calc Polynomial.aeval jb (pb i) * pres.b i * (Polynomial.aeval jb q)⁻¹ * pres.b j'
          = Polynomial.aeval jb (pb i) * (Polynomial.aeval jb q)⁻¹ * (pres.b i * pres.b j') := by
            ring
        _ = Polynomial.aeval jb (pb i) * (Polynomial.aeval jb q)⁻¹
              * ((∑ k, Polynomial.aeval jb (Ab i k j') * pres.b k) * (Polynomial.aeval jb db)⁻¹) := by
            rw [hbb i j']
        _ = ∑ k, Polynomial.aeval jb (pb i) * Polynomial.aeval jb (Ab i k j') * pres.b k
              * ((Polynomial.aeval jb q)⁻¹ * (Polynomial.aeval jb db)⁻¹) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
    have hRsum : (∑ k, (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
          (Mb k j') / algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
            (q * db)) • pres.b k)
        = ∑ k, ∑ i, Polynomial.aeval jb (pb i) * Polynomial.aeval jb (Ab i k j') * pres.b k
            * ((Polynomial.aeval jb q)⁻¹ * (Polynomial.aeval jb db)⁻¹) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hR k, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hL, hRsum, Finset.sum_comm]

  set B := mwRED_basis N pres with hB
  have hBapp : ⇑B = pres.b := mwRED_basis_apply N pres
  have hLM : Algebra.leftMulMatrix B (mwREDcomb N pres mdeg q u)
      = (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (q * db))⁻¹
          • Mb.map (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))) := by
    refine Matrix.ext fun k j' => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, hBapp, hcoord j', ← hBapp, Module.Basis.repr_sum_self,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, div_eq_inv_mul]
  rw [Algebra.norm_eq_matrix_det B, hLM, Matrix.det_smul, Fintype.card_fin,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, inv_pow, ← map_pow, inv_mul_eq_div]

end mwRED_normP_section

private theorem mwRED_normP (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (pres : MwREDPres N) (mdeg qdeg : ℕ) :
    ∃ (dP : ℕ) (c : ℝ), 0 ≤ c ∧
      ∀ (pk : Fin pres.n × Fin (mdeg + 1) → K) (qK : Polynomial K),
        pk ≠ 0 → qK ≠ 0 → qK.natDegree ≤ qdeg →
        mwREDcombK N K pres mdeg qK pk ≠ 0 →
        ∃ P : Polynomial K, mwRED_normWitness N K dP (mwREDcombK N K pres mdeg qK pk) P ∧
          Height.logHeight (fun j : Fin (dP + 1) => P.coeff (j : ℕ))
            ≤ c + (pres.n : ℝ) * Height.logHeight pk := by
  classical

  set AK : Fin pres.n → Matrix (Fin pres.n) (Fin pres.n) (Polynomial K) :=
    fun i => (pres.A i).map (Polynomial.map (algebraMap ℚ K)) with hAK
  set dK : Polynomial K := pres.d.map (algebraMap ℚ K) with hdK
  set mA : ℕ := Finset.univ.sup fun iab : Fin pres.n × Fin pres.n × Fin pres.n =>
    (pres.A iab.1 iab.2.1 iab.2.2).natDegree with hmA
  set dP : ℕ := pres.n * (mdeg + mA) with hdP
  obtain ⟨c₀, hc₀⟩ := MwREDdet.logHeight_coeff_det_le (↥K) pres.n mdeg dP AK
  refine ⟨dP, max c₀ 0, le_max_right _ _, ?_⟩
  intro pk qK _hpk hqK _hqdeg hf
  set P : Polynomial K := Matrix.det (∑ i, mwREDpack pres.n mdeg pk i • AK i) with hPdef

  have htower : (algebraMap (↥K) (AlgebraicClosure ℚ)).comp (algebraMap ℚ (↥K))
      = algebraMap ℚ (AlgebraicClosure ℚ) := (IsScalarTower.algebraMap_eq ℚ (↥K) (AlgebraicClosure ℚ)).symm
  have hinjK := (algebraMap (↥K) (AlgebraicClosure ℚ)).injective
  have hAKe : ∀ i a b, AK i a b = (pres.A i a b).map (algebraMap ℚ (↥K)) := fun _ _ _ => rfl
  have hAKmap : ∀ i, (AK i).map (Polynomial.map (algebraMap (↥K) (AlgebraicClosure ℚ)))
      = (pres.A i).map (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    intro i
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply, hAKe, Matrix.map_apply, Polynomial.map_map, htower]
  have hdKmap : dK.map (algebraMap (↥K) (AlgebraicClosure ℚ))
      = pres.d.map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    rw [hdK, Polynomial.map_map, htower]
  have hPmap : P.map (algebraMap (↥K) (AlgebraicClosure ℚ))
      = Matrix.det (∑ i, mwREDpack pres.n mdeg (fun x => algebraMap (↥K) (AlgebraicClosure ℚ) (pk x)) i
          • (pres.A i).map (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
    rw [hPdef, show Polynomial.map (algebraMap (↥K) (AlgebraicClosure ℚ))
        = (mapRingHom (algebraMap (↥K) (AlgebraicClosure ℚ)) : _ → _) from rfl, RingHom.map_det,
      RingHom.mapMatrix_apply]
    congr 1
    refine Matrix.ext fun a b => ?_
    rw [Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, coe_mapRingHom,
      mwRED_map_pack, ← hAKmap i, Matrix.map_apply]

  have hnorm := mwRED_norm_comb N pres mdeg (qK.map (algebraMap (↥K) (AlgebraicClosure ℚ)))
    ((Polynomial.map_ne_zero_iff hinjK).mpr hqK) (fun x => algebraMap (↥K) (AlgebraicClosure ℚ) (pk x))
  have hQmap : ((qK * dK) ^ pres.n).map (algebraMap (↥K) (AlgebraicClosure ℚ))
      = (qK.map (algebraMap (↥K) (AlgebraicClosure ℚ)) * pres.d.map (algebraMap ℚ (AlgebraicClosure ℚ)))
          ^ pres.n := by
    rw [Polynomial.map_pow, Polynomial.map_mul, hdKmap]
  have hnorm' : (letI := algebraAlong (mwRED_phi N)
      Algebra.norm (RatFunc (AlgebraicClosure ℚ)) (mwREDcombK N K pres mdeg qK pk) =
        algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
            (P.map (algebraMap K (AlgebraicClosure ℚ))) /
          algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
            (((qK * dK) ^ pres.n).map (algebraMap K (AlgebraicClosure ℚ)))) := by
    rw [hPmap, hQmap]
    exact hnorm

  have hP0 : P ≠ 0 := by
    intro hP
    letI := algebraAlong (mwRED_phi N)
    haveI := Module.Free.of_basis (mwRED_basis N pres)
    haveI := Module.Finite.of_basis (mwRED_basis N pres)
    have hN : Algebra.norm (RatFunc (AlgebraicClosure ℚ)) (mwREDcombK N K pres mdeg qK pk) ≠ 0 :=
      Algebra.norm_ne_zero_iff.mpr hf
    apply hN
    rw [hnorm', hP, Polynomial.map_zero, map_zero, zero_div]

  have hpackdeg : ∀ i, (mwREDpack pres.n mdeg pk i).natDegree ≤ mdeg := by
    intro i
    unfold mwREDpack
    refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
    exact le_trans (natDegree_C_mul_X_pow_le _ _) (Nat.lt_succ_iff.mp d.2)
  have hAKdeg : ∀ i a b, (AK i a b).natDegree ≤ mA := by
    intro i a b
    rw [hAKe]
    refine le_trans natDegree_map_le ?_
    exact Finset.le_sup (f := fun iab : Fin pres.n × Fin pres.n × Fin pres.n =>
      (pres.A iab.1 iab.2.1 iab.2.2).natDegree) (Finset.mem_univ (i, a, b))
  have hPdeg : P.natDegree ≤ dP :=
    MwREDdet.natDegree_det_le _ fun a b => MwREDdet.natDegree_sum_smul_apply_le AK hAKdeg _ hpackdeg a b

  refine ⟨P, ⟨hP0, hPdeg, mwRED_phi N, ?_, mwRED_finiteAlong N pres, (qK * dK) ^ pres.n, ?_, hnorm'⟩, ?_⟩
  · rw [mwRED_phi_X]; rfl
  · refine pow_ne_zero _ (mul_ne_zero hqK ?_)
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ (↥K)).injective).mpr pres.hd

  have htuple : (fun ik : Fin pres.n × Fin (mdeg + 1) => (mwREDpack pres.n mdeg pk ik.1).coeff ik.2)
      = pk := by
    funext ik
    rw [mwRED_coeff_pack]
  have h := hc₀ (fun i => mwREDpack pres.n mdeg pk i) hpackdeg
  rw [htuple] at h
  have hmax : c₀ ≤ max c₀ 0 := le_max_left _ _
  linarith

end

private theorem mwRED_map_mulVec {R S : Type*} [CommSemiring R] [CommSemiring S] (ι : R →+* S)
    {ρ σ : Type*} [Fintype σ] (M : Matrix ρ σ R) (p : σ → R) :
    (M.map ι).mulVec (fun x => ι (p x)) = fun i => ι (M.mulVec p i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun x _ => (map_mul ι _ _).symm

end

section mwRED_asm

set_option autoImplicit false in
private theorem mwRED_asm_exists_D' {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {ι : Sort*} (ρ : ι → SemilinearAut K F)
    (vInf : Place K F) (hvInf : ∀ i, ρ i • vInf = vInf) (g' g'' : ℕ)
    (D : Divisor K F) (E : Divisor.degZero (K := K) (F := F))
    (hDeq : (E : Divisor K F) + (g'' : ℤ) • Finsupp.single vInf 1 = D)
    (hDstab : ∀ i, ρ i • D = D)
    (f : F) (hf0 : f ≠ 0)
    (hfL : ∀ v, 0 ≤ ((D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single vInf 1 : Divisor K F)) v + v.ord f)
    (hfG : ∀ i, ρ i • f = f) :
    ∃ (D' : Divisor K F) (E' : Divisor.degZero (K := K) (F := F)),
      (∀ v, 0 ≤ D' v) ∧
      (E' : Divisor K F) + (g' : ℤ) • Finsupp.single vInf 1 = D' ∧
      (∀ i, ρ i • D' = D') ∧
      Pic0.mk E' = Pic0.mk E ∧
      (∀ v, D' v
        = ((D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single vInf 1 : Divisor K F)) v + v.ord f) := by
  obtain ⟨Df, hDford, hDfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0

  have hD₀ :
      (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single vInf 1 : Divisor K F)
        = (E : Divisor K F) + (g' : ℤ) • Finsupp.single vInf 1 := by
    rw [← hDeq, add_sub_assoc, ← sub_smul]
    exact congrArg (fun c => (E : Divisor K F) + c • Finsupp.single vInf 1) (by ring)
  refine ⟨D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single vInf 1 + Df,
    E + ⟨Df, Divisor.mem_degZero.mpr hDfdeg⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v; rw [Finsupp.add_apply, hDford v]; exact hfL v
  ·
    rw [AddMemClass.coe_add, hD₀, add_right_comm]
  ·
    intro i
    have hDfstab : ρ i • Df = Df := by
      refine Finsupp.ext fun w => ?_
      rw [SemilinearAut.divisor_smul_apply, hDford, hDford]
      have h := SemilinearAut.ord_smul (ρ i) ((ρ i)⁻¹ • w) f
      rw [smul_inv_smul, hfG i] at h
      exact h.symm
    rw [smul_add, hDfstab, smul_sub, hDstab i,
      show ((g'' : ℤ) - (g' : ℤ)) • (Finsupp.single vInf 1 : Divisor K F)
        = Finsupp.single vInf ((g'' : ℤ) - (g' : ℤ)) from
        by rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      SemilinearAut.smul_single, hvInf i]
  ·
    have hmk0 : Pic0.mk (K := K) (F := F) ⟨Df, Divisor.mem_degZero.mpr hDfdeg⟩ = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ⟨f, hf0, hDford⟩)
    rw [Pic0.mk_add, hmk0, add_zero]
  ·
    intro v; rw [Finsupp.add_apply, hDford v]

end mwRED_asm

noncomputable section

p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_JZero_naiveHeight_reduce.AlgebraicCurve Polynomial"

set_option autoImplicit false in
private theorem mwRED_IF_SEC (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f)
    (g'' : ℕ) (hle : g' ≤ g'') :
    ∃ (nP : ℕ) (R_A C_A : ℝ), 0 ≤ R_A ∧
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        ∃ (f : modularFunctionFieldBar N) (P : Polynomial K), f ≠ 0 ∧
          (∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
            0 ≤ (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
                  : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) v + v.ord f) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
              arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f = f) ∧
          mwRED_normWitness N K nP f P ∧
          Height.logHeight (fun j : Fin (nP + 1) => P.coeff (j : ℕ))
            ≤ R_A * divNaiveHeight N K g'' D + C_A := by
  classical
  obtain ⟨pres⟩ := mwRED_standin_presentation N
  obtain ⟨mdeg, rdim, qdeg, α, β, hα0, hsys⟩ := mwRED_standin_system N K g' g'' hle pres
  obtain ⟨ck, hck0, hkern⟩ := MwRED.exists_kernel_logHeight_le' K (AlgebraicClosure ℚ)
    (Fin rdim) (Fin pres.n × Fin (mdeg + 1))
  obtain ⟨dP, cP, hcP0, hP⟩ := mwRED_normP N K pres mdeg qdeg
  refine ⟨dP, (pres.n : ℝ) * ((Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) * α),
    cP + (pres.n : ℝ) * (ck + (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) * β),
    by positivity, ?_⟩
  intro D E hDeff hDeq hDstab
  have hmem : ∀ k, symVec N g'' D k ∈ K := ModularCurve.symVec_mem_of_stable N K g'' D hDstab

  have hdegD : Divisor.degree D = (g'' : ℤ) := by
    rw [← hDeq, map_add, (Divisor.mem_degZero.mp E.2), zero_add, Finsupp.smul_single,
      smul_eq_mul, mul_one, Divisor.degree_single,
      deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one, mul_one]
  have hdeg : (g' : ℤ) ≤ Divisor.degree
      (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1
        : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by
    rw [map_sub, hdegD, map_zsmul, Divisor.degree_single,
      deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one, mul_one,
      smul_eq_mul, mul_one]
    omega
  obtain ⟨f₀, hf₀ne, hf₀⟩ := hR _ hdeg
  obtain ⟨qK, hqK0, hqKdeg, Msys, hMht, hiff, hcontain⟩ := hsys D E hDeff hDeq hDstab hmem
  obtain ⟨u₀, hu₀ne, hu₀⟩ := hcontain f₀ hf₀ne hf₀
  have hker₀ : (Msys.map (algebraMap K (AlgebraicClosure ℚ))).mulVec u₀ = 0 :=
    (hiff u₀ hu₀ne).mpr (by rw [hu₀]; exact hf₀)
  obtain ⟨pk, hpkne, hpk0, hpkht⟩ := hkern Msys u₀ hu₀ne hker₀
  have hι : (fun x => algebraMap K (AlgebraicClosure ℚ) (pk x)) ≠ 0 := by
    intro h
    apply hpkne
    funext x
    have hx := congrFun h x
    simp only [Pi.zero_apply] at hx ⊢
    exact (algebraMap K (AlgebraicClosure ℚ)).injective (by rw [hx, map_zero])
  have hkerι : (Msys.map (algebraMap K (AlgebraicClosure ℚ))).mulVec
      (fun x => algebraMap K (AlgebraicClosure ℚ) (pk x)) = 0 := by
    rw [mwRED_map_mulVec, hpk0]
    funext i
    simp
  have hqmapne : qK.map (algebraMap K (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h
    exact hqK0 ((Polynomial.map_eq_zero_iff (algebraMap K (AlgebraicClosure ℚ)).injective).mp h)
  have hfne : mwREDcombK N K pres mdeg qK pk ≠ 0 :=
    mwRED_comb_ne_zero N pres mdeg hqmapne hι
  have hfpole := (hiff _ hι).mp hkerι
  obtain ⟨P, hwit, hPht⟩ := hP pk qK hpkne hqK0 hqKdeg hfne
  refine ⟨mwREDcombK N K pres mdeg qK pk, P, hfne, hfpole, fun σ hσ =>
    mwRED_smul_combK N K pres mdeg qK pk σ hσ, hwit, ?_⟩

  have hdiv : divNaiveHeight N K g'' D
      = Height.logHeight (fun k => (⟨symVec N g'' D k, hmem k⟩ : K)) := by
    rw [divNaiveHeight, dif_pos hmem]
  have hent0 : (0 : ℝ) ≤ Height.logHeight
      (fun ij : Fin rdim × (Fin pres.n × Fin (mdeg + 1)) => Msys ij.1 ij.2) :=
    Height.logHeight_nonneg _
  have hn0 : (0 : ℝ) ≤ (pres.n : ℝ) := Nat.cast_nonneg _
  have hcard0 : (0 : ℝ) ≤ (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) := Nat.cast_nonneg _
  have hsym0 : (0 : ℝ) ≤ Height.logHeight (fun k => (⟨symVec N g'' D k, hmem k⟩ : K)) :=
    Height.logHeight_nonneg _
  have step1 : Height.logHeight (fun j : Fin (dP + 1) => P.coeff (j : ℕ))
      ≤ cP + (pres.n : ℝ) * Height.logHeight pk := hPht
  have step2 : Height.logHeight pk ≤ ck + (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) *
      Height.logHeight (fun ij : Fin rdim × (Fin pres.n × Fin (mdeg + 1)) => Msys ij.1 ij.2) :=
    hpkht
  have step3 : Height.logHeight
      (fun ij : Fin rdim × (Fin pres.n × Fin (mdeg + 1)) => Msys ij.1 ij.2)
      ≤ α * Height.logHeight (fun k => (⟨symVec N g'' D k, hmem k⟩ : K)) + β := hMht
  rw [hdiv]
  calc Height.logHeight (fun j : Fin (dP + 1) => P.coeff (j : ℕ))
      ≤ cP + (pres.n : ℝ) * Height.logHeight pk := step1
    _ ≤ cP + (pres.n : ℝ) * (ck + (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) *
          Height.logHeight (fun ij : Fin rdim × (Fin pres.n × Fin (mdeg + 1)) =>
            Msys ij.1 ij.2)) := by
        have := mul_le_mul_of_nonneg_left step2 hn0
        linarith
    _ ≤ cP + (pres.n : ℝ) * (ck + (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) *
          (α * Height.logHeight (fun k => (⟨symVec N g'' D k, hmem k⟩ : K)) + β)) := by
        have h1 := mul_le_mul_of_nonneg_left step3 hcard0
        have h2 := mul_le_mul_of_nonneg_left h1 hn0
        linarith
    _ = (pres.n : ℝ) * ((Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) * α)
          * Height.logHeight (fun k => (⟨symVec N g'' D k, hmem k⟩ : K))
        + (cP + (pres.n : ℝ) * (ck + (Fintype.card (Fin pres.n × Fin (mdeg + 1)) : ℝ) * β)) := by
        ring

end

section mwRED_packet_algebra

open Polynomial

variable {N : ℕ} [NeZero N]

set_option autoImplicit false in
private theorem mwRED_jFactor_monic (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (jFactor N v).Monic := by
  unfold jFactor
  split_ifs
  · exact monic_X_sub_C _
  · exact monic_one

set_option autoImplicit false in
private theorem mwRED_natDegree_jFactor_le
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (jFactor N v).natDegree ≤ 1 := by
  unfold jFactor
  split_ifs
  · rw [natDegree_X_sub_C]
  · rw [natDegree_one]; exact zero_le_one

set_option autoImplicit false in
private theorem mwRED_symPoly_eq_prod
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    symPoly N D = ∏ v ∈ D.support, jFactor N v ^ (D v).toNat := rfl

set_option autoImplicit false in
private theorem mwRED_symPoly_monic (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (symPoly N D).Monic := by
  rw [mwRED_symPoly_eq_prod]
  exact monic_prod_of_monic _ _ fun v _ => (mwRED_jFactor_monic v).pow _

set_option autoImplicit false in

private theorem mwRED_natDegree_symPoly_le
    (hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v) :
    ((symPoly N D).natDegree : ℤ) ≤ Divisor.degree D := by
  have h1 : (symPoly N D).natDegree ≤ ∑ v ∈ D.support, (D v).toNat := by
    rw [mwRED_symPoly_eq_prod]
    refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun v _ => ?_)
    refine le_trans natDegree_pow_le ?_
    calc (D v).toNat * (jFactor N v).natDegree ≤ (D v).toNat * 1 :=
          Nat.mul_le_mul_left _ (mwRED_natDegree_jFactor_le v)
      _ = (D v).toNat := mul_one _
  have h2 : Divisor.degree D = ∑ v ∈ D.support, D v := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]
  have h3 : ((∑ v ∈ D.support, (D v).toNat : ℕ) : ℤ) = ∑ v ∈ D.support, D v := by
    push_cast
    exact Finset.sum_congr rfl fun v _ => Int.toNat_of_nonneg (hD v)
  rw [h2, ← h3]
  exact_mod_cast h1

set_option autoImplicit false in
private theorem mwRED_rootMultiplicity_prod {L : Type*} [Field L] {ι : Type*} (s : Finset ι)
    (g : ι → Polynomial L) (hg : ∀ i ∈ s, g i ≠ 0) (c : L) :
    (∏ i ∈ s, g i).rootMultiplicity c = ∑ i ∈ s, (g i).rootMultiplicity c := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ← C_1, rootMultiplicity_C]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      rootMultiplicity_mul (mul_ne_zero (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi))),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

set_option autoImplicit false in

private theorem mwRED_ord_j_nonneg_of_pos (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (c : AlgebraicClosure ℚ)
    (hw : 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) :
    0 ≤ w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) := by
  set j : modularFunctionFieldBar N := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ with hj
  have hne : j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hw; exact lt_irrefl _ hw
  have hmem : j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
      ∈ w.toValuationSubring := Place.mem_of_ord_nonneg w hne hw.le
  have hjmem : j ∈ w.toValuationSubring := by
    have h := add_mem hmem (w.algebraMap_mem' c)
    rwa [sub_add_cancel] at h
  exact Place.ord_nonneg_of_mem w hjmem

set_option autoImplicit false in

private theorem mwRED_rootMultiplicity_symPoly
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ)
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) :
    (symPoly N D).rootMultiplicity c = ∑ w ∈ T, (D w).toNat := by
  classical
  have hP2 := (ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).1

  have key : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (jFactor N v ^ (D v).toNat).rootMultiplicity c = if v ∈ T then (D v).toNat else 0 := by
    intro v
    by_cases hv : 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
    · rw [jFactor_of_nonneg hv]
      have hsat : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) -
          algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)) :=
        Classical.epsilon_spec (hP2 v hv).exists
      have hiff : v ∈ T ↔ c = jCoord N v := by
        rw [hT]
        refine ⟨fun h => (hP2 v hv).unique h hsat, fun h => h ▸ hsat⟩
      by_cases hcv : c = jCoord N v
      · rw [if_pos (hiff.mpr hcv), hcv, rootMultiplicity_X_sub_C_pow]
      · rw [if_neg (fun h => hcv (hiff.mp h))]
        refine rootMultiplicity_eq_zero fun hroot => hcv ?_
        rw [IsRoot, eval_pow] at hroot
        have h1 : ((X - C (jCoord N v)).eval c) = 0 := eq_zero_of_pow_eq_zero hroot
        rw [eval_sub, eval_X, eval_C, sub_eq_zero] at h1
        exact h1
    · rw [jFactor_of_neg (not_le.mp hv), one_pow, ← C_1, rootMultiplicity_C]
      rw [if_neg]
      intro hvT
      exact hv (mwRED_ord_j_nonneg_of_pos v c ((hT v).mp hvT))
  rw [mwRED_symPoly_eq_prod, mwRED_rootMultiplicity_prod _ _
    (fun v _ => pow_ne_zero _ (mwRED_jFactor_monic v).ne_zero)]
  simp_rw [key]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm,
    ← Finset.filter_mem_eq_inter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.mp h]; rfl

end mwRED_packet_algebra

set_option autoImplicit false in

private theorem mwRED_IF_NORM (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' g'' : ℕ) (hle : g' ≤ g'') (n : ℕ) :
    ∃ R_B R_B' C_B : ℝ, 0 ≤ R_B ∧ 0 ≤ R_B' ∧ 0 ≤ C_B ∧
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        ∀ (f : modularFunctionFieldBar N), f ≠ 0 →
          (∀ v, 0 ≤ ((D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1 :
            Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) v + v.ord f) →
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
              arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • f = f) →
        ∀ (P : Polynomial K), mwRED_normWitness N K n f P →
        ∀ (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          (∀ v, D' v = ((D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1 :
            Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) v + v.ord f) →
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
              arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D' = D') →
          divNaiveHeight N K g' D'
            ≤ R_B * divNaiveHeight N K g'' D
              + R_B' * Height.logHeight (fun i : Fin (n + 1) => P.coeff i) + C_B := by
  classical
  obtain ⟨c, hc0, hc⟩ :=
    mwRED_logHeight_window_le_of_rootMultiplicity (↥K) (AlgebraicClosure ℚ) g' g'' n hle
  refine ⟨1, 1, c, zero_le_one, zero_le_one, hc0, ?_⟩
  intro D E hDeff hDeq hDstab f hf hfpole _hfrat P hW D' hD'eq _hD'stab
  have hdeg := ModularCurve.deg_eq_one_modularFunctionFieldBar N
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hRHS0 : 0 ≤ 1 * divNaiveHeight N K g'' D
      + 1 * Height.logHeight (fun i : Fin (n + 1) => P.coeff i) + c := by
    have h1 := divNaiveHeight_nonneg (K := K) g'' D
    have h2 := Height.logHeight_nonneg (fun i : Fin (n + 1) => P.coeff i)
    linarith
  by_cases hD'K : ∀ k, symVec N g' D' k ∈ K
  swap
  · unfold divNaiveHeight; rw [dif_neg hD'K]
    unfold divNaiveHeight at hRHS0; exact hRHS0
  have hDK : ∀ k, symVec N g'' D k ∈ K :=
    fun k => ModularCurve.symVec_mem_of_stable N K g'' D hDstab k
  unfold divNaiveHeight
  rw [dif_pos hD'K, dif_pos hDK, one_mul, one_mul]

  obtain ⟨hP0, hPdeg, φ, hφX, hfin, Q, hQ0, hnorm⟩ := hW

  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
  have hD'eff : ∀ v, 0 ≤ D' v := fun v => (hD'eq v).symm ▸ hfpole v
  have hdeginf : Divisor.degree (Finsupp.single (cuspInftyBar N) (1 : ℤ)) = 1 := by
    rw [Divisor.degree_single, hdeg, Nat.cast_one, mul_one]
  have hdegD : Divisor.degree D = g'' := by
    rw [← hDeq, map_add, map_zsmul, hdeginf, Divisor.mem_degZero.mp E.2, zero_add, smul_eq_mul,
      mul_one]
  have hD'sum : D' = (D - ((g'' : ℤ) - (g' : ℤ)) • Finsupp.single (cuspInftyBar N) 1) + Df := by
    ext v; rw [Finsupp.add_apply, hD'eq v, hDf v]
  have hdegD' : Divisor.degree D' = g' := by
    rw [hD'sum, map_add, map_sub, map_zsmul, hdeginf, hdegD, hDf0, smul_eq_mul, mul_one, add_zero]
    ring
  have hSd : (symPoly N D).natDegree ≤ g'' := by
    have h := mwRED_natDegree_symPoly_le hdeg D hDeff
    rw [hdegD] at h
    exact_mod_cast h
  have hS'd : (symPoly N D').natDegree ≤ g' := by
    have h := mwRED_natDegree_symPoly_le hdeg D' hD'eff
    rw [hdegD'] at h
    exact_mod_cast h

  have hroot : ∀ c : AlgebraicClosure ℚ, (symPoly N D').rootMultiplicity c
      ≤ (symPoly N D).rootMultiplicity c
        + (P.map (algebraMap K (AlgebraicClosure ℚ))).rootMultiplicity c := by
    intro c
    letI := algebraAlong φ
    haveI := isScalarTower_along φ
    haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) := hfin
    haveI : CharZero (RatFunc (AlgebraicClosure ℚ)) := charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))).injective
    haveI : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) (modularFunctionFieldBar N) :=
      inferInstance
    set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
      (mwRED_placeAt c).fiberOver (modularFunctionFieldBar N) with hTdef
    have hjc : φ RatFunc.X - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c
        = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by rw [hφX]
    have hTφ : ∀ w, w ∈ T ↔ 0 < w.ord (φ RatFunc.X
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      intro w
      rw [hTdef, Place.mem_fiberOver, mwRED_restrict_eq_placeAt_iff, ← mwRED_phi_X_sub_C]
      rfl
    have hT : ∀ w, w ∈ T ↔ 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
      intro w; rw [hTφ, hjc]
    have hinjK := (algebraMap (↥K) (AlgebraicClosure ℚ)).injective
    have hP0' : P.map (algebraMap K (AlgebraicClosure ℚ)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinjK).mpr hP0
    have hQ0' : Q.map (algebraMap K (AlgebraicClosure ℚ)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff hinjK).mpr hQ0
    have hsumf := mwRED_sum_ord_fiber_eq φ hfin hdeg hf hP0' hQ0' hnorm c T hTφ
    have hS := mwRED_rootMultiplicity_symPoly D c T hT
    have hS' := mwRED_rootMultiplicity_symPoly D' c T hT

    have hinfT : cuspInftyBar N ∉ T := by
      intro h
      have h0 := mwRED_ord_j_nonneg_of_pos (cuspInftyBar N) c ((hT _).mp h)
      rw [ModularCurve.ord_cuspInftyBar_coeffEmb_jq N] at h0
      exact absurd h0 (by norm_num)
    have hptw : ∀ w ∈ T, D' w = D w + w.ord f := by
      intro w hw
      have hne : w ≠ cuspInftyBar N := fun h => hinfT (h ▸ hw)
      rw [hD'eq w, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_apply,
        if_neg (Ne.symm hne), smul_zero, sub_zero]
    have hsumD' : ∑ w ∈ T, ((D' w).toNat : ℤ) = ∑ w ∈ T, ((D w).toNat : ℤ) + ∑ w ∈ T, w.ord f := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [Int.toNat_of_nonneg (hD'eff w), Int.toNat_of_nonneg (hDeff w), hptw w hw]
    have hZ : ((symPoly N D').rootMultiplicity c : ℤ)
        = (symPoly N D).rootMultiplicity c
          + ((P.map (algebraMap K (AlgebraicClosure ℚ))).rootMultiplicity c
            - (Q.map (algebraMap K (AlgebraicClosure ℚ))).rootMultiplicity c) := by
      rw [hS, hS', ← hsumf]
      push_cast
      exact hsumD'
    have hZle : ((symPoly N D').rootMultiplicity c : ℤ)
        ≤ (symPoly N D).rootMultiplicity c
          + (P.map (algebraMap K (AlgebraicClosure ℚ))).rootMultiplicity c := by
      rw [hZ]
      have : (0 : ℤ) ≤ (Q.map (algebraMap K (AlgebraicClosure ℚ))).rootMultiplicity c :=
        Nat.cast_nonneg _
      linarith
    exact_mod_cast hZle
  exact hc (symPoly N D) (symPoly N D') P (mwRED_symPoly_monic D) (mwRED_symPoly_monic D') hP0
    hSd hS'd hPdeg hroot _ _ (fun k => rfl) (fun k => rfl)

end mwRED_aux1_helpers

set_option autoImplicit false in
private theorem mwRED_standin_perRep_reduce (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f)
    (g'' : ℕ) (hle : g' ≤ g'') :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : ↥(JZero N ^+ ↥K.fixingSubgroup),
      ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
        (∀ v, 0 ≤ D v) →
        (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            + (g'' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D →
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
            arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D = D) →
        Pic0.mk E = (x : JZero N) →
        ∃ (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          (E' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
          (∀ v, 0 ≤ D' v) ∧
          (E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
              + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D' ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
              arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ • D' = D') ∧
          Pic0.mk E' = (x : JZero N) ∧
          divNaiveHeight N K g' D' ≤ R * divNaiveHeight N K g'' D + C := by
  obtain ⟨n, R_A, C_A, hR_A, hSEC⟩ := mwRED_IF_SEC N K g' hR g'' hle
  obtain ⟨R_B, R_B', C_B, hR_B, hR_B', hC_B, hNORM⟩ := mwRED_IF_NORM N K g' g'' hle n
  refine ⟨R_B + R_B' * R_A, R_B' * C_A + C_B,
    add_nonneg hR_B (mul_nonneg hR_B' hR_A), fun x D E hDeff hDeq hDstab hDmk => ?_⟩
  obtain ⟨f, P, hf0, hfL, hfK, hfW, hPle⟩ := hSEC D E hDeff hDeq hDstab
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D', E', hD'eff, hD'eq, hD'stab, hD'mk, hD'pt⟩ :=
    mwRED_asm_exists_D'
      (ι := { σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ // σ ∈ K.fixingSubgroup })
      (fun σ => arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ.1)
      (cuspInftyBar N)
      (fun σ => ModularCurve.arithmeticGalois_smul_cuspInftyBar N σ.1) g' g'' D E hDeq
      (fun σ => hDstab σ.1 σ.2) f hf0 hfL (fun σ => hfK σ.1 σ.2)
  refine ⟨D', E', hD'eff, hD'eq, fun σ hσ => hD'stab ⟨σ, hσ⟩, hD'mk.trans hDmk, ?_⟩
  calc divNaiveHeight N K g' D'
      ≤ R_B * divNaiveHeight N K g'' D
          + R_B' * Height.logHeight (fun i : Fin (n + 1) => P.coeff i) + C_B :=
        hNORM D E hDeff hDeq hDstab f hf0 hfL hfK P hfW D' hD'pt
          (fun σ hσ => hD'stab ⟨σ, hσ⟩)
    _ ≤ R_B * divNaiveHeight N K g'' D
          + R_B' * (R_A * divNaiveHeight N K g'' D + C_A) + C_B := by
        have := mul_le_mul_of_nonneg_left hPle hR_B'; linarith
    _ = (R_B + R_B' * R_A) * divNaiveHeight N K g'' D + (R_B' * C_A + C_B) := by ring

set_option autoImplicit false in
theorem solution (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f)
    (g'' : ℕ) (hle : g' ≤ g'') :
    ∃ R C : ℝ, 0 ≤ R ∧ ∀ x : ↥(JZero N ^+ ↥K.fixingSubgroup),
      JZero.naiveHeight N K g' x ≤ R * JZero.naiveHeight N K g'' x + C := by
      obtain ⟨R₀, C₀, hR₀, hper⟩ := mwRED_standin_perRep_reduce N K g' hR g'' hle
      have hRlift : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (g'' : ℤ) ≤ Divisor.degree D →
            ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
              ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f :=
        fun D hdeg => hR D (le_trans (by exact_mod_cast hle) hdeg)
      refine ⟨max R₀ 1, max C₀ 0, le_trans zero_le_one (le_max_right R₀ 1), fun x => ?_⟩
      have hM : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
      obtain ⟨D0, E0, hD0eff, hD0eq, hD0stab, hD0mk⟩ :=
        ModularCurve.JZero.exists_galoisStable_rep N K g'' hRlift (x : JZero N) x.2
      have hne : (JZero.repHeights N K g'' x).Nonempty :=
        ⟨divNaiveHeight N K g'' D0, D0, E0, hD0eff, hD0eq, hD0stab, hD0mk, rfl⟩
      have hdom : ∀ r ∈ JZero.repHeights N K g'' x,
          JZero.naiveHeight N K g' x ≤ max R₀ 1 * r + max C₀ 0 := by
        rintro r ⟨D, E, hDeff, hDeq, hDstab, hDmk, rfl⟩
        obtain ⟨D', E', hD'eff, hD'eq, hD'stab, hD'mk, hD'le⟩ :=
          hper x D E hDeff hDeq hDstab hDmk
        calc JZero.naiveHeight N K g' x
            ≤ divNaiveHeight N K g' D' :=
              JZero.naiveHeight_le g' x D' E' hD'eff hD'eq hD'stab hD'mk
          _ ≤ R₀ * divNaiveHeight N K g'' D + C₀ := hD'le
          _ ≤ max R₀ 1 * divNaiveHeight N K g'' D + max C₀ 0 :=
              add_le_add (mul_le_mul_of_nonneg_right (le_max_left R₀ 1)
                (divNaiveHeight_nonneg g'' D)) (le_max_left C₀ 0)
      have hinf : (JZero.naiveHeight N K g' x - max C₀ 0) / max R₀ 1
          ≤ JZero.naiveHeight N K g'' x := by
        refine le_csInf hne fun r hr => ?_
        rw [div_le_iff₀ hM, mul_comm]
        have h1 := hdom r hr
        linarith
      have h3 := (div_le_iff₀ hM).mp hinf
      have h4 : JZero.naiveHeight N K g'' x * max R₀ 1
          = max R₀ 1 * JZero.naiveHeight N K g'' x := mul_comm _ _
      linarith

end S_ModularCurve_JZero_naiveHeight_reduce
end P2MW
export P2MW.S_ModularCurve_JZero_naiveHeight_reduce (solution)
