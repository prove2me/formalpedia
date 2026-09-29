-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ddc853d6-c310-510c-b1ca-23760ff75d00

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_LaurentDescent
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

private theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

private theorem sep_ord_pos {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    {c₁ c₂ : ResidueField A}
    (h₁ : 0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁))
    (h₂ : 0 < v.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂)) : c₁ = c₂ := by
  by_contra hne
  have hsub : ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂) - ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁) = algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂) := by
    rw [map_sub]
    ring
  have hv₁ : v.adicValuation ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₁) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₁), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv₂ : v.adicValuation ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c₂) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₂), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : v.adicValuation (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) < 1 := by
    rw [← hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv₂ hv₁)
  have hord0 : v.ord (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c₁ - c₂)) = 0 :=
    ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)
  rw [v.adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (sub_ne_zero.mpr hne)), hord0] at hval
  simp at hval

open Classical in
private noncomputable def jval {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) : ResidueField A :=
  if h : ∃ c, 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) then h.choose else 0

private theorem jval_eq {N : ℕ} [NeZero N] {A : ValuationSubring (AlgebraicClosure ℚ)}
    (t : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))
    {c : ResidueField A}
    (h : 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c)) : jval t = c := by
  have hex : ∃ c', 0 < t.ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c') := ⟨c, h⟩
  unfold jval
  rw [dif_pos hex]
  exact sep_ord_pos t hex.choose_spec h

private theorem negOrd_sub_algebraMap_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (W : Place K F) (g : F) (c : K) :
    max (-(W.ord (g - algebraMap K F c))) 0 = max (-(W.ord g)) 0 := by
  by_cases hg : W.ord g < 0
  · have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    have hgc0 : g - algebraMap K F c ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h] at hg
      rcases eq_or_ne c 0 with rfl | hc
      · simp at hg
      · rw [ConstantReduction.ord_algebraMap W hc] at hg
        exact lt_irrefl _ hg
    have hv : W.adicValuation (-(algebraMap K F c)) < W.adicValuation g := by
      rw [Valuation.map_neg, W.adicValuation_eq_exp_neg_ord hg0]
      refine lt_of_le_of_lt (W.adicValuation_algebraMap_le_one c) ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have h1 := Valuation.map_add_eq_of_lt_left _ hv
    rw [← sub_eq_add_neg, W.adicValuation_eq_exp_neg_ord hgc0, W.adicValuation_eq_exp_neg_ord hg0] at h1
    have h2 : W.ord (g - algebraMap K F c) = W.ord g := by
      have := WithZero.exp_injective h1
      omega
    rw [h2]
  · push_neg at hg
    have h1 : 0 ≤ W.ord (g - algebraMap K F c) := by
      rcases eq_or_ne g 0 with rfl | hg0
      · rw [zero_sub, ← map_neg]
        rcases eq_or_ne c 0 with rfl | hc
        · simp
        · rw [ConstantReduction.ord_algebraMap W (neg_ne_zero.mpr hc)]
      · exact W.ord_nonneg_of_mem (sub_mem (W.mem_of_ord_nonneg hg0 hg) (W.algebraMap_mem' c))
    rw [max_eq_right (by omega), max_eq_right (by omega)]

private theorem arithGalois_smul_jFunNq (N q : ℕ) [NeZero N] [NeZero q]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull (N * q)) σ •
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q)) :=
  Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact coeffMap_coeffEmb σ jq)

private theorem H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ (v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) (c : ResidueField A),
          0 < v.ord
              (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) →
            0 < (frobOnPlacesGeomLevel (ResidueField A) N data hKr v).ord
                (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                      (c ^ q)) := by
  intro W hW data hKr hα hβ P v c h
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : CharP (modularFunctionFieldC (ResidueField A) N) q :=
    charP_of_injective_algebraMap
      (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)).injective q
  have hperf : ∀ x : ResidueField A, ∃ d : ResidueField A, d ^ q = x := fun x =>
    IsAlgClosed.exists_pow_nat_eq x hq.pos
  have hg : frobeniusGeomLevel (ResidueField A) N data hKr ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) (c ^ q))
      = ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) ^ q := by
    rw [map_sub, frobeniusGeomLevel_jq, (frobeniusGeomLevel (ResidueField A) N data hKr).commutes,
      sub_pow_char, map_pow]
  have heq := ord_frobOnPlaces_of_pow_eq (ResidueField A) N data hKr hperf hg v
  rw [heq]
  exact h

private theorem H2Recon.n3_isStrictFst_or_isStrictSnd_of_frobSq_ne
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst W)) ≠ P.reduceFst W →
            P.IsStrictFst W ∨ P.IsStrictSnd W := by
  intro W hW data hKr hα hβ P W' h
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  rcases P.d1 W' with hrel | hrel
  · have hrel' : P.reduceFst W' =
        frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceSnd W') := hrel
    refine Or.inr ⟨hrel', fun heq => h ?_⟩
    rw [hrel', heq]
  · have hrel' : frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst W') =
        P.reduceSnd W' := hrel
    exact Or.inl ⟨hrel', h⟩

private theorem H2Recon.n1_reduceFst_ord_pos_of_ord_pos_jFun_sub
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (a : A),
          0 < W.ord
              (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                    (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
                    (a : AlgebraicClosure ℚ)) →
            0 < (P.reduceFst W).ord
                (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩
                  - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
                      (IsLocalRing.residue A a)) := by
  intro W hW data hKr hα hβ P W' a hpos
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have htrans : heckeAlphaBar (AlgebraicClosure ℚ) N q
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
    rw [map_sub]
    congr 1
  have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W'
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
  rw [htrans] at hord
  rw [hord] at hpos
  have hre : 0 < (W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
    by_contra hle
    push_neg at hle
    have h0 : (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) W' : ℤ) *
        (W'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
          ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle
    omega
  exact P.d0_j _ a hre

open H2Recon in

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀) := by
  intro W hW data hKr hα hβ P T
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  have hc2 : 1 < q ^ 2 := by
    have := hq.two_le
    nlinarith
  set Tφ := T ∪ T.image (frobOnPlacesGeomLevel (ResidueField A) N data hKr) with hTφ
  set badT := Tφ.image (fun t => jval t) with hbadT
  set bad := (((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial (ResidueField A)).roots).toFinset
      ∪ badT) ∪ badT.preimage (frobenius (ResidueField A) q) (frobenius_inj (ResidueField A) q).injOn
    with hbad
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset bad
  rw [hbad] at hc
  simp only [Finset.mem_union, not_or] at hc
  obtain ⟨⟨hc_fixed, hc_badT⟩, hc_pre⟩ := hc
  have hc_pow : c ^ (q ^ 2) ≠ c := by
    intro h
    apply hc_fixed
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero
      (ResidueField A) hc2)]
    simp [h]
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := A) c
  set f : ↥(modularFunctionFieldBar (N * q)) := (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
    with hf_def

  have hjpole : ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q))) ∉ (cuspInftyBar (N * q)).toValuationSubring := by
    rw [cuspInftyBar_toValuationSubring, mem_qIntegersBar_iff, not_le]
    show (coeffEmb (AlgebraicClosure ℚ) jq).order < 0
    rw [order_coeffEmb_jq]
    norm_num
  have hfpole : f ∉ (cuspInftyBar (N * q)).toValuationSubring := by
    intro h
    apply hjpole
    have h' := add_mem h ((cuspInftyBar (N * q)).algebraMap_mem' (a : AlgebraicClosure ℚ))
    rwa [hf_def, sub_add_cancel] at h'
  have hf0 : f ≠ 0 := fun h => hfpole (h ▸ zero_mem _)
  have hford : (cuspInftyBar (N * q)).ord f < 0 := by
    by_contra hge
    push_neg at hge
    exact hfpole ((cuspInftyBar (N * q)).mem_of_ord_nonneg hf0 hge)
  obtain ⟨Df, hDf, hDfdeg⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)).exists_divisor f hf0
  set E₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    Df.mapRange (fun n => max n 0) (by simp) with hE₀def
  set C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    Df.mapRange (fun n => max (-n) 0) (by simp) with hC₀def
  have hE₀ : ∀ V, E₀ V = max (V.ord f) 0 := fun V => by
    simp only [hE₀def, Finsupp.mapRange_apply, hDf V]
  have hC₀ : ∀ V, C₀ V = max (-(V.ord f)) 0 := fun V => by
    simp only [hC₀def, Finsupp.mapRange_apply, hDf V]

  have hpin : ∀ V ∈ E₀.support,
      0 < (P.reduceFst V).ord ((⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ : modularFunctionFieldC (ResidueField A) N) - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N) c) := by
    intro V hV
    have hpos : 0 < V.ord f := by
      have h := Finsupp.mem_support_iff.mp hV
      rw [hE₀] at h
      by_contra hle
      push_neg at hle
      exact h (max_eq_right (by omega))
    have := H2Recon.n1_reduceFst_ord_pos_of_ord_pos_jFun_sub
      N q hq hqN A hA W hW data hKr hα hβ P V a (by rw [← hf_def]; exact hpos)
    rwa [ha] at this

  have hgood : P.IsGoodDiv E₀ := by
    intro V hV
    have h1 := hpin V hV
    by_cases hfix : frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V)) = P.reduceFst V
    · exfalso
      have h2 := H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
        N q hq hqN A hA W hW data hKr hα hβ P (P.reduceFst V) c h1
      have h3 := H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
        N q hq hqN A hA W hW data hKr hα hβ P (frobOnPlacesGeomLevel (ResidueField A) N data hKr (P.reduceFst V)) (c ^ q) h2
      rw [hfix, ← pow_mul, ← sq] at h3
      exact hc_pow (sep_ord_pos (P.reduceFst V) h3 h1)
    · exact H2Recon.n3_isStrictFst_or_isStrictSnd_of_frobSq_ne
        N q hq hqN A hA W hW data hKr hα hβ P V hfix
  refine ⟨E₀, C₀, fun V => by rw [hE₀]; exact le_max_right _ _, hgood, ?_, ?_,
    fun V => by rw [hC₀]; exact le_max_right _ _, ?_, ?_, ?_⟩
  ·
    intro V hV
    have h1 := hpin V hV
    constructor
    · intro hmem
      apply hc_badT
      rw [hbadT]
      refine Finset.mem_image.mpr ⟨P.reduceFst V, ?_, jval_eq _ h1⟩
      rw [hTφ]
      exact Finset.mem_union_left _ hmem
    · intro hmem
      rcases hgood V hV with hs1 | hs2
      ·
        have h2 := H2Recon.n2_frobOnPlacesGeomLevel_ord_pos_pow
          N q hq hqN A hA W hW data hKr hα hβ P (P.reduceFst V) c h1
        rw [hs1.1] at h2
        apply hc_pre
        rw [Finset.mem_preimage]
        have : jval (P.reduceSnd V) = c ^ q := jval_eq _ h2
        rw [frobenius_def, ← this, hbadT]
        refine Finset.mem_image.mpr ⟨P.reduceSnd V, ?_, rfl⟩
        rw [hTφ]
        exact Finset.mem_union_left _ hmem
      ·
        apply hc_badT
        rw [hbadT]
        refine Finset.mem_image.mpr ⟨P.reduceFst V, ?_, jval_eq _ h1⟩
        rw [hTφ, hs2.1]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨P.reduceSnd V, hmem, rfl⟩)
  ·
    have hdegC : 0 < Divisor.degree C₀ := by
      have hcusp : 0 < C₀ (cuspInftyBar (N * q)) := by
        rw [hC₀]
        exact lt_max_of_lt_left (by omega)
      have hmem : cuspInftyBar (N * q) ∈ C₀.support := Finsupp.mem_support_iff.mpr hcusp.ne'
      have hsum : Divisor.degree C₀ = ∑ v ∈ C₀.support, C₀ v := by
        show (Finsupp.liftAddHom _) C₀ = _
        rw [Finsupp.liftAddHom_apply, Finsupp.sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        show C₀ v * ((v.deg : ℕ) : ℤ) = C₀ v
        rw [deg_eq_one_modularFunctionFieldBar (N * q) v]
        simp
      rw [hsum]
      exact lt_of_lt_of_le hcusp
        (Finset.single_le_sum (fun v _ => by rw [hC₀]; exact le_max_right _ _) hmem)
    have hEC : E₀ - C₀ = Df := Finsupp.ext fun V => by
      simp only [Finsupp.coe_sub, Pi.sub_apply, hE₀, hC₀, hDf V]
      omega
    have h1 : (E₀ - C₀).degree = 0 := by rw [hEC]; exact hDfdeg
    rw [map_sub] at h1
    linarith
  ·
    intro σ _
    ext V
    rw [SemilinearAut.divisor_smul_apply, hC₀, hC₀]
    have h1 : ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ)⁻¹ • V).ord f
        = V.ord ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ) • f) := by
      have h := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull (N * q)) σ)
        ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ)⁻¹ • V) f
      rw [smul_inv_smul] at h
      exact h.symm
    have h2 : (arithmeticGalois (modularFunctionFieldFull (N * q)) σ) • f
        = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (N * q) (jq_mem (N * q)))⟩ : modularFunctionFieldBar (N * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (σ (a : AlgebraicClosure ℚ)) := by
      rw [hf_def, SemilinearAut.smul_def, map_sub, ← SemilinearAut.smul_def,
        ← SemilinearAut.smul_def, arithGalois_smul_jFunNq, SemilinearAut.smul_algebraMap]
      rfl
    rw [h1, h2, negOrd_sub_algebraMap_eq, hf_def, negOrd_sub_algebraMap_eq]
  ·
    have hcusp : 0 < C₀ (cuspInftyBar (N * q)) := by
      rw [hC₀]
      exact lt_max_of_lt_left (by omega)
    have hmem : cuspInftyBar (N * q) ∈ C₀.support := Finsupp.mem_support_iff.mpr hcusp.ne'
    have hsum : Divisor.degree C₀ = ∑ v ∈ C₀.support, C₀ v := by
      show (Finsupp.liftAddHom _) C₀ = _
      rw [Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      show C₀ v * ((v.deg : ℕ) : ℤ) = C₀ v
      rw [deg_eq_one_modularFunctionFieldBar (N * q) v]
      simp
    rw [hsum]
    exact lt_of_lt_of_le hcusp
      (Finset.single_le_sum (fun v _ => by rw [hC₀]; exact le_max_right _ _) hmem)
  ·
    exact ⟨f, hf0, fun V => by
      simp only [Finsupp.coe_sub, Pi.sub_apply, hE₀, hC₀]
      omega⟩

#print axioms solution

end S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq (solution)
