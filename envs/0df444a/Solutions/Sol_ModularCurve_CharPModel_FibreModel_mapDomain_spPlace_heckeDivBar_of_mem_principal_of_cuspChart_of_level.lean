-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/68567007-0ddc-57c7-b3b6-e417800da31f

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_modularPolynomialData
import Theorems.Thm_ModularCurve_kroneckerCongruence_norm_heckeBetaBar
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_injective~jBar ModularCurve.CharPModel AlgebraicCurve Polynomial"

noncomputable section

namespace Sol637

local notation "ℚbar" => AlgebraicClosure ℚ

section LegOne

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private scoped instance charZero_modularFunctionFieldBar : CharZero (modularFunctionFieldBar N) :=
  charZero_of_injective_algebraMap
    (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective

private theorem separableAlong_heckeAlphaBar (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) :
    SeparableAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) := by
  unfold SeparableAlong
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
  haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) halpha
  exact Algebra.IsSeparable.of_integral _ _

private theorem heckeDivBar_apply_eq_ord (data : ModularPolynomialData ℓ)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    {G : modularFunctionFieldBar N} (hG : G ≠ 0)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hD : ∀ v, D v = v.ord G) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    heckeDivBar halpha hbeta D v =
      v.ord (letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
        Algebra.norm (modularFunctionFieldBar N) (heckeBetaBar (AlgebraicClosure ℚ) N ℓ G)) := by
  have hfin := finiteAlong_heckeAlphaBar_of_modularPolynomialData (AlgebraicClosure ℚ) data
    Fact.out N
  have hNF := AlgebraicCurve.normFormulaAlong_of_separableAlong
    (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hfin (separableAlong_heckeAlphaBar N ℓ halpha)
  have hpull : ∀ w, Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hbeta D w
      = w.ord (heckeBetaBar (AlgebraicClosure ℚ) N ℓ G) := by
    intro w
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
    haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
    haveI := isIntegral_along _ hbeta
    exact Divisor.pullback_apply_eq_ord hD w
  rw [heckeDivBar, Divisor.correspondence_apply]
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
  haveI := isIntegral_along _ halpha
  haveI : Module.Finite (modularFunctionFieldBar N)
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))) := hfin
  exact hNF _ (by simpa using hG) _ hpull v

end LegOne

section Transport

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  {k : Type*} [Field k] [CharP k ℓ] (red : A →+* k) (hred : Function.Surjective red)

include hred in
private theorem ker_red_eq : RingHom.ker red = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)

private def resEquiv : IsLocalRing.ResidueField A ≃+* k :=
  (Ideal.quotEquivOfEq (ker_red_eq A red hred).symm).trans
    (RingHom.quotientKerEquivOfSurjective hred)

private theorem resEquiv_residue (a : A) :
    resEquiv A red hred (IsLocalRing.residue A a) = red a := rfl

private theorem resEquiv_comp_residue :
    ((resEquiv A red hred : IsLocalRing.ResidueField A →+* k)).comp
      (IsLocalRing.residue A) = red :=
  RingHom.ext fun a => resEquiv_residue A red hred a

omit [Fact ℓ.Prime] in
include hred in
private theorem charP_residueField : CharP (IsLocalRing.ResidueField A) ℓ := by
  exact charP_of_injective_ringHom
    (f := ((resEquiv A red hred).symm : k →+* IsLocalRing.ResidueField A))
    (resEquiv A red hred).symm.injective ℓ

private theorem coeffMap_red (y : LaurentSeries A) :
    coeffMap red y = coeffMap (resEquiv A red hred : IsLocalRing.ResidueField A →+* k)
      (coeffMap (IsLocalRing.residue A) y) := by
  rw [coeffMap_coeffMap, coeffMap_congr (resEquiv_comp_residue A red hred)]

private theorem coeffMap_resEquiv_frobenius (hch : CharP (IsLocalRing.ResidueField A) ℓ)
    (x : LaurentSeries (IsLocalRing.ResidueField A)) :
    coeffMap (resEquiv A red hred : IsLocalRing.ResidueField A →+* k)
        (coeffMap (frobenius (IsLocalRing.ResidueField A) ℓ) x)
      = coeffMap (frobenius k ℓ)
          (coeffMap (resEquiv A red hred : IsLocalRing.ResidueField A →+* k) x) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  refine coeffMap_congr (RingHom.ext fun a => ?_) x
  simp only [RingHom.comp_apply, frobenius_def, RingHom.coe_coe, map_pow]

include hred in

private theorem kronecker_red (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N)
    (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    ∃ y' : LaurentSeries A, coeffMap A.subtype y' =
      ((letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
        Algebra.norm (modularFunctionFieldBar N)
          (heckeBetaBar (AlgebraicClosure ℚ) N ℓ ⟨coeffMap A.subtype y, hy⟩) :
            modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap red y' = coeffMap (frobenius k ℓ) (coeffMap red y) *
        qExpand k ℓ (coeffMap red y) := by
  haveI := charP_residueField A red hred
  obtain ⟨y', h1, h2⟩ := kroneckerCongruence_norm_heckeBetaBar N hℓN A y hy
  refine ⟨y', h1, ?_⟩
  rw [coeffMap_red A red hred, coeffMap_red A red hred y, h2, map_mul,
    coeffMap_resEquiv_frobenius A red hred inferInstance, ModularCurve.coeffMap_qExpand]

omit [CharP k ℓ] in
include hred in

private theorem perfect_red : ∀ c : k, ∃ d : k, d ^ ℓ = c := by
  intro c
  obtain ⟨a, rfl⟩ := hred c
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure ℚ)
    (Fact.out : ℓ.Prime).pos
  have hbA : b ∈ A := ValuationSubring.mem_of_pow_mem' A (Fact.out : ℓ.Prime).pos.ne'
    (hb ▸ a.2)
  refine ⟨red ⟨b, hbA⟩, ?_⟩
  rw [← map_pow]
  congr 1
  exact Subtype.ext hb

end Transport

section LegThree

variable (k : Type*) [Field k] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

include data hKr in

private theorem coeffMap_frobenius_mem_and_qExpand {x : LaurentSeries k}
    (hx : x ∈ modularFunctionFieldC k N) :
    coeffMap (frobenius k ℓ) x ∈ modularFunctionFieldC k N ∧
      qExpand k ℓ (coeffMap (frobenius k ℓ) x) = x ^ ℓ := by
  haveI : CharP (LaurentSeries k) ℓ := charP_laurentSeries k
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [coeffSemilinearAut.coeffMap_jqModC]
      exact ⟨jqModC_mem k N, qExpand_jqModC_eq_pow k data hKr⟩
    · rw [coeffSemilinearAut.coeffMap_jqNModC]
      exact ⟨jqNModC_mem k N, qExpand_jqNModC_eq_pow k N data hKr⟩
  | algebraMap c =>
    rw [coeffMap_algebraMap]
    refine ⟨(modularFunctionFieldC k N).algebraMap_mem _, ?_⟩
    rw [frobenius_def, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single,
      qExpand_single, mul_zero, HahnSeries.single_pow, smul_zero]
  | add y z _ _ hy hz =>
    rw [map_add, map_add, add_pow_char, hy.2, hz.2]
    exact ⟨add_mem hy.1 hz.1, rfl⟩
  | inv y _ hy =>
    rw [map_inv₀, map_inv₀, hy.2, inv_pow]
    exact ⟨inv_mem hy.1, rfl⟩
  | mul y z _ _ hy hz =>
    rw [map_mul, map_mul, mul_pow, hy.2, hz.2]
    exact ⟨mul_mem hy.1 hz.1, rfl⟩

include data hKr in
private theorem coeffMap_frobenius_mul_qExpand_mem {x : LaurentSeries k}
    (hx : x ∈ modularFunctionFieldC k N) :
    coeffMap (frobenius k ℓ) x * qExpand k ℓ x ∈ modularFunctionFieldC k N :=
  mul_mem (coeffMap_frobenius_mem_and_qExpand k N data hKr hx).1
    (by simpa only [frobeniusGeomLevel_apply_coe] using (frobeniusGeomLevel k N data hKr ⟨x, hx⟩).2)

private theorem heckeFibreGeomLevel_apply_eq_ord (hperf : ∀ c : k, ∃ d : k, d ^ ℓ = c)
    {f : modularFunctionFieldC k N} (hf : f ≠ 0)
    {E : Divisor k (modularFunctionFieldC k N)} (hE : ∀ w, E w = w.ord f)
    (hmem : coeffMap (frobenius k ℓ) (f : LaurentSeries k) * qExpand k ℓ (f : LaurentSeries k)
      ∈ modularFunctionFieldC k N)
    (v : Place k (modularFunctionFieldC k N)) :
    heckeFibreGeomLevel k N data hKr E v =
      v.ord (⟨coeffMap (frobenius k ℓ) (f : LaurentSeries k) * qExpand k ℓ (f : LaurentSeries k),
        hmem⟩ : modularFunctionFieldC k N) := by
  obtain ⟨hgmem, hgq⟩ := coeffMap_frobenius_mem_and_qExpand k N data hKr f.2
  set g : modularFunctionFieldC k N := ⟨coeffMap (frobenius k ℓ) (f : LaurentSeries k), hgmem⟩
    with hg_def
  have hg : frobeniusGeomLevel k N data hKr g = f ^ ℓ := by
    refine Subtype.ext ?_
    rw [frobeniusGeomLevel_apply_coe]
    push_cast
    exact hgq
  have hg0 : g ≠ 0 := by
    intro h0
    apply pow_ne_zero ℓ hf
    rw [← hg, h0, map_zero]
  have hFf0 : frobeniusGeomLevel k N data hKr f ≠ 0 :=
    (map_ne_zero_iff _ (frobeniusGeomLevel_injective k N data hKr)).mpr hf
  have key : heckeFibreGeomLevel k N data hKr E
      = frobeniusPushforwardGeomLevel k N data hKr E
        + frobeniusPullbackGeomLevel k N data hKr E := rfl
  rw [key, Finsupp.add_apply, frobeniusPushforwardGeomLevel_normFormula' k N data hKr hperf hg hE,
    frobeniusPullbackGeomLevel_pullbackFormula k N data hKr hperf
      (frobOnPlacesGeomLevel_surjective k N data hKr hperf) hE,
    ← Place.ord_mul _ hg0 hFf0]
  congr 1

end LegThree

section Eval

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

private def ev₂ (φ : R →+* S) (a b : S) : (Polynomial (Polynomial R)) →+* S :=
  eval₂RingHom (eval₂RingHom φ a) b

omit [CommRing T] in
private theorem ev₂_C_C (φ : R →+* S) (a b : S) (r : R) : ev₂ φ a b (C (C r)) = φ r := by
  simp [ev₂]

omit [CommRing T] in
private theorem ev₂_C_X (φ : R →+* S) (a b : S) : ev₂ φ a b (C (X : Polynomial R)) = a := by
  simp [ev₂]

omit [CommRing T] in
private theorem ev₂_X (φ : R →+* S) (a b : S) : ev₂ φ a b (X : Polynomial (Polynomial R)) = b := by
  simp [ev₂]

private theorem map_ev₂ (φ : R →+* S) (a b : S) (g : S →+* T) (P : (Polynomial (Polynomial R))) :
    g (ev₂ φ a b P) = ev₂ (g.comp φ) (g a) (g b) P := by
  simp only [ev₂, coe_eval₂RingHom]
  rw [hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp
  · simp

private theorem ev₂_map (f : R →+* S) (φ : S →+* T) (a b : T) (P : (Polynomial (Polynomial R))) :
    ev₂ φ a b (P.map (mapRingHom f)) = ev₂ (φ.comp f) a b P := by
  simp only [ev₂, coe_eval₂RingHom]
  rw [eval₂_map]
  congr 1
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp
  · simp

variable (R) in

private def evJ (N : ℕ) [NeZero N] : (Polynomial (Polynomial R)) →+* LaurentSeries R :=
  ev₂ HahnSeries.C (jqModC R) (jqNModC R N)

omit [CommRing T] in

private theorem coeffMap_evJ (f : R →+* S) (N : ℕ) [NeZero N] (P : (Polynomial (Polynomial R))) :
    coeffMap f (evJ R N P) = evJ S N (P.map (mapRingHom f)) := by
  have hφ : (coeffMap f).comp (HahnSeries.C : R →+* LaurentSeries R)
      = (HahnSeries.C : S →+* LaurentSeries S).comp f := by
    ext r : 1
    simp
  rw [evJ, evJ, map_ev₂, ev₂_map, coeffSemilinearAut.coeffMap_jqModC,
    coeffSemilinearAut.coeffMap_jqNModC, hφ]

end Eval

section EvalFields

variable (N : ℕ) [NeZero N]

private theorem coe_jBar : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  exact coeffSemilinearAut.coeffMap_jqModC _

private theorem coe_jNBar : ((jNBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) N := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ N) = _
  exact coeffSemilinearAut.coeffMap_jqNModC _ N

private def evF : (Polynomial (Polynomial (AlgebraicClosure ℚ))) →+* modularFunctionFieldBar N :=
  ev₂ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (jBar N) (jNBar N)

private theorem coe_evF (P : (Polynomial (Polynomial (AlgebraicClosure ℚ)))) :
    ((evF N P : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = evJ (AlgebraicClosure ℚ) N P := by
  have h := map_ev₂ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (jBar N)
    (jNBar N) ((modularFunctionFieldBar N).val : modularFunctionFieldBar N →+*
      LaurentSeries (AlgebraicClosure ℚ)) P
  rw [evF]
  refine h.trans ?_
  rw [evJ]
  have hj : ((modularFunctionFieldBar N).val : modularFunctionFieldBar N →+*
      LaurentSeries (AlgebraicClosure ℚ)) (jBar N) = jqModC (AlgebraicClosure ℚ) := coe_jBar N
  have hjN : ((modularFunctionFieldBar N).val : modularFunctionFieldBar N →+*
      LaurentSeries (AlgebraicClosure ℚ)) (jNBar N) = jqNModC (AlgebraicClosure ℚ) N := coe_jNBar N
  rw [hj, hjN]
  have hφ : ((modularFunctionFieldBar N).val : modularFunctionFieldBar N →+*
      LaurentSeries (AlgebraicClosure ℚ)).comp
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = HahnSeries.C := by
    ext c : 1
    simp [algebraMap_laurentSeries_eq_single]
  rw [hφ]

variable (k : Type*) [Field k]

private def evC : (Polynomial (Polynomial k)) →+* modularFunctionFieldC k N :=
  ev₂ (algebraMap k (modularFunctionFieldC k N)) ⟨jqModC k, jqModC_mem k N⟩
    ⟨jqNModC k N, jqNModC_mem k N⟩

private theorem coe_evC (P : (Polynomial (Polynomial k))) :
    ((evC N k P : modularFunctionFieldC k N) : LaurentSeries k) = evJ k N P := by
  have h := map_ev₂ (algebraMap k (modularFunctionFieldC k N)) ⟨jqModC k, jqModC_mem k N⟩
    ⟨jqNModC k N, jqNModC_mem k N⟩
    ((modularFunctionFieldC k N).val : modularFunctionFieldC k N →+* LaurentSeries k) P
  rw [evC]
  refine h.trans ?_
  rw [evJ]
  have hj : ((modularFunctionFieldC k N).val : modularFunctionFieldC k N →+* LaurentSeries k)
      ⟨jqModC k, jqModC_mem k N⟩ = jqModC k := rfl
  have hjN : ((modularFunctionFieldC k N).val : modularFunctionFieldC k N →+* LaurentSeries k)
      ⟨jqNModC k N, jqNModC_mem k N⟩ = jqNModC k N := rfl
  rw [hj, hjN]
  have hφ : ((modularFunctionFieldC k N).val : modularFunctionFieldC k N →+*
      LaurentSeries k).comp (algebraMap k (modularFunctionFieldC k N)) = HahnSeries.C := by
    ext c : 1
    simp [algebraMap_laurentSeries_eq_single]
  rw [hφ]

private theorem evF_map_Phi (dN : ModularPolynomialData N) :
    evF N (dN.Φ.map (mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))) = 0 := by
  have h0 := dN.eval_eq_zero

  have h1 : dN.Φ.eval₂ evalAtJ (jqN N)
      = evJ ℚ N (dN.Φ.map (mapRingHom (Int.castRingHom ℚ))) := by
    rw [evJ, ev₂_map, ev₂, coe_eval₂RingHom]
    congr 1
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp [evalAtJ_X, jqModC_rat]

  have h2 : coeffMap (algebraMap ℚ (AlgebraicClosure ℚ))
      (evJ ℚ N (dN.Φ.map (mapRingHom (Int.castRingHom ℚ))))
        = evJ (AlgebraicClosure ℚ) N
          (dN.Φ.map (mapRingHom (Int.castRingHom (AlgebraicClosure ℚ)))) := by
    rw [coeffMap_evJ, Polynomial.map_map]
    congr 2
    ext1
    · exact RingHom.ext_int _ _
    · simp
  apply Subtype.ext
  rw [coe_evF, ← h2, ← h1, h0, map_zero]
  rfl

end EvalFields

section Nonvanishing

variable (k : Type*) [Field k] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]

private theorem evJ_ne_zero_of_natDegree_lt (hℓN : ¬ ℓ ∣ N) {P : Polynomial (Polynomial k)}
    (hP : P ≠ 0) (hdeg : P.natDegree < dedekindPsi N) : evJ k N P ≠ 0 := by
  intro hzero
  have hle : IntermediateField.adjoin k {jqModC k} ≤ modularFunctionFieldC k N :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem k N))

  have hJt : Transcendental k (⟨jqModC k, IntermediateField.mem_adjoin_simple_self k _⟩ :
      IntermediateField.adjoin k {jqModC k}) := by
    have h := transcendental_jqModC k
    have e : (algebraMap (IntermediateField.adjoin k {jqModC k}) (LaurentSeries k))
        ⟨jqModC k, IntermediateField.mem_adjoin_simple_self k _⟩ = jqModC k := rfl
    rw [← e] at h
    exact (transcendental_algebraMap_iff
      (algebraMap (IntermediateField.adjoin k {jqModC k}) (LaurentSeries k)).injective).mp h
  have hφ := transcendental_iff_injective.mp hJt

  have hP₁0 : P.map (Polynomial.aeval (R := k) (⟨jqModC k,
      IntermediateField.mem_adjoin_simple_self k _⟩ :
        IntermediateField.adjoin k {jqModC k})).toRingHom ≠ 0 :=
    fun h => hP ((Polynomial.map_eq_zero_iff (f := (Polynomial.aeval (R := k) (⟨jqModC k,
      IntermediateField.mem_adjoin_simple_self k _⟩ :
        IntermediateField.adjoin k {jqModC k})).toRingHom) hφ).mp h)
  have hP₁deg : (P.map (Polynomial.aeval (R := k) (⟨jqModC k,
      IntermediateField.mem_adjoin_simple_self k _⟩ :
        IntermediateField.adjoin k {jqModC k})).toRingHom).natDegree < dedekindPsi N :=
    (natDegree_map_le ..).trans_lt hdeg
  have heval : Polynomial.aeval (R := IntermediateField.adjoin k {jqModC k}) (jqNModC k N)
      (P.map (Polynomial.aeval (R := k) (⟨jqModC k,
        IntermediateField.mem_adjoin_simple_self k _⟩ :
          IntermediateField.adjoin k {jqModC k})).toRingHom)
      = evJ k N P := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, evJ, ev₂, coe_eval₂RingHom]
    congr 1
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_C]
      rw [← IsScalarTower.algebraMap_apply, algebraMap_laurentSeries_eq_single]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  rw [hzero] at heval
  have halg : IsAlgebraic (IntermediateField.adjoin k {jqModC k}) (jqNModC k N) :=
    ⟨_, hP₁0, heval⟩
  have hint : IsIntegral (IntermediateField.adjoin k {jqModC k}) (jqNModC k N) :=
    halg.isIntegral

  have hψ : (minpoly (IntermediateField.adjoin k {jqModC k}) (jqNModC k N)).natDegree
      = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint,
      ← relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N ℓ hℓN,
      IntermediateField.relfinrank_eq_finrank_of_le hle]
    have hext : IntermediateField.extendScalars hle
        = IntermediateField.adjoin (IntermediateField.adjoin k {jqModC k}) {jqNModC k N} := by
      apply IntermediateField.restrictScalars_injective k
      show modularFunctionFieldC k N = _
      exact (IntermediateField.adjoin_simple_adjoin_simple k (jqModC k) (jqNModC k N)).symm
    rw [hext]
  have hmin := minpoly.degree_le_of_ne_zero (IntermediateField.adjoin k {jqModC k})
    (jqNModC k N) hP₁0 heval
  have := natDegree_le_natDegree hmin
  omega

end Nonvanishing

section Repr

variable (N : ℕ) [NeZero N]

private theorem exists_evF_repr (G : modularFunctionFieldBar N) :
    ∃ p q : Polynomial (Polynomial ℚbar), evF N q ≠ 0 ∧ G * evF N q = evF N p := by
  have hG : G ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange _ (jq_mem_full N)⟩,
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange _ (jqd_mem_full N (dvd_refl N))⟩} :
        Set (modularFunctionFieldBar N)) := by
    rw [adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N]; trivial
  induction hG using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · refine ⟨C X, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [map_one, mul_one]
      exact (ev₂_C_X _ _ _).symm
    · refine ⟨X, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [map_one, mul_one]
      exact (ev₂_X _ _ _).symm
  | algebraMap c =>
    refine ⟨C (C c), 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one]
    exact (ev₂_C_C _ _ _ _).symm
  | add x y _ _ hx hy =>
    obtain ⟨p₁, q₁, hq₁, h₁⟩ := hx
    obtain ⟨p₂, q₂, hq₂, h₂⟩ := hy
    refine ⟨p₁ * q₂ + p₂ * q₁, q₁ * q₂, by rw [map_mul]; exact mul_ne_zero hq₁ hq₂, ?_⟩
    rw [map_mul, map_add, map_mul, map_mul, ← h₁, ← h₂]; ring
  | inv x _ hx =>
    obtain ⟨p, q, hq, h⟩ := hx
    by_cases hx0 : x = 0
    · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [hx0, inv_zero, zero_mul, map_zero]
    · refine ⟨q, p, ?_, ?_⟩
      · rw [← h]; exact mul_ne_zero hx0 hq
      · rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, q₁, hq₁, h₁⟩ := hx
    obtain ⟨p₂, q₂, hq₂, h₂⟩ := hy
    refine ⟨p₁ * p₂, q₁ * q₂, by rw [map_mul]; exact mul_ne_zero hq₁ hq₂, ?_⟩
    rw [map_mul, map_mul, ← h₁, ← h₂]; ring

private theorem exists_evF_repr_lt (dN : ModularPolynomialData N) (G : modularFunctionFieldBar N) :
    ∃ p q : Polynomial (Polynomial ℚbar), q ≠ 0 ∧ p.natDegree < dedekindPsi N ∧
      q.natDegree < dedekindPsi N ∧ evF N q ≠ 0 ∧ G * evF N q = evF N p := by
  obtain ⟨p, q, hq, h⟩ := exists_evF_repr N G
  have hmon : (dN.Φ.map (mapRingHom (Int.castRingHom ℚbar))).Monic := dN.monic.map _
  have hΦ0 : evF N (dN.Φ.map (mapRingHom (Int.castRingHom ℚbar))) = 0 := evF_map_Phi N dN
  have hΦ1 : dN.Φ.map (mapRingHom (Int.castRingHom ℚbar)) ≠ 1 := by
    intro h1
    rw [h1, map_one] at hΦ0
    exact one_ne_zero hΦ0
  have hdegΦ : (dN.Φ.map (mapRingHom (Int.castRingHom ℚbar))).natDegree = dedekindPsi N := by
    rw [dN.monic.natDegree_map, dN.natDegree_eq]
  have hev : ∀ r, evF N (r %ₘ dN.Φ.map (mapRingHom (Int.castRingHom ℚbar))) = evF N r := by
    intro r
    conv_rhs => rw [← modByMonic_add_div r (dN.Φ.map (mapRingHom (Int.castRingHom ℚbar)))]
    rw [map_add, map_mul, hΦ0, zero_mul, add_zero]
  refine ⟨p %ₘ dN.Φ.map (mapRingHom (Int.castRingHom ℚbar)),
    q %ₘ dN.Φ.map (mapRingHom (Int.castRingHom ℚbar)), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hq
    rw [← hev q, h0, map_zero]
  · rw [← hdegΦ]; exact natDegree_modByMonic_lt p hmon hΦ1
  · rw [← hdegΦ]; exact natDegree_modByMonic_lt q hmon hΦ1
  · rw [hev]; exact hq
  · rw [hev, hev]; exact h

variable (A : ValuationSubring ℚbar)

private theorem exists_lift₂ (P : Polynomial (Polynomial ℚbar)) (hP : ∀ i j, (P.coeff i).coeff j ∈ A) :
    ∃ P₀ : Polynomial (Polynomial A), P₀.map (mapRingHom A.subtype) = P := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro i
  have hi : P.coeff i ∈ Polynomial.lifts (A.subtype : A →+* ℚbar) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨_, hP i j⟩, rfl⟩
  obtain ⟨q, hq⟩ := (mem_lifts _).mp hi
  exact ⟨q, hq⟩

private theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simpa only [coeffMap_coeff] using this

variable {ℓ : ℕ} [Fact ℓ.Prime] (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)

private theorem exists_primitive (hℓN : ¬ ℓ ∣ N) {p : Polynomial (Polynomial ℚbar)} (hp : p ≠ 0)
    (hdeg : p.natDegree < dedekindPsi N) :
    ∃ (c : ℚbar) (y : LaurentSeries A), c ≠ 0 ∧
      coeffMap A.subtype y ∈ modularFunctionFieldBar N ∧
      coeffMap red y ∈ modularFunctionFieldC k N ∧ coeffMap red y ≠ 0 ∧
      ((evF N p : modularFunctionFieldBar N) : LaurentSeries ℚbar) =
        HahnSeries.C c * coeffMap A.subtype y := by
  classical

  obtain ⟨i₀, j₀, hc0, hcmax⟩ : ∃ i₀ j₀, (p.coeff i₀).coeff j₀ ≠ 0 ∧
      ∀ i j, A.valuation ((p.coeff i).coeff j) ≤ A.valuation ((p.coeff i₀).coeff j₀) := by
    have hTne : (p.support.biUnion fun i =>
        ((p.coeff i).support).image fun j => (p.coeff i).coeff j).Nonempty := by
      refine ⟨(p.coeff p.natDegree).coeff (p.coeff p.natDegree).natDegree, ?_⟩
      rw [Finset.mem_biUnion]
      exact ⟨p.natDegree, natDegree_mem_support_of_nonzero hp, Finset.mem_image.mpr
        ⟨_, natDegree_mem_support_of_nonzero
          (mem_support_iff.mp (natDegree_mem_support_of_nonzero hp)), rfl⟩⟩
    obtain ⟨c, hcT, hcmax⟩ := Finset.exists_max_image _ (fun d => A.valuation d) hTne
    rw [Finset.mem_biUnion] at hcT
    obtain ⟨i₀, -, hi₀⟩ := hcT
    obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.mp hi₀
    refine ⟨i₀, j₀, mem_support_iff.mp hj₀, fun i j => ?_⟩
    by_cases h0 : (p.coeff i).coeff j = 0
    · rw [h0, map_zero]; exact zero_le'
    · apply hcmax
      rw [Finset.mem_biUnion]
      have hi : p.coeff i ≠ 0 := fun h1 => h0 (by rw [h1, coeff_zero])
      exact ⟨i, mem_support_iff.mpr hi, Finset.mem_image.mpr ⟨j, mem_support_iff.mpr h0, rfl⟩⟩

  have hA : ∀ i j, ((C (C ((p.coeff i₀).coeff j₀)⁻¹) * p).coeff i).coeff j ∈ A := by
    intro i j
    rw [coeff_C_mul, coeff_C_mul, ← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    have hvc : 0 < A.valuation ((p.coeff i₀).coeff j₀) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0)
    exact (inv_mul_le_one₀ hvc).mpr (hcmax i j)
  obtain ⟨P₀, hP₀⟩ := exists_lift₂ A _ hA

  have hone : (P₀.coeff i₀).coeff j₀ = 1 := by
    have h := congrArg (fun P : Polynomial (Polynomial ℚbar) => (P.coeff i₀).coeff j₀) hP₀
    simp only [coeff_map, coe_mapRingHom, coeff_C_mul] at h
    rw [inv_mul_cancel₀ hc0] at h
    exact Subtype.ext (by simpa using h)

  have hred0 : P₀.map (mapRingHom red) ≠ 0 := by
    intro h0
    have h := congrArg (fun P : Polynomial (Polynomial k) => (P.coeff i₀).coeff j₀) h0
    simp only [coeff_map, coe_mapRingHom, hone, map_one, coeff_zero] at h
    exact one_ne_zero h
  have hinj : Function.Injective (mapRingHom (A.subtype : A →+* ℚbar)) :=
    fun a b h => map_injective _ Subtype.val_injective h
  have hdeg0 : (P₀.map (mapRingHom red)).natDegree < dedekindPsi N := by
    refine (natDegree_map_le ..).trans_lt ?_
    rw [← natDegree_map_eq_of_injective hinj P₀, hP₀]
    exact (natDegree_C_mul_le _ _).trans_lt hdeg
  refine ⟨(p.coeff i₀).coeff j₀, evJ A N P₀, hc0, ?_, ?_, ?_, ?_⟩
  · rw [coeffMap_evJ, hP₀, ← coe_evF]
    exact SetLike.coe_mem _
  · rw [coeffMap_evJ, ← coe_evC]
    exact SetLike.coe_mem _
  · rw [coeffMap_evJ]
    exact evJ_ne_zero_of_natDegree_lt k N ℓ hℓN hred0 hdeg0
  · rw [coeffMap_evJ, hP₀, map_mul, coe_evF, ← mul_assoc]
    have hCC : evJ ℚbar N (C (C ((p.coeff i₀).coeff j₀)⁻¹))
        = HahnSeries.C ((p.coeff i₀).coeff j₀)⁻¹ := ev₂_C_C _ _ _ _
    rw [hCC, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end Repr

section Core

variable (A : ValuationSubring ℚbar) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
  (hlN : ¬ ℓ ∣ N) (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
  (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
  (halpha : HeckeAlphaBarIntegral ℚbar N ℓ) (hbeta : HeckeBetaBarIntegral ℚbar N ℓ)
  [HasPrincipalDivisors ℚbar (laurentBaseChange ℚbar (modularFunctionFieldFull (N * ℓ)))]
  (hred : Function.Surjective red)
  (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
  (hsep : (((dataAll N (dvd_refl N)).Φ.map
      (Polynomial.mapRingHom (Int.castRingHom k))).map
    (algebraMap (Polynomial k) (RatFunc k))).Separable)
  (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)

include hlN cc in

private theorem core (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hyk : coeffMap red y ∈ modularFunctionFieldC k N) (hne : coeffMap red y ≠ 0)
    (Dy : Divisor ℚbar (modularFunctionFieldBar N))
    (hDy : ∀ v, Dy v = v.ord (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta Dy) =
      heckeFibreGeomLevel k N data hKr (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) Dy) := by

  have hy0 : coeffMap A.subtype y ≠ 0 := by
    intro h
    apply hne
    have : y = 0 := coeffMap_injective Subtype.val_injective (by rw [h, map_zero])
    rw [this, map_zero]
  have hY0 : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ≠ 0 :=
    fun h => hy0 (congrArg Subtype.val h)

  have hT := heckeDivBar_apply_eq_ord N ℓ data halpha hbeta hY0 hDy

  obtain ⟨y', h1, h2⟩ := kronecker_red A red hred N hlN y hy
  have hy' : coeffMap A.subtype y' ∈ modularFunctionFieldBar N := by
    rw [h1]; exact SetLike.coe_mem _
  have hyk' : coeffMap red y' ∈ modularFunctionFieldC k N := by
    rw [h2]; exact coeffMap_frobenius_mul_qExpand_mem k N data hKr hyk
  have hne' : coeffMap red y' ≠ 0 := by
    rw [h2]
    refine mul_ne_zero (fun h => hne ?_) (fun h => hne ?_)
    · exact coeffMap_injective (frobenius k ℓ).injective (by rw [h, map_zero])
    · exact qExpand_injective (R := k) (N := ℓ) (by rw [h, map_zero])

  have hL : ∀ Q, Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta Dy) Q
      = Q.ord (⟨coeffMap red y', hyk'⟩ : modularFunctionFieldC k N) := fun Q =>
    ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective N ℓ A k
      red hred hlN fm cc dataAll hsep y' hy' hyk' hne' _ (fun P => by
        rw [hT P]; congr 1; exact Subtype.ext h1.symm) Q
  have hE : ∀ w, Finsupp.mapDomain (fm.spPlace hred dataAll hsep) Dy w
      = w.ord (⟨coeffMap red y, hyk⟩ : modularFunctionFieldC k N) := fun w =>
    ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap_of_surjective N ℓ A k
      red hred hlN fm cc dataAll hsep y hy hyk hne Dy hDy w
  have hf0 : (⟨coeffMap red y, hyk⟩ : modularFunctionFieldC k N) ≠ 0 :=
    fun h => hne (congrArg Subtype.val h)
  ext Q
  rw [hL Q, heckeFibreGeomLevel_apply_eq_ord k N data hKr (perfect_red A red hred) hf0 hE
    (coeffMap_frobenius_mul_qExpand_mem k N data hKr hyk) Q]
  congr 1
  exact Subtype.ext h2

include hlN cc in

private theorem main (D : Divisor ℚbar (modularFunctionFieldBar N))
    (hD : D ∈ Divisor.principal (K := ℚbar) (F := modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) := by
  obtain ⟨G, hG0, hDG⟩ := hD

  obtain ⟨p, q, hq0, hpdeg, hqdeg, hevq, hGpq⟩ :=
    exists_evF_repr_lt N (dataAll N (dvd_refl N)) G
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hGpq
    exact mul_ne_zero hG0 hevq hGpq

  obtain ⟨c₁, y₁, hc₁, hy₁, hyk₁, hne₁, hev₁⟩ := exists_primitive N A k red hlN hp0 hpdeg
  obtain ⟨c₂, y₂, hc₂, hy₂, hyk₂, hne₂, hev₂⟩ := exists_primitive N A k red hlN hq0 hqdeg
  have hY0 : ∀ {y : LaurentSeries A} (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      coeffMap red y ≠ 0 → (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ≠ 0 := by
    intro y hy hne h
    apply hne
    have h' : coeffMap A.subtype y = 0 := congrArg Subtype.val h
    have : y = 0 := coeffMap_injective Subtype.val_injective (by rw [h', map_zero])
    rw [this, map_zero]
  have hY₁0 := hY0 hy₁ hne₁
  have hY₂0 := hY0 hy₂ hne₂

  obtain ⟨D₁, hD₁, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor _ hY₁0
  obtain ⟨D₂, hD₂, -⟩ :=
    (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor _ hY₂0

  have hcoe : ∀ c : ℚbar, ((algebraMap ℚbar (modularFunctionFieldBar N) c :
      modularFunctionFieldBar N) : LaurentSeries ℚbar) = HahnSeries.C c := fun c => by
    simp [algebraMap_laurentSeries_eq_single]
  have hE₁ : evF N p = algebraMap ℚbar (modularFunctionFieldBar N) c₁ *
      (⟨coeffMap A.subtype y₁, hy₁⟩ : modularFunctionFieldBar N) :=
    Subtype.ext (by rw [hev₁, MulMemClass.coe_mul, hcoe])
  have hE₂ : evF N q = algebraMap ℚbar (modularFunctionFieldBar N) c₂ *
      (⟨coeffMap A.subtype y₂, hy₂⟩ : modularFunctionFieldBar N) :=
    Subtype.ext (by rw [hev₂, MulMemClass.coe_mul, hcoe])
  have ha₁ : algebraMap ℚbar (modularFunctionFieldBar N) c₁ ≠ 0 := (_root_.map_ne_zero _).mpr hc₁
  have ha₂ : algebraMap ℚbar (modularFunctionFieldBar N) c₂ ≠ 0 := (_root_.map_ne_zero _).mpr hc₂
  rw [hE₁, hE₂] at hGpq

  have hDeq : D = D₁ - D₂ := by
    refine Finsupp.ext fun v => ?_
    have h := congrArg (Place.ord v) hGpq
    rw [Place.ord_mul _ hG0 (mul_ne_zero ha₂ hY₂0), Place.ord_mul _ ha₂ hY₂0,
      Place.ord_mul _ ha₁ hY₁0, Place.ord_algebraMap, Place.ord_algebraMap] at h
    rw [Finsupp.sub_apply, hDG v, hD₁ v, hD₂ v]
    omega
  have hmd : ∀ E₁ E₂ : Divisor ℚbar (modularFunctionFieldBar N),
      Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (E₁ - E₂) =
        Finsupp.mapDomain (fm.spPlace hred dataAll hsep) E₁ -
          Finsupp.mapDomain (fm.spPlace hred dataAll hsep) E₂ := fun E₁ E₂ =>
    map_sub (Finsupp.mapDomain.addMonoidHom (fm.spPlace hred dataAll hsep)) E₁ E₂
  rw [hDeq, map_sub, hmd, hmd, map_sub,
    core A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsep fm cc y₁ hy₁ hyk₁ hne₁ D₁ hD₁,
    core A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsep fm cc y₂ hy₂ hyk₂ hne₂ D₂ hD₂]

end Core

end Sol637
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level.Sol637"

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : D ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)) :
    Finsupp.mapDomain (fm.spPlace hred dataAll hsep) (heckeDivBar halpha hbeta D) =
      heckeFibreGeomLevel k N data hKr
        (Finsupp.mapDomain (fm.spPlace hred dataAll hsep) D) :=
  Sol637.main A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsep fm cc D hD

end
end S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_mem_principal_of_cuspChart_of_level (solution)
