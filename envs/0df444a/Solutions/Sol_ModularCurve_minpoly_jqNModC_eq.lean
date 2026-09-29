-- Prove2me | solution 1 for ModularCurve.minpoly_jqNModC_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f1f68ee3-c106-55cb-a63d-8e26dae083c3

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Div
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_minpoly_jqNModC_eq
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "qExpand jq jqN dedekindPsi evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full jqModC jqNModC relfinrank_laurentBaseChange_modularFunctionFieldFull jq_mem_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange relfinrank_full_eq_dedekindPsi laurentBaseChange_adjoin_pair functionFieldGeneration coeffEmb_jq coeffEmb_jqN transcendental_jqModC"
p2m_open "ModularCurve~jAdj"

namespace B1Zero

abbrev jAdj (L : Type*) [Field L] [Algebra ℚ L] : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L))

abbrev jGenL (L : Type*) [Field L] [Algebra ℚ L] : jAdj L :=
  ⟨jqModC L, IntermediateField.mem_adjoin_simple_self L (jqModC L)⟩

abbrev ΦL (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    Polynomial (jAdj L) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jAdj L)) (jGenL L))

theorem eval₂_Φ_jqModC_jqNModC (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (jqModC L))
      (jqNModC L N) = 0 := by
  have hθ : (coeffEmb L).comp evalAtJ =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (jqModC L) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, evalAtJ_X]
    exact coeffEmb_jq L
  have h := congrArg (coeffEmb L) data.eval_eq_zero
  rw [Polynomial.hom_eval₂, hθ, map_zero, coeffEmb_jqN] at h
  exact h

theorem monic_ΦL (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) : (ΦL L N data).Monic :=
  data.monic.map _

theorem aeval_jqNModC_ΦL (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    Polynomial.aeval (jqNModC L N) (ΦL L N data) = 0 := by
  have hcomp : (algebraMap (jAdj L) (LaurentSeries L)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (jAdj L)) (jGenL L)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (jqModC L) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact eval₂_Φ_jqModC_jqNModC L N data

theorem isIntegral_jqNModC (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) : IsIntegral (jAdj L) (jqNModC L N) :=
  ⟨ΦL L N data, monic_ΦL L N data, by
    rw [← Polynomial.aeval_def]; exact aeval_jqNModC_ΦL L N data⟩

theorem laurentBaseChange_eq_adjoin_pair (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    laurentBaseChange L (modularFunctionFieldFull N) =
      IntermediateField.adjoin L {jqModC L, jqNModC L N} :=
  laurentBaseChange_adjoin_pair L N (functionFieldGeneration N)

theorem jAdj_le_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    jAdj L ≤ laurentBaseChange L (modularFunctionFieldFull N) := by
  rw [IntermediateField.adjoin_simple_le_iff, laurentBaseChange_eq_adjoin_pair L N]
  exact IntermediateField.subset_adjoin L _ (Set.mem_insert _ _)

theorem adjoin_jqNModC_eq_extendScalars (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    IntermediateField.adjoin (jAdj L) ({jqNModC L N} : Set (LaurentSeries L)) =
      IntermediateField.extendScalars (jAdj_le_laurentBaseChange L N) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_extendScalars,
      laurentBaseChange_eq_adjoin_pair L N]
    exact IntermediateField.subset_adjoin L _ (Set.mem_insert_of_mem _ rfl)
  · intro x hx
    rw [IntermediateField.mem_extendScalars, laurentBaseChange_eq_adjoin_pair L N] at hx

    have ha : jqModC L ∈
        IntermediateField.adjoin (jAdj L) ({jqNModC L N} : Set (LaurentSeries L)) := by
      have h := (IntermediateField.adjoin (jAdj L)
        ({jqNModC L N} : Set (LaurentSeries L))).algebraMap_mem (jGenL L)
      rwa [IntermediateField.algebraMap_apply] at h
    have hb : jqNModC L N ∈
        IntermediateField.adjoin (jAdj L) ({jqNModC L N} : Set (LaurentSeries L)) :=
      IntermediateField.mem_adjoin_simple_self (jAdj L) (jqNModC L N)
    have hle : IntermediateField.adjoin L ({jqModC L, jqNModC L N} : Set (LaurentSeries L)) ≤
        (IntermediateField.adjoin (jAdj L)
          ({jqNModC L N} : Set (LaurentSeries L))).restrictScalars L :=
      IntermediateField.adjoin_le_iff.mpr
        (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩)
    exact (IntermediateField.mem_restrictScalars L).mp (hle hx)

theorem finrank_adjoin_jqNModC (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    Module.finrank (jAdj L)
      (IntermediateField.adjoin (jAdj L) ({jqNModC L N} : Set (LaurentSeries L))) =
      dedekindPsi N := by
  rw [adjoin_jqNModC_eq_extendScalars L N,
    ← IntermediateField.relfinrank_eq_finrank_of_le (jAdj_le_laurentBaseChange L N)]
  have e1 : jAdj L = IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) := by
    rw [coeffEmb_jq]
  rw [e1, relfinrank_laurentBaseChange_modularFunctionFieldFull L N, relfinrank_full_eq_dedekindPsi N]

theorem natDegree_minpoly_jqNModC (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    (minpoly (jAdj L) (jqNModC L N)).natDegree = dedekindPsi N := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_jqNModC L N data), finrank_adjoin_jqNModC L N]

end B1Zero

open B1Zero in

private theorem minpoly_jqNModC_eq (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    minpoly (↥(IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))) (jqNModC L N) =
      data.Φ.map (Polynomial.eval₂RingHom
        (Int.castRingHom (↥(IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))))
        ⟨jqModC L, IntermediateField.mem_adjoin_simple_self L (jqModC L)⟩) := by
  show minpoly (jAdj L) (jqNModC L N) = ΦL L N data
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (isIntegral_jqNModC L N data))
    (monic_ΦL L N data) (minpoly.dvd _ _ (aeval_jqNModC_ΦL L N data)) (le_of_eq ?_)
  rw [natDegree_minpoly_jqNModC L N data, (data.monic).natDegree_map, data.natDegree_eq]

section B1cFurniture

variable (L : Type*) [Field L]

abbrev jAdjField : IntermediateField L (LaurentSeries L) := L⟮jqModC L⟯

abbrev jGenL : jAdjField L := AdjoinSimple.gen L (jqModC L)

variable {A : Type*} [Field A] [Algebra L A]

def jBaseHom {c : A} (hc : Transcendental L c) : jAdjField L →ₐ[L] A :=
  ((L⟮c⟯.val).comp (RatFunc.algEquivOfTranscendental c hc).toAlgHom).comp
    (RatFunc.algEquivOfTranscendental (jqModC L) (transcendental_jqModC L)).symm.toAlgHom

theorem jBaseHom_jGenL {c : A} (hc : Transcendental L c) : jBaseHom L hc (jGenL L) = c := by
  have h1 : (RatFunc.algEquivOfTranscendental (jqModC L) (transcendental_jqModC L)).symm
      (jGenL L) = RatFunc.X :=
    RatFunc.algEquivOfTranscendental_symm_gen (jqModC L) (transcendental_jqModC L)
  show L⟮c⟯.val ((RatFunc.algEquivOfTranscendental c hc)
    ((RatFunc.algEquivOfTranscendental (jqModC L) (transcendental_jqModC L)).symm (jGenL L))) = c
  rw [h1]
  exact RatFunc.algEquivOfTranscendental_X c hc

end B1cFurniture

private theorem exists_algHom_of_isRoot (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) {A : Type*} [Field A] [Algebra L A] (c y : A)
    (hc : Transcendental L c)
    (hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)).IsRoot y) :
    ∃ ψ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A,
      ψ ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ = c ∧
      ψ ⟨coeffEmb L (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩ = y := by
  have hB10 := minpoly_jqNModC_eq L N data

  let φ₀ : jAdjField L →ₐ[L] A := jBaseHom L hc
  have hφ₀c : φ₀ (jGenL L) = c := jBaseHom_jGenL L hc

  letI : Algebra (jAdjField L) A := φ₀.toRingHom.toAlgebra
  have hamap : ∀ x, algebraMap (jAdjField L) A x = φ₀ x := fun _ => rfl
  haveI : IsScalarTower L (jAdjField L) A :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ₀.commutes x).symm)

  have hΦmonic : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jAdjField L))
      (jGenL L))).Monic := data.monic.map _
  have hint : IsIntegral (jAdjField L) (jqNModC L N) := by
    rw [← minpoly.ne_zero_iff, hB10]; exact hΦmonic.ne_zero

  have hminmap : (minpoly (jAdjField L) (jqNModC L N)).map (algebraMap (jAdjField L) A)
      = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c) := by
    rw [hB10, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, hamap]
    exact hφ₀c
  have hyroots : y ∈ (minpoly (jAdjField L) (jqNModC L N)).aroots A := by
    rw [Polynomial.mem_aroots', Polynomial.aeval_def, ← Polynomial.eval_map, hminmap]
    exact ⟨(data.monic.map _).ne_zero, hy⟩

  let ψ₁ : (jAdjField L)⟮jqNModC L N⟯ →ₐ[jAdjField L] A :=
    (algHomAdjoinIntegralEquiv (jAdjField L) hint).symm ⟨y, hyroots⟩
  have hψ₁gen : ψ₁ (AdjoinSimple.gen (jAdjField L) (jqNModC L N)) = y :=
    algHomAdjoinIntegralEquiv_symm_apply_gen (jAdjField L) hint ⟨y, hyroots⟩

  have hadj : ((jAdjField L)⟮jqNModC L N⟯).restrictScalars L
      = laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [laurentBaseChange_adjoin_pair L N (functionFieldGeneration N),
      show ({jqModC L, jqNModC L N} : Set (LaurentSeries L))
        = {jqModC L} ∪ {jqNModC L N} from (Set.singleton_union).symm,
      ← IntermediateField.adjoin_adjoin_left]
  let ψ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A :=
    (ψ₁.restrictScalars L).comp (IntermediateField.equivOfEq hadj).symm.toAlgHom
  refine ⟨ψ, ?_, ?_⟩
  ·

    have hamb : ((equivOfEq hadj).symm
          ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩
          : (jAdjField L)⟮jqNModC L N⟯)
        = algebraMap (jAdjField L) ((jAdjField L)⟮jqNModC L N⟯) (jGenL L) :=
      Subtype.ext (coeffEmb_jq L)
    show ψ₁ ((equivOfEq hadj).symm ⟨coeffEmb L jq, _⟩) = c
    rw [hamb, ψ₁.commutes, hamap, hφ₀c]
  ·

    have hamb' : ((equivOfEq hadj).symm
          ⟨coeffEmb L (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩
          : (jAdjField L)⟮jqNModC L N⟯)
        = AdjoinSimple.gen (jAdjField L) (jqNModC L N) :=
      Subtype.ext (coeffEmb_jqN L N)
    show ψ₁ ((equivOfEq hadj).symm ⟨coeffEmb L (qExpand ℚ N jq), _⟩) = y
    rw [hamb', hψ₁gen]

end ModularCurve

end

p2m_open "ModularCurve~jAdj" in open _root_.P2MW.S_ModularCurve_minpoly_jqNModC_eq.ModularCurve in

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) :
    minpoly (↥(IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))) (jqNModC L N) =
      data.Φ.map (Polynomial.eval₂RingHom
        (Int.castRingHom (↥(IntermediateField.adjoin L ({jqModC L} : Set (LaurentSeries L)))))
        ⟨jqModC L, IntermediateField.mem_adjoin_simple_self L (jqModC L)⟩) :=
  ModularCurve.minpoly_jqNModC_eq L N data

#print axioms solution

end S_ModularCurve_minpoly_jqNModC_eq
end P2MW
export P2MW.S_ModularCurve_minpoly_jqNModC_eq (solution)
