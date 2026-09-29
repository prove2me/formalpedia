-- Prove2me | solution 1 for ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/69226d11-4321-531b-870b-04e566f40c03

import Mathlib
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
import Theorems.Thm_ModularCurve_heckePic0BarTranspose_fricke_smul
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeInputsAllTranspose
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DegeneracyPullbackInputs degeneracyPullbackPair heckeOperatorBar heckeOperatorBar_apply heckeOperatorAlong_eq heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral heckePic0Bar heckePic0BarTranspose modularFunctionFieldBar JZero qExpand jq modularFunctionFieldFull coeffEmb laurentBaseChange DegeneracyPushforwardInputs degeneracyPushforwardPair degeneracyPushforwardPair_eq pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair heckePic0BarTranspose_fricke_smul heckeInputsAll heckeInputsAllTranspose exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull"
namespace PEdge
p2m_open "ModularCurve"

section PullWrapper

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlongHom' (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hP : HasPrincipalDivisors K F') (hFI : FundamentalIdentityAlong K φ hφ) :
    Pic0 K F →+ Pic0 K F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI := hP
  haveI : FundamentalIdentity K F F' := hFI
  Pic0.pullbackHom _

theorem pullbackAlongHom'_mk (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hP : HasPrincipalDivisors K F') (hFI : FundamentalIdentityAlong K φ hφ)
    (D : Divisor.degZero (K := K) (F := F)) :
    pullbackAlongHom' φ hφ hP hFI (Pic0.mk D) =
      (letI := algebraAlong φ
       haveI := isScalarTower_along φ
       haveI := isIntegral_along φ hφ
       haveI := hP
       haveI : FundamentalIdentity K F F' := hFI
       Pic0.mk (Pic0.pullbackDegZeroHom F' D)) := rfl

theorem correspondence_eq_pushforwardAlongHom_pullbackAlongHom' [hP : HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (y : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN y
      = Pic0.pushforwardAlongHom ψ hψ hfin hN (pullbackAlongHom' φ hφ hP hFI y) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  rw [pullbackAlongHom'_mk, Pic0.correspondence_mk, Pic0.pushforwardAlongHom_mk]
  exact congrArg Pic0.mk (Subtype.ext rfl)

end PullWrapper

section Identification

variable (N q : ℕ) [NeZero N] [NeZero q]

theorem degeneracyPullbackPair_eq
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hP : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))))
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) :
    degeneracyPullbackPair N q =
      ![pullbackAlongHom' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hP hFIα,
        pullbackAlongHom' (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hP hFIβ] := by
  rw [degeneracyPullbackPair, dif_pos ⟨hα, hβ, hP, hFIα, hFIβ⟩]
  rfl

theorem heckePic0Bar_eq_push_pull
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    [hP : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))]
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ)
    (z : JZero N) :
    heckePic0Bar hα hβ hFIβ hfinα hNα z = degeneracyPushforwardPair N q 0 (degeneracyPullbackPair N q 1 z) := by
  rw [degeneracyPushforwardPair_eq hα hβ hfinα hNα hfinβ hNβ, degeneracyPullbackPair_eq N q hα hβ hP hFIα hFIβ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact correspondence_eq_pushforwardAlongHom_pullbackAlongHom' _ _ hβ hα hFIβ hfinα hNα z

theorem heckePic0BarTranspose_eq_push_pull
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    [hP : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))]
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q))
    (hNα : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hfinα)
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q))
    (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hfinβ)
    (z : JZero N) :
    heckePic0BarTranspose hα hβ hFIα hfinβ hNβ z
      = degeneracyPushforwardPair N q 1 (degeneracyPullbackPair N q 0 z) := by
  rw [degeneracyPushforwardPair_eq hα hβ hfinα hNα hfinβ hNβ, degeneracyPullbackPair_eq N q hα hβ hP hFIα hFIβ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact correspondence_eq_pushforwardAlongHom_pullbackAlongHom' _ _ hα hβ hFIα hfinβ hNβ z

end Identification

section BalLevel

variable (N : ℕ) [NeZero N] (ℓ : Nat.Primes) {n : ℕ} [NeZero n]

omit [NeZero n] in

theorem mem_torsion_map {M M' : ℕ} [NeZero M] [NeZero M'] (f : JZero M →+ JZero M')
    {x : JZero M} (hx : x ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) n) :
    f x ∈ Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M') n := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← map_zsmul, hx, map_zero]

theorem pair_heckeOperatorBar_fricke
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (e' : DivisorialWeilPairingData (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) n)
    (σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
          ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq))
    (x y Tx wy wTy : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) n)
    (hTx : (Tx : JZero N) = heckeOperatorBar N ℓ (x : JZero N))
    (hwy : (wy : JZero N) = SemilinearAut.ofAlgAut σ • (y : JZero N))
    (hwTy : (wTy : JZero N) = SemilinearAut.ofAlgAut σ • heckeOperatorBar N ℓ (y : JZero N)) :
    e.pair Tx wy = e.pair x wTy := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  obtain ⟨hα, hβ, hP, hfinα, hFIβ, hNα⟩ := ModularCurve.heckeInputsAll N ℓ
  obtain ⟨hα', hβ', hP', hfinβ, hFIα, hNβ⟩ := ModularCurve.heckeInputsAllTranspose N ℓ
  have hpull : DegeneracyPullbackInputs N ℓ := ⟨hα, hβ, hP, hFIα, hFIβ⟩
  have hpush : DegeneracyPushforwardInputs N ℓ := ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩

  have hT : ∀ z : JZero N,
      heckeOperatorBar N ℓ z = degeneracyPushforwardPair N ℓ 0 (degeneracyPullbackPair N ℓ 1 z) := by
    intro z
    rw [heckeOperatorBar_apply, heckeOperatorAlong_eq hα hβ hFIβ hfinα hNα]
    exact heckePic0Bar_eq_push_pull N ℓ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ z
  have hTt : ∀ z : JZero N, heckePic0BarTranspose hα hβ hFIα hfinβ hNβ z
      = degeneracyPushforwardPair N ℓ 1 (degeneracyPullbackPair N ℓ 0 z) :=
    heckePic0BarTranspose_eq_push_pull N ℓ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ

  let bx : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) n :=
    ⟨degeneracyPullbackPair N ℓ 1 (x : JZero N), mem_torsion_map (degeneracyPullbackPair N ℓ 1) x.2⟩
  let awy : Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) n :=
    ⟨degeneracyPullbackPair N ℓ 0 (wy : JZero N), mem_torsion_map (degeneracyPullbackPair N ℓ 0) wy.2⟩

  have key1 : e'.pair awy bx = e.pair wy Tx :=
    pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair N ℓ n hpull hpush e e' 0 wy awy bx Tx rfl
      (by rw [hTx, hT])

  have key2 : e'.pair bx awy = e.pair x wTy :=
    pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair N ℓ n hpull hpush e e' 1 x bx awy wTy rfl
      (by
        show (wTy : JZero N)
          = degeneracyPushforwardPair N ℓ 1 (degeneracyPullbackPair N ℓ 0 (wy : JZero N))
        rw [hwy, ← hTt, heckePic0BarTranspose_fricke_smul N ℓ σ hσ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ,
          hwTy, heckeOperatorBar_apply, heckeOperatorAlong_eq hα hβ hFIβ hfinα hNα])
  calc e.pair Tx wy = (e.pair wy Tx)⁻¹ := e.pair_swap_eq_inv wy Tx
    _ = (e'.pair awy bx)⁻¹ := by rw [key1]
    _ = e'.pair bx awy := (e'.pair_swap_eq_inv awy bx).symm
    _ = e.pair x wTy := key2

end BalLevel

end ModularCurve.PEdge

theorem solution
    (N : ℕ) [NeZero N] (ℓ : Nat.Primes) (n : ℕ) [NeZero n]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar (N * ℓ))]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
    (σ : ModularCurve.modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] ModularCurve.modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : ModularCurve.modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ a ModularCurve.jq) →
          ((σ x : ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ b ModularCurve.jq))
    (x y Tx wy wTy : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
    (hTx : (Tx : ModularCurve.JZero N) = ModularCurve.heckeOperatorBar N ℓ (x : ModularCurve.JZero N))
    (hwy : (wy : ModularCurve.JZero N) = AlgebraicCurve.SemilinearAut.ofAlgAut σ • (y : ModularCurve.JZero N))
    (hwTy : (wTy : ModularCurve.JZero N)
      = AlgebraicCurve.SemilinearAut.ofAlgAut σ • ModularCurve.heckeOperatorBar N ℓ (y : ModularCurve.JZero N)) :
    e.pair Tx wy = e.pair x wTy := by
  haveI : NeZero (N * (ℓ : ℕ)) := ⟨mul_ne_zero (NeZero.ne N) ℓ.2.ne_zero⟩
  obtain ⟨t, ht, hfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar (N * ℓ)
  haveI := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (N * ℓ)
  exact ModularCurve.PEdge.pair_heckeOperatorBar_fricke N ℓ e
    (AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * ℓ)) ⟨t, ht, hfin⟩ n).some
    σ hσ x y Tx wy wTy hTx hwy hwTy

end

end S_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
end P2MW
export P2MW.S_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar (solution)
