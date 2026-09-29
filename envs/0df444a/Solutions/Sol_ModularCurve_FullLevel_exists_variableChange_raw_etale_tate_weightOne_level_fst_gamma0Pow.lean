-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6669cf98-2bab-56e8-84ec-5a5c7240e439

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level
import Theorems.Thm_ModularCurve_FullLevel_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst
import Theorems.Thm_ModularCurve_exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint
import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace TPAux

p2m_open "ModularCurve WeierstrassCurve~cusp"
open scoped Classical

theorem isLevelPStructure_of_map {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {p : ℕ} {D : ModularCurve.LevelPData K}
    (h : ModularCurve.IsLevelPStructure (W.map φ) p (D.map φ)) : ModularCurve.IsLevelPStructure W p D := by
  have hinj : Function.Injective φ := φ.injective
  have heq : ∀ {x y : K}, (W.map φ).toAffine.Equation (φ x) (φ y) → W.toAffine.Equation x y := by
    intro x y hxy
    rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
    apply hinj
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at hxy
    simpa only [map_add, map_mul, map_pow] using hxy
  have hpsi : ∀ {x : K}, ((W.map φ).preΨ p).eval (φ x) = 0 → (W.preΨ p).eval x = 0 := by
    intro x hx
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
    exact hinj (by rw [hx, map_zero])
  have hind : ∀ {x y : K}, IsUnit (ModularCurve.indepElt (W.map φ) p (φ x) (φ y)) → IsUnit (ModularCurve.indepElt W p x y) := by
    intro x y hu
    rw [ModularCurve.indepElt_map] at hu
    rw [isUnit_iff_ne_zero] at hu ⊢
    intro h0; exact hu (by rw [h0, map_zero])
  exact ⟨heq h.equation_P, heq h.equation_Q, hpsi h.preΨ_P, hpsi h.preΨ_Q, hind h.isUnit_indepElt_PQ,
    hind h.isUnit_indepElt_QP⟩

theorem isCyclicKernel_of_map {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {N : ℕ} {h : Polynomial K}
    (hh : (W.map φ).IsCyclicKernel N (h.map φ)) : W.IsCyclicKernel N h := by
  have hinj : Function.Injective φ := φ.injective
  have hdeg : h.natDegree = (h.map φ).natDegree := (Polynomial.natDegree_map_eq_of_injective hinj h).symm
  have hcoeff : h.coeff ((N - 1) / 2) = 1 := by
    apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  have hmonic : h.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff]
    have hle : h.natDegree ≤ (N - 1) / 2 := hdeg ▸ hh.natDegree_le
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      have := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [hcoeff] at this; exact one_ne_zero this
    · rw [heq]; exact hcoeff
  refine ⟨hdeg ▸ hh.natDegree_le, hcoeff, ?_, ?_⟩
  · have := hh.dvd_preΨ
    rw [WeierstrassCurve.map_preΨ] at this
    exact (Polynomial.map_dvd_map φ hinj hmonic).mp this
  · intro a ha ha'
    have := hh.dvd_smulNumerator a ha ha'
    rw [W.smulNumerator_map φ] at this
    exact (Polynomial.map_dvd_map φ hinj hmonic).mp this

theorem isGamma0PowAt_of_map {K F : Type} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {p k : ℕ} {h : Polynomial K}
    (hh : ModularCurve.IsGamma0PowAt (W.map φ) p k (h.map φ)) : ModularCurve.IsGamma0PowAt W p k h := by
  have hinj : Function.Injective φ := φ.injective
  by_cases hpk : p ^ k = 2
  · rw [ModularCurve.isGamma0PowAt_of_pow_eq_two _ hpk] at hh ⊢
    refine ⟨(Polynomial.natDegree_map_eq_of_injective hinj h) ▸ hh.natDegree_le, ?_, ?_⟩
    · apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
    · have := hh.dvd_Ψ₂Sq
      rw [WeierstrassCurve.map_Ψ₂Sq] at this
      exact (Polynomial.map_dvd_map' φ).mp this
  · rw [ModularCurve.isGamma0PowAt_of_pow_ne_two _ hpk] at hh ⊢
    refine ⟨(Polynomial.natDegree_map_eq_of_injective hinj h) ▸ hh.natDegree_le, ?_, ?_, ?_⟩
    · apply hinj; rw [← Polynomial.coeff_map, hh.coeff_eq_one, map_one]
    · have := hh.mul_preΨ_dvd
      rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.map_preΨ, ← Polynomial.map_mul] at this
      exact (Polynomial.map_dvd_map' φ).mp this
    · intro a ha ha' hpa
      have := hh.dvd_smulNumerator a ha ha' hpa
      rw [W.smulNumerator_map φ] at this
      exact (Polynomial.map_dvd_map' φ).mp this

end TPAux

set_option maxHeartbeats 6400000 in

theorem solution
    (M' : ℕ) [NeZero M']
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓ)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (ℓ ^ 2 * M')
        (ModularCurve.FullLevel.levelH ℓ M')))
    (A : Type) [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries L))
      (x : (((ModularCurve.gamma0PowComponent A M' hM).prod ((ModularCurve.levelPComponent A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).toRigid).Raw ↥K),

      (((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).2 + (ModularCurve.cuspPoint L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![1, 0]).1 ∧
        C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹)) ∧

      x.curve.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L ℓ ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : L →+* F') (ζ' : F'),
        IsPrimitiveRoot ζ' ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((x.level.1 p).map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' ℓ (ζ' ^ a)).1))) ∧

      x.level.2.1.map (algebraMap ↥K (LaurentSeries L)) = (ModularCurve.cuspData L ℓ (hζ.isUnit (Fact.out : ℓ.Prime).ne_zero).unit ![(1 : ZMod ℓ), 0] ![0, -(1 : ZMod ℓ)]).variableChange C := by
  classical
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hℓ2 : ℓ ≠ 2 := by omega
  haveI : NeZero ℓ := ⟨hℓ0⟩

  obtain ⟨C, hu, hr, hs, ht, ha1, ha2, ha3, ha4, ha6, hcusp⟩ :=
    ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_prime_level M'
      ℓ hℓ3 hℓM' L ζ hζ hιζ K hK

  have hinj : Function.Injective (algebraMap ↥K (LaurentSeries L)) := (algebraMap ↥K (LaurentSeries L)).injective

  obtain ⟨b1, hb1⟩ := ha1
  obtain ⟨b2, hb2⟩ := ha2
  obtain ⟨b3, hb3⟩ := ha3
  obtain ⟨b4, hb4⟩ := ha4
  obtain ⟨b6, hb6⟩ := ha6
  let W₀ : WeierstrassCurve ↥K := ⟨b1, b2, b3, b4, b6⟩
  have hW₀ : W₀.map (algebraMap ↥K (LaurentSeries L)) = C • ModularCurve.tateBase L ℓ := by
    exact WeierstrassCurve.ext hb1 hb2 hb3 hb4 hb6
  have hΔ₀ : IsUnit W₀.Δ := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu' : IsUnit (C • ModularCurve.tateBase L ℓ).Δ :=
      (ModularCurve.tateBase L ℓ).isUnit_Δ_variableChange C (ModularCurve.isUnit_Δ_tateBase L ℓ)
    rw [← hW₀, WeierstrassCurve.map_Δ, h0, map_zero] at hu'
    exact not_isUnit_zero hu'

  have hζu : ((hζ.isUnit hℓ0).unit : L) = ζ := IsUnit.unit_spec _
  have hℓL : IsUnit ((ℓ : ℕ) : L) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hℓ0)
  have hsumℓ : ∑ i ∈ Finset.range ℓ, ((((hζ.isUnit hℓ0).unit : Lˣ) : L) ^ (ℓ / ℓ)) ^ i = 0 := by
    rw [hζu, Nat.div_self (Nat.pos_of_ne_zero hℓ0), pow_one]
    exact hζ.geom_sum_eq_zero (by omega)

  have h1ne : (1 : ZMod ℓ) ≠ 0 := by
    haveI : Fact (1 < ℓ) := ⟨by omega⟩
    exact one_ne_zero
  have hv1 : (![(1 : ZMod ℓ), 0] : Fin 2 → ZMod ℓ) ≠ 0 := fun h => h1ne (by simpa using congrFun h 0)
  have hv2 : (![0, -(1 : ZMod ℓ)] : Fin 2 → ZMod ℓ) ≠ 0 := fun h => h1ne (by simpa using congrFun h 1)

  obtain ⟨xP, hxP⟩ := (hcusp _ _ hv1 hv2).1
  obtain ⟨yP, hyP⟩ := (hcusp _ _ hv1 hv2).2
  obtain ⟨xQ, hxQ⟩ := (hcusp _ _ hv2 hv1).1
  obtain ⟨yQ, hyQ⟩ := (hcusp _ _ hv2 hv1).2
  let D₀ : ModularCurve.LevelPData ↥K := ⟨xP, yP, xQ, yQ⟩
  have hD₀map : D₀.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L ℓ (hζ.isUnit hℓ0).unit ![(1 : ZMod ℓ), 0] ![0, -(1 : ZMod ℓ)]).variableChange C := by
    refine ModularCurve.LevelPData.ext hxP hyP ?_ ?_
    · exact hxQ
    · exact hyQ
  have hTwℓ : ModularCurve.IsLevelPStructure (ModularCurve.tateBase L ℓ) ℓ
      (ModularCurve.cuspData L ℓ (hζ.isUnit hℓ0).unit ![(1 : ZMod ℓ), 0] ![0, -(1 : ZMod ℓ)]) := by
    have := ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd (R := L) (p := ℓ) hℓ2 hℓL ℓ
      (dvd_refl ℓ) (hζ.isUnit hℓ0).unit hsumℓ
    rwa [Nat.div_self (Nat.pos_of_ne_zero hℓ0), Nat.cast_one] at this
  have hD₀ : ModularCurve.IsLevelPStructure W₀ ℓ D₀ :=
    TPAux.isLevelPStructure_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hD₀map]; exact hTwℓ.variableChange C)

  letI algA : Algebra A (LaurentSeries L) := ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)).toAlgebra
  have h20 : (![(1 : ZMod ℓ), 0] : Fin 2 → ZMod ℓ) ≠ 0 := hv1
  have h2ne : (![(2 : ZMod ℓ), 0] : Fin 2 → ZMod ℓ) ≠ 0 := by
    intro h
    have h2 : (2 : ZMod ℓ) = 0 := by simpa using congrFun h 0
    have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd two_pos this) (by omega)
  have hcomp : ∀ p : ↥M'.primeFactors, ∃ h₀ : Polynomial ↥K,
      ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) h₀ ∧
      ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ' : F'),
        IsPrimitiveRoot ζ' ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        (h₀.map (algebraMap ↥K (LaurentSeries L))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' ℓ (ζ' ^ a)).1)) := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    haveI : Fact (p : ℕ).Prime := ⟨hp⟩
    have hpL : ((p : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' (p : ℕ)
    obtain ⟨h, hhk, hh⟩ :=
      ModularCurve.exists_isGamma0PowAt_tateBase_and_map_coeffMap_eq_prod_X_sub_C_toricPoint L (p : ℕ)
        (M'.factorization (p : ℕ)) hpL ℓ
    have hhC := hM (LaurentSeries L) (ModularCurve.tateBase L ℓ) C (p : ℕ) (M'.factorization (p : ℕ)) h hhk
    have hcoefK :=
      ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst
        M' ℓ hℓ3 hℓM' L ζ hζ hιζ K hK (p : ℕ) (M'.factorization (p : ℕ)) hpk h
        (fun F' _ f ζ' hζ' => hh F' f ζ' hζ') C (hcusp _ _ hv1 h2ne).1 hr
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : Polynomial ↥K, h₀.map (algebraMap ↥K (LaurentSeries L)) =
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h := by
      have hl : ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) h ∈
          Polynomial.lifts (algebraMap ↥K (LaurentSeries L)) :=
        (Polynomial.lifts_iff_coeff_lifts _).mpr (fun n => hcoefK n)
      obtain ⟨h₀, hh₀⟩ := RingHom.mem_rangeS.mp hl
      exact ⟨h₀, hh₀⟩
    refine ⟨h₀, TPAux.isGamma0PowAt_of_map (algebraMap ↥K (LaurentSeries L)) (by rw [hW₀, hh₀]; exact hhC), ?_⟩
    intro F' _ f ζ' hζ'
    rw [hh₀, ModularCurve.kernelVariableChangeDeg_map, hh F' f ζ' hζ']
  choose hT hTspec hTtoric using hcomp

  exact ⟨C, ⟨W₀, hΔ₀, (hT, (D₀, PUnit.unit)), ⟨hTspec, hD₀, trivial⟩⟩, ⟨hu, hr, hs, ht⟩, hW₀,
    (fun p F' _ f ζ' hζ' => hTtoric p F' f ζ' hζ'), hD₀map⟩

end S_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_variableChange_raw_etale_tate_weightOne_level_fst_gamma0Pow (solution)
