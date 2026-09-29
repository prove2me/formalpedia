-- Prove2me | solution 1 for ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4a9f631e-060c-543a-87de-bad58d54c883

import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve

noncomputable section

open ModularCurve in

private def Phi2Fin.jbar (K : Type*) [Field K] (N : ℕ) [NeZero N] : modularFunctionFieldC K N :=
  ⟨jqModC K, jqModC_mem K N⟩

open ModularCurve in
private theorem Phi2Fin.transcendental_jbar (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Transcendental K (Phi2Fin.jbar K N) := by
  have h := transcendental_jqModC K
  rw [show jqModC K = ((modularFunctionFieldC K N).val (Phi2Fin.jbar K N)) from rfl,
    Transcendental, isAlgebraic_algHom_iff (modularFunctionFieldC K N).val
      (modularFunctionFieldC K N).val.injective] at h
  exact h

private theorem Phi2Fin.jbar_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Phi2Fin.jbar K N ≠ 0 := fun h0 =>
  Phi2Fin.transcendental_jbar K N (h0 ▸ isAlgebraic_zero)

open ModularCurve in
private theorem Phi2Fin.jbar_sub_algebraMap_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] (a : K) :
    Phi2Fin.jbar K N - algebraMap K (modularFunctionFieldC K N) a ≠ 0 := fun h0 =>
  Phi2Fin.transcendental_jbar K N ((sub_eq_zero.mp h0) ▸ isAlgebraic_algebraMap a)

open ModularCurve in

private theorem Phi2Fin.frob_frob_jbar_sub (K : Type*) [Field K] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data) (a : K) :
    frobeniusGeomLevel K N data hKr (frobeniusGeomLevel K N data hKr
        (Phi2Fin.jbar K N - algebraMap K (modularFunctionFieldC K N) a))
      = Phi2Fin.jbar K N ^ (ℓ * ℓ) - algebraMap K (modularFunctionFieldC K N) a := by
  have hj : frobeniusGeomLevel K N data hKr (Phi2Fin.jbar K N) = Phi2Fin.jbar K N ^ ℓ :=
    frobeniusGeomLevel_jq K N data hKr
  rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, hj, map_pow, hj, ← pow_mul]

private theorem Phi2Fin.residue_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) (c : K) :
    IsLocalRing.residue w.toValuationSubring (algebraMap K w.toValuationSubring c)
      = algebraMap K w.ResidueField c := by
  rw [IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField c,
    IsLocalRing.ResidueField.algebraMap_eq]

private theorem Phi2Fin.exists_isUnit_of_ord_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) {f : F} (hf : f ≠ 0) (h : w.ord f = 0) :
    ∃ hm : f ∈ w.toValuationSubring, IsUnit (⟨f, hm⟩ : w.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : w.toValuationSubring).2, u.isUnit⟩

private theorem Phi2Fin.ord_ne_zero_of_residue_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) {f : F} (hf : f ≠ 0) (hm : f ∈ w.toValuationSubring)
    (hr : IsLocalRing.residue w.toValuationSubring ⟨f, hm⟩ = 0) : w.ord f ≠ 0 := by
  intro h0
  obtain ⟨_, hu⟩ := Phi2Fin.exists_isUnit_of_ord_eq_zero w hf h0
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu hr

private theorem Phi2Fin.ord_eq_zero_of_residue_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) {f : F} (hm : f ∈ w.toValuationSubring)
    (hr : IsLocalRing.residue w.toValuationSubring ⟨f, hm⟩ ≠ 0) : w.ord f = 0 := by
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hr
  have hf : f = ((u : w.toValuationSubring) : F) := by rw [hu]
  rw [hf]
  exact w.ord_coe_unit u

open ModularCurve in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data) :
    {w : Place K (modularFunctionFieldC K N) |
      frobOnPlacesGeomLevel K N data hKr (frobOnPlacesGeomLevel K N data hKr w) = w}.Finite := by
  haveI : IsCurveOver K (modularFunctionFieldC K N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField K N
  have hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c := fun c =>
    IsAlgClosed.exists_pow_nat_eq c (Fact.out : ℓ.Prime).pos
  have hsurj : ∀ w : Place K (modularFunctionFieldC K N),
      Function.Surjective (algebraMap K w.ResidueField) := fun w => by
    haveI : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
    haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

  have hzp : ∀ f : modularFunctionFieldC K N, f ≠ 0 →
      {w : Place K (modularFunctionFieldC K N) | w.ord f ≠ 0}.Finite := by
    intro f hf
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    refine Df.support.finite_toSet.subset ?_
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDf w]
    exact hw

  have hroots : {a : K | a ^ (ℓ * ℓ) = a}.Finite := by
    have hp : (Polynomial.X ^ (ℓ * ℓ) - Polynomial.X : Polynomial K) ≠ 0 := by
      intro h0
      have h1 := congrArg Polynomial.natDegree (sub_eq_zero.mp h0)
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h1
      have h2 := (Fact.out : ℓ.Prime).two_le
      nlinarith
    refine (Polynomial.finite_setOf_isRoot hp).subset ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact sub_eq_zero.mpr ha
  refine ((hzp _ (Phi2Fin.jbar_ne_zero K N)).union (hroots.biUnion fun a _ =>
    hzp _ (Phi2Fin.jbar_sub_algebraMap_ne_zero K N a))).subset ?_
  intro w hw
  rw [Set.mem_setOf_eq] at hw
  by_cases hjw : Phi2Fin.jbar K N ∈ w.toValuationSubring
  · right

    obtain ⟨a, ha⟩ := hsurj w (IsLocalRing.residue w.toValuationSubring ⟨Phi2Fin.jbar K N, hjw⟩)
    have hamem : algebraMap K (modularFunctionFieldC K N) a ∈ w.toValuationSubring :=
      w.algebraMap_mem' a

    have hordg : w.ord (Phi2Fin.jbar K N - algebraMap K (modularFunctionFieldC K N) a) ≠ 0 := by
      refine Phi2Fin.ord_ne_zero_of_residue_eq_zero w (Phi2Fin.jbar_sub_algebraMap_ne_zero K N a)
        (sub_mem hjw hamem) ?_
      have hsplit : (⟨Phi2Fin.jbar K N - algebraMap K (modularFunctionFieldC K N) a,
          sub_mem hjw hamem⟩ : w.toValuationSubring)
          = ⟨Phi2Fin.jbar K N, hjw⟩ - algebraMap K w.toValuationSubring a := Subtype.ext (by simp)
      rw [hsplit, map_sub, Phi2Fin.residue_algebraMap, ha, sub_self]

    have hroot : a ^ (ℓ * ℓ) = a := by
      by_contra hne
      have hpmem : Phi2Fin.jbar K N ^ (ℓ * ℓ) ∈ w.toValuationSubring := pow_mem hjw _
      have hord0 :
          w.ord (Phi2Fin.jbar K N ^ (ℓ * ℓ) - algebraMap K (modularFunctionFieldC K N) a) = 0 := by
        refine Phi2Fin.ord_eq_zero_of_residue_ne_zero w (sub_mem hpmem hamem) ?_
        have hsplit : (⟨Phi2Fin.jbar K N ^ (ℓ * ℓ) - algebraMap K (modularFunctionFieldC K N) a,
            sub_mem hpmem hamem⟩ : w.toValuationSubring)
            = ⟨Phi2Fin.jbar K N, hjw⟩ ^ (ℓ * ℓ) - algebraMap K w.toValuationSubring a :=
          Subtype.ext (by simp)
        rw [hsplit, map_sub, map_pow, Phi2Fin.residue_algebraMap, ← ha, ← map_pow, ← map_sub]
        exact (map_ne_zero (algebraMap K w.ResidueField)).mpr (sub_ne_zero.mpr hne)
      rw [← Phi2Fin.frob_frob_jbar_sub K N data hKr a,
        ord_frobeniusGeomLevel_eq_mul K N data hKr hperf,
        ord_frobeniusGeomLevel_eq_mul K N data hKr hperf, hw] at hord0
      have hℓ0 : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
      rcases mul_eq_zero.mp hord0 with h | h
      · exact hℓ0 h
      rcases mul_eq_zero.mp h with h | h
      · exact hℓ0 h
      exact hordg h
    exact Set.mem_biUnion (x := a) hroot hordg
  · left
    show w.ord (Phi2Fin.jbar K N) ≠ 0
    intro h0
    exact hjw (w.mem_of_ord_nonneg (Phi2Fin.jbar_ne_zero K N) h0.ge)

end

end S_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
end P2MW
export P2MW.S_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self (solution)
