-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ecea5961-d272-5bf2-a3b6-b3c03e15bc78

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
import Theorems.Thm_AlgebraicCurve_GluedPic0_exists_zsmul_eq_zero_and_toPic0Pair_eq
import Theorems.Thm_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_GluedPic0_eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_zero_of_mem_toricPts_pow
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mem_finPts_iff_and_isTorsionPoint_section_and_specialPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (n : ℕ) (hn : 0 < n) :
    (∀ b : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
        (p ^ n) • b = 0 →
        ∃ x ∈ O.finPts (p ^ n), ∃ (s : SchemeHomOver Λ.σA O.g) (_ : (O.pts x).1 = barPt A ≫ s.1)
          (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (_ : sκ.1 = resPt A ≫ s.1),
          GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm sκ) = b) ∧
    (∀ x ∈ O.finPts (p ^ n), ∀ (s : SchemeHomOver Λ.σA O.g), (O.pts x).1 = barPt A ≫ s.1 →
      ∀ (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g), sκ.1 = resPt A ≫ s.1 →
        (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm sκ) = 0 ↔ O.ptsSp.symm sκ = 0)) ∧

    (∀ x ∈ O.toricPts (p ^ n), ∀ (s : SchemeHomOver Λ.σA O.g), (O.pts x).1 = barPt A ≫ s.1 →
      ∀ (sκ : SchemeHomOver (resPt A ≫ Λ.σA) O.g), sκ.1 = resPt A ≫ s.1 → O.ptsSp.symm sκ = 0) := by
  classical

  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

  obtain ⟨hPD, hCB, hrat⟩ :=
    ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
      p M H hpM hpM2 (ResidueField ↥A)
  haveI := hPD
  have hrat' : ∀ s ∈ O.ssFinset,
      Function.Surjective (algebraMap (ResidueField ↥A) (s.1.ResidueField)) ∧
        Function.Surjective (algebraMap (ResidueField ↥A) (s.2.ResidueField)) :=
    fun s _ => ⟨hrat s.1, hrat s.2⟩
  have hrat'' : ∀ s : ↥O.ssFinset,
      Function.Surjective (algebraMap (ResidueField ↥A)
        ((s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1.ResidueField)) ∧
      Function.Surjective (algebraMap (ResidueField ↥A)
        ((s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2.ResidueField)) :=
    fun s => ⟨hrat s.1.1, hrat s.1.2⟩

  obtain ⟨hsp_nsmul, hsp_zero, hsp_tors⟩ :=
    ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint p M H hpM A hA Λ O
  obtain ⟨hmem, hgen, hsec, hspec⟩ :=
    ModularCurve.JHNeronObjectAtP.mem_finPts_iff_and_isTorsionPoint_section_and_specialPt p M H hpM A hA Λ O (p ^ n)
  refine ⟨?_, ?_, ?_⟩

  · intro b hb

    have hb' : ((p ^ n : ℕ) : ℤ) • b = 0 := by rw [natCast_zsmul]; exact hb
    obtain ⟨z, hz, hzb⟩ :=
      AlgebraicCurve.GluedPic0.exists_zsmul_eq_zero_and_toPic0Pair_eq O.ssFinset hrat' (p ^ n) b hb'
    have hz' : (p ^ n) • z = 0 := by rw [← natCast_zsmul]; exact hz

    have hy : O.L.IsTorsionPoint (resPt A ≫ Λ.σA) (p ^ n) (O.ptsSp z) := (hsp_tors (p ^ n) z).mp hz'

    haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
    haveI : IsSeparated O.g := O.separated
    haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
    obtain ⟨hqf, hqc, hfl⟩ :=
      ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange p M H hpM A hA Λ O (p ^ n) hpn
    haveI := hqf; haveI := hqc; haveI := hfl
    haveI : LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeKerStr (p ^ n)) := by
      unfold RelativeGroupLaw.schemeKerStr; infer_instance
    haveI : QuasiCompact ((O.L.baseChange Λ.σA).schemeKerStr (p ^ n)) := by
      unfold RelativeGroupLaw.schemeKerStr; infer_instance
    haveI : Flat ((O.L.baseChange Λ.σA).schemeKerStr (p ^ n)) := by
      unfold RelativeGroupLaw.schemeKerStr; infer_instance
    obtain ⟨s, hs_tor, hs_red⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_isTorsionPoint_specMap_residue_comp_eq_of_isAlgClosed
        A Λ.σA O.L (fun t x y => O.comm t x y) (p ^ n) (O.ptsSp z) hy

    refine ⟨O.pts.symm (schemeHomOverComp (barPt A) Λ.hσA s), hgen s hs_tor, s, ?_, O.ptsSp z, hs_red.symm, ?_⟩
    · rw [Equiv.apply_symm_apply, GoodReductionJacobian.schemeHomOverComp_coe]
    · rw [Equiv.symm_apply_apply, hzb]

  · intro x hx s hs sκ hsκ
    constructor
    · intro h0

      have htor_s : O.L.IsTorsionPoint Λ.σA (p ^ n) s := hsec x hx s hs
      have htor_κ : O.L.IsTorsionPoint (resPt A ≫ Λ.σA) (p ^ n) sκ := hspec s htor_s sκ hsκ
      have hz : (p ^ n) • O.ptsSp.symm sκ = 0 := by
        rw [hsp_tors, Equiv.apply_symm_apply]; exact htor_κ

      have hker : O.ptsSp.symm sκ ∈ (GluedPic0.nodeUnit O.ssFinset).range := by
        rw [← AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit O.ssFinset hrat'', AddMonoidHom.mem_ker]
        exact h0
      have hz' : ((p ^ n : ℕ) : ℤ) • O.ptsSp.symm sκ = 0 := by rw [natCast_zsmul]; exact hz
      exact AlgebraicCurve.GluedPic0.eq_zero_of_mem_range_nodeUnit_of_pow_char_smul_eq_zero p hCB O.ssFinset n _ hker
        (by exact_mod_cast hz')
    · intro h0
      rw [h0, map_zero]

  · intro x hx s hs sκ hsκ
    exact ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_zero_of_mem_toricPts_pow p M H hpM A hA Λ O n hn x hx s hs sκ hsκ

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mem_finPts_toPic0Pair_ptsSp_symm_eq_and_eq_zero_iff_and_of_mem_toricPts_of_not_sq_dvd (solution)
