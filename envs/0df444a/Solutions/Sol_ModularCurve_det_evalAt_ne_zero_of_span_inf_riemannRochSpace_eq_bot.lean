-- Prove2me | solution 1 for ModularCurve.det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7e0e9d19-5c6e-52eb-ac33-9bcd9d764a0f

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace P2MRankCrit

section Eval

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem evalAt_add_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem smul_mem_of_mem (v : Place (AlgebraicClosure ℚ) F) (a : AlgebraicClosure ℚ) {f : F}
    (hf : f ∈ v.toValuationSubring) : a • f ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational)
    (a : AlgebraicClosure ℚ) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (a • f) = a * v.evalAt f := by
  rw [Algebra.smul_def, v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem sum_smul_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (c : ι → AlgebraicClosure ℚ) {f : ι → F} (hf : ∀ i, f i ∈ v.toValuationSubring) :
    (∑ i ∈ S, c i • f i) ∈ v.toValuationSubring :=
  sum_mem fun i _ => smul_mem_of_mem v (c i) (hf i)

theorem evalAt_sum_smul_of_mem {ι : Type} (S : Finset ι) (v : Place (AlgebraicClosure ℚ) F)
    (hv : v.IsRational) (c : ι → AlgebraicClosure ℚ) {f : ι → F}
    (hf : ∀ i, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (v.evalAt_algebraMap_eq 0 ▸ by rw [map_zero])
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem v hv (smul_mem_of_mem v _ (hf a)) (sum_smul_mem S v c hf),
      evalAt_smul_of_mem v hv _ (hf a), ih]

end Eval

end P2MRankCrit

open P2MRankCrit in
theorem solution (N : ℕ) [NeZero N]
    {m : ℕ} (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (u : Fin m → modularFunctionFieldBar N) (hu : LinearIndependent (AlgebraicClosure ℚ) u)
    (huA : ∀ j, u j ∈ riemannRochSpace A)
    (P : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hP : Function.Injective P) (hAP : ∀ i, A (P i) = 0)
    (hbot : Submodule.span (AlgebraicClosure ℚ) (Set.range u)
        ⊓ riemannRochSpace (A - ∑ i, Finsupp.single (P i) 1) = ⊥) :
    (Matrix.of fun i j => (P i).evalAt (u j)).det ≠ 0 := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  have hrat : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  intro hdet
  obtain ⟨c, hc0, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set g : modularFunctionFieldBar N := ∑ j, c j • u j with hg

  have hg0 : g ≠ 0 := by
    intro h
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp hu c h j
  have hgspan : g ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range u) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hgA : g ∈ riemannRochSpace A :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (huA j)

  have hureg : ∀ i j, u j ∈ (P i).toValuationSubring := by
    intro i j
    rcases eq_or_ne (u j) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · have h1 := ((mem_riemannRochSpace_iff.mp (huA j)) (P i)).resolve_left h0
      rw [hAP i, neg_zero] at h1
      exact Place.mem_toValuationSubring_of_ord_nonneg_alt _ h0 h1

  have hval : ∀ i, (P i).evalAt g = 0 := by
    intro i
    have h1 : (P i).evalAt g = ∑ j, c j * (P i).evalAt (u j) := by
      rw [hg]; exact evalAt_sum_smul_of_mem Finset.univ (P i) (hrat _) c (hureg i)
    have h2 : (Matrix.of fun i j => (P i).evalAt (u j)).mulVec c i = ∑ j, (P i).evalAt (u j) * c j := rfl
    have h3 := congrFun hMc i
    rw [h2, Pi.zero_apply] at h3
    rw [h1, ← h3]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  have hord : ∀ i, 1 ≤ (P i).ord g := by
    intro i
    have hge : 0 ≤ (P i).ord g := by
      have h1 := ((mem_riemannRochSpace_iff.mp hgA) (P i)).resolve_left hg0
      rw [hAP i, neg_zero] at h1
      exact h1
    by_contra hlt
    have h0 : (P i).ord g = 0 := by omega
    exact Place.evalAt_ne_zero_of_ord_eq_zero (P i) (hrat _) hg0 h0 (hval i)

  have hgAP : g ∈ riemannRochSpace (A - ∑ i, Finsupp.single (P i) 1) := by
    refine mem_riemannRochSpace_iff.mpr fun v => Or.inr ?_
    have hA := ((mem_riemannRochSpace_iff.mp hgA) v).resolve_left hg0
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.single_apply]
    by_cases hv : ∃ i, P i = v
    · obtain ⟨i, rfl⟩ := hv
      have hs : (∑ x, if P x = P i then (1 : ℤ) else 0) = 1 := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; rw [if_neg (fun h => hji (hP h))]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hs, hAP i]
      have := hord i
      omega
    · have hs : (∑ x, if P x = v then (1 : ℤ) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ => if_neg fun h => hv ⟨j, h⟩
      rw [hs, sub_zero]
      exact hA

  have hmem : g ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range u)
      ⊓ riemannRochSpace (A - ∑ i, Finsupp.single (P i) 1) := ⟨hgspan, hgAP⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hg0 hmem

end S_ModularCurve_det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot
end P2MW
export P2MW.S_ModularCurve_det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot (solution)
