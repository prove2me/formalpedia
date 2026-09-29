-- Prove2me | solution 1 for ModularCurve.JZero.naiveHeight_northcott
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/47ae4c8b-4185-5638-82f0-31356ebc2dfb

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.Order.Northcott
import Theorems.Thm_northcott_projMulHeight_numberField
import Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_symVec_mem_of_stable
import Theorems.Thm_ModularCurve_JZero_exists_galoisStable_rep
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_naiveHeight_northcott
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

open ModularCurve AlgebraicCurve

noncomputable section

namespace P7Dev

open Polynomial

section Generic

variable {E : Type*} [Field E]

private theorem sum_coeff_eq {g' : ℕ} {P : Polynomial E} (hP : P.natDegree ≤ g') :
    (∑ k : Fin (g' + 1), Polynomial.C (P.coeff (g' - (k : ℕ))) * Polynomial.X ^ (g' - (k : ℕ))) = P := by
  ext n
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hn : n ≤ g'
  · have h0 : ∀ b ∈ (Finset.univ : Finset (Fin (g' + 1))),
        b ≠ (⟨g' - n, by omega⟩ : Fin (g' + 1)) →
        (if n = g' - (b : ℕ) then P.coeff (g' - (b : ℕ)) else 0) = 0 := by
      intro k _ hk
      have hk' := k.isLt
      exact if_neg fun hEq => hk (by apply Fin.ext; show (k : ℕ) = g' - n; omega)
    rw [Finset.sum_eq_single_of_mem (⟨g' - n, by omega⟩ : Fin (g' + 1)) (Finset.mem_univ _) h0]
    have hval : (((⟨g' - n, by omega⟩ : Fin (g' + 1))) : ℕ) = g' - n := rfl
    rw [hval, Nat.sub_sub_self hn, if_pos rfl]
  · rw [not_le] at hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hn)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk' := k.isLt
    exact if_neg (by omega)

private def IsNormalized {m : ℕ} (w : Fin m → E) : Prop :=
  ∃ i, w i = 1 ∧ ∀ j, j < i → w j = 0

private theorem IsNormalized.ne_zero {m : ℕ} {w : Fin m → E} (hw : IsNormalized w) : w ≠ 0 := by
  obtain ⟨i, hi1, -⟩ := hw
  intro h
  rw [h] at hi1
  simp at hi1

private theorem IsNormalized.eq_of_smul {m : ℕ} {w w' : Fin m → E} (hw : IsNormalized w)
    (hw' : IsNormalized w') {t : E} (h : t • w' = w) : w' = w := by
  obtain ⟨i, hi1, hi0⟩ := hw
  obtain ⟨i', hi'1, hi'0⟩ := hw'
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exfalso
    have hzero : w i = 0 := by
      rw [← h]
      simp [hi'0 i hlt]
    rw [hi1] at hzero
    exact one_ne_zero hzero
  · subst heq
    have ht : t = 1 := by
      have hti : w i = t * w' i := by rw [← h]; simp [smul_eq_mul]
      rw [hi1, hi'1, mul_one] at hti
      exact hti.symm
    funext j
    have htj : w j = t * w' j := by rw [← h]; simp [smul_eq_mul]
    rw [htj, ht, one_mul]
  · exfalso
    have ht : t = 0 := by
      have hti : w i' = t * w' i' := by rw [← h]; simp [smul_eq_mul]
      rw [hi0 i' hgt, hi'1, mul_one] at hti
      exact hti.symm
    have hzero : w i = 0 := by
      rw [← h]
      simp [smul_eq_mul, ht]
    rw [hi1] at hzero
    exact one_ne_zero hzero

private theorem isNormalized_coeffVec {g' : ℕ} {P : Polynomial E} (hmonic : P.Monic)
    (hdeg : P.natDegree ≤ g') :
    IsNormalized (fun k : Fin (g' + 1) => P.coeff (g' - (k : ℕ))) := by
  refine ⟨⟨g' - P.natDegree, by omega⟩, ?_, ?_⟩
  · show P.coeff (g' - (g' - P.natDegree)) = 1
    rw [Nat.sub_sub_self hdeg]
    exact hmonic.coeff_natDegree
  · intro j hj
    have hj' : (j : ℕ) < g' - P.natDegree := hj
    have hjlt := j.isLt
    show P.coeff (g' - (j : ℕ)) = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private theorem isNormalized_lift {F E' : Type*} [Field F] [Field E'] [Algebra F E']
    (K : IntermediateField F E') {m : ℕ} (w : Fin m → ↥K)
    (h : IsNormalized fun k => ((w k : E'))) : IsNormalized w := by
  obtain ⟨i, hi1, hi0⟩ := h
  exact ⟨i, Subtype.ext hi1, fun j hj => Subtype.ext (hi0 j hj)⟩

private theorem finite_isNormalized_mulHeight_le {E' : Type*} [Field E']
    [Height.AdmissibleAbsValues E'] {m : ℕ}
    (hN : Northcott (Projectivization.mulHeight : Projectivization E' (Fin (m + 1) → E') → ℝ))
    (R : ℝ) :
    {w : Fin (m + 1) → E' | IsNormalized w ∧ Height.mulHeight w ≤ R}.Finite := by
  classical
  have hone : (fun _ : Fin (m + 1) => (1 : E')) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  refine Set.Finite.of_finite_image (f := fun w =>
    if h : w = 0 then Projectivization.mk E' _ hone else Projectivization.mk E' w h) ?_ ?_
  · refine Set.Finite.subset (hN.finite_le R) ?_
    rintro x ⟨w, ⟨hwn, hwH⟩, rfl⟩
    have hw0 : w ≠ 0 := hwn.ne_zero
    simp only [Set.mem_setOf_eq, dif_neg hw0, Projectivization.mulHeight_mk hw0]
    exact hwH
  · rintro w₁ ⟨hw₁n, -⟩ w₂ ⟨hw₂n, -⟩ hEq
    simp only [dif_neg hw₁n.ne_zero, dif_neg hw₂n.ne_zero] at hEq
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' E' _ _ _ _).mp hEq
    exact (hw₁n.eq_of_smul hw₂n ht).symm

private theorem finite_finsupp_bounded {α : Type*} (S : Finset α) (m : ℕ) :
    {μ : α →₀ ℤ | μ.support ⊆ S ∧ ∀ v, 0 ≤ μ v ∧ μ v ≤ (m : ℤ)}.Finite := by
  classical
  haveI hfinI : Finite ↥(Set.Icc (0 : ℤ) (m : ℤ)) := (Set.finite_Icc _ _).to_subtype
  haveI hfinS : Finite ↥(S : Set α) := S.finite_toSet.to_subtype
  refine Set.Finite.of_finite_image (f := fun (μ : α →₀ ℤ) (v : ↥(S : Set α)) =>
    (⟨max 0 (min (μ v) (m : ℤ)), by simp only [Set.mem_Icc]; omega⟩ :
      ↥(Set.Icc (0 : ℤ) (m : ℤ)))) (Set.toFinite _) ?_
  rintro μ₁ ⟨hs₁, hb₁⟩ μ₂ ⟨hs₂, hb₂⟩ hEq
  ext v
  by_cases hv : v ∈ S
  · have hfun := congrFun hEq ⟨v, hv⟩
    have hval := congrArg Subtype.val hfun
    simp only at hval
    obtain ⟨h1l, h1r⟩ := hb₁ v
    obtain ⟨h2l, h2r⟩ := hb₂ v
    rw [min_eq_left h1r, max_eq_right h1l, min_eq_left h2r, max_eq_right h2l] at hval
    exact hval
  · have h1 : μ₁ v = 0 := by
      by_contra h
      exact hv (hs₁ (Finsupp.mem_support_iff.mpr h))
    have h2 : μ₂ v = 0 := by
      by_contra h
      exact hv (hs₂ (Finsupp.mem_support_iff.mpr h))
    rw [h1, h2]

private theorem apply_le_sum {α : Type*} (μ : α →₀ ℤ) (h0 : ∀ v, 0 ≤ μ v) (v : α) :
    μ v ≤ μ.sum fun _ n => n := by
  classical
  by_cases hv : v ∈ μ.support
  · exact Finset.single_le_sum (f := fun w => μ w) (fun i _ => h0 i) hv
  · have hz : μ v = 0 := by
      by_contra h
      exact hv (Finsupp.mem_support_iff.mpr h)
    rw [hz]
    exact Finset.sum_nonneg fun i _ => h0 i

end Generic

variable (N : ℕ) [NeZero N]

private abbrev jBar : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

private def cusps : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
  {v | v.ord (jBar N) < 0}

private def fiber (c : AlgebraicClosure ℚ) :
    Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
  {v | 0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)}

open scoped Classical in

private def targetSet (P : Polynomial (AlgebraicClosure ℚ)) :
    Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
  cusps N ∪ ⋃ c ∈ P.roots.toFinset, fiber N c

private theorem targetSet_finite (P : Polynomial (AlgebraicClosure ℚ)) :
    (targetSet N P).Finite := by
  classical
  exact Set.Finite.union ((ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).2.2)
    (Set.Finite.biUnion (Multiset.toFinset _).finite_toSet
      fun c _ => (ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).2.1 c)

private theorem jFactor_monic (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (jFactor N v).Monic := by
  unfold ModularCurve.jFactor
  split_ifs
  · exact Polynomial.monic_X_sub_C _
  · exact Polynomial.monic_one

private theorem jFactor_natDegree_le (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (jFactor N v).natDegree ≤ 1 := by
  unfold ModularCurve.jFactor
  split_ifs
  · exact le_of_eq (Polynomial.natDegree_X_sub_C _)
  · simp

private theorem symPoly_monic (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (symPoly N D).Monic := by
  unfold ModularCurve.symPoly
  exact Polynomial.monic_prod_of_monic _ _ fun v _ => (jFactor_monic N v).pow _

private theorem sum_eq_of_rep (g' : ℕ)
    (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hE : (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D) :
    (D.sum fun _ n => n) = (g' : ℤ) := by
  classical
  have hker : Divisor.degree (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) = 0 :=
    E.2
  have hdegD : Divisor.degree D = (g' : ℤ) := by
    rw [← hE, map_add, map_zsmul, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), hker]
    simp
  have hdeg_sum : Divisor.degree D = D.sum fun _ n => n := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply]
    exact Finsupp.sum_congr fun v _ => by
      rw [AddMonoidHom.mulRight_apply,
        ModularCurve.deg_eq_one_modularFunctionFieldBar N v]
      simp
  rw [← hdeg_sum, hdegD]

private theorem natDegree_symPoly_le (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (heff : ∀ v, 0 ≤ D v) {g' : ℕ} (hsum : (D.sum fun _ n => n) = (g' : ℤ)) :
    (symPoly N D).natDegree ≤ g' := by
  classical
  have h1 : (symPoly N D).natDegree
      = ∑ v ∈ D.support, ((jFactor N v) ^ (D v).toNat).natDegree := by
    unfold ModularCurve.symPoly
    exact Polynomial.natDegree_prod _ _ fun v _ => ((jFactor_monic N v).pow _).ne_zero
  have h2 : ∀ v ∈ D.support, ((jFactor N v) ^ (D v).toNat).natDegree ≤ (D v).toNat := by
    intro v _
    rw [Polynomial.natDegree_pow]
    calc (D v).toNat * (jFactor N v).natDegree ≤ (D v).toNat * 1 :=
          Nat.mul_le_mul le_rfl (jFactor_natDegree_le N v)
      _ = (D v).toNat := mul_one _
  have h3 : (symPoly N D).natDegree ≤ ∑ v ∈ D.support, (D v).toNat :=
    h1 ▸ Finset.sum_le_sum h2
  have h4 : (∑ v ∈ D.support, ((D v).toNat : ℤ)) = (g' : ℤ) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun v _ => Int.toNat_of_nonneg (heff v)
  have h5 : ((∑ v ∈ D.support, (D v).toNat : ℕ) : ℤ) = (g' : ℤ) := by
    rw [Nat.cast_sum]
    exact h4
  have h6 : ∑ v ∈ D.support, (D v).toNat = g' := Nat.cast_injective h5
  omega

private theorem support_subset (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (heff : ∀ v, 0 ≤ D v) :
    ↑D.support ⊆ targetSet N (symPoly N D) := by
  classical
  intro v hv
  rw [Finset.mem_coe, Finsupp.mem_support_iff] at hv
  show v ∈ cusps N ∪ ⋃ c ∈ (symPoly N D).roots.toFinset, fiber N c
  by_cases hcusp : v.ord (jBar N) < 0
  · exact Set.mem_union_left _ hcusp
  · rw [not_lt] at hcusp
    have hex : ∃ c : AlgebraicClosure ℚ,
        0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) :=
      ((ModularCurve.jCoordinate_spec_modularFunctionFieldBar N).1 v hcusp).exists
    have hspec : 0 < v.ord (jBar N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (jCoord N v)) := by
      unfold ModularCurve.jCoord
      exact Classical.epsilon_spec hex
    have hpos : 0 < D v := lt_of_le_of_ne (heff v) hv.symm
    have hdvd : (Polynomial.X - Polynomial.C (jCoord N v)) ∣ symPoly N D := by
      have h1 : (Polynomial.X - Polynomial.C (jCoord N v)) ∣ (jFactor N v) ^ (D v).toNat := by
        rw [jFactor_of_nonneg hcusp]
        exact dvd_pow_self _ (by omega)
      exact h1.trans (Finset.dvd_prod_of_mem _ (Finsupp.mem_support_iff.mpr hv))
    have hroot : jCoord N v ∈ (symPoly N D).roots.toFinset := by
      rw [Multiset.mem_toFinset,
        Polynomial.mem_roots ((symPoly_monic N D).ne_zero)]
      exact Polynomial.dvd_iff_isRoot.mp hdvd
    exact Set.mem_union_right _ (Set.mem_biUnion hroot hspec)

private theorem divNaiveHeight_eq_logHeight (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : ∀ k, symVec N g' D k ∈ K) :
    divNaiveHeight N K g' D = Height.logHeight fun k => (⟨symVec N g' D k, h k⟩ : K) := by
  unfold ModularCurve.divNaiveHeight
  rw [dif_pos h]

end P7Dev

theorem solution (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f) :
    Northcott (JZero.naiveHeight N K g') := by
  classical
  refine ⟨fun B => ?_⟩

  have hvec : {w : Fin (g' + 1) → ↥K |
      P7Dev.IsNormalized w ∧ Height.mulHeight w ≤ Real.exp (B + 1)}.Finite :=
    P7Dev.finite_isNormalized_mulHeight_le
      (northcott_projMulHeight_numberField ↥K (Fin (g' + 1))) _

  have hDfin : {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
      (∀ v, 0 ≤ D v) ∧ (D.sum fun _ n => n) = (g' : ℤ) ∧
      (∀ k, symVec N g' D k ∈ K) ∧ divNaiveHeight N K g' D ≤ B + 1}.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hvec fun w _ =>
      P7Dev.finite_finsupp_bounded
        ((P7Dev.targetSet_finite N (∑ k : Fin (g' + 1),
          Polynomial.C ((w k : AlgebraicClosure ℚ)) * Polynomial.X ^ (g' - (k : ℕ)))).toFinset)
        g') ?_
    rintro D ⟨heff, hsum, hmem, hle⟩
    have hdeg : (symPoly N D).natDegree ≤ g' := P7Dev.natDegree_symPoly_le N D heff hsum
    have hnormK : P7Dev.IsNormalized (fun k => (⟨symVec N g' D k, hmem k⟩ : K)) :=
      P7Dev.isNormalized_lift K _
        (P7Dev.isNormalized_coeffVec (P7Dev.symPoly_monic N D) hdeg)
    have hle' : Height.logHeight (fun k => (⟨symVec N g' D k, hmem k⟩ : K)) ≤ B + 1 := by
      rw [← P7Dev.divNaiveHeight_eq_logHeight N K g' D hmem]
      exact hle
    have hH : Height.mulHeight (fun k => (⟨symVec N g' D k, hmem k⟩ : K)) ≤ Real.exp (B + 1) := by
      calc Height.mulHeight (fun k => (⟨symVec N g' D k, hmem k⟩ : K))
          = Real.exp (Real.log (Height.mulHeight (fun k => (⟨symVec N g' D k, hmem k⟩ : K)))) :=
            (Real.exp_log (Height.mulHeight_pos _)).symm
        _ ≤ Real.exp (B + 1) := Real.exp_le_exp.mpr hle'
    refine Set.mem_biUnion (⟨hnormK, hH⟩ :
      (fun k => (⟨symVec N g' D k, hmem k⟩ : K)) ∈ {w : Fin (g' + 1) → ↥K |
        P7Dev.IsNormalized w ∧ Height.mulHeight w ≤ Real.exp (B + 1)}) ?_
    refine ⟨?_, fun v => ⟨heff v, ?_⟩⟩
    · intro v hv
      rw [Set.Finite.mem_toFinset]
      show v ∈ P7Dev.targetSet N (∑ k : Fin (g' + 1),
        Polynomial.C ((symPoly N D).coeff (g' - (k : ℕ))) * Polynomial.X ^ (g' - (k : ℕ)))
      rw [P7Dev.sum_coeff_eq hdeg]
      exact P7Dev.support_subset N D heff (Finset.mem_coe.mpr hv)
    · calc D v ≤ D.sum fun _ n => n := P7Dev.apply_le_sum D heff v
        _ = (g' : ℤ) := hsum

  have key : ∀ c : ↥(JZero N ^+ ↥K.fixingSubgroup), JZero.naiveHeight N K g' c ≤ B →
      ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)),
          (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
              + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D ∧ Pic0.mk E = (c : JZero N)) ∧
        (∀ v, 0 ≤ D v) ∧ (D.sum fun _ n => n) = (g' : ℤ) ∧
        (∀ k, symVec N g' D k ∈ K) ∧ divNaiveHeight N K g' D ≤ B + 1 := by
    intro c hc
    obtain ⟨D₁, E₁, h1eff, h1eq, h1st, h1mk⟩ :=
      ModularCurve.JZero.exists_galoisStable_rep N K g' hR (c : JZero N) c.2
    have hne : (JZero.repHeights N K g' c).Nonempty :=
      ⟨divNaiveHeight N K g' D₁, D₁, E₁, h1eff, h1eq, h1st, h1mk, rfl⟩
    have hbdd : BddBelow (JZero.repHeights N K g' c) :=
      ⟨0, fun r hr => JZero.repHeights_nonneg hr⟩
    have hlt : sInf (JZero.repHeights N K g' c) < B + 1 :=
      lt_of_le_of_lt hc (lt_add_one B)
    obtain ⟨r, hrmem, hrlt⟩ := (csInf_lt_iff hbdd hne).mp hlt
    obtain ⟨D, E, heff, heq, hst, hmk, rfl⟩ := hrmem
    exact ⟨D, ⟨E, heq, hmk⟩, heff, P7Dev.sum_eq_of_rep N g' E D heq,
      fun k => ModularCurve.symVec_mem_of_stable N K g' D hst k, hrlt.le⟩

  refine Set.Finite.of_finite_image (f := fun c =>
    if hc : JZero.naiveHeight N K g' c ≤ B then (key c hc).choose else 0) ?_ ?_
  · refine Set.Finite.subset hDfin ?_
    rintro _ ⟨c, hc, rfl⟩
    have hc' : JZero.naiveHeight N K g' c ≤ B := hc
    obtain ⟨-, h2, h3, h4, h5⟩ := (key c hc').choose_spec
    simp only [dif_pos hc']
    exact ⟨h2, h3, h4, h5⟩
  · intro c₁ hc₁ c₂ hc₂ hEq
    have hc₁' : JZero.naiveHeight N K g' c₁ ≤ B := hc₁
    have hc₂' : JZero.naiveHeight N K g' c₂ ≤ B := hc₂
    simp only [dif_pos hc₁', dif_pos hc₂'] at hEq
    obtain ⟨⟨E₁, heq₁, hmk₁⟩, -⟩ := (key c₁ hc₁').choose_spec
    obtain ⟨⟨E₂, heq₂, hmk₂⟩, -⟩ := (key c₂ hc₂').choose_spec
    rw [hEq] at heq₁
    have hE : (E₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        = (E₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
      add_right_cancel (heq₁.trans heq₂.symm)
    have hEE : E₁ = E₂ := Subtype.ext hE
    apply Subtype.ext
    rw [← hmk₁, ← hmk₂, hEE]

end

end S_ModularCurve_JZero_naiveHeight_northcott
end P2MW
export P2MW.S_ModularCurve_JZero_naiveHeight_northcott (solution)
