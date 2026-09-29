-- Prove2me | solution 1 for ModularCurve.JZero.naiveHeight_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/072cf1fa-de52-50c4-a272-0555e4f39969

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Mathlib.NumberTheory.Height.MvPolynomial
import Theorems.Thm_ModularCurve_symVec_mem_of_stable
import Theorems.Thm_ModularCurve_JZero_exists_galoisStable_rep
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_naiveHeight_add_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

open ModularCurve AlgebraicCurve

noncomputable section

namespace P89MulDev

open Polynomial

section Generic

variable {E : Type*} [Field E]

private theorem coeffVec_ne_zero {m : ℕ} {P : Polynomial E} (hmonic : P.Monic)
    (hdeg : P.natDegree ≤ m) :
    (fun k : Fin (m + 1) => P.coeff (m - (k : ℕ))) ≠ 0 := by
  intro h
  have h1 := congrFun h (⟨m - P.natDegree, by omega⟩ : Fin (m + 1))
  have h2 : ((⟨m - P.natDegree, by omega⟩ : Fin (m + 1)) : ℕ) = m - P.natDegree := rfl
  rw [h2, Nat.sub_sub_self hdeg] at h1
  rw [hmonic.coeff_natDegree] at h1
  exact one_ne_zero h1

private theorem coeffVecK_ne_zero {F E' : Type*} [Field F] [Field E'] [Algebra F E']
    (K : IntermediateField F E') {m : ℕ} (w : Fin m → ↥K)
    (hw : (fun k => ((w k : E'))) ≠ 0) : w ≠ 0 := by
  intro h
  exact hw (by funext k; rw [h]; simp)

private theorem coeff_mul_eq_sum_filter {m n : ℕ} {P Q : Polynomial E}
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (j : Fin (m + n + 1)) :
    (P * Q).coeff (m + n - (j : ℕ)) =
      ∑ q ∈ Finset.univ.filter
        (fun q : Fin (m + 1) × Fin (n + 1) => (q.1 : ℕ) + (q.2 : ℕ) = (j : ℕ)),
        P.coeff (m - (q.1 : ℕ)) * Q.coeff (n - (q.2 : ℕ)) := by
  classical
  have hj : (j : ℕ) ≤ m + n := by omega
  rw [Polynomial.coeff_mul]
  rw [← Finset.sum_filter_of_ne
    (p := fun q : ℕ × ℕ => q.1 ≤ m ∧ q.2 ≤ n) ?_]
  · refine Finset.sum_bij'
      (i := fun (a : ℕ × ℕ)
        (ha : a ∈ (Finset.HasAntidiagonal.antidiagonal (m + n - (j : ℕ))).filter
          fun q => q.1 ≤ m ∧ q.2 ≤ n) =>
        ((⟨m - a.1, by
            have h1 := Finset.mem_filter.mp ha
            omega⟩ : Fin (m + 1)),
         (⟨n - a.2, by
            have h1 := Finset.mem_filter.mp ha
            omega⟩ : Fin (n + 1))))
      (j := fun (b : Fin (m + 1) × Fin (n + 1))
        (_ : b ∈ Finset.univ.filter
          fun q : Fin (m + 1) × Fin (n + 1) => (q.1 : ℕ) + (q.2 : ℕ) = (j : ℕ)) =>
        ((m - (b.1 : ℕ), n - (b.2 : ℕ)) : ℕ × ℕ))
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have h1 := Finset.mem_filter.mp ha
      have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp h1.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro b hb
      have h1 := (Finset.mem_filter.mp hb).2
      have hb1 := b.1.isLt
      have hb2 := b.2.isLt
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      omega
    · intro a ha
      have h1 := Finset.mem_filter.mp ha
      have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp h1.1
      obtain ⟨h3, h4⟩ := h1.2
      show (m - (m - a.1), n - (n - a.2)) = a
      refine Prod.ext ?_ ?_ <;> omega
    · intro b hb
      have h1 := (Finset.mem_filter.mp hb).2
      have hb1 := b.1.isLt
      have hb2 := b.2.isLt
      refine Prod.ext ?_ ?_ <;> apply Fin.ext <;> simp only [] <;> omega
    · intro a ha
      have h1 := Finset.mem_filter.mp ha
      have h3 : m - (m - a.1) = a.1 := by omega
      have h4 : n - (n - a.2) = a.2 := by omega
      simp only [h3, h4]
  · intro q hq hne
    by_contra hcon
    rcases Nat.lt_or_ge m q.1 with h1 | h1
    · exact hne (by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP h1), zero_mul])
    · rcases Nat.lt_or_ge n q.2 with h2 | h2
      · exact hne (by
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ h2), mul_zero])
      · exact hcon ⟨h1, h2⟩

private theorem logHeight_conv_le (E' : Type) [Field E'] [Height.AdmissibleAbsValues E']
    (m n : ℕ) :
    ∃ C : ℝ, ∀ (v : Fin (m + 1) → E') (w : Fin (n + 1) → E') (u : Fin (m + n + 1) → E'),
      v ≠ 0 → w ≠ 0 →
      (∀ j, u j = ∑ q ∈ Finset.univ.filter
          (fun q : Fin (m + 1) × Fin (n + 1) => (q.1 : ℕ) + (q.2 : ℕ) = (j : ℕ)),
          v q.1 * w q.2) →
      Height.logHeight u ≤ C + (Height.logHeight v + Height.logHeight w) := by
  classical
  set p : Fin (m + n + 1) → MvPolynomial (Fin (m + 1) × Fin (n + 1)) E' := fun j =>
    ∑ q ∈ Finset.univ.filter
      (fun q : Fin (m + 1) × Fin (n + 1) => (q.1 : ℕ) + (q.2 : ℕ) = (j : ℕ)),
      MvPolynomial.X q with hp
  have hom : ∀ j, (p j).IsHomogeneous 1 := fun j =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun q _ => MvPolynomial.isHomogeneous_X E' q
  obtain ⟨C, hC⟩ := Height.logHeight_eval_le' hom
  refine ⟨C, fun v w u hv hw hu => ?_⟩
  have hx := hC fun q : Fin (m + 1) × Fin (n + 1) => v q.1 * w q.2
  have heval : (fun j => MvPolynomial.eval
      (fun q : Fin (m + 1) × Fin (n + 1) => v q.1 * w q.2) (p j)) = u := by
    funext j
    rw [hu j]
    simp only [hp, map_sum, MvPolynomial.eval_X]
  have houter : Height.logHeight (fun q : Fin (m + 1) × Fin (n + 1) => v q.1 * w q.2)
      = Height.logHeight v + Height.logHeight w := by
    rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight,
      Height.logHeight_eq_log_mulHeight, Height.mulHeight_fun_mul_eq hv hw,
      Real.log_mul (Height.mulHeight_ne_zero v) (Height.mulHeight_ne_zero w)]
  rw [heval, houter, Nat.cast_one, one_mul] at hx
  linarith [hx]

end Generic

variable (N : ℕ) [NeZero N]

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

private theorem symPoly_add_of_nonneg
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hD : ∀ v, 0 ≤ D v) (hD' : ∀ v, 0 ≤ D' v) :
    symPoly N (D + D') = symPoly N D * symPoly N D' := by
  classical
  unfold ModularCurve.symPoly
  rw [Finsupp.prod_of_support_subset (D + D') Finsupp.support_add _ (fun v _ => by simp),
    Finsupp.prod_of_support_subset D Finset.subset_union_left _ (fun v _ => by simp),
    Finsupp.prod_of_support_subset D' Finset.subset_union_right _ (fun v _ => by simp),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have htn : (D v + D' v).toNat = (D v).toNat + (D' v).toNat := by
    have h1 := hD v
    have h2 := hD' v
    omega
  rw [Finsupp.add_apply, htn, pow_add]

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

private theorem divNaiveHeight_eq_logHeight (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : ∀ k, symVec N g' D k ∈ K) :
    divNaiveHeight N K g' D = Height.logHeight fun k => (⟨symVec N g' D k, h k⟩ : K) := by
  unfold ModularCurve.divNaiveHeight
  rw [dif_pos h]

end P89MulDev

theorem solution (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (g' : ℕ)
    (hR : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (g' : ℤ) ≤ Divisor.degree D →
        ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
          ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f) :
    ∃ A C : ℝ, 0 ≤ A ∧ ∀ x y : ↥(JZero N ^+ ↥K.fixingSubgroup),
      JZero.naiveHeight N K (2 * g') (x + y) ≤
        A * (JZero.naiveHeight N K g' x + JZero.naiveHeight N K g' y) + C := by
  classical
  obtain ⟨C₀, hC₀⟩ := P89MulDev.logHeight_conv_le (↥K) g' g'
  refine ⟨1, C₀, zero_le_one, fun x y => ?_⟩
  rw [two_mul g', one_mul]

  obtain ⟨D₁, E₁, h1eff, h1eq, h1st, h1mk⟩ :=
    ModularCurve.JZero.exists_galoisStable_rep N K g' hR (x : JZero N) x.2
  obtain ⟨D₂, E₂, h2eff, h2eq, h2st, h2mk⟩ :=
    ModularCurve.JZero.exists_galoisStable_rep N K g' hR (y : JZero N) y.2
  have hne_x : (JZero.repHeights N K g' x).Nonempty :=
    ⟨divNaiveHeight N K g' D₁, D₁, E₁, h1eff, h1eq, h1st, h1mk, rfl⟩
  have hne_y : (JZero.repHeights N K g' y).Nonempty :=
    ⟨divNaiveHeight N K g' D₂, D₂, E₂, h2eff, h2eq, h2st, h2mk, rfl⟩

  have hbound : ∀ r₁ ∈ JZero.repHeights N K g' x, ∀ r₂ ∈ JZero.repHeights N K g' y,
      JZero.naiveHeight N K (g' + g') (x + y) ≤ r₁ + r₂ + C₀ := by
    rintro r₁ ⟨D₁', E₁', h1eff', h1eq', h1st', h1mk', rfl⟩
      r₂ ⟨D₂', E₂', h2eff', h2eq', h2st', h2mk', rfl⟩
    have heff12 : ∀ v, 0 ≤ (D₁' + D₂') v := fun v => by
      rw [Finsupp.add_apply]
      exact add_nonneg (h1eff' v) (h2eff' v)
    have hshape12 : ((E₁' + E₂' : Divisor.degZero (K := AlgebraicClosure ℚ)
          (F := ↥(modularFunctionFieldBar N))) :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + ((g' + g' : ℕ) : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D₁' + D₂' := by
      have hcast : ((g' + g' : ℕ) : ℤ) = (g' : ℤ) + (g' : ℤ) := by push_cast; ring
      rw [AddSubgroup.coe_add, hcast, add_smul, ← h1eq', ← h2eq']
      abel
    have hst12 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) σ
          • (D₁' + D₂') = D₁' + D₂' := fun σ hσ => by
      rw [smul_add, h1st' σ hσ, h2st' σ hσ]
    have hmk12 : Pic0.mk (E₁' + E₂') = ((x + y : ↥(JZero N ^+ ↥K.fixingSubgroup)) : JZero N) := by
      rw [AddSubgroup.coe_add, Pic0.mk_add, h1mk', h2mk']

    have hd1 : (symPoly N D₁').natDegree ≤ g' :=
      P89MulDev.natDegree_symPoly_le N D₁' h1eff' (P89MulDev.sum_eq_of_rep N g' E₁' D₁' h1eq')
    have hd2 : (symPoly N D₂').natDegree ≤ g' :=
      P89MulDev.natDegree_symPoly_le N D₂' h2eff' (P89MulDev.sum_eq_of_rep N g' E₂' D₂' h2eq')
    have hmem1 : ∀ k, symVec N g' D₁' k ∈ K :=
      fun k => ModularCurve.symVec_mem_of_stable N K g' D₁' h1st' k
    have hmem2 : ∀ k, symVec N g' D₂' k ∈ K :=
      fun k => ModularCurve.symVec_mem_of_stable N K g' D₂' h2st' k
    have hmem12 : ∀ k, symVec N (g' + g') (D₁' + D₂') k ∈ K :=
      fun k => ModularCurve.symVec_mem_of_stable N K (g' + g') (D₁' + D₂') hst12 k

    have hne1' : (fun k : Fin (g' + 1) => (symPoly N D₁').coeff (g' - (k : ℕ))) ≠ 0 :=
      P89MulDev.coeffVec_ne_zero (P89MulDev.symPoly_monic N D₁') hd1
    have hne2' : (fun k : Fin (g' + 1) => (symPoly N D₂').coeff (g' - (k : ℕ))) ≠ 0 :=
      P89MulDev.coeffVec_ne_zero (P89MulDev.symPoly_monic N D₂') hd2
    have hne1 : (fun k : Fin (g' + 1) => (⟨symVec N g' D₁' k, hmem1 k⟩ : ↥K)) ≠ 0 :=
      P89MulDev.coeffVecK_ne_zero K _ hne1'
    have hne2 : (fun k : Fin (g' + 1) => (⟨symVec N g' D₂' k, hmem2 k⟩ : ↥K)) ≠ 0 :=
      P89MulDev.coeffVecK_ne_zero K _ hne2'

    have hu : ∀ j : Fin (g' + g' + 1),
        (⟨symVec N (g' + g') (D₁' + D₂') j, hmem12 j⟩ : ↥K) =
        ∑ q ∈ Finset.univ.filter
          (fun q : Fin (g' + 1) × Fin (g' + 1) => (q.1 : ℕ) + (q.2 : ℕ) = (j : ℕ)),
          (⟨symVec N g' D₁' q.1, hmem1 q.1⟩ : ↥K) * (⟨symVec N g' D₂' q.2, hmem2 q.2⟩ : ↥K) := by
      intro j
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul]
      show symVec N (g' + g') (D₁' + D₂') j = _
      unfold ModularCurve.symVec
      rw [P89MulDev.symPoly_add_of_nonneg N h1eff' h2eff']
      exact P89MulDev.coeff_mul_eq_sum_filter hd1 hd2 j
    calc JZero.naiveHeight N K (g' + g') (x + y)
        ≤ divNaiveHeight N K (g' + g') (D₁' + D₂') :=
          JZero.naiveHeight_le (g' + g') (x + y) (D₁' + D₂') (E₁' + E₂')
            heff12 hshape12 hst12 hmk12
      _ = Height.logHeight (fun j => (⟨symVec N (g' + g') (D₁' + D₂') j, hmem12 j⟩ : ↥K)) :=
          P89MulDev.divNaiveHeight_eq_logHeight N K (g' + g') _ hmem12
      _ ≤ C₀ + (Height.logHeight (fun k => (⟨symVec N g' D₁' k, hmem1 k⟩ : ↥K))
            + Height.logHeight (fun k => (⟨symVec N g' D₂' k, hmem2 k⟩ : ↥K))) :=
          hC₀ _ _ _ hne1 hne2 hu
      _ = divNaiveHeight N K g' D₁' + divNaiveHeight N K g' D₂' + C₀ := by
          rw [P89MulDev.divNaiveHeight_eq_logHeight N K g' _ hmem1,
            P89MulDev.divNaiveHeight_eq_logHeight N K g' _ hmem2]
          ring

  have step1 : ∀ r₁ ∈ JZero.repHeights N K g' x,
      JZero.naiveHeight N K (g' + g') (x + y) - C₀ - r₁ ≤ JZero.naiveHeight N K g' y := by
    intro r₁ hr₁
    exact le_csInf hne_y fun r₂ hr₂ => by linarith [hbound r₁ hr₁ r₂ hr₂]
  have step2 : JZero.naiveHeight N K (g' + g') (x + y) - C₀ - JZero.naiveHeight N K g' y
      ≤ JZero.naiveHeight N K g' x :=
    le_csInf hne_x fun r₁ hr₁ => by linarith [step1 r₁ hr₁]
  linarith [step2]

end

end S_ModularCurve_JZero_naiveHeight_add_le
end P2MW
export P2MW.S_ModularCurve_JZero_naiveHeight_add_le (solution)
