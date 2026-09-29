-- Prove2me | solution 1 for ModularCurve.jqModC_mem_adjoin_jqNModC_of_prime_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/20b95dca-f406-5576-9c41-e0f856b011cf

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open ModularCurve Polynomial IntermediateField

namespace JGenDual

section Bivariate

theorem eval₂_swapBivar {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    (swapBivar Φ).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) y) x
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y := by
  have key1 : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) y) x).comp swapInner
      = Polynomial.eval₂RingHom (Int.castRingHom R) x := by
    apply Polynomial.ringHom_ext
    · intro n
      simp [swapInner]
    · simp [swapInner]
  have key : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) y) x).comp swapBivar
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) y := by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : swapBivar (Polynomial.C a) = swapInner a := by
        simp [swapBivar]
      rw [RingHom.comp_apply, h1]
      have h2 := congrFun (congrArg DFunLike.coe key1) a
      rw [RingHom.comp_apply] at h2
      rw [h2]
      simp
    · rw [RingHom.comp_apply, swapBivar_X]
      simp
  have := congrFun (congrArg DFunLike.coe key) Φ
  simpa using this

theorem eval₂_comm_of_evalSymm {R : Type*} [CommRing R] {Φ : Polynomial (Polynomial ℤ)}
    (h : EvalSymm Φ) (x y : R) :
    Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) y) x := by
  rw [← eval₂_swapBivar Φ y x, swapBivar_eq_of_evalSymm h]

variable (K : Type*) [Field K]

theorem eval₂_phi_jd_jdn {n : ℕ} [NeZero n] (data : ModularPolynomialData n) (d : ℕ) [NeZero d] :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqNModC K d))
      (jqNModC K (d * n)) = 0 := by
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero data K d
  have h3 : (Polynomial.aeval (R := ℤ) (jqNModC K d)).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqNModC K d) := by
    apply Polynomial.ringHom_ext
    · intro m; simp
    · simp
  rw [← h3]
  exact h

end Bivariate

section FibreOverSubfield

variable {K : Type*} [Field K]

def fibreAt (Φ : Polynomial (Polynomial ℤ)) (A : IntermediateField K (LaurentSeries K)) (c : A) :
    Polynomial A :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)

theorem fibreAt_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (A : IntermediateField K (LaurentSeries K)) (c : A) : (fibreAt Φ A c).Monic :=
  hΦ.map _

theorem fibreAt_natDegree {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (A : IntermediateField K (LaurentSeries K)) (c : A) : (fibreAt Φ A c).natDegree = Φ.natDegree :=
  hΦ.natDegree_map _

theorem fibreAt_map_val (Φ : Polynomial (Polynomial ℤ)) (A : IntermediateField K (LaurentSeries K)) (c : A) :
    (fibreAt Φ A c).map (algebraMap A (LaurentSeries K))
      = Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (c : LaurentSeries K)) := by
  unfold fibreAt
  rw [Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro m; simp
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl

theorem aeval_fibreAt (Φ : Polynomial (Polynomial ℤ)) (A : IntermediateField K (LaurentSeries K)) (c : A)
    (y : LaurentSeries K) :
    Polynomial.aeval y (fibreAt Φ A c)
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (c : LaurentSeries K)) y := by
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, fibreAt_map_val, Polynomial.eval_map]

theorem fibreAt_map_equiv (Φ : Polynomial (Polynomial ℤ)) {A B : IntermediateField K (LaurentSeries K)}
    (e : A ≃ₐ[K] B) (c : A) :
    (fibreAt Φ A c).map (e : A →+* B) = fibreAt Φ B (e c) := by
  unfold fibreAt
  rw [Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro m; simp
  · simp

theorem fibreAt_irreducible_equiv (Φ : Polynomial (Polynomial ℤ)) {A B : IntermediateField K (LaurentSeries K)}
    (e : A ≃ₐ[K] B) (c : A) (h : Irreducible (fibreAt Φ A c)) : Irreducible (fibreAt Φ B (e c)) := by
  rw [← fibreAt_map_equiv]
  have hme : (fibreAt Φ A c).map (e : A →+* B) = Polynomial.mapEquiv (e : A ≃+* B) (fibreAt Φ A c) := rfl
  rw [hme]
  exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (e : A ≃+* B))).mpr h

end FibreOverSubfield

section Degrees

variable {K : Type*} [Field K]

theorem relfinrank_eq_natDegree_minpoly (A B : IntermediateField K (LaurentSeries K)) (x : LaurentSeries K)
    (hx : IsIntegral A x) (hAB : A ≤ B) (hB : B = adjoin K ((A : Set (LaurentSeries K)) ∪ {x})) :
    relfinrank A B = (minpoly A x).natDegree := by
  subst hB
  rw [relfinrank_eq_finrank_of_le hAB, extendScalars_adjoin hAB]
  have h : adjoin A ((A : Set (LaurentSeries K)) ∪ {x}) = adjoin A ({x} : Set (LaurentSeries K)) := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact (adjoin A ({x} : Set (LaurentSeries K))).algebraMap_mem ⟨y, hy⟩
      · exact subset_adjoin A _ hy
    · exact adjoin.mono _ _ _ Set.subset_union_right
  rw [h]
  exact adjoin.finrank hx

theorem irreducible_of_root_of_natDegree_le (A B : IntermediateField K (LaurentSeries K)) (x : LaurentSeries K)
    (hAB : A ≤ B) (hB : B = adjoin K ((A : Set (LaurentSeries K)) ∪ {x}))
    (P : Polynomial A) (hP : P.Monic) (hroot : Polynomial.aeval x P = 0)
    (hdeg : P.natDegree ≤ relfinrank A B) : Irreducible P := by
  have hx : IsIntegral A x := ⟨P, hP, by rwa [Polynomial.aeval_def] at hroot⟩
  have hmin : minpoly A x ∣ P := minpoly.dvd A x hroot
  have hdeg' : P.natDegree ≤ (minpoly A x).natDegree := by
    rw [← relfinrank_eq_natDegree_minpoly A B x hx hAB hB]; exact hdeg
  have hEq : P = minpoly A x :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) hP hmin hdeg'
  rw [hEq]
  exact minpoly.irreducible hx

end Degrees

section Modular

variable (K : Type*) [Field K] (s ℓ : ℕ) [NeZero s] [NeZero ℓ] [NeZero (s * ℓ)]

theorem jqNModC_mul' (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    jqNModC K (a * b) = qExpand K b (jqNModC K a) := by
  unfold jqNModC
  rw [qExpand_qExpand, qExpand_congr (Nat.mul_comm b a)]

theorem jqNModC_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) : jqNModC K a = jqNModC K b := by
  subst h; rfl

abbrev bigL : IntermediateField K (LaurentSeries K) := modularFunctionFieldFullC K (s * ℓ)

abbrev fS : IntermediateField K (LaurentSeries K) := modularFunctionFieldFullC K s

abbrev eE : IntermediateField K (LaurentSeries K) := (modularFunctionFieldFullC K s).map (qExpandAlgHomC K ℓ)

abbrev kPrime : IntermediateField K (LaurentSeries K) :=
  adjoin K ({jqNModC K s, jqNModC K ℓ, jqNModC K (s * ℓ)} : Set (LaurentSeries K))

theorem jqModC_mem_fS : jqModC K ∈ fS K s := jqModC_mem_full K s

theorem jqNModC_mem_fS : jqNModC K s ∈ fS K s := jqModCd_mem_full K s dvd_rfl

theorem jℓ_mem_eE : jqNModC K ℓ ∈ eE K s ℓ :=
  ⟨jqModC K, jqModC_mem_fS K s, rfl⟩

theorem jsℓ_mem_eE : jqNModC K (s * ℓ) ∈ eE K s ℓ :=
  ⟨jqNModC K s, jqNModC_mem_fS K s, by
    show qExpand K ℓ (jqNModC K s) = jqNModC K (s * ℓ)
    rw [← jqNModC_mul']⟩

theorem eE_le_kPrime (p : ℕ) [CharP K p] (hps : ¬ p ∣ s) : eE K s ℓ ≤ kPrime K s ℓ := by
  have hF : fS K s = adjoin K ({jqModC K, jqNModC K s} : Set (LaurentSeries K)) := by
    show modularFunctionFieldFullC K s = _
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC K p s hps]
    rfl
  show (fS K s).map (qExpandAlgHomC K ℓ) ≤ _
  rw [hF, adjoin_map, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · refine subset_adjoin K _ (Or.inr (Or.inl ?_))
    show qExpand K ℓ (jqModC K) = jqNModC K ℓ
    rfl
  · refine subset_adjoin K _ (Or.inr (Or.inr ?_))
    rw [Set.mem_singleton_iff]
    show qExpand K ℓ (jqNModC K s) = jqNModC K (s * ℓ)
    rw [← jqNModC_mul']

theorem kPrime_le_bigL : kPrime K s ℓ ≤ bigL K s ℓ := by
  rw [adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact jqModCd_mem_full K (s * ℓ) (dvd_mul_right s ℓ)
  · exact jqModCd_mem_full K (s * ℓ) (dvd_mul_left ℓ s)
  · exact jqModCd_mem_full K (s * ℓ) dvd_rfl

theorem fS_le_bigL : fS K s ≤ bigL K s ℓ := full_degeneracyC_le K (dvd_mul_right s ℓ)

theorem eE_le_bigL : eE K s ℓ ≤ bigL K s ℓ := full_degeneracyC_map_le K s ℓ

theorem bigL_eq_adjoin_fS (p : ℕ) [CharP K p] (hpsℓ : ¬ p ∣ s * ℓ) :
    bigL K s ℓ = adjoin K ((fS K s : Set (LaurentSeries K)) ∪ {jqNModC K (s * ℓ)}) := by
  apply le_antisymm
  · show modularFunctionFieldFullC K (s * ℓ) ≤ _
    rw [← modularFunctionFieldC_eq_modularFunctionFieldFullC K p (s * ℓ) hpsℓ]
    show adjoin K {jqModC K, jqNModC K (s * ℓ)} ≤ _
    apply adjoin.mono
    intro x hx
    rcases hx with rfl | rfl
    · exact Or.inl (jqModC_mem_fS K s)
    · exact Or.inr rfl
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact fS_le_bigL K s ℓ hx
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact jqModCd_mem_full K (s * ℓ) dvd_rfl

theorem kPrime_eq_adjoin_eE (p : ℕ) [CharP K p] (hps : ¬ p ∣ s) :
    kPrime K s ℓ = adjoin K ((eE K s ℓ : Set (LaurentSeries K)) ∪ {jqNModC K s}) := by
  apply le_antisymm
  · apply adjoin.mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (jℓ_mem_eE K s ℓ)
    · exact Or.inl (jsℓ_mem_eE K s ℓ)
  · rw [adjoin_le_iff]
    rintro x (hx | hx)
    · exact eE_le_kPrime K s ℓ p hps hx
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact subset_adjoin K _ (Or.inl rfl)

theorem relfinrank_fS_and_eE (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ) (hK : ((s * ℓ : ℕ) : K) ≠ 0) :
    relfinrank (fS K s) (bigL K s ℓ) = dedekindPsi ℓ ∧ relfinrank (eE K s ℓ) (bigL K s ℓ) = dedekindPsi ℓ := by
  have h := relfinrank_modularFunctionFieldFullC_mul_dedekindPsi K s ℓ hK
  have hcop : Nat.Coprime s ℓ := (Nat.coprime_primes hs hℓ).mpr hne
  rw [dedekindPsi_mul_of_coprime s ℓ hcop] at h
  have hpos : 0 < dedekindPsi s := dedekindPsi_pos s (NeZero.ne s)
  constructor
  · apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h.1, Nat.mul_comm]
  · apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h.2, Nat.mul_comm]

def jsF : fS K s := ⟨jqNModC K s, jqNModC_mem_fS K s⟩

theorem irreducible_fibreAt_fS (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ) (hK : ((s * ℓ : ℕ) : K) ≠ 0)
    (p : ℕ) [CharP K p] (hpsℓ : ¬ p ∣ s * ℓ) (data : ModularPolynomialData ℓ) :
    Irreducible (fibreAt data.Φ (fS K s) (jsF K s)) := by
  refine irreducible_of_root_of_natDegree_le (fS K s) (bigL K s ℓ) (jqNModC K (s * ℓ))
    (fS_le_bigL K s ℓ) (bigL_eq_adjoin_fS K s ℓ p hpsℓ) _ (fibreAt_monic data.monic _ _) ?_ ?_
  · rw [aeval_fibreAt]
    exact eval₂_phi_jd_jdn K data s
  · rw [fibreAt_natDegree data.monic, data.natDegree_eq, (relfinrank_fS_and_eE K s ℓ hs hℓ hne hK).1]

def sigma : fS K s ≃ₐ[K] eE K s ℓ := (modularFunctionFieldFullC K s).equivMap (qExpandAlgHomC K ℓ)

theorem sigma_jsF : (sigma K s ℓ (jsF K s) : LaurentSeries K) = jqNModC K (s * ℓ) := by
  show qExpandAlgHomC K ℓ (jqNModC K s) = _
  rw [qExpandAlgHomC_apply, ← jqNModC_mul']

theorem irreducible_fibreAt_eE (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ) (hK : ((s * ℓ : ℕ) : K) ≠ 0)
    (p : ℕ) [CharP K p] (hpsℓ : ¬ p ∣ s * ℓ) (data : ModularPolynomialData ℓ) :
    Irreducible (fibreAt data.Φ (eE K s ℓ) (sigma K s ℓ (jsF K s))) :=
  fibreAt_irreducible_equiv data.Φ (sigma K s ℓ) (jsF K s) (irreducible_fibreAt_fS K s ℓ hs hℓ hne hK p hpsℓ data)

theorem aeval_js_fibreAt_eE {data : ModularPolynomialData ℓ} (hsymm : EvalSymm data.Φ) :
    Polynomial.aeval (jqNModC K s) (fibreAt data.Φ (eE K s ℓ) (sigma K s ℓ (jsF K s))) = 0 := by
  rw [aeval_fibreAt, sigma_jsF, eval₂_comm_of_evalSymm hsymm]
  exact eval₂_phi_jd_jdn K data s

theorem relfinrank_eE_kPrime (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ) (hK : ((s * ℓ : ℕ) : K) ≠ 0)
    (p : ℕ) [CharP K p] (hpsℓ : ¬ p ∣ s * ℓ) (hps : ¬ p ∣ s) :
    relfinrank (eE K s ℓ) (kPrime K s ℓ) = dedekindPsi ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  set P := fibreAt data.Φ (eE K s ℓ) (sigma K s ℓ (jsF K s)) with hP
  have hmonic : P.Monic := fibreAt_monic data.monic _ _
  have hroot : Polynomial.aeval (jqNModC K s) P = 0 := aeval_js_fibreAt_eE K s ℓ hsymm
  have hirr : Irreducible P := irreducible_fibreAt_eE K s ℓ hs hℓ hne hK p hpsℓ data
  have hx : IsIntegral (eE K s ℓ) (jqNModC K s) := ⟨P, hmonic, by rwa [Polynomial.aeval_def] at hroot⟩
  have hmin : P = minpoly (eE K s ℓ) (jqNModC K s) := minpoly.eq_of_irreducible_of_monic hirr hroot hmonic
  rw [relfinrank_eq_natDegree_minpoly (eE K s ℓ) (kPrime K s ℓ) (jqNModC K s) hx
    (eE_le_kPrime K s ℓ p hps) (kPrime_eq_adjoin_eE K s ℓ p hps), ← hmin, hP,
    fibreAt_natDegree data.monic, data.natDegree_eq]

theorem jqModC_mem_kPrime (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ) (hK : ((s * ℓ : ℕ) : K) ≠ 0) :
    jqModC K ∈ kPrime K s ℓ := by

  let p := ringChar K
  haveI : CharP K p := ringChar.charP K
  have hpsℓ : ¬ p ∣ s * ℓ := fun h => hK ((CharP.cast_eq_zero_iff K p _).mpr h)
  have hps : ¬ p ∣ s := fun h => hpsℓ (dvd_mul_of_dvd_left h ℓ)

  have hEL : relfinrank (eE K s ℓ) (bigL K s ℓ) = dedekindPsi ℓ := (relfinrank_fS_and_eE K s ℓ hs hℓ hne hK).2
  have hEK : relfinrank (eE K s ℓ) (kPrime K s ℓ) = dedekindPsi ℓ :=
    relfinrank_eE_kPrime K s ℓ hs hℓ hne hK p hpsℓ hps
  have hmul := relfinrank_mul_relfinrank (eE_le_kPrime K s ℓ p hps) (kPrime_le_bigL K s ℓ)
  rw [hEL, hEK] at hmul
  have hψ : 0 < dedekindPsi ℓ := dedekindPsi_pos ℓ (NeZero.ne ℓ)
  have hone : relfinrank (kPrime K s ℓ) (bigL K s ℓ) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hψ
    rw [hmul, Nat.mul_one]
  have hle : bigL K s ℓ ≤ kPrime K s ℓ := (relfinrank_eq_one_iff).mp hone
  exact hle (jqModC_mem_full K (s * ℓ))

end Modular

end JGenDual

end

open ModularCurve in
theorem solution (K : Type*) [Field K] (s ℓ : ℕ)
    [NeZero s] [NeZero ℓ] [NeZero (s * ℓ)] (hs : s.Prime) (hℓ : ℓ.Prime) (hne : s ≠ ℓ)
    (hK : ((s * ℓ : ℕ) : K) ≠ 0) :
    jqModC K ∈ IntermediateField.adjoin K
      ({jqNModC K s, jqNModC K ℓ, jqNModC K (s * ℓ)} : Set (LaurentSeries K)) :=
  JGenDual.jqModC_mem_kPrime K s ℓ hs hℓ hne hK

end S_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne
end P2MW
export P2MW.S_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne (solution)
