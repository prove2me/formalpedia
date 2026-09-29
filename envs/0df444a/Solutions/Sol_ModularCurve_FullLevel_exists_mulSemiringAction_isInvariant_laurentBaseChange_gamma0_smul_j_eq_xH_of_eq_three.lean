-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/04eb623c-f847-5c95-842a-9165cbc06ad1

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace GDAux

open IntermediateField

theorem relfinrank_lift_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (L : IntermediateField K F) :
    (IntermediateField.lift L).relfinrank F = Module.finrank L F := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (IntermediateField.lift_le L)]
  let i : L ≃+* (IntermediateField.lift L) := (IntermediateField.liftAlgEquiv L).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars (IntermediateField.lift_le L)) := RingEquiv.refl _
  refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  ext a
  rfl

open scoped MatrixGroups in

theorem gamma0Units_surjective' (M : ℕ) [NeZero M] : Function.Surjective (CohCarrier.gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, CongruenceSubgroup.Gamma0Map]
  simp [γ]

open scoped MatrixGroups in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem diamond (K : Type) [Field K] [CharZero K] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →* (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))),
      Finite ↥ρ.range ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))), (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) → ρ γ x = x) ∧
      (∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)), (∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ x = x) → (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by
  classical
  have hΓ : CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H
  have hb0H : (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) ≤ (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) := ModularCurve.qExpFunctionFieldC_mono K hΓ
  obtain ⟨ρ, hρfix, hρker⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_apply_eq_one_iff_of_charZero K M H

  have hker : ρ.ker = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).comap (CohCarrier.gamma0Units M) := by
    ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact hρker γ
  have hidx : ρ.ker.index = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [hker]; exact Subgroup.index_comap_of_surjective _ (gamma0Units_surjective' M)
  haveI : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).FiniteIndex := inferInstance
  haveI : ρ.ker.FiniteIndex := ⟨by rw [hidx]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : Finite (↥(CongruenceSubgroup.Gamma0 M) ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  haveI hfinr : Finite ρ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  haveI : Fintype ρ.range := Fintype.ofFinite _
  have hcard : Fintype.card ρ.range = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, hidx]

  have hartin : Module.finrank (IntermediateField.fixedField ρ.range) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) = Fintype.card ρ.range :=
    FixedPoints.finrank_eq_card _ _
  have hL : IntermediateField.lift (IntermediateField.fixedField ρ.range) ≤ (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) := IntermediateField.lift_le _
  have h0L : (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) ≤ IntermediateField.lift (IntermediateField.fixedField ρ.range) := by
    intro x hx
    have hxH : x ∈ (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) := hb0H hx
    have hfx : (⟨x, hxH⟩ : (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))) ∈ IntermediateField.fixedField ρ.range := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨γ, rfl⟩
      exact hρfix γ ⟨x, hxH⟩ hx
    exact (IntermediateField.mem_lift ⟨x, hxH⟩).mpr hfx
  have eP : (IntermediateField.lift (IntermediateField.fixedField ρ.range)).relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) =
      (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    (relfinrank_lift_eq_finrank _ _).trans (hartin.trans hcard)
  have eQ : (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)).relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)) = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero K M H
  have hmul := IntermediateField.relfinrank_mul_relfinrank h0L hL
  rw [eP, eQ] at hmul
  have hone : (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)).relfinrank (IntermediateField.lift (IntermediateField.fixedField ρ.range)) = 1 := by
    have hne : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have := hmul
    nth_rewrite 2 [← one_mul ((H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index)] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  have hLe : IntermediateField.lift (IntermediateField.fixedField ρ.range) ≤ (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) :=
    IntermediateField.relfinrank_eq_one_iff.mp hone
  refine ⟨ρ, hfinr, hρfix, fun x hx => ?_⟩
  have hmem : x ∈ IntermediateField.fixedField ρ.range := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, rfl⟩
    exact hx γ
  exact hLe ((IntermediateField.mem_lift x).mpr hmem)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem core (L : Type) [Field L] [CharZero L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (E E₂ : IntermediateField L (LaurentSeries L))
    (hE : E = ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))
    (hE₂ : E₂ = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M))
    (j : ↥E) (hj : ((j : LaurentSeries L)) ∈ E₂) (hle : E₂ ≤ E) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥E),
      (letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
       SMulCommClass G ↥E₂ ↥E ∧ Algebra.IsInvariant ↥E₂ ↥E G) ∧
      SMulCommClass G L ↥E ∧ FaithfulSMul G ↥E ∧
      (∀ g : G, g • j = j) := by
  classical
  subst hE hE₂
  obtain ⟨ρ, hfin, hfix, hinv⟩ := diamond L M H
  haveI := hfin
  haveI : Fintype ↥ρ.range := Fintype.ofFinite _
  letI act : MulSemiringAction ↥ρ.range ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) :=
    MulSemiringAction.compHom _ ρ.range.subtype
  have hsmul : ∀ (g : ↥ρ.range) (x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))),
      g • x = (g : _ ≃ₐ[L] _) x := fun _ _ => rfl
  have hfix' : ∀ (g : ↥ρ.range) (x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))),
      (x : LaurentSeries L) ∈ ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M) → g • x = x := by
    rintro ⟨_, ⟨γ, rfl⟩⟩ x hx
    exact hfix γ x hx
  refine ⟨↥ρ.range, inferInstance, inferInstance, act, ?_, ?_, ?_, ?_⟩
  · letI instA := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    have hfixK₂ : ∀ (g : ↥ρ.range) (k : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M))),
        g • (IntermediateField.inclusion hle k) = IntermediateField.inclusion hle k :=
      fun g k => hfix' g _ (by simp)
    refine ⟨⟨fun g k x => ?_⟩, ⟨fun b hb => ?_⟩⟩
    · show g • (IntermediateField.inclusion hle k * x) = IntermediateField.inclusion hle k * g • x
      rw [smul_mul', hfixK₂]
    · have hb' : ∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ b = b := fun γ => by
        have := hb ⟨ρ γ, ⟨γ, rfl⟩⟩
        exact this
      refine ⟨⟨(b : LaurentSeries L), hinv b hb'⟩, ?_⟩
      · apply Subtype.ext
        show (((⟨(b : LaurentSeries L), hinv b hb'⟩ : ↥(ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M))) :
          LaurentSeries L)) = (b : LaurentSeries L)
        rfl
  · exact ⟨fun g c x => (g : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) ≃ₐ[L]
      ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))).toLinearEquiv.map_smul c x⟩
  · refine ⟨fun {g₁} {g₂} h => ?_⟩
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    exact h x
  · intro g
    exact hfix' g j hj

end GDAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')))
    (hle : K₂ ≤ K) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥K),
      (letI := (IntermediateField.inclusion hle).toRingHom.toAlgebra
       SMulCommClass G ↥K₂ ↥K ∧ Algebra.IsInvariant ↥K₂ ↥K G) ∧
      SMulCommClass G L ↥K ∧ FaithfulSMul G ↥K ∧
      (∀ g : G, g • j = j) := by
  have eK : ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) =
      ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) :=
    ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq L _
  have eK₂ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) =
      ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) := by
    rw [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull,
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq]
  subst hK hK₂
  have hjmem : ((j : LaurentSeries L)) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) := by
    rw [hj]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.modularFunctionField_le_full _ (ModularCurve.jq_mem _))
  exact GDAux.core L (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') _ _ eK eK₂ j hjmem hle

end S_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_xH_of_eq_three (solution)
